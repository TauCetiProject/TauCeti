/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.SemilocalUnits
public import TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteSIdeles
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Pi

/-!
# The Tate cohomology of the finite `S`-ideles

Let `L/K` be a cyclic extension of number fields and `S` a finite set of finite places of `K`
containing every place ramified in `L`. The finite `S`-ideles of `L` are, as a representation of
`Gal(L/K)`, the product of the semi-local factors `∏_{w ∣ v} L_wˣ` for `v ∈ S` and
`∏_{w ∣ v} 𝒪_wˣ` for `v ∉ S` (`TauCeti.finiteSIdelesPiIso`). The factors of the second kind have
no Tate cohomology, because `v` is unramified. Since Tate cohomology commutes with products
(`TauCeti.TateCohomology.linearEquivPi`), the Tate cohomology of the finite `S`-ideles is, in every
degree,

```text
H-hat^n(Gal(L/K), I_{L,S}^f) ≃ ∏_{v ∈ S} H-hat^n(Gal(L/K), (K_v ⊗[K] L)ˣ),
```

and by Shapiro's lemma each factor is `H-hat^n(Gal(L_w/K_v), L_wˣ)` for a place `w` above `v`
(`semilocalUnitsTateCohomologyIso`). In degree `2` this is the finite part of the description of
`H²(Gal(L/K), I_L)` by the local Brauer groups `Br(L_w/K_v)` (Milne, *Class Field Theory*, VII,
Proposition 2.5), through which the local invariants of an idele class are read.

A factor of the first kind has Herbrand quotient the local degree `[L_w : K_v]`, and the Herbrand
quotient of a product is the product of the Herbrand quotients of the factors outside a
cohomologically trivial part (`TauCeti.TateCohomology.herbrandQuotient_pi`), so

```text
h(I_{L,S}^f) = ∏_{v ∈ S} [L_w : K_v].
```

Together with the factors at the infinite places, this is the Herbrand quotient of the `S`-ideles
`I_{L,S}`, the idelic half of the computation `h(C_L) = [L : K]` of the Herbrand quotient of the
idele classes, from which the first fundamental inequality for cyclic extensions follows.

## Main definitions

* `TauCeti.ClassFieldTheory.placeAbove`: a choice of a place of `L` above each place of `S`.
* `TauCeti.ClassFieldTheory.finiteSIdelesTateCohomologyEquiv`: for `L/K` cyclic and unramified
  outside `S`, `H-hat^n(Gal(L/K), I_{L,S}^f) ≃ ∏_{v ∈ S} H-hat^n(Gal(L/K), (K_v ⊗[K] L)ˣ)`.

## Main results

* `TauCeti.ClassFieldTheory.finiteSIdelesTateCohomologyEquiv_apply`: its component at `v ∈ S` is
  induced by the semi-local component at `v`.
* `TauCeti.ClassFieldTheory.herbrandQuotient_finiteSIdelesRep`: for `L/K` cyclic and unramified
  outside `S`, `h(I_{L,S}^f) = ∏_{v ∈ S} [L_w : K_v]`, for any choice of places `w` above the
  places of `S`.
* `TauCeti.ClassFieldTheory.finite_tateCohomology_finiteSIdelesRep`: the Tate cohomology of the
  finite `S`-ideles is finite in degrees `0` and `-1`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Lemma 2.4 and Proposition 2.7.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §§6–7.
-/

public section
noncomputable section

open CategoryTheory Limits IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Module
open scoped AdicCompletionExtension

namespace TauCeti.ClassFieldTheory

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

omit [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] in
variable (L) in
/-- A choice of a place of `L` above each place of a finite set `S` of finite places of `K`. -/
def placeAbove (S : Finset (HeightOneSpectrum (𝒪 K))) (v : S) :
    {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.1.asIdeal} :=
  have hw : ∃ w : HeightOneSpectrum (𝒪 L), w.asIdeal.LiesOver v.1.asIdeal := by
    obtain ⟨w, hw⟩ := under_surjective (𝒪 K) (𝒪 L) v.1
    exact ⟨w, ⟨congrArg HeightOneSpectrum.asIdeal hw.symm⟩⟩
  ⟨hw.choose, hw.choose_spec⟩

/-- The integral semi-local units at a place `v ∉ S` have no Tate cohomology when `L/K` is
unramified outside `S`. -/
private theorem isZero_tateCohomology_semilocalIntegralUnitsRep_of_notMem
    {S : Finset (HeightOneSpectrum (𝒪 K))}
    (hS : ∀ w : HeightOneSpectrum (𝒪 L), w.under (𝒪 K) ∉ S →
      Algebra.IsUnramifiedAt (𝒪 K) w.asIdeal)
    {v : HeightOneSpectrum (𝒪 K)} (hv : v ∉ S) (n : ℤ) :
    IsZero (tateCohomology (semilocalIntegralUnitsRep L v) n) := by
  obtain ⟨w', rfl⟩ := under_surjective (𝒪 K) (𝒪 L) v
  have := hS w' hv
  exact isZero_tateCohomology_semilocalIntegralUnitsRep (w'.under (𝒪 K)) w' n

/-- **The Tate cohomology of the finite `S`-ideles is the product of the semi-local Tate
cohomologies at the places of `S`.** For a cyclic extension `L/K` of number fields and a finite set
`S` of finite places of `K` outside which `L/K` is unramified,

`H-hat^n(Gal(L/K), I_{L,S}^f) ≃ ∏_{v ∈ S} H-hat^n(Gal(L/K), (K_v ⊗[K] L)ˣ)`

in every degree `n : ℤ`, the component at `v` being induced by the semi-local component at `v`
(`finiteSIdelesTateCohomologyEquiv_apply`). The factors at the places outside `S` drop out, having
no Tate cohomology. By Shapiro's lemma (`semilocalUnitsTateCohomologyIso`) each factor is the Tate
cohomology `H-hat^n(Gal(L_w/K_v), L_wˣ)` of the completion at a place `w` above `v`. -/
def finiteSIdelesTateCohomologyEquiv (S : Finset (HeightOneSpectrum (𝒪 K)))
    (hS : ∀ w : HeightOneSpectrum (𝒪 L), w.under (𝒪 K) ∉ S →
      Algebra.IsUnramifiedAt (𝒪 K) w.asIdeal) (n : ℤ) :
    tateCohomology (finiteSIdelesRep L S) n ≃+
      ∀ v : S, tateCohomology (semilocalUnitsRep L v.1) n :=
  -- the factors at the places outside `S` vanish, so dropping them is an isomorphism
  have (v : {v : HeightOneSpectrum (𝒪 K) // v ∉ S}) : Subsingleton (tateCohomology
      (Sum.elim (fun v : S ↦ semilocalUnitsRep L v.1)
        (fun v : {v : HeightOneSpectrum (𝒪 K) // v ∉ S} ↦ semilocalIntegralUnitsRep L v.1)
        (Sum.inr v)) n) :=
    ModuleCat.subsingleton_of_isZero
      (isZero_tateCohomology_semilocalIntegralUnitsRep_of_notMem hS v.2 n)
  have : Unique (∀ v : {v : HeightOneSpectrum (𝒪 K) // v ∉ S},
      tateCohomology (Sum.elim (fun v : S ↦ semilocalUnitsRep L v.1)
        (fun v : {v : HeightOneSpectrum (𝒪 K) // v ∉ S} ↦ semilocalIntegralUnitsRep L v.1)
        (Sum.inr v)) n) :=
    { default := 0, uniq := fun _ ↦ Subsingleton.elim _ _ }
  let e := TateCohomology.linearEquivPi (Sum.elim (fun v : S ↦ semilocalUnitsRep L v.1)
    (fun v : {v : HeightOneSpectrum (𝒪 K) // v ∉ S} ↦ semilocalIntegralUnitsRep L v.1)) n
  ((tateCohomologyFunctor n).mapIso (finiteSIdelesPiIso L S)).toLinearEquiv.toAddEquiv.trans <|
    { e.toEquiv.trans ((Equiv.sumPiEquivProdPi _).trans (Equiv.prodUnique _ _)) with
      map_add' := fun x y ↦ funext fun v ↦ congrFun (map_add e x y) (Sum.inl v) }

/-- The component at `v ∈ S` of `finiteSIdelesTateCohomologyEquiv` is induced by the semi-local
component at `v`, the factor at `v` of `finiteSIdelesPiIso`. -/
@[simp]
theorem finiteSIdelesTateCohomologyEquiv_apply (S : Finset (HeightOneSpectrum (𝒪 K)))
    (hS : ∀ w : HeightOneSpectrum (𝒪 L), w.under (𝒪 K) ∉ S →
      Algebra.IsUnramifiedAt (𝒪 K) w.asIdeal) (n : ℤ)
    (x : tateCohomology (finiteSIdelesRep L S) n) (v : S) :
    finiteSIdelesTateCohomologyEquiv S hS n x v =
      ((tateCohomologyFunctor n).map
        ((finiteSIdelesPiIso L S).hom ≫ Rep.piProj _ (Sum.inl v))).hom x := by
  rw [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    ← TateCohomology.linearEquivPi_apply]
  -- the definition of `finiteSIdelesTateCohomologyEquiv`, read at the component `Sum.inl v`
  rfl

/-- **The Herbrand quotient of the finite `S`-ideles.** For a cyclic extension `L/K` of number
fields and a finite set `S` of finite places of `K` outside which `L/K` is unramified, the finite
`S`-ideles of `L` have Herbrand quotient `∏_{v ∈ S} [L_w : K_v]` as a representation of
`Gal(L/K)`, for any choice of a place `w` of `L` above each `v ∈ S`. -/
theorem herbrandQuotient_finiteSIdelesRep (S : Finset (HeightOneSpectrum (𝒪 K)))
    (hS : ∀ w : HeightOneSpectrum (𝒪 L), w.under (𝒪 K) ∉ S →
      Algebra.IsUnramifiedAt (𝒪 K) w.asIdeal)
    (w : ∀ v : S, {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.1.asIdeal}) :
    TateCohomology.herbrandQuotient (finiteSIdelesRep L S) =
      ∏ v : S, (finrank (v.1.adicCompletion K) ((w v).1.adicCompletion L) : ℚ) := by
  -- the integral factors at the places outside `S` have no Tate cohomology
  have hzero (v : HeightOneSpectrum (𝒪 K)) (hv : v ∉ S) (n : ℤ) :=
    ModuleCat.subsingleton_of_isZero
      (isZero_tateCohomology_semilocalIntegralUnitsRep_of_notMem hS hv n)
  have hS' (i : S ⊕ {v : HeightOneSpectrum (𝒪 K) // v ∉ S})
      (hi : i ∉ Finset.univ.map (Function.Embedding.inl)) :
      ∃ v : {v : HeightOneSpectrum (𝒪 K) // v ∉ S}, i = Sum.inr v := by
    rcases i with v | v
    · exact absurd (Finset.mem_map_of_mem _ (Finset.mem_univ v)) hi
    · exact ⟨v, rfl⟩
  rw [TateCohomology.herbrandQuotient_eq_of_iso (finiteSIdelesPiIso L S),
    TateCohomology.herbrandQuotient_pi _ (Finset.univ.map Function.Embedding.inl)
      (fun i hi ↦ by obtain ⟨v, rfl⟩ := hS' i hi; exact hzero v.1 v.2 0)
      (fun i hi ↦ by obtain ⟨v, rfl⟩ := hS' i hi; exact hzero v.1 v.2 (-1)),
    Finset.prod_map]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have := (w v).2
  exact herbrandQuotient_semilocalUnitsRep v.1 (w v).1

/-- For a cyclic extension `L/K` of number fields unramified outside a finite set `S` of finite
places of `K`, the Herbrand quotient of the finite `S`-ideles is nonzero: by
`herbrandQuotient_finiteSIdelesRep` it is a product of local degrees. -/
theorem herbrandQuotient_finiteSIdelesRep_ne_zero (S : Finset (HeightOneSpectrum (𝒪 K)))
    (hS : ∀ w : HeightOneSpectrum (𝒪 L), w.under (𝒪 K) ∉ S →
      Algebra.IsUnramifiedAt (𝒪 K) w.asIdeal) :
    TateCohomology.herbrandQuotient (finiteSIdelesRep L S) ≠ 0 := by
  rw [herbrandQuotient_finiteSIdelesRep S hS (placeAbove L S), Finset.prod_ne_zero_iff]
  intro v _
  have := (placeAbove L S v).2
  rw [Nat.cast_ne_zero, ← card_stabilizer_eq_finrank_adicCompletion v.1]
  exact Nat.card_pos.ne'

/-- **The Tate cohomology of the finite `S`-ideles is finite** in degrees `0` and `-1`, for a
cyclic extension `L/K` of number fields unramified outside a finite set `S` of finite places of
`K`. -/
theorem finite_tateCohomology_finiteSIdelesRep (S : Finset (HeightOneSpectrum (𝒪 K)))
    (hS : ∀ w : HeightOneSpectrum (𝒪 L), w.under (𝒪 K) ∉ S →
      Algebra.IsUnramifiedAt (𝒪 K) w.asIdeal) :
    Finite (tateCohomology (finiteSIdelesRep L S) 0) ∧
      Finite (tateCohomology (finiteSIdelesRep L S) (-1)) :=
  TateCohomology.finite_tateCohomology_of_herbrandQuotient_ne_zero
    (herbrandQuotient_finiteSIdelesRep_ne_zero S hS)

end TauCeti.ClassFieldTheory
