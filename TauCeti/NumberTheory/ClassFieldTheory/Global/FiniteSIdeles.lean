/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.SemilocalUnits
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.FiniteSIdeles
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Pi

/-!
# The Herbrand quotient of the finite `S`-ideles

Let `L/K` be a cyclic extension of number fields and `S` a finite set of finite places of `K`
containing every place ramified in `L`. The finite `S`-ideles of `L` are, as a representation of
`Gal(L/K)`, the product of the semi-local factors `∏_{w ∣ v} L_wˣ` for `v ∈ S` and
`∏_{w ∣ v} 𝒪_wˣ` for `v ∉ S` (`TauCeti.finiteSIdelesPiIso`). The factors of the second kind have
no Tate cohomology, because `v` is unramified, and a factor of the first kind has Herbrand quotient
the local degree `[L_w : K_v]`. Since the Herbrand quotient of a product is the product of the
Herbrand quotients of the factors outside a cohomologically trivial part
(`TauCeti.TateCohomology.herbrandQuotient_pi`), the finite `S`-ideles have Herbrand quotient

```text
h(I_{L,S}^f) = ∏_{v ∈ S} [L_w : K_v].
```

Together with the factors at the infinite places, this is the Herbrand quotient of the `S`-ideles
`I_{L,S}`, the idelic half of the computation `h(C_L) = [L : K]` of the Herbrand quotient of the
idele classes, from which the first fundamental inequality for cyclic extensions follows.

## Main results

* `TauCeti.ClassFieldTheory.herbrandQuotient_finiteSIdelesRep`: for `L/K` cyclic and unramified
  outside `S`, `h(I_{L,S}^f) = ∏_{v ∈ S} [L_w : K_v]`, for any choice of places `w` above the
  places of `S`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Lemma 2.4 and Proposition 2.7.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §§6–7.
-/

public section
noncomputable section

open CategoryTheory IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Module
open scoped AdicCompletionExtension

namespace TauCeti.ClassFieldTheory

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

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
  have hzero (v : HeightOneSpectrum (𝒪 K)) (hv : v ∉ S) (n : ℤ) :
      Subsingleton (tateCohomology (semilocalIntegralUnitsRep L v) n) := by
    obtain ⟨w', rfl⟩ := under_surjective (𝒪 K) (𝒪 L) v
    have := hS w' hv
    exact ModuleCat.subsingleton_of_isZero
      (isZero_tateCohomology_semilocalIntegralUnitsRep (w'.under (𝒪 K)) w' n)
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

end TauCeti.ClassFieldTheory
