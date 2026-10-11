/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.FiniteSIdeles
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.SIdeles
public import TauCeti.NumberTheory.ClassFieldTheory.Global.InfiniteIdeles

/-!
# The Herbrand quotient of the `S`-ideles

Let `L/K` be an extension of number fields and `S` a finite set of finite places of `K`. An
`S`-idele of `L` is an idele whose finite part is a finite `S`-idele, with arbitrary infinite
part, so the `S`-ideles split as `I_{L,S} = L_∞ˣ × I_{L,S}^f`. As representations of `Aut(L/K)`
this is the short exact sequence

```text
0 → L_∞ˣ → I_{L,S} → I_{L,S}^f → 0
```

(`sIdelesInfiniteShortComplex_shortExact`), given by the infinite ideles and the finite part.

For a cyclic extension unramified outside `S`, the Herbrand quotient is multiplicative along it,
so the archimedean computation `herbrandQuotient_infiniteIdelesRep` and the finite one
`herbrandQuotient_finiteSIdelesRep` combine to

```text
h(I_{L,S}) = ∏_{v ∣ ∞} [L_w : K_v] · ∏_{v ∈ S} [L_w : K_v]
```

(`herbrandQuotient_sIdelesRep`). This is also the Herbrand quotient of the permutation lattice on
the infinite places of `L` and the primes above `S`
(`herbrandQuotient_sIdelesRep_eq_herbrandQuotient_ofMulAction`), the lattice with which the
logarithmic embedding compares the `S`-units. In the formula
`h(C_L) = h(I_{L,S}) / h(U_{L,S})` of `herbrandQuotient_ideleClassRep`, it is the idelic factor
of the computation `h(C_L) = [L : K]`, from which the first fundamental inequality for cyclic
extensions follows.

## Main definitions

* `TauCeti.ClassFieldTheory.sIdelesInfiniteShortComplex L S`: the sequence
  `L_∞ˣ → I_{L,S} → I_{L,S}^f`.

## Main results

* `TauCeti.ClassFieldTheory.sIdelesInfiniteShortComplex_shortExact`: the sequence is short exact.
* `TauCeti.ClassFieldTheory.herbrandQuotient_sIdelesRep`: for `L/K` cyclic and unramified outside
  `S`, `h(I_{L,S})` is the product of the local degrees at the infinite places and at `S`.
* `TauCeti.ClassFieldTheory.herbrandQuotient_sIdelesRep_eq_herbrandQuotient_ofMulAction`: it is
  the Herbrand quotient of the permutation lattice on the infinite places and the primes above
  `S`.
* `TauCeti.ClassFieldTheory.finite_tateCohomology_sIdelesRep`: the Tate cohomology of the
  `S`-ideles is finite in degrees `0` and `-1`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §2 and the proof of Theorem 4.3.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §§6–7.
-/

public section

noncomputable section

open CategoryTheory IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Module
open scoped AdeleGaloisAction

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

variable {K : Type} [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

/-! ### The infinite ideles and the finite part -/

/-- The idele `(x, 1)`, as an `S`-idele. -/
private def infiniteIdelesToSIdelesHom : (InfiniteAdeleRing L)ˣ →* sIdeles (K := K) L S :=
  (IdeleGroup.ofInfiniteIdele (𝓞 L) L).codRestrict _ (ofInfiniteIdele_mem_sIdeles _)

omit [NumberField K] in
private theorem coe_infiniteIdelesToSIdelesHom (x : (InfiniteAdeleRing L)ˣ) :
    ((infiniteIdelesToSIdelesHom L S x : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L) =
      ((x : InfiniteAdeleRing L), (1 : FiniteAdeleRing (𝓞 L) L)) :=
  IdeleGroup.coe_ofInfiniteIdele _ _ x

omit [NumberField K] in
private theorem fst_infiniteIdelesToSIdelesHom (x : (InfiniteAdeleRing L)ˣ) :
    ((infiniteIdelesToSIdelesHom L S x : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L).1 = x := by
  rw [coe_infiniteIdelesToSIdelesHom]

omit [NumberField K] in
private theorem snd_infiniteIdelesToSIdelesHom (x : (InfiniteAdeleRing L)ˣ) :
    ((infiniteIdelesToSIdelesHom L S x : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L).2 = 1 := by
  rw [coe_infiniteIdelesToSIdelesHom]

private theorem infiniteIdelesToSIdelesHom_smul (σ : L ≃ₐ[K] L) (x : (InfiniteAdeleRing L)ˣ) :
    infiniteIdelesToSIdelesHom L S (σ • x) = σ • infiniteIdelesToSIdelesHom L S x := by
  refine Subtype.ext <| Units.ext <| Prod.ext ?_ ?_
  · simp only [coe_smul_sIdeles, coe_idele_smul, adeleGaloisAction_fst,
      fst_infiniteIdelesToSIdelesHom, coe_infiniteIdele_smul]
  · simp only [coe_smul_sIdeles, coe_idele_smul, adeleGaloisAction_snd,
      snd_infiniteIdelesToSIdelesHom, map_one]

/-- The finite part of an `S`-idele, a finite `S`-idele. -/
private def sIdelesToFiniteSIdelesHom : sIdeles (K := K) L S →* finiteSIdeles L S :=
  ((IdeleGroup.toFiniteIdele (𝓞 L) L).comp (sIdeles L _).subtype).codRestrict _ fun x ↦
    toFiniteIdele_mem_finiteSIdeles_iff.2 x.2

private theorem coe_sIdelesToFiniteSIdelesHom (x : sIdeles (K := K) L S) :
    ((sIdelesToFiniteSIdelesHom L S x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      ((x : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L).2 :=
  IdeleGroup.coe_toFiniteIdele _ _ _

private theorem sIdelesToFiniteSIdelesHom_smul (σ : L ≃ₐ[K] L) (x : sIdeles (K := K) L S) :
    sIdelesToFiniteSIdelesHom L S (σ • x) = σ • sIdelesToFiniteSIdelesHom L S x := by
  refine Subtype.ext <| Units.ext ?_
  simp only [coe_sIdelesToFiniteSIdelesHom, coe_smul_finiteSIdeles, Units.coe_map,
    MonoidHom.coe_ofClass, coe_smul_sIdeles, coe_idele_smul, adeleGaloisAction_snd]

/-- An `S`-idele with trivial finite part is the idele of its infinite part. -/
private theorem sIdelesToFiniteSIdelesHom_eq_one_iff (x : sIdeles (K := K) L S) :
    sIdelesToFiniteSIdelesHom L S x = 1 ↔ ∃ y, infiniteIdelesToSIdelesHom L S y = x := by
  refine ⟨fun hx ↦ ⟨Units.map (MonoidHom.fst _ _) (x : IdeleGroup (𝓞 L) L), ?_⟩, ?_⟩
  · have hx := congrArg (fun u : finiteSIdeles L S ↦ ((u : (FiniteAdeleRing (𝓞 L) L)ˣ) :
      FiniteAdeleRing (𝓞 L) L)) hx
    rw [coe_sIdelesToFiniteSIdelesHom] at hx
    refine Subtype.ext <| Units.ext ?_
    rw [coe_infiniteIdelesToSIdelesHom]
    -- `Units.map (MonoidHom.fst _ _)` takes the infinite component of the underlying adele by
    -- definition, as `IdeleGroup.toFiniteIdele` takes the finite one (`coe_toFiniteIdele`); the
    -- product structure `MonoidHom.fst` expects is `AdeleRing` only up to unfolding, so
    -- `Units.coe_map` does not rewrite here.
    exact Prod.ext (rfl) hx.symm
  · rintro ⟨y, rfl⟩
    exact Subtype.ext <| Units.ext <| by
      simp only [coe_sIdelesToFiniteSIdelesHom, coe_infiniteIdelesToSIdelesHom,
        OneMemClass.coe_one, Units.val_one]

omit [NumberField K] in
private theorem infiniteIdelesToSIdelesHom_injective :
    Function.Injective (infiniteIdelesToSIdelesHom L S) := fun x y hxy ↦ Units.ext <| by
  simpa only [coe_infiniteIdelesToSIdelesHom] using
    congrArg (fun z : sIdeles (K := K) L S ↦ ((z : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L).1) hxy

private theorem sIdelesToFiniteSIdelesHom_surjective :
    Function.Surjective (sIdelesToFiniteSIdelesHom L S) := fun y ↦
  ⟨⟨IdeleGroup.ofFiniteIdele (𝓞 L) L y,
      toFiniteIdele_mem_finiteSIdeles_iff.1 (by simp)⟩,
    Subtype.ext (IdeleGroup.toFiniteIdele_ofFiniteIdele _ _ _)⟩

/-- The inclusion `L_∞ˣ → I_{L,S}` of the infinite ideles, with all finite components `1`, as a
morphism of representations of `Aut(L/K)`. -/
def infiniteIdelesToSIdeles : infiniteIdelesRep K L ⟶ sIdelesRep (K := K) L S :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (infiniteIdelesToSIdelesHom L S).toAdditive.toIntLinearMap fun σ x ↦
      congrArg Additive.ofMul (infiniteIdelesToSIdelesHom_smul L S σ x.toMul)

/-- `infiniteIdelesToSIdeles` sends an infinite idele `x` to the idele `(x, 1)`. -/
@[simp]
theorem infiniteIdelesToSIdeles_hom_apply (x : Additive (InfiniteAdeleRing L)ˣ) :
    (infiniteIdelesToSIdeles L S).hom x = Additive.ofMul
      ⟨IdeleGroup.ofInfiniteIdele (𝓞 L) L x.toMul, ofInfiniteIdele_mem_sIdeles _ x.toMul⟩ :=
  (rfl)

/-- The finite part `I_{L,S} → I_{L,S}^f` of an `S`-idele, as a morphism of representations of
`Aut(L/K)`. -/
def sIdelesToFiniteSIdeles : sIdelesRep (K := K) L S ⟶ finiteSIdelesRep L S :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (sIdelesToFiniteSIdelesHom L S).toAdditive.toIntLinearMap fun σ x ↦
      congrArg Additive.ofMul (sIdelesToFiniteSIdelesHom_smul L S σ x.toMul)

/-- `sIdelesToFiniteSIdeles` sends an `S`-idele to its finite part. -/
@[simp]
theorem sIdelesToFiniteSIdeles_hom_apply (x : Additive (sIdeles (K := K) L S)) :
    (sIdelesToFiniteSIdeles L S).hom x = Additive.ofMul
      ⟨IdeleGroup.toFiniteIdele (𝓞 L) L x.toMul, toFiniteIdele_mem_finiteSIdeles_iff.2 x.toMul.2⟩ :=
  (rfl)

/-- **The sequence `L_∞ˣ → I_{L,S} → I_{L,S}^f`** of representations of `Aut(L/K)`, given by the
infinite ideles and the finite part of an `S`-idele. -/
def sIdelesInfiniteShortComplex : ShortComplex (Rep ℤ (L ≃ₐ[K] L)) :=
  ShortComplex.mk (infiniteIdelesToSIdeles L S) (sIdelesToFiniteSIdeles L S) <| by
    ext x
    exact congrArg Additive.ofMul
      ((sIdelesToFiniteSIdelesHom_eq_one_iff L S _).2 ⟨x.toMul, rfl⟩)

/-- **The sequence `0 → L_∞ˣ → I_{L,S} → I_{L,S}^f → 0` is exact**: an `S`-idele is determined
by its infinite and finite parts, and those parts can be prescribed independently. -/
theorem sIdelesInfiniteShortComplex_shortExact : (sIdelesInfiniteShortComplex L S).ShortExact where
  exact := by
    rw [Rep.exact_iff_function_exact]
    intro (x : Additive (sIdeles (K := K) L S))
    refine ⟨fun hx ↦ ?_, ?_⟩
    · obtain ⟨y, hy⟩ := (sIdelesToFiniteSIdelesHom_eq_one_iff L S x.toMul).1
        (congrArg Additive.toMul hx)
      exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩
    · rintro ⟨y, rfl⟩
      exact congrArg Additive.ofMul
        ((sIdelesToFiniteSIdelesHom_eq_one_iff L S _).2 ⟨y.toMul, rfl⟩)
  mono_f := by
    rw [Rep.mono_iff_injective]
    intro x y hxy
    exact Additive.toMul.injective
      (infiniteIdelesToSIdelesHom_injective L S (congrArg Additive.toMul hxy))
  epi_g := by
    rw [Rep.epi_iff_surjective]
    intro y
    obtain ⟨x, hx⟩ := sIdelesToFiniteSIdelesHom_surjective L S y.toMul
    exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩

/-! ### The Herbrand quotient -/

section Herbrand

open scoped AdicCompletionExtension NumberField.LiesOver

variable [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

/-- A choice of a place of `L` above each place of `S`. -/
private def placeAbove (v : S) :
    {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.1.asIdeal} :=
  have hw : ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.1.asIdeal := by
    obtain ⟨w, hw⟩ := under_surjective (𝓞 K) (𝓞 L) v.1
    exact ⟨w, ⟨congrArg HeightOneSpectrum.asIdeal hw.symm⟩⟩
  ⟨hw.choose, hw.choose_spec⟩

variable {L S}

/-- The Herbrand quotient of the `S`-ideles is that of the infinite ideles times that of the
finite `S`-ideles. -/
private theorem herbrandQuotient_sIdelesRep_eq_mul
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
      Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    TateCohomology.herbrandQuotient (sIdelesRep (K := K) L S) =
      TateCohomology.herbrandQuotient (infiniteIdelesRep K L) *
        TateCohomology.herbrandQuotient (finiteSIdelesRep L S) := by
  -- The outer terms of `sIdelesInfiniteShortComplex L S` are `infiniteIdelesRep K L` and
  -- `finiteSIdelesRep L S` by definition, which instance search does not see through.
  have : Finite (tateCohomology (sIdelesInfiniteShortComplex L S).X₁ (-1)) :=
    finite_tateCohomology_infiniteIdelesRep.2
  have : Finite (tateCohomology (sIdelesInfiniteShortComplex L S).X₃ (-1)) :=
    (finite_tateCohomology_finiteSIdelesRep S hS).2
  exact TateCohomology.herbrandQuotient_eq_mul_of_shortExact
    (sIdelesInfiniteShortComplex_shortExact L S)

/-- **The Herbrand quotient of the `S`-ideles.** For a cyclic extension `L/K` of number fields and
a finite set `S` of finite places of `K` outside which `L/K` is unramified, the `S`-ideles of `L`
have Herbrand quotient `∏_{v ∣ ∞} [L_w : K_v] · ∏_{v ∈ S} [L_w : K_v]` as a representation of
`Gal(L/K)`, the first product running over the infinite places of `K`. The places `w` above each
`v` may be chosen arbitrarily. -/
theorem herbrandQuotient_sIdelesRep
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
      Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    (wInf : ∀ v : InfinitePlace K, {w : InfinitePlace L // w.LiesOver v})
    (w : ∀ v : S, {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.1.asIdeal}) :
    TateCohomology.herbrandQuotient (sIdelesRep (K := K) L S) =
      (∏ v, (finrank v.Completion (wInf v).1.Completion : ℚ)) *
        ∏ v : S, (finrank (v.1.adicCompletion K) ((w v).1.adicCompletion L) : ℚ) := by
  rw [herbrandQuotient_sIdelesRep_eq_mul hS, herbrandQuotient_infiniteIdelesRep wInf,
    herbrandQuotient_finiteSIdelesRep S hS w]

/-- **The `S`-ideles and the place lattice** have the same Herbrand quotient: for a cyclic
extension `L/K` of number fields unramified outside a finite set `S` of finite places of `K`,
`h(I_{L,S})` is the Herbrand quotient of the permutation lattice on the infinite places of `L` and
the primes of `L` above `S` (`herbrandQuotient_ofMulAction_places`). -/
theorem herbrandQuotient_sIdelesRep_eq_herbrandQuotient_ofMulAction
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
      Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    TateCohomology.herbrandQuotient (sIdelesRep (K := K) L S) =
      TateCohomology.herbrandQuotient (Rep.ofMulAction ℤ (L ≃ₐ[K] L)
        (InfinitePlace L ⊕ ↥(primesAbove (𝓞 K) (𝓞 L) ↑S))) := by
  classical
  rw [herbrandQuotient_sIdelesRep_eq_mul hS,
    herbrandQuotient_infiniteIdelesRep_eq_herbrandQuotient_ofMulAction,
    herbrandQuotient_ofMulAction_infinitePlace,
    herbrandQuotient_finiteSIdelesRep S hS (placeAbove L S),
    herbrandQuotient_ofMulAction_places S (placeAbove L S)]

/-- **The Tate cohomology of the `S`-ideles is finite** in degrees `0` and `-1`, for a cyclic
extension `L/K` of number fields unramified outside a finite set `S` of finite places of `K`: the
Herbrand quotient of the `S`-ideles is nonzero. -/
theorem finite_tateCohomology_sIdelesRep
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
      Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    Finite (tateCohomology (sIdelesRep (K := K) L S) 0) ∧
      Finite (tateCohomology (sIdelesRep (K := K) L S) (-1)) := by
  refine TateCohomology.finite_tateCohomology_of_herbrandQuotient_ne_zero ?_
  rw [herbrandQuotient_sIdelesRep_eq_mul hS]
  exact mul_ne_zero herbrandQuotient_infiniteIdelesRep_ne_zero
    (herbrandQuotient_finiteSIdelesRep_ne_zero S hS)

end Herbrand

end TauCeti.ClassFieldTheory
