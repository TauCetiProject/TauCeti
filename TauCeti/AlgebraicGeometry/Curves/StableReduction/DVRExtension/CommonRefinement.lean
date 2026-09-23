/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import TauCeti.Algebra.Algebra.Tower
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.DVRExtension.Tower
public import TauCeti.RingTheory.IntegralClosure.Map

/-!
# Common refinements of chosen finite DVR extensions

Two chosen finite extensions `E` and `F` of a discrete valuation ring `R` admit a *common
refinement*: a third chosen extension receiving maps from both, in the category
`TauCeti.FiniteDVRExtension.finiteDVRExtensionCategory`. In categorical language this is a
binary cofan on `E` and `F`; this file proves that one always exists.

A common field is easy: embed both extension fields into a separable closure of `K` and take the
Galois closure `N` of the compositum. The chosen places need more care. Lying over gives primes of
the integral closure of `R` in `N` above each chosen place separately, but they need not agree,
and one *cannot* in general keep both embeddings. For example, if `E` and `F` have the same split
quadratic extension field but different chosen places, one field embedding must be twisted.
Since `N / K` is Galois, its Galois group acts transitively on the primes above the closed point
of `R`, so one embedding can be twisted by an automorphism until the two primes coincide.
The common prime then restricts to both chosen places,
and `TauCeti.FiniteDVRExtension.Hom.ofAlgHom` upgrades the two field embeddings to maps of chosen
extensions.

## Main results

* `TauCeti.FiniteDVRExtension.exists_isPrime_liesOver_comap_mapIntegralClosure_eq`: the chosen
  place lifts along any embedding of the extension field.
* `TauCeti.FiniteDVRExtension.nonempty_binaryCofan_of_isGalois`: chosen extensions whose fields
  embed in a common finite Galois extension of `K` admit a common refinement with that field.
* `TauCeti.FiniteDVRExtension.nonempty_binaryCofan`: any two chosen extensions admit a common
  refinement.

## References

The Galois-twist argument is the standard proof that some place of a compositum restricts to any
prescribed pair of places, using transitivity of the Galois group on the places above a fixed one;
see J. Neukirch, *Algebraic Number Theory*, Chapter II, §§8–9.
-/

public section

universe u

namespace TauCeti

open CategoryTheory IsLocalRing

namespace FiniteDVRExtension

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] (E F : FiniteDVRExtension R K)

/-- The chosen place of a chosen extension lifts along any `K`-embedding of its extension field
into a further field `L` over `R`: some prime of the integral closure of `R` in `L` lies above the
closed point of `R` and restricts to the chosen place. -/
theorem exists_isPrime_liesOver_comap_mapIntegralClosure_eq (L : Type*) [Field L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] (k : E.extensionField →ₐ[K] L) :
    ∃ Q : Ideal (_root_.integralClosure R L), Q.IsPrime ∧ Q.LiesOver (maximalIdeal R) ∧
      Q.comap (k.restrictScalars R).mapIntegralClosure = E.prime := by
  obtain ⟨Q, hQ, hQE⟩ :=
    E.prime.exists_isPrime_comap_mapIntegralClosure_eq (k.restrictScalars R).injective
  refine ⟨Q, hQ, ⟨?_⟩, hQE⟩
  rw [← E.under_prime, ← hQE]
  exact Ideal.ext fun x => by simp only [Ideal.under_def, Ideal.mem_comap, AlgHom.commutes]

/-- Chosen extensions whose extension fields embed over `K` into a common finite Galois extension
`N` of `K` admit a common refinement, with extension field `N`: lying over gives a prime of the
integral closure of `R` in `N` above each chosen place, and Galois transitivity twists the second
embedding until the two primes agree. -/
theorem nonempty_binaryCofan_of_isGalois (N : Type u) [Field N] [Algebra K N]
    [FiniteDimensional K N] [IsGalois K N] [Algebra R N] [IsScalarTower R K N]
    (k₁ : E.extensionField →ₐ[K] N) (k₂ : F.extensionField →ₐ[K] N) :
    Nonempty (Limits.BinaryCofan E F) := by
  obtain ⟨Q₁, hQ₁, hQ₁R, hQ₁E⟩ := E.exists_isPrime_liesOver_comap_mapIntegralClosure_eq N k₁
  obtain ⟨Q₂, hQ₂, hQ₂R, hQ₂F⟩ := F.exists_isPrime_liesOver_comap_mapIntegralClosure_eq N k₂
  -- twist the second embedding by a Galois automorphism carrying `Q₂` to `Q₁`
  obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq R K N (_root_.integralClosure R N)
    (p := maximalIdeal R) ⟨hQ₁, hQ₁R⟩ ⟨hQ₂, hQ₂R⟩
  have hmap (x : _root_.integralClosure R N) :
      ((σ : N →ₐ[K] N).restrictScalars R).mapIntegralClosure x =
        galRestrict R K N (_root_.integralClosure R N) σ x :=
    Subtype.ext (algebraMap_galRestrict_apply R σ x).symm
  have hσ' : Q₁.comap ((σ : N →ₐ[K] N).restrictScalars R).mapIntegralClosure = Q₂ := by
    rw [← hσ]
    exact Ideal.ext fun x => by rw [Ideal.mem_comap, Ideal.mem_comap, hmap x]
  have hQ₁F : Q₁.comap (((σ : N →ₐ[K] N).comp k₂).restrictScalars R).mapIntegralClosure =
      F.prime := by
    rw [AlgHom.restrictScalars_comp, AlgHom.mapIntegralClosure_comp,
      ← Ideal.comap_comapₐ, hσ', hQ₂F]
  -- assemble the refinement on the chosen extension cut out by `Q₁`
  obtain ⟨e, he⟩ := exists_algEquiv_comap_prime_eq R K N Q₁
  refine ⟨Limits.BinaryCofan.mk (P := of R K N Q₁)
    (Hom.ofAlgHom ((e.symm : N →ₐ[K] _).comp k₁) ?_)
    (Hom.ofAlgHom ((e.symm : N →ₐ[K] _).comp ((σ : N →ₐ[K] N).comp k₂)) ?_)⟩
  · rw [AlgHom.restrictScalars_comp, AlgHom.mapIntegralClosure_comp,
      ← Ideal.comap_comapₐ, he, hQ₁E]
  · rw [AlgHom.restrictScalars_comp, AlgHom.mapIntegralClosure_comp,
      ← Ideal.comap_comapₐ, he, hQ₁F]

/-- Any two chosen finite extensions of a discrete valuation ring admit a common refinement: a
chosen extension receiving maps from both. Its extension field is the Galois closure of the
compositum of the two extension fields inside a separable closure of `K`. -/
theorem nonempty_binaryCofan : Nonempty (Limits.BinaryCofan E F) := by
  let Ω := separableClosure K (AlgebraicClosure K)
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  let j₁ : E.extensionField →ₐ[K] Ω := IsSepClosed.lift
  let j₂ : F.extensionField →ₐ[K] Ω := IsSepClosed.lift
  -- the finite Galois subextension of `Ω` generated by both images
  let L₀ : IntermediateField K Ω := j₁.fieldRange ⊔ j₂.fieldRange
  have : FiniteDimensional K j₁.fieldRange := j₁.toLinearMap.finiteDimensional_range
  have : FiniteDimensional K j₂.fieldRange := j₂.toLinearMap.finiteDimensional_range
  let N : IntermediateField K Ω := IntermediateField.normalClosure K L₀ Ω
  have hL₀ : L₀ ≤ N := IntermediateField.le_normalClosure L₀
  exact nonempty_binaryCofan_of_isGalois E F N
    ((IntermediateField.inclusion (le_sup_left.trans hL₀)).comp j₁.equivFieldRange.toAlgHom)
    ((IntermediateField.inclusion (le_sup_right.trans hL₀)).comp j₂.equivFieldRange.toAlgHom)

end FiniteDVRExtension

end TauCeti
