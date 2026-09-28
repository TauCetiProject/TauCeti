/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Quotient
public import TauCeti.RingTheory.Ideal.GoingDown
public import TauCeti.RingTheory.KrullDimension.FiniteType
public import TauCeti.RingTheory.KrullDimension.Quotient
public import TauCeti.RingTheory.TensorProduct.IsDomain
public import TauCeti.Topology.PureDimension

/-!
# Irreducible components under extension of the base field

Let `A` be an algebra over a field `K` and let `L / K` be a field extension. The irreducible
components of `Spec (L ⊗[K] A)` correspond to the minimal primes `Q` of `L ⊗[K] A`. This file
shows that each such `Q` contracts to a minimal prime `P` of `A`, and that when `A` is finitely
generated the component `V(Q)` has the dimension of `V(P)`:
`dim ((L ⊗[K] A) ⧸ Q) = dim (A ⧸ P)`. Consequently `Spec A` is pure-dimensional of dimension `d`
exactly when `Spec (L ⊗[K] A)` is. This is the affine case of the invariance of
pure-dimensionality of a scheme locally of finite type over a field under extension of the base
field, which makes pure relative dimension stable under base change.

The contraction is minimal because `L ⊗[K] A` is flat over `A`, so it satisfies going down. For
the dimension, choose a transcendence basis of `L / K`, generating an intermediate field `E` that
is a rational function field over `K`, with `L / E` algebraic.

* Over the algebraic extension `L / E`, the algebra `L ⊗[K] A = L ⊗[E] (E ⊗[K] A)` is integral
  and flat over `E ⊗[K] A`. So `Q` contracts to a minimal prime `Q'` of `E ⊗[K] A` and the
  integral injective extension `(E ⊗[K] A) ⧸ Q' → (L ⊗[K] A) ⧸ Q` preserves the dimension.
* Over the rational function field `E`, the ring `E ⊗[K] (A ⧸ P)` is a domain
  (`TauCeti.isDomain_fractionRing_mvPolynomial_tensorProduct`), so the extension of `P` to
  `E ⊗[K] A` is prime. It is contained in `Q'`, hence equals it by minimality, and
  `(E ⊗[K] A) ⧸ Q' ≅ E ⊗[K] (A ⧸ P)` has the dimension of `A ⧸ P`
  (`TauCeti.ringKrullDim_tensorProduct_field_of_finiteType`).

## Main results

* `TauCeti.isPureDimensional_primeSpectrum_iff`: `Spec R` is pure-dimensional of dimension `d`
  exactly when `R ⧸ P` has dimension `d` for every minimal prime `P`.
* `TauCeti.comap_includeRight_mem_minimalPrimes`: for `L` flat over `K`, a minimal prime of
  `L ⊗[K] A` contracts to a minimal prime of `A`.
* `TauCeti.ringKrullDim_quotient_tensorProduct_of_mem_minimalPrimes`: for finitely generated `A`,
  a minimal prime `Q` of `L ⊗[K] A` satisfies `dim ((L ⊗[K] A) ⧸ Q) = dim (A ⧸ Q ∩ A)`.
* `TauCeti.isPureDimensional_primeSpectrum_tensorProduct_iff`: pure-dimensionality of the
  spectrum of a finitely generated algebra is invariant under extension of the base field.

## References

* [Stacks Project, Tag 00P4](https://stacks.math.columbia.edu/tag/00P4), the pointwise form of
  the invariance of dimension under extension of the base field
-/

public section

open scoped TensorProduct
open Algebra.TensorProduct (includeRight)

namespace TauCeti

section PrimeSpectrum

variable {R : Type*} [CommRing R]

/-- The spectrum of a ring `R` is pure-dimensional of dimension `d` if and only if `R ⧸ P` has
Krull dimension `d` for every minimal prime `P` of `R`. -/
theorem isPureDimensional_primeSpectrum_iff {d : ℕ} :
    IsPureDimensional d (PrimeSpectrum R) ↔ ∀ P ∈ minimalPrimes R, ringKrullDim (R ⧸ P) = d := by
  simp_rw [isPureDimensional_iff, ← PrimeSpectrum.zeroLocus_minimalPrimes, Set.forall_mem_image,
    Function.comp_apply, Ideal.topologicalKrullDim_zeroLocus]

end PrimeSpectrum

section CommRing

variable {K : Type*} [CommRing K] {A : Type*} [CommRing A] [Algebra K A]

/-- A minimal prime `Q` of `E ⊗[K] A` is the extension of its contraction `P` to `A`, provided
`E ⊗[K] (A ⧸ P)` is a domain. -/
theorem eq_map_comap_includeRight_of_isDomain (E : Type*) [CommRing E] [Algebra K E]
    {Q : Ideal (E ⊗[K] A)} (hQ : Q ∈ minimalPrimes (E ⊗[K] A))
    (hdom : IsDomain (E ⊗[K] (A ⧸ Q.comap includeRight))) :
    Q = (Q.comap includeRight).map includeRight := by
  have hPQ : (Q.comap includeRight).map includeRight ≤ Q := Ideal.map_le_iff_le_comap.mpr le_rfl
  refine le_antisymm (hQ.2 ⟨?_, bot_le⟩ hPQ) hPQ
  -- `(E ⊗[K] A) ⧸ P.map includeRight` is `E ⊗[K] (A ⧸ P)`, a domain.
  have := (Algebra.TensorProduct.tensorQuotientEquiv (R := K) K A E (Q.comap includeRight)).symm
    |>.toMulEquiv.isDomain
  exact Ideal.Quotient.isDomain_iff_prime _ |>.mp this

/-- A minimal prime of `L ⊗[K] A` contracts to a minimal prime of `A` when `L` is flat over `K`:
then `L ⊗[K] A` is flat over `A` and satisfies going down. -/
theorem comap_includeRight_mem_minimalPrimes (L : Type*) [CommRing L] [Algebra K L]
    [Module.Flat K L] {Q : Ideal (L ⊗[K] A)} (hQ : Q ∈ minimalPrimes (L ⊗[K] A)) :
    Q.comap (includeRight : A →ₐ[K] L ⊗[K] A) ∈ minimalPrimes A := by
  have hflat : (includeRight : A →ₐ[K] L ⊗[K] A).toRingHom.Flat := by
    have : (includeRight : A →ₐ[K] L ⊗[K] A).toRingHom =
        (Algebra.TensorProduct.comm K A L).toRingHom.comp (algebraMap A (A ⊗[K] L)) := by
      ext; simp
    rw [this]
    exact .comp (RingHom.flat_algebraMap_iff.mpr inferInstance)
      (.of_bijective (Algebra.TensorProduct.comm K A L).bijective)
  algebraize [(includeRight : A →ₐ[K] L ⊗[K] A).toRingHom]
  exact Ideal.under_mem_minimalPrimes hQ

/-- For a flat, integral `E`-algebra `L` with compatible `K`-algebra structures, the ring
`L ⊗[K] A` is integral and flat over `E ⊗[K] A`. So a minimal prime of `L ⊗[K] A` contracts to a
minimal prime of `E ⊗[K] A`, and the two quotients have the same Krull dimension. -/
theorem mem_minimalPrimes_comap_and_ringKrullDim_eq_of_isIntegral
    (L E : Type*) [CommRing L] [Algebra K L]
    [CommRing E] [Algebra K E] [Algebra E L] [IsScalarTower K E L] [Module.Flat E L]
    [Algebra.IsIntegral E L] {Q : Ideal (L ⊗[K] A)} (hQ : Q ∈ minimalPrimes (L ⊗[K] A)) :
    Q.comap (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K A)) ∈
        minimalPrimes (E ⊗[K] A) ∧
      ringKrullDim ((L ⊗[K] A) ⧸ Q) = ringKrullDim ((E ⊗[K] A) ⧸
        Q.comap (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K A))) := by
  set f := Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K A)
  algebraize [f.toRingHom]
  have : IsScalarTower E (E ⊗[K] A) (L ⊗[K] A) := .of_algebraMap_eq fun x ↦ by
    simp [RingHom.algebraMap_toAlgebra, f]
  -- `L ⊗[K] A` is the base change of `L / E` along `E → E ⊗[K] A`.
  have hpush : Algebra.IsPushout E L (E ⊗[K] A) (L ⊗[K] A) :=
    Algebra.IsPushout.tensorProduct_tensorProduct K A E L
      (by ext; simp [RingHom.algebraMap_toAlgebra, f])
  have : Module.Flat (E ⊗[K] A) (L ⊗[K] A) :=
    Module.Flat.isBaseChange E (E ⊗[K] A) L _ hpush.symm.out
  have : Algebra.IsIntegral (E ⊗[K] A) (L ⊗[K] A) :=
    Algebra.IsPushout.isIntegral (R := E) (S := L) (A := E ⊗[K] A) (SA := L ⊗[K] A)
  have : Q.IsPrime := hQ.1.1
  -- The algebra structure has `algebraMap = f`, so `Q` lies over its contraction along `f`.
  have : Q.LiesOver (Q.comap f) := ⟨rfl⟩
  exact ⟨Ideal.under_mem_minimalPrimes hQ, ringKrullDim_eq_of_isIntegral_of_faithfulSMul⟩

end CommRing

variable {K : Type*} [Field K] {A : Type*} [CommRing A] [Algebra K A]

/-- Let `A` be a finitely generated algebra over a field `K` and `L / K` a field extension. For a
minimal prime `Q` of `L ⊗[K] A`, the irreducible component `V(Q)` of `Spec (L ⊗[K] A)` has the
dimension of the irreducible component `V(Q ∩ A)` of `Spec A`. -/
theorem ringKrullDim_quotient_tensorProduct_of_mem_minimalPrimes (L : Type*) [Field L]
    [Algebra K L] [Algebra.FiniteType K A] {Q : Ideal (L ⊗[K] A)}
    (hQ : Q ∈ minimalPrimes (L ⊗[K] A)) :
    ringKrullDim ((L ⊗[K] A) ⧸ Q) = ringKrullDim (A ⧸ Q.comap includeRight) := by
  -- `L` is algebraic over the rational function field `E` generated by a transcendence basis.
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  let E := IntermediateField.adjoin K (Set.range ((↑) : s → L))
  have : Algebra.IsAlgebraic E L := hs.isAlgebraic_field
  obtain ⟨h1, hdim⟩ := mem_minimalPrimes_comap_and_ringKrullDim_eq_of_isIntegral L E hQ
  have hdom (P : Ideal A) (_ : P.IsPrime) : IsDomain (E ⊗[K] (A ⧸ P)) :=
    (Algebra.TensorProduct.congr hs.1.aevalEquivField AlgEquiv.refl).symm.toMulEquiv.isDomain
  have := h1.1.1
  have hQ' := eq_map_comap_includeRight_of_isDomain E h1 (hdom _ inferInstance)
  have hP : (Q.comap (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L)
      (AlgHom.id K A))).comap (includeRight : A →ₐ[K] E ⊗[K] A) = Q.comap includeRight := by
    ext a
    simp [Ideal.mem_comap]
  rw [hP] at hQ'
  -- `(E ⊗[K] A) ⧸ Q'` is `E ⊗[K] (A ⧸ P)`, which has the dimension of `A ⧸ P`.
  rw [hdim, ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hQ').trans
      (Algebra.TensorProduct.tensorQuotientEquiv (R := K) K A E
        (Q.comap includeRight)).symm.toRingEquiv),
    ringKrullDim_tensorProduct_field_of_finiteType]

/-- The spectrum of a finitely generated algebra `A` over a field `K` is pure-dimensional of
dimension `d` if and only if the spectrum of `L ⊗[K] A` is, for any field extension `L / K`. -/
theorem isPureDimensional_primeSpectrum_tensorProduct_iff (L : Type*) [Field L] [Algebra K L]
    [Algebra.FiniteType K A] {d : ℕ} :
    IsPureDimensional d (PrimeSpectrum (L ⊗[K] A)) ↔ IsPureDimensional d (PrimeSpectrum A) := by
  simp_rw [isPureDimensional_primeSpectrum_iff]
  refine ⟨fun h P hP ↦ ?_, fun h Q hQ ↦ ?_⟩
  · -- Every minimal prime of `A` is the contraction of a minimal prime of `L ⊗[K] A`.
    let i : A →+* L ⊗[K] A := (includeRight : A →ₐ[K] L ⊗[K] A)
    have hker : (⊥ : Ideal (L ⊗[K] A)).comap i = ⊥ :=
      Ideal.comap_bot_of_injective _
        (Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective)
    obtain ⟨Q, hQ, rfl⟩ := Ideal.exists_minimalPrimes_comap_eq i P (by rwa [hker])
    rw [Ideal.comap_coe, ← ringKrullDim_quotient_tensorProduct_of_mem_minimalPrimes L hQ]
    exact h Q hQ
  · rw [ringKrullDim_quotient_tensorProduct_of_mem_minimalPrimes L hQ]
    exact h _ (comap_includeRight_mem_minimalPrimes L hQ)

end TauCeti
