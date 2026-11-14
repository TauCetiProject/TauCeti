/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.Algebra.Module.GradedModule.Idempotent
public import TauCeti.RingTheory.GradedAlgebra.Connected

/-!
# Positively weighted polynomial rings as connected graded algebras

For a weight function `w : σ → M` taking values in an ordered additive commutative monoid `M`:

* If `0 ≤ w i` for every variable `i`, then every exponent vector `d : σ →₀ ℕ` has `0 ≤ d.weight w`,
  so `MvPolynomial.weightedHomogeneousSubmodule R w m = ⊥` whenever `m < 0`.
* If `0 < w i` for every variable `i`, then `d.weight w = 0 ↔ d = 0`, so the degree-zero weighted
  homogeneous component of `φ : MvPolynomial σ R` is `C (φ.coeff 0)` and the degree-zero weighted
  homogeneous submodule is the image of `algebraMap R (MvPolynomial σ R)`.

Note that Mathlib's `MvPolynomial.weightedHomogeneousComponent_zero` and
`Finsupp.weight_eq_zero_iff_eq_zero` assume `[CanonicallyOrderedAdd M]`, which holds for `ℕ` but not
for `ℤ`. Specializing `M = ℤ` with strictly positive integer weights makes `MvPolynomial σ R` a
connected nonnegatively `ℤ`-graded `R`-algebra whose canonical graded augmentation is
`MvPolynomial.constantCoeff`, so the graded retract and homogeneous idempotent-splitting theorems
over a principal ideal domain apply directly to `MvPolynomial σ R`.

## Main results

* `Finsupp.weight_nonneg`, `Finsupp.weight_eq_zero_iff_of_pos`: nonnegativity and zero-weight
  characterization of `Finsupp.weight` for ordered additive monoid weights.
* `MvPolynomial.weightedHomogeneousComponent_zero_of_pos`: degree-zero weighted homogeneous
  component for strictly positive weights in an ordered additive monoid.
* `TauCeti.MvPolynomial.weightedHomogeneousSubmodule_eq_bot_of_lt_zero`,
  `TauCeti.MvPolynomial.weightedHomogeneousSubmodule_zero_eq_range`: negative-degree vanishing and
  connectedness of `MvPolynomial.weightedHomogeneousSubmodule R w`.
* `TauCeti.MvPolynomial.connectedAugmentation_weightedHomogeneousSubmodule_eq_constantCoeff`:
  agreement of `GradedAlgebra.connectedAugmentation` with `MvPolynomial.constantCoeff`.
* `TauCeti.MvPolynomial.exists_weightedHomogeneous_splitting_of_idempotent`,
  `TauCeti.MvPolynomial.exists_weightedHomogeneous_basis_range_idempotent`,
  `TauCeti.MvPolynomial.multiset_map_eq_of_weightedHomogeneous_basis_range_idempotent`:
  homogeneous splittings, homogeneous bases, and shift-multiset invariance for degree-zero
  idempotents over positively `ℤ`-weighted polynomial rings over a PID.
-/

public section

namespace Finsupp

variable {σ M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]

/-- If every variable weight is nonnegative, every exponent vector `d : σ →₀ ℕ` has nonnegative
weight. -/
theorem weight_nonneg (d : σ →₀ ℕ) {w : σ → M} (hw : ∀ i, 0 ≤ w i) : 0 ≤ weight w d := by
  rw [weight_apply, Finsupp.sum]
  exact Finset.sum_nonneg fun i _ ↦ nsmul_nonneg (hw i) (d i)

/-- If every variable has strictly positive weight in an ordered additive commutative monoid, then
an exponent vector `d : σ →₀ ℕ` has weight zero if and only if `d = 0`. -/
theorem weight_eq_zero_iff_of_pos (d : σ →₀ ℕ) {w : σ → M} (hw : ∀ i, 0 < w i) :
    weight w d = 0 ↔ d = 0 := by
  refine ⟨fun hd ↦ ?_, fun h ↦ by simp [h]⟩
  ext i
  by_contra hi
  exact not_lt_of_ge (le_weight_of_ne_zero (fun s ↦ (hw s).le) hi) (hd ▸ hw i)

end Finsupp

namespace MvPolynomial

variable {σ R M : Type*} [CommSemiring R]
  [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]

/-- If every variable has strictly positive weight in an ordered additive commutative monoid `M`,
the degree-zero weighted homogeneous component of `φ` is `C (φ.coeff 0)`. -/
@[simp]
theorem weightedHomogeneousComponent_zero_of_pos (φ : MvPolynomial σ R) {w : σ → M}
    (hw : ∀ i, 0 < w i) :
    weightedHomogeneousComponent w 0 φ = C (φ.coeff 0) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_C]
  by_cases hd : d = 0
  · subst hd
    simp
  · simp [(d.weight_eq_zero_iff_of_pos hw).not.mpr hd, Ne.symm hd]

end MvPolynomial

namespace TauCeti.MvPolynomial

section OrderedMonoid

variable (R : Type*) [CommSemiring R] {σ M : Type*}
  [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]

/-- For nonnegative weights `w : σ → M`, every weighted homogeneous submodule of strictly negative
degree vanishes. -/
theorem weightedHomogeneousSubmodule_eq_bot_of_lt_zero {w : σ → M} (hw : ∀ i, 0 ≤ w i) {m : M}
    (hm : m < 0) : _root_.MvPolynomial.weightedHomogeneousSubmodule R w m = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun _ hφ ↦
    _root_.MvPolynomial.IsWeightedHomogeneous.eq_zero_of_no_monomials hφ fun d ↦
      ne_of_gt (lt_of_lt_of_le hm (d.weight_nonneg hw))

/-- For strictly positive weights `w : σ → M`, the degree-zero weighted homogeneous submodule of
`MvPolynomial σ R` is the image of `algebraMap R (MvPolynomial σ R)`. -/
theorem weightedHomogeneousSubmodule_zero_eq_range {w : σ → M} (hw : ∀ i, 0 < w i) :
    _root_.MvPolynomial.weightedHomogeneousSubmodule R w 0 =
      LinearMap.range (Algebra.linearMap R (_root_.MvPolynomial σ R)) := by
  ext φ
  rw [_root_.MvPolynomial.mem_weightedHomogeneousSubmodule, LinearMap.mem_range]
  constructor
  · intro hφ
    refine ⟨φ.coeff 0, ?_⟩
    rw [Algebra.linearMap_apply, _root_.MvPolynomial.algebraMap_eq, _root_.MvPolynomial.C_apply]
    exact (_root_.MvPolynomial.IsWeightedHomogeneous.eq_monomial_of_unique_weight hφ
      fun d hd ↦ (d.weight_eq_zero_iff_of_pos hw).mp hd).symm
  · rintro ⟨c, rfl⟩
    rw [Algebra.linearMap_apply, _root_.MvPolynomial.algebraMap_eq]
    exact _root_.MvPolynomial.isWeightedHomogeneous_C w c

end OrderedMonoid

section IntWeights

attribute [local instance] _root_.MvPolynomial.weightedGradedAlgebra

/-- For strictly positive integer weights `w : σ → ℤ`, the canonical graded augmentation on
`MvPolynomial σ R` agrees with `MvPolynomial.constantCoeff`. -/
@[simp]
theorem connectedAugmentation_weightedHomogeneousSubmodule_eq_constantCoeff
    (R : Type*) [CommSemiring R] {σ : Type*} {w : σ → ℤ} (hw : ∀ i, 0 < w i)
    (φ : _root_.MvPolynomial σ R) :
    GradedAlgebra.connectedAugmentation
      (𝒜 := _root_.MvPolynomial.weightedHomogeneousSubmodule R w)
      (fun _ hm ↦ weightedHomogeneousSubmodule_eq_bot_of_lt_zero R (fun i ↦ (hw i).le) hm)
      (fun _ ha ↦ (weightedHomogeneousSubmodule_zero_eq_range R hw) ▸ ha) φ =
      _root_.MvPolynomial.constantCoeff φ := by
  have h := GradedAlgebra.algebraMap_connectedAugmentation
    (𝒜 := _root_.MvPolynomial.weightedHomogeneousSubmodule R w)
    (fun _ hm ↦ weightedHomogeneousSubmodule_eq_bot_of_lt_zero R (fun i ↦ (hw i).le) hm)
    (fun _ ha ↦ (weightedHomogeneousSubmodule_zero_eq_range R hw) ▸ ha) φ
  have h' := congrArg _root_.MvPolynomial.constantCoeff h
  have hdec : (DirectSum.decompose (_root_.MvPolynomial.weightedHomogeneousSubmodule R w) φ 0 :
      _root_.MvPolynomial σ R) = _root_.MvPolynomial.weightedHomogeneousComponent w 0 φ :=
    _root_.MvPolynomial.weightedDecomposition.decompose'_apply R w φ 0
  rwa [_root_.MvPolynomial.algebraMap_eq, _root_.MvPolynomial.constantCoeff_C, hdec,
    φ.weightedHomogeneousComponent_zero_of_pos hw, _root_.MvPolynomial.constantCoeff_C] at h'

/-- Over a principal ideal domain `k`, any degree-zero idempotent on a finite shifted free module
over a positively `ℤ`-weighted polynomial ring `MvPolynomial σ k` splits homogeneously. -/
theorem exists_weightedHomogeneous_splitting_of_idempotent
    {k : Type*} [CommRing k] [IsDomain k] [IsPrincipalIdealRing k]
    {σ : Type*} {w : σ → ℤ} (hw : ∀ i, 0 < w i)
    {I : Type*} [Finite I] (s : I → ℤ)
    (p : (I → _root_.MvPolynomial σ k) →ₗ[_root_.MvPolynomial σ k] (I → _root_.MvPolynomial σ k))
    (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → _root_.MvPolynomial σ k),
      (∀ j, v j ∈ _root_.MvPolynomial.weightedHomogeneousSubmodule k w (d - s j)) →
      ∀ j, p v j ∈ _root_.MvPolynomial.weightedHomogeneousSubmodule k w (d - s j)) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : (Fin n → _root_.MvPolynomial σ k) →ₗ[_root_.MvPolynomial σ k]
        (I → _root_.MvPolynomial σ k))
      (π : (I → _root_.MvPolynomial σ k) →ₗ[_root_.MvPolynomial σ k]
        (Fin n → _root_.MvPolynomial σ k)),
      π.comp ι = LinearMap.id ∧
      ι.comp π = p ∧
      (∀ (q : ℤ) (u : Fin n → _root_.MvPolynomial σ k),
        (∀ i, u i ∈ _root_.MvPolynomial.weightedHomogeneousSubmodule k w (q - d i)) →
        ∀ j, ι u j ∈ _root_.MvPolynomial.weightedHomogeneousSubmodule k w (q - s j)) ∧
      (∀ (q : ℤ) (v : I → _root_.MvPolynomial σ k),
        (∀ j, v j ∈ _root_.MvPolynomial.weightedHomogeneousSubmodule k w (q - s j)) →
        ∀ i, π v i ∈ _root_.MvPolynomial.weightedHomogeneousSubmodule k w (q - d i)) :=
  exists_homogeneous_splitting_of_idempotent_of_connected
    (𝒜 := _root_.MvPolynomial.weightedHomogeneousSubmodule k w)
    (fun _ hm ↦ weightedHomogeneousSubmodule_eq_bot_of_lt_zero k (fun i ↦ (hw i).le) hm)
    (fun _ ha ↦ (weightedHomogeneousSubmodule_zero_eq_range k hw) ▸ ha) s p hp hhom

/-- Over a principal ideal domain `k`, the range of any degree-zero idempotent on a finite shifted
free module over a positively `ℤ`-weighted polynomial ring `MvPolynomial σ k` admits a finite
basis of weighted homogeneous vectors. -/
theorem exists_weightedHomogeneous_basis_range_idempotent
    {k : Type*} [CommRing k] [IsDomain k] [IsPrincipalIdealRing k]
    {σ : Type*} {w : σ → ℤ} (hw : ∀ i, 0 < w i)
    {I : Type*} [Finite I] (s : I → ℤ)
    (p : (I → _root_.MvPolynomial σ k) →ₗ[_root_.MvPolynomial σ k] (I → _root_.MvPolynomial σ k))
    (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → _root_.MvPolynomial σ k),
      (∀ j, v j ∈ _root_.MvPolynomial.weightedHomogeneousSubmodule k w (d - s j)) →
      ∀ j, p v j ∈ _root_.MvPolynomial.weightedHomogeneousSubmodule k w (d - s j)) :
    ∃ (n : ℕ)
      (b : Module.Basis (Fin n) (_root_.MvPolynomial σ k) (LinearMap.range p))
      (d : Fin n → ℤ),
      ∀ i j, (b i).val j ∈ _root_.MvPolynomial.weightedHomogeneousSubmodule k w (d i - s j) :=
  exists_homogeneous_basis_range_idempotent_of_connected
    (𝒜 := _root_.MvPolynomial.weightedHomogeneousSubmodule k w)
    (fun _ hm ↦ weightedHomogeneousSubmodule_eq_bot_of_lt_zero k (fun i ↦ (hw i).le) hm)
    (fun _ ha ↦ (weightedHomogeneousSubmodule_zero_eq_range k hw) ▸ ha) s p hp hhom

/-- Over a nontrivial commutative ring `k`, any two finite weighted homogeneous bases of the range
of a degree-zero endomorphism over a positively `ℤ`-weighted polynomial ring `MvPolynomial σ k`
have the same multiset of basis degrees. -/
theorem multiset_map_eq_of_weightedHomogeneous_basis_range_idempotent
    {k : Type*} [CommRing k] [Nontrivial k]
    {σ : Type*} {w : σ → ℤ} (hw : ∀ i, 0 < w i)
    {I : Type*} [Finite I] (s : I → ℤ)
    (p : (I → _root_.MvPolynomial σ k) →ₗ[_root_.MvPolynomial σ k] (I → _root_.MvPolynomial σ k))
    (hhom : ∀ (d : ℤ) (v : I → _root_.MvPolynomial σ k),
      (∀ j, v j ∈ _root_.MvPolynomial.weightedHomogeneousSubmodule k w (d - s j)) →
      ∀ j, p v j ∈ _root_.MvPolynomial.weightedHomogeneousSubmodule k w (d - s j))
    {n₁ n₂ : ℕ}
    (b₁ : Module.Basis (Fin n₁) (_root_.MvPolynomial σ k) (LinearMap.range p)) (d₁ : Fin n₁ → ℤ)
    (hb₁ : ∀ i j,
      (b₁ i).val j ∈ _root_.MvPolynomial.weightedHomogeneousSubmodule k w (d₁ i - s j))
    (b₂ : Module.Basis (Fin n₂) (_root_.MvPolynomial σ k) (LinearMap.range p)) (d₂ : Fin n₂ → ℤ)
    (hb₂ : ∀ i j,
      (b₂ i).val j ∈ _root_.MvPolynomial.weightedHomogeneousSubmodule k w (d₂ i - s j)) :
    Multiset.map d₁ Finset.univ.val = Multiset.map d₂ Finset.univ.val :=
  multiset_map_eq_of_homogeneous_basis_range_idempotent
    (𝒜 := _root_.MvPolynomial.weightedHomogeneousSubmodule k w)
    (fun _ hm ↦ weightedHomogeneousSubmodule_eq_bot_of_lt_zero k (fun i ↦ (hw i).le) hm)
    (fun _ ha ↦ (weightedHomogeneousSubmodule_zero_eq_range k hw) ▸ ha) s p hhom
    b₁ d₁ hb₁ b₂ d₂ hb₂

end IntWeights

end TauCeti.MvPolynomial
