/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.Basic
import TauCeti.Data.Matrix.Basic
import TauCeti.Data.Matrix.Mul
import TauCeti.LinearAlgebra.Matrix.Range

/-!
# The signature condition for a family of matrices

Let `ρ : O → B` be a function to a commutative ring and `m : O → Matrix n n B` a family of square
matrices, for instance the matrices by which the elements of a ring `O` act on a tangent space,
and `ρ` a character of `O`. For `b b' : O` the family satisfies the *signature condition*
`TauCeti.HasSignature ρ m b b'` if some vector `X` with a unit entry is a common eigenvector,
`m a *ᵥ X = ρ a • X` for every `a`, and `m b - ρ b' • 1 = vecMulVec X ξ` is the outer product
`X ξᵀ` for some vector `ξ`.

The condition is preserved by ring homomorphisms. It also passes from a family of ring
homomorphisms `σ k : B →+* D k` without a common nonzero kernel element to every local ring in
which `ρ b - ρ b'` becomes a unit: writing `M = m b - ρ b' • 1`, the condition implies the
polynomial identities `M i j * M k l = M i l * M k j`, `m a * M = ρ a • M` and
`trace M = ρ b - ρ b'`, which hold in `B` as soon as they hold after each `σ k`; over a local
ring in which the trace of `M` is a unit some diagonal entry `M i i` is a unit, and the column
`i` of `M` is then a suitable vector `X`. Over a field, the condition says that the image of `M`
lies in the line spanned by a nonzero common eigenvector.

## Main definitions

* `TauCeti.HasSignature ρ m b b'`: the signature condition.

## Main results

* `TauCeti.HasSignature.map`: the signature condition is preserved by ring homomorphisms.
* `TauCeti.HasSignature.of_forall_map`: if the signature condition holds after each member of a
  family of ring homomorphisms `σ k : B →+* D k` without a common nonzero kernel element, it
  holds after every ring homomorphism `φ : B →+* C` to a local ring with `φ (ρ b - ρ b')` a unit.
* `TauCeti.hasSignature_iff_exists_common_eigenvector_span`: over a field, the signature
  condition in terms of a nonzero common eigenvector whose span contains the image of
  `m b - ρ b' • 1`.

## References

* The definition and the descent statement correspond to `New.HasSignature` and
  `New.HasSignature.of_points` in the folder `grh` of https://github.com/lsernau/grh-lean at
  commit 72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section

namespace TauCeti

open Matrix

variable {O B C n : Type*} [CommRing B] [CommRing C] [Fintype n] [DecidableEq n]

/-- The *signature condition* for matrices `m a` and scalars `ρ a`, at `b b' : O`: some vector
`X` with a unit entry satisfies `m a *ᵥ X = ρ a • X` for all `a`, and `m b - ρ b' • 1` is the
outer product `vecMulVec X ξ` for some vector `ξ`. -/
def HasSignature (ρ : O → B) (m : O → Matrix n n B) (b b' : O) : Prop :=
  ∃ X ξ : n → B, (∃ i, IsUnit (X i)) ∧ (∀ a, m a *ᵥ X = ρ a • X) ∧
    m b - ρ b' • (1 : Matrix n n B) = vecMulVec X ξ

/-- Unfolding lemma for `TauCeti.HasSignature`. -/
theorem hasSignature_iff {ρ : O → B} {m : O → Matrix n n B} {b b' : O} :
    HasSignature ρ m b b' ↔ ∃ X ξ : n → B, (∃ i, IsUnit (X i)) ∧
      (∀ a, m a *ᵥ X = ρ a • X) ∧ m b - ρ b' • (1 : Matrix n n B) = vecMulVec X ξ :=
  Iff.rfl

/-- The signature condition is preserved by every ring homomorphism. -/
theorem HasSignature.map {ρ : O → B} {m : O → Matrix n n B} {b b' : O}
    (h : HasSignature ρ m b b') (φ : B →+* C) :
    HasSignature (fun a ↦ φ (ρ a)) (fun a ↦ (m a).map φ) b b' := by
  obtain ⟨X, ξ, ⟨i, hi⟩, hX, hM⟩ := h
  refine ⟨φ ∘ X, φ ∘ ξ, ⟨i, hi.map φ⟩, fun a ↦ ?_, by rw [← map_sub_smul_one, hM, map_vecMulVec]⟩
  ext j
  rw [← RingHom.map_mulVec, hX, Pi.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, smul_eq_mul,
    Function.comp_apply]

/-- The polynomial identities satisfied by `M = m b - ρ b' • 1` and `t = ρ b - ρ b'` under the
signature condition: the `2 × 2` minors of `M` vanish, `m a * M = ρ a • M`, and
`trace M = t`. -/
private def Identities (ρ : O → B) (m : O → Matrix n n B) (M : Matrix n n B) (t : B) : Prop :=
  (∀ i j k l, M i j * M k l = M i l * M k j) ∧ (∀ a, m a * M = ρ a • M) ∧ trace M = t

private theorem HasSignature.identities {ρ : O → B} {m : O → Matrix n n B} {b b' : O}
    (h : HasSignature ρ m b b') : Identities ρ m (m b - ρ b' • 1) (ρ b - ρ b') := by
  obtain ⟨X, ξ, ⟨i, hi⟩, hX, hM⟩ := h
  refine ⟨fun i j k l ↦ ?_, fun a ↦ ?_, ?_⟩
  · rw [hM]
    exact vecMulVec_apply_mul_vecMulVec_apply X ξ i k j l
  · rw [hM, mul_vecMulVec, hX, smul_vecMulVec]
  · -- `M *ᵥ X` is both `(ρ b - ρ b') • X` and `(ξ ⬝ᵥ X) • X`; cancel the unit entry `X i`.
    have h₁ : (m b - ρ b' • 1) *ᵥ X = (ρ b - ρ b') • X := by
      rw [sub_mulVec, hX, smul_mulVec, one_mulVec, sub_smul]
    rw [hM, vecMulVec_mulVec] at h₁
    rw [hM, trace_vecMulVec, dotProduct_comm]
    have := congrFun h₁ i
    simp only [Pi.smul_apply, op_smul_eq_mul, smul_eq_mul] at this
    exact hi.mul_left_injective ((mul_comm _ _).trans this)

omit [DecidableEq n] in
private theorem Identities.map {ρ : O → B} {m : O → Matrix n n B} {M : Matrix n n B} {t : B}
    (h : Identities ρ m M t) (φ : B →+* C) :
    Identities (fun a ↦ φ (ρ a)) (fun a ↦ (m a).map φ) (M.map φ) (φ t) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨fun i j k l ↦ ?_, fun a ↦ ?_, ?_⟩
  · simp only [map_apply, ← map_mul, h₁]
  · rw [← Matrix.map_mul, h₂, map_smul' _ _ _ (map_mul φ)]
  · rw [← AddMonoidHom.map_trace, h₃]

omit [DecidableEq n] in
/-- The identities descend along a family of ring homomorphisms without a common nonzero kernel
element. -/
private theorem Identities.of_forall_map {ι : Type*} {D : ι → Type*} [∀ k, CommRing (D k)]
    (σ : ∀ k, B →+* D k) (hσ : ∀ x, (∀ k, σ k x = 0) → x = 0) {ρ : O → B}
    {m : O → Matrix n n B} {M : Matrix n n B} {t : B}
    (h : ∀ k, Identities (fun a ↦ σ k (ρ a)) (fun a ↦ (m a).map (σ k)) (M.map (σ k)) (σ k t)) :
    Identities ρ m M t := by
  have hinj {x y : B} (hxy : ∀ k, σ k x = σ k y) : x = y :=
    sub_eq_zero.mp (hσ _ fun k ↦ by rw [map_sub, hxy, sub_self])
  refine ⟨fun i j k l ↦ hinj fun s ↦ ?_, fun a ↦ ?_, hinj fun s ↦ ?_⟩
  · simpa only [map_mul, map_apply] using (h s).1 i j k l
  · ext i j
    refine hinj fun s ↦ ?_
    have := congrArg (fun A ↦ A i j) ((h s).2.1 a)
    rw [← Matrix.map_mul, ← map_smul' _ _ _ (map_mul (σ s))] at this
    simpa only [Matrix.map_apply] using this
  · rw [AddMonoidHom.map_trace]
    exact (h s).2.2

omit [DecidableEq n] in
/-- Over a local ring, the identities with `t` a unit give the data of the signature condition:
a common eigenvector `X` of the `m a`, with eigenvalues `ρ a` and a unit entry, such that `M` is
an outer product `vecMulVec X ξ`. -/
private theorem Identities.exists_vecMulVec [IsLocalRing C] {ρ : O → C}
    {m : O → Matrix n n C} {M : Matrix n n C} {t : C} (h : Identities ρ m M t) (ht : IsUnit t) :
    ∃ X ξ : n → C, (∃ i, IsUnit (X i)) ∧ (∀ a, m a *ᵥ X = ρ a • X) ∧ M = vecMulVec X ξ := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  -- The trace of `M` is a unit, so some diagonal entry `M i i` is a unit; column `i` of `M` is
  -- the eigenvector, and `M` is that column times row `i` divided by `M i i`.
  rw [← h₃, trace] at ht
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum ht
  rw [diag_apply] at hi
  refine ⟨M.col i, _, ⟨i, hi⟩, fun a ↦ ?_, eq_vecMulVec_of_isUnit_apply h₁ hi⟩
  rw [← col_mul_eq_mulVec_col, h₂, col_smul, Pi.smul_apply]

/-- If the signature condition holds after each ring homomorphism `σ k : B →+* D k`, and the
`σ k` have no common nonzero kernel element, then it holds after every ring homomorphism
`φ : B →+* C` to a local ring with `φ (ρ b - ρ b')` a unit. -/
theorem HasSignature.of_forall_map {ι : Type*} {D : ι → Type*} [∀ k, CommRing (D k)]
    [IsLocalRing C] {ρ : O → B} {m : O → Matrix n n B} {b b' : O} (σ : ∀ k, B →+* D k)
    (hσ : ∀ x, (∀ k, σ k x = 0) → x = 0)
    (h : ∀ k, HasSignature (fun a ↦ σ k (ρ a)) (fun a ↦ (m a).map (σ k)) b b')
    (φ : B →+* C) (hφ : IsUnit (φ (ρ b - ρ b'))) :
    HasSignature (fun a ↦ φ (ρ a)) (fun a ↦ (m a).map φ) b b' := by
  have hB : Identities ρ m (m b - ρ b' • 1) (ρ b - ρ b') :=
    Identities.of_forall_map σ hσ fun k ↦ by
      simpa only [map_sub_smul_one, map_sub] using (h k).identities
  obtain ⟨X, ξ, hX, hmX, hM⟩ := (hB.map φ).exists_vecMulVec hφ
  exact ⟨X, ξ, hX, hmX, by rw [← map_sub_smul_one, hM]⟩

/-- Over a field, the signature condition says that some nonzero common eigenvector `Y`, with
`m a *ᵥ Y = ρ a • Y` for all `a`, spans a line containing the image of `m b - ρ b' • 1`. -/
theorem hasSignature_iff_exists_common_eigenvector_span {K : Type*} [Field K] {ρ : O → K}
    {m : O → Matrix n n K} {b b' : O} :
    HasSignature ρ m b b' ↔ ∃ Y : n → K, Y ≠ 0 ∧ (∀ a, m a *ᵥ Y = ρ a • Y) ∧
      ∀ v, (m b - ρ b' • 1) *ᵥ v ∈ Submodule.span K {Y} := by
  constructor
  · rintro ⟨X, ξ, ⟨i, hi⟩, hX, hM⟩
    exact ⟨X, fun h ↦ hi.ne_zero (congrFun h i), hX,
      forall_mulVec_mem_span_singleton_iff.mpr ⟨ξ, hM⟩⟩
  · rintro ⟨Y, hY, hmY, hM⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hY
    obtain ⟨ξ, hξ⟩ := forall_mulVec_mem_span_singleton_iff.mp hM
    exact ⟨Y, ξ, ⟨i, hi.isUnit⟩, hmY, hξ⟩

end TauCeti
