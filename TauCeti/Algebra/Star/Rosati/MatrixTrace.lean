/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.Algebra.Star.Rosati.Basic
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Reduced matrix traces, cyclic functionals, and Rosati positivity

This file develops the matrix-level trace and positivity lemmas used to standardize positive
involutions on simple real matrix algebras `Matrix n n D`:

* `TauCeti.stdMatrixTrace` composes a linear map `rePart : D →ₗ[R] M` with `Matrix.traceLinearMap`.
* `TauCeti.isRosatiPositive_stdMatrixTrace_iff` identifies
  `IsRosatiPositive (stdMatrixTrace rePart)` with Hermitian matrices whose quadratic form
  `v ↦ rePart (∑ j, ∑ k, star (v j) * S j k * v k)` is strictly positive on nonzero vectors;
  over `ℝ` and `ℂ` this matches Mathlib's `Matrix.PosDef`.
* `TauCeti.cyclic_linearMap_matrix_eq_trace` shows that every cyclic `R`-linear map on
  `Matrix n n D` factors through `Matrix.trace` via a cyclic `R`-linear map on `D`.
* `TauCeti.stdMatrixTrace_rankOne_mul_conj` evaluates `stdMatrixTrace rePart (X * u * Xᴴ * u⁻¹)`
  on a rank-one matrix `X i j = v i * star (w j)` as the product of the quadratic forms of `u⁻¹` at
  `v` and of `u` at `w`.

## Main definitions

* `TauCeti.stdMatrixTrace`: the reduced trace `X ↦ rePart (Matrix.trace X)` on `Matrix n n D`.

## Main results

* `TauCeti.isRosatiPositive_stdMatrixTrace_iff`: quadratic-form characterization of
  `IsRosatiPositive` for `stdMatrixTrace`.
* `TauCeti.isRosatiPositive_stdMatrixTrace_real_iff` and
  `TauCeti.isRosatiPositive_stdMatrixTrace_complex_iff`: identification with `Matrix.PosDef` over
  `ℝ` and `ℂ`.
* `TauCeti.cyclic_linearMap_matrix_eq_trace`: factorization of cyclic linear maps on `Matrix n n D`
  through `Matrix.trace`.
* `TauCeti.stdMatrixTrace_rankOne_mul_conj`: rank-one trace identity for unit-conjugated
  involutions.
-/

public section

open scoped Matrix ComplexOrder

namespace TauCeti

/-! ### Standard reduced matrix trace and positivity -/

section StdMatrixTrace

/-- The reduced matrix trace `X ↦ rePart (Matrix.trace X)` on `Matrix n n D`. -/
abbrev stdMatrixTrace {R D M : Type*} [CommSemiring R] [AddCommMonoid D] [Module R D]
    [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n]
    (rePart : D →ₗ[R] M) : Matrix n n D →ₗ[R] M :=
  rePart.comp (Matrix.traceLinearMap n R D)

@[simp]
theorem stdMatrixTrace_apply {R D M : Type*} [CommSemiring R] [AddCommMonoid D] [Module R D]
    [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n]
    (rePart : D →ₗ[R] M) (X : Matrix n n D) :
    stdMatrixTrace rePart X = rePart (Matrix.trace X) :=
  rfl

/-- `stdMatrixTrace rePart` is cyclic whenever `rePart` is cyclic on `D`. -/
theorem stdMatrixTrace_cyclic {R D M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring D]
    [Module R D] [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n]
    {rePart : D →ₗ[R] M} (hre_cyclic : ∀ a b : D, rePart (a * b) = rePart (b * a))
    (X Y : Matrix n n D) :
    stdMatrixTrace rePart (X * Y) = stdMatrixTrace rePart (Y * X) := by
  simp only [stdMatrixTrace_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ hre_cyclic _ _

/-- `stdMatrixTrace rePart (X * Xᴴ) > 0` for every nonzero matrix `X`. -/
theorem stdMatrixTrace_pos {D : Type*} [NonUnitalNonAssocSemiring D] [Module ℝ D] [StarRing D]
    {n : Type*} [Fintype n] {rePart : D →ₗ[ℝ] ℝ}
    (hre_pos : ∀ a : D, a ≠ 0 → 0 < rePart (a * star a))
    {X : Matrix n n D} (hX : X ≠ 0) :
    0 < stdMatrixTrace rePart (X * star X) := by
  obtain ⟨i₀, j₀, hX₀⟩ : ∃ i j : n, X i j ≠ 0 := by
    by_contra h; push Not at h; exact hX (Matrix.ext h)
  have hnn (i j : n) : 0 ≤ rePart (X i j * star (X i j)) := by
    rcases eq_or_ne (X i j) 0 with h0 | hne <;> [simp [h0]; exact (hre_pos _ hne).le]
  simp only [stdMatrixTrace_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, map_sum]
  exact Finset.sum_pos' (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hnn i j)
    ⟨i₀, Finset.mem_univ i₀, Finset.sum_pos' (fun j _ ↦ hnn i₀ j)
      ⟨j₀, Finset.mem_univ j₀, hre_pos _ hX₀⟩⟩

/-- Expansion of `stdMatrixTrace rePart (S * X * Xᴴ)` as a sum of Hermitian quadratic forms over
the columns of `X`. -/
private theorem stdMatrixTrace_mul_mul_star_eq_sum {D : Type*} [Semiring D] [Module ℝ D]
    [StarRing D] {n : Type*} [Fintype n] {rePart : D →ₗ[ℝ] ℝ}
    (hre_cyclic : ∀ a b : D, rePart (a * b) = rePart (b * a))
    (S X : Matrix n n D) :
    stdMatrixTrace rePart (S * X * star X) =
      ∑ m : n, rePart (∑ j : n, ∑ k : n, star (X j m) * S j k * X k m) := by
  simp only [stdMatrixTrace_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Finset.sum_mul, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ by rw [hre_cyclic (S j k * X k m) (star (X j m)), mul_assoc]

/-- Characterization of `IsRosatiPositive (stdMatrixTrace rePart)` via Hermitian matrices and
strict positivity of the quadratic form `v ↦ rePart (∑ j, ∑ k, star (v j) * S j k * v k)`. -/
theorem isRosatiPositive_stdMatrixTrace_iff {D : Type*} [Semiring D] [Module ℝ D] [StarRing D]
    {n : Type*} [Fintype n] {rePart : D →ₗ[ℝ] ℝ}
    (hre_cyclic : ∀ a b : D, rePart (a * b) = rePart (b * a))
    (S : Matrix n n D) :
    IsRosatiPositive (stdMatrixTrace rePart) S ↔
      S.IsHermitian ∧ ∀ v : n → D, v ≠ 0 →
        0 < rePart (∑ j : n, ∑ k : n, star (v j) * S j k * v k) := by
  classical
  rw [isRosatiPositive_iff, Matrix.isHermitian_iff_isSelfAdjoint]
  refine and_congr_right fun _ ↦ ⟨fun h v hv ↦ ?_, fun h X hX ↦ ?_⟩
  · obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv
    let X : Matrix n n D := Matrix.of fun i m ↦ if m = i₀ then v i else 0
    have hpos := h X fun h0 ↦ hi₀ (by simpa [X] using congrFun (congrFun h0 i₀) i₀)
    rw [stdMatrixTrace_mul_mul_star_eq_sum hre_cyclic,
      Finset.sum_eq_single i₀ (fun m _ hm0 ↦ by simp [X, hm0])
        (fun h0 ↦ absurd (Finset.mem_univ i₀) h0)] at hpos
    simpa [X] using hpos
  · rw [stdMatrixTrace_mul_mul_star_eq_sum hre_cyclic]
    obtain ⟨m₀, hm₀⟩ : ∃ m : n, (fun j ↦ X j m) ≠ 0 := by
      by_contra hall; push Not at hall
      exact hX (Matrix.ext fun j m ↦ congrFun (hall m) j)
    refine Finset.sum_pos' (fun m _ ↦ ?_) ⟨m₀, Finset.mem_univ m₀, h _ hm₀⟩
    rcases eq_or_ne (fun j ↦ X j m) 0 with h0 | hne
    · simp [fun j ↦ congrFun h0 j]
    · exact (h _ hne).le

/-- Over `ℝ`, `IsRosatiPositive` for the standard matrix trace agrees with `Matrix.PosDef`. -/
theorem isRosatiPositive_stdMatrixTrace_real_iff {n : Type*} [Fintype n] (S : Matrix n n ℝ) :
    IsRosatiPositive (stdMatrixTrace (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) S ↔ S.PosDef := by
  rw [isRosatiPositive_stdMatrixTrace_iff (fun a b ↦ mul_comm a b),
    Matrix.posDef_iff_dotProduct_mulVec]
  refine and_congr_right fun _ ↦ forall_congr' fun v ↦ imp_congr_right fun _ ↦ ?_
  simp only [LinearMap.id_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc,
    Pi.star_apply]

/-- Over `ℂ`, `IsRosatiPositive` for the real part of the matrix trace agrees with
`Matrix.PosDef`. -/
theorem isRosatiPositive_stdMatrixTrace_complex_iff {n : Type*} [Fintype n] (S : Matrix n n ℂ) :
    IsRosatiPositive (stdMatrixTrace Complex.reLm) S ↔ S.PosDef := by
  rw [isRosatiPositive_stdMatrixTrace_iff (fun a b ↦ by rw [mul_comm]),
    Matrix.posDef_iff_dotProduct_mulVec]
  refine and_congr_right fun hS ↦ forall_congr' fun v ↦ imp_congr_right fun _ ↦ ?_
  have hsum : star v ⬝ᵥ (S *ᵥ v) = ∑ j : n, ∑ k : n, star (v j) * S j k * v k := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply]
  have him : (star v ⬝ᵥ (S *ᵥ v)).im = 0 := by
    simpa using Matrix.IsHermitian.im_star_dotProduct_mulVec_self hS v
  rw [Complex.pos_iff, hsum]
  exact ⟨fun h ↦ ⟨h, by simpa [hsum] using him.symm⟩, fun h ↦ h.1⟩

end StdMatrixTrace

/-! ### Cyclic functionals and rank-one trace identity -/

section CyclicAndRankOne

/-- Every cyclic `R`-linear map on `Matrix n n D` factors through `Matrix.trace` via a cyclic
`R`-linear map on `D`. -/
theorem cyclic_linearMap_matrix_eq_trace {R D M : Type*} [CommSemiring R] [Ring D] [Module R D]
    [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n]
    (t : Matrix n n D →ₗ[R] M)
    (hcyclic : ∀ X Y : Matrix n n D, t (X * Y) = t (Y * X)) :
    ∃ τ : D →ₗ[R] M, (∀ a b : D, τ (a * b) = τ (b * a)) ∧
      ∀ X : Matrix n n D, t X = τ (Matrix.trace X) := by
  classical
  rcases isEmpty_or_nonempty n with hempty | ⟨⟨i₀⟩⟩
  · exact ⟨0, fun _ _ ↦ rfl, fun X ↦ by simp [Subsingleton.elim X 0]⟩
  · let τ : D →ₗ[R] M := t.comp (Matrix.singleLinearMap R i₀ i₀)
    have hsingle_ne {i j : n} (hij : i ≠ j) (a : D) : t (Matrix.single i j a) = 0 := by
      have h1 : Matrix.single i j a = Matrix.single i j a * Matrix.single j j (1 : D) := by
        rw [Matrix.single_mul_single_same, mul_one]
      rw [h1, hcyclic]; simp [hij.symm]
    have hsingle_diag (i : n) (a : D) : t (Matrix.single i i a) = τ a := by
      have h1 : Matrix.single i i a = Matrix.single i i₀ a * Matrix.single i₀ i (1 : D) := by
        rw [Matrix.single_mul_single_same, mul_one]
      have h2 : Matrix.single i₀ i (1 : D) * Matrix.single i i₀ a = Matrix.single i₀ i₀ a := by
        rw [Matrix.single_mul_single_same, one_mul]
      rw [h1, hcyclic, h2]; rfl
    refine ⟨τ, fun a b ↦ ?_, fun X ↦ ?_⟩
    · change t (Matrix.single i₀ i₀ (a * b)) = t (Matrix.single i₀ i₀ (b * a))
      have hmul (x y : D) : Matrix.single i₀ i₀ (x * y) =
          Matrix.single i₀ i₀ x * Matrix.single i₀ i₀ y := by rw [Matrix.single_mul_single_same]
      rw [hmul, hmul, hcyclic]
    · conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      simp only [map_sum, Matrix.trace, Matrix.diag_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_eq_single i (fun j _ hji ↦ hsingle_ne hji.symm (X i j))
        (fun hi ↦ absurd (Finset.mem_univ i) hi), hsingle_diag]

/-- Rank-one trace identity: for `X = Matrix.vecMulVec v (star w)`,
`stdMatrixTrace rePart (X * u * Xᴴ * u⁻¹)` equals `rePart (Q_{u⁻¹}(v) * Q_u(w))`. -/
theorem stdMatrixTrace_rankOne_mul_conj {R D M : Type*} [CommSemiring R] [Ring D] [Module R D]
    [StarRing D] [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n] [DecidableEq n]
    {rePart : D →ₗ[R] M} (hre_cyclic : ∀ a b : D, rePart (a * b) = rePart (b * a))
    (u : (Matrix n n D)ˣ) (v w : n → D) :
    let X : Matrix n n D := Matrix.vecMulVec v (star w)
    stdMatrixTrace rePart (X * (u : Matrix n n D) * Xᴴ * (↑u⁻¹ : Matrix n n D)) =
      rePart ((∑ i : n, ∑ m : n, star (v i) * (↑u⁻¹ : Matrix n n D) i m * v m) *
        (∑ j : n, ∑ k : n, star (w j) * (u : Matrix n n D) j k * w k)) := by
  intro X
  have hX : X * (u : Matrix n n D) * Xᴴ * (↑u⁻¹ : Matrix n n D) =
      Matrix.vecMulVec v
        ((((star w) ᵥ* (u : Matrix n n D)) ⬝ᵥ w) • ((star v) ᵥ* (↑u⁻¹ : Matrix n n D))) := by
    rw [mul_assoc (X * (u : Matrix n n D)), Matrix.conjTranspose_vecMulVec, star_star,
      Matrix.vecMulVec_mul w (star v) (↑u⁻¹ : Matrix n n D),
      Matrix.vecMulVec_mul v (star w) (u : Matrix n n D), Matrix.vecMulVec_mul_vecMulVec]
  rw [stdMatrixTrace_apply, hX, Matrix.trace_vecMulVec]
  have htr : rePart (v ⬝ᵥ ((((star w) ᵥ* (u : Matrix n n D)) ⬝ᵥ w) •
      ((star v) ᵥ* (↑u⁻¹ : Matrix n n D)))) =
      rePart (((star v ᵥ* (↑u⁻¹ : Matrix n n D)) ⬝ᵥ v) *
        ((star w ᵥ* (u : Matrix n n D)) ⬝ᵥ w)) := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, map_sum]
    rw [Finset.sum_congr rfl fun i _ ↦ by rw [hre_cyclic, mul_assoc], ← map_sum,
      ← Finset.mul_sum, hre_cyclic]
  rw [htr, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply]

end CyclicAndRankOne

end TauCeti
