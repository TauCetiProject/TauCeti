/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.MatrixFinTwo.Basic
public import Mathlib.Topology.GDelta.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Instances.Matrix
import TauCeti.Analysis.SpecialFunctions.Trigonometric.LevelSet
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# Nondegenerate iterates of real `2 × 2` matrices of determinant one

A fixed point of an area-preserving map of a surface is *nondegenerate* when its linearized
return map `A`, a real `2 × 2` matrix of determinant one, does not have `1` as an eigenvalue, that
is, when `det (1 - A) ≠ 0`. The `k`-fold iterate of the map has linearization `A ^ k`, so all
iterates are nondegenerate when `det (1 - A ^ k) ≠ 0` for every `k ≥ 1`.

For determinant one, `det (1 - A ^ k) = 2 - trace (A ^ k)`, and if `trace A = 2 cos θ` then
`trace (A ^ k) = 2 cos (k θ)` (`Matrix.trace_pow_eq_two_mul_cos_fin_two`). If instead
`|trace A| > 2` no iterate has eigenvalue `1`. Hence `A ^ k` has eigenvalue `1` exactly when
`trace A = 2 cos (2π j / k)` for some integer `j` (`Matrix.det_one_sub_pow_eq_zero_iff_fin_two`),
and some positive iterate has eigenvalue `1` exactly when `trace A = 2 cos (2π q)` for some
rational `q` (`Matrix.exists_det_one_sub_pow_eq_zero_iff_fin_two`): the eigenvalues of `A` are then
roots of unity.

These degenerate traces form a countable set. The trace of `R(θ) A`, where
`R(θ) = Matrix.SpecialLinearGroup.rotation θ`, is `trace A cos θ + (A₁₀ - A₀₁) sin θ`, and the two
coefficients do not both vanish when `det A = 1`. So for all but countably many `θ`, every positive
iterate of `R(θ) A` is nondegenerate
(`Matrix.SpecialLinearGroup.countable_setOf_exists_det_one_sub_pow_rotation_mul_eq_zero`), and
such `θ` are dense in `ℝ`, in particular arbitrarily close to `0` on either side. The rotations
`R(θ)` are the linear Hamiltonian flow of the quadratic Hamiltonian `(x² + y²) / 2`, run forwards
or backwards according to the sign convention for Hamiltonian vector fields. So `R(θ) A` is the
linearized return map of the surface map composed with the time-`θ` map of a Hamiltonian that has
a critical point at the fixed point, with this quadratic form as its `2`-jet there. Consequently
the matrices of `SL(2, ℝ)` with all positive powers nondegenerate form a dense `Gδ` subset
(`Matrix.SpecialLinearGroup.dense_setOf_forall_det_one_sub_pow_ne_zero`,
`Matrix.SpecialLinearGroup.isGδ_setOf_forall_det_one_sub_pow_ne_zero`).

## Main results

* `Matrix.det_one_sub_pow_eq_two_sub_two_mul_cos_fin_two`: `det (1 - A ^ n) = 2 - 2 cos (n θ)`
  when `det A = 1` and `trace A = 2 cos θ`.
* `Matrix.det_one_sub_pow_eq_zero_iff_fin_two`: `det (1 - A ^ k) = 0` for `k ≠ 0` exactly when
  `trace A = 2 cos (2π j / k)` for an integer `j`.
* `Matrix.exists_det_one_sub_pow_eq_zero_iff_fin_two`: some positive power of `A` has eigenvalue
  `1` exactly when `trace A = 2 cos (2π q)` for a rational `q`.
* `Matrix.SpecialLinearGroup.dense_setOf_forall_det_one_sub_pow_rotation_mul_ne_zero`: the
  rotation angles making every positive iterate of `R(θ) A` nondegenerate are dense.
* `Matrix.SpecialLinearGroup.dense_setOf_forall_det_one_sub_pow_ne_zero` and
  `Matrix.SpecialLinearGroup.isGδ_setOf_forall_det_one_sub_pow_ne_zero`: the elements of
  `SL(2, ℝ)` with all positive powers nondegenerate form a dense `Gδ` set.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818–893, for the nondegeneracy of all iterates of the return
  maps of the orbits of an area-preserving surface map.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford (2017),
  Section 1.2, for linear symplectic maps of the plane and their traces.
-/

public section

noncomputable section

open Real Set
open scoped MatrixGroups

namespace Matrix

variable {A : Matrix (Fin 2) (Fin 2) ℝ}

/-- For a real `2 × 2` matrix `A` of determinant one and trace `2 cos θ`,
`det (1 - A ^ n) = 2 - 2 cos (n θ)`. -/
theorem det_one_sub_pow_eq_two_sub_two_mul_cos_fin_two (hdet : A.det = 1) {θ : ℝ}
    (htr : A.trace = 2 * cos θ) (n : ℕ) : (1 - A ^ n).det = 2 - 2 * cos (n * θ) := by
  rw [det_one_sub_eq_two_sub_trace_of_det_eq_one (by rw [det_pow, hdet, one_pow]),
    trace_pow_eq_two_mul_cos_fin_two hdet htr]

/-- **The `k`-th power of a real `2 × 2` matrix of determinant one has eigenvalue `1` exactly when
its trace is `2 cos (2π j / k)`** for an integer `j`, that is, when its eigenvalues are `k`-th roots
of unity. -/
theorem det_one_sub_pow_eq_zero_iff_fin_two (hdet : A.det = 1) {k : ℕ} (hk : k ≠ 0) :
    (1 - A ^ k).det = 0 ↔ ∃ j : ℤ, A.trace = 2 * cos (2 * π * j / k) := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  constructor
  · intro h
    by_cases htr : |A.trace| ≤ 2
    · -- Elliptic or parabolic: write `trace A = 2 cos θ` and solve `cos (k θ) = 1`.
      have hθ : A.trace = 2 * cos (arccos (A.trace / 2)) := by
        rw [cos_arccos (by linarith [neg_abs_le A.trace]) (by linarith [le_abs_self A.trace])]
        ring
      rw [det_one_sub_pow_eq_two_sub_two_mul_cos_fin_two hdet hθ] at h
      obtain ⟨j, hj⟩ := (cos_eq_one_iff (k * arccos (A.trace / 2))).1 (by linarith)
      refine ⟨j, hθ.trans ?_⟩
      rw [show arccos (A.trace / 2) = 2 * π * j / k by rw [eq_div_iff hk']; linarith]
    · -- Hyperbolic: no power has trace `2`.
      have hpow := two_lt_abs_trace_pow hdet (not_le.1 htr) hk
      rw [det_one_sub_eq_two_sub_trace_of_det_eq_one (by rw [det_pow, hdet, one_pow]),
        sub_eq_zero] at h
      rw [← h, abs_two] at hpow
      exact absurd hpow (lt_irrefl 2)
  · rintro ⟨j, hj⟩
    rw [det_one_sub_pow_eq_two_sub_two_mul_cos_fin_two hdet hj,
      show (k : ℝ) * (2 * π * j / k) = j * (2 * π) by field_simp, cos_int_mul_two_pi]
    norm_num

/-- **Some positive power of a real `2 × 2` matrix of determinant one has eigenvalue `1` exactly
when its trace is `2 cos (2π q)`** for a rational `q`, that is, when its eigenvalues are roots of
unity. -/
theorem exists_det_one_sub_pow_eq_zero_iff_fin_two (hdet : A.det = 1) :
    (∃ k ≠ 0, (1 - A ^ k).det = 0) ↔ ∃ q : ℚ, A.trace = 2 * cos (2 * π * q) := by
  constructor
  · rintro ⟨k, hk, h⟩
    obtain ⟨j, hj⟩ := (det_one_sub_pow_eq_zero_iff_fin_two hdet hk).1 h
    exact ⟨j / k, by rw [hj]; push_cast; ring_nf⟩
  · rintro ⟨q, hq⟩
    refine ⟨q.den, q.den_ne_zero, (det_one_sub_pow_eq_zero_iff_fin_two hdet q.den_ne_zero).2
      ⟨q.num, ?_⟩⟩
    rw [hq, Rat.cast_def, mul_div_assoc]

namespace SpecialLinearGroup

/-- For a real `2 × 2` matrix of determinant one, the coefficients `trace A` and `A₁₀ - A₀₁` of
`trace (R(θ) A)` in `cos θ` and `sin θ` do not both vanish: otherwise `A` would be symmetric and
traceless, of determinant `-A₀₀² - A₀₁² ≤ 0`. -/
private theorem trace_ne_zero_or_sub_ne_zero (hdet : A.det = 1) :
    A.trace ≠ 0 ∨ A 1 0 - A 0 1 ≠ 0 := by
  by_contra! h
  rw [trace_fin_two] at h
  rw [det_fin_two] at hdet
  rw [show A 1 1 = -A 0 0 by linarith [h.1], show A 1 0 = A 0 1 by linarith [h.2]] at hdet
  nlinarith [sq_nonneg (A 0 0), sq_nonneg (A 0 1)]

/-- For a real `2 × 2` matrix `A` of determinant one and a countable set `T` of reals, only
countably many angles `θ` give `trace (R(θ) A) ∈ T`. -/
theorem countable_setOf_trace_rotation_mul_mem (hdet : A.det = 1) {T : Set ℝ}
    (hT : T.Countable) :
    {θ : ℝ | ((rotation θ : Matrix (Fin 2) (Fin 2) ℝ) * A).trace ∈ T}.Countable := by
  refine (hT.biUnion fun t _ ↦ countable_setOf_mul_cos_add_mul_sin_eq
    (trace_ne_zero_or_sub_ne_zero hdet) t).mono fun θ hθ ↦ ?_
  rw [mem_iUnion₂]
  exact ⟨_, hθ, by rw [mem_ofPred_eq, ← trace_rotation_mul]⟩

/-- **Rotating a return map makes all its iterates nondegenerate, for all but countably many
angles.** For a real `2 × 2` matrix `A` of determinant one, only countably many `θ` make some
positive power of `R(θ) A` have eigenvalue `1`. -/
theorem countable_setOf_exists_det_one_sub_pow_rotation_mul_eq_zero (hdet : A.det = 1) :
    {θ : ℝ | ∃ k ≠ 0,
      (1 - ((rotation θ : Matrix (Fin 2) (Fin 2) ℝ) * A) ^ k).det = 0}.Countable := by
  refine (countable_setOf_trace_rotation_mul_mem hdet
    (countable_range fun q : ℚ ↦ 2 * cos (2 * π * q))).mono fun θ hθ ↦ ?_
  have hdet' : ((rotation θ : Matrix (Fin 2) (Fin 2) ℝ) * A).det = 1 := by
    rw [det_mul, (rotation θ).det_coe, hdet, one_mul]
  obtain ⟨q, hq⟩ := (exists_det_one_sub_pow_eq_zero_iff_fin_two hdet').1 hθ
  exact ⟨q, hq.symm⟩

/-- **The rotation angles making every positive iterate of `R(θ) A` nondegenerate are dense.** In
particular there are such angles arbitrarily close to `0` (`Dense.exists_between`). -/
theorem dense_setOf_forall_det_one_sub_pow_rotation_mul_ne_zero (hdet : A.det = 1) :
    Dense {θ : ℝ | ∀ k ≠ 0,
      (1 - ((rotation θ : Matrix (Fin 2) (Fin 2) ℝ) * A) ^ k).det ≠ 0} := by
  convert (countable_setOf_exists_det_one_sub_pow_rotation_mul_eq_zero hdet).dense_compl ℝ
    using 1
  ext θ
  simp only [mem_ofPred_eq, mem_compl_iff, not_exists, not_and, ne_eq]

/-- **The elements of `SL(2, ℝ)` none of whose positive powers has eigenvalue `1` are dense.** Each
element is a limit of its rotations `R(θ) A` with `θ → 0`. -/
theorem dense_setOf_forall_det_one_sub_pow_ne_zero :
    Dense {A : SL(2, ℝ) | ∀ k ≠ 0, (1 - (A : Matrix (Fin 2) (Fin 2) ℝ) ^ k).det ≠ 0} := by
  intro A
  have hf : Continuous fun θ : ℝ ↦ rotation θ * A := continuous_rotation.mul continuous_const
  have h0 : (0 : ℝ) ∈ closure {θ : ℝ | ∀ k ≠ 0,
      (1 - ((rotation θ : Matrix (Fin 2) (Fin 2) ℝ) * A) ^ k).det ≠ 0} :=
    (dense_setOf_forall_det_one_sub_pow_rotation_mul_ne_zero A.det_coe) 0
  have h := mem_closure_image hf.continuousAt h0
  rw [rotation_zero, one_mul] at h
  refine closure_mono ?_ h
  rintro _ ⟨θ, hθ, rfl⟩
  simpa only [mem_ofPred_eq, coe_mul] using hθ

/-- **The elements of `SL(2, ℝ)` none of whose positive powers has eigenvalue `1` form a `Gδ`
set**: for each `k`, the condition `det (1 - A ^ k) ≠ 0` is open. -/
theorem isGδ_setOf_forall_det_one_sub_pow_ne_zero :
    IsGδ {A : SL(2, ℝ) | ∀ k ≠ 0, (1 - (A : Matrix (Fin 2) (Fin 2) ℝ) ^ k).det ≠ 0} := by
  have h : {A : SL(2, ℝ) | ∀ k ≠ 0, (1 - (A : Matrix (Fin 2) (Fin 2) ℝ) ^ k).det ≠ 0} =
      ⋂ k : ℕ, {A : SL(2, ℝ) | (1 - (A : Matrix (Fin 2) (Fin 2) ℝ) ^ (k + 1)).det ≠ 0} := by
    ext A
    simp only [mem_ofPred_eq, mem_iInter]
    exact ⟨fun h k ↦ h _ k.succ_ne_zero, fun h k hk ↦ by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      exact h m⟩
  rw [h]
  exact IsGδ.iInter_of_isOpen fun k ↦ isOpen_ne_fun
    (continuous_const.sub (continuous_subtype_val.pow _)).matrix_det continuous_const

end SpecialLinearGroup

end Matrix
