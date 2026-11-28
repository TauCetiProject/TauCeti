/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.Algebra.Star.Rosati.Basic
public import TauCeti.LinearAlgebra.Matrix.PosDef.Quaternion
public import TauCeti.LinearAlgebra.Matrix.Trace.Comp
import Mathlib.Analysis.Matrix.Hermitian
import TauCeti.Algebra.Quaternion.Basic

/-!
# Rosati positivity for postcomposed matrix traces

Compares `TauCeti.IsRosatiPositive` for `rePart.comp (Matrix.traceLinearMap n ℝ D)` against
`Matrix.PosDef` over `ℝ` and `ℂ`, and against `Matrix.QuatPosDef` over `ℍ[ℝ]` (where
`QuaternionAlgebra.reₗ (-1) 0 (-1)` gives the real part, half the quaternionic reduced trace),
and classifies cyclic star-invariant real linear functionals on `Matrix n n ℂ`.
-/

public section

open scoped Matrix ComplexOrder Quaternion

namespace LinearMap

/-- For nonempty `n`, a cyclic `ℝ`-linear functional `t : Matrix n n ℂ →ₗ[ℝ] ℝ` satisfying
`0 < t 1` and `t (Complex.I • 1) = 0` is a positive real multiple of
`Complex.reLm.comp (Matrix.traceLinearMap n ℝ ℂ)`. -/
theorem exists_pos_smul_comp_traceLinearMap_complex_of_apply_I {n : Type*} [Fintype n]
    [DecidableEq n] [Nonempty n] (t : Matrix n n ℂ →ₗ[ℝ] ℝ)
    (hcyc : ∀ X Y : Matrix n n ℂ, t (X * Y) = t (Y * X)) (ht1 : 0 < t 1)
    (hI : t (Complex.I • 1) = 0) :
    ∃ c : ℝ, 0 < c ∧ t = c • (Complex.reLm.comp (Matrix.traceLinearMap n ℝ ℂ)) := by
  obtain ⟨τ, hc, -, hτ⟩ := exists_eq_comp_traceLinearMap_pos_of_cyclic t hcyc ht1
  have hτI : τ Complex.I = 0 := by
    have h2 : (Fintype.card n : ℝ) * τ Complex.I = 0 := by
      have h := LinearMap.congr_fun hτ (Complex.I • 1)
      rw [comp_apply, Matrix.traceLinearMap_apply, τ.map_trace_smul_one, smul_eq_mul] at h
      exact h.symm.trans hI
    exact (mul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  refine ⟨τ 1, hc, ext fun X ↦ ?_⟩
  have htr : Matrix.trace X =
      (Matrix.trace X).re • (1 : ℂ) + (Matrix.trace X).im • Complex.I := by
    simp [Complex.real_smul, Complex.re_add_im]
  rw [LinearMap.congr_fun hτ X, comp_apply, Matrix.traceLinearMap_apply, htr, map_add,
    map_smul, map_smul, hτI, smul_zero, add_zero, smul_eq_mul, mul_comm]
  simp [Complex.reLm_coe]

/-- For nonempty `n`, a cyclic, star-invariant `ℝ`-linear functional `t : Matrix n n ℂ →ₗ[ℝ] ℝ`
with `0 < t 1` is a positive real multiple of `Complex.reLm.comp (Matrix.traceLinearMap n ℝ ℂ)`. -/
theorem exists_pos_smul_comp_traceLinearMap_complex {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (t : Matrix n n ℂ →ₗ[ℝ] ℝ)
    (hcyc : ∀ X Y : Matrix n n ℂ, t (X * Y) = t (Y * X))
    (hstar : ∀ X : Matrix n n ℂ, t (star X) = t X) (ht1 : 0 < t 1) :
    ∃ c : ℝ, 0 < c ∧ t = c • (Complex.reLm.comp (Matrix.traceLinearMap n ℝ ℂ)) := by
  refine exists_pos_smul_comp_traceLinearMap_complex_of_apply_I t hcyc ht1 ?_
  have h : t (-(Complex.I • (1 : Matrix n n ℂ))) = t (Complex.I • (1 : Matrix n n ℂ)) := by
    simpa [Matrix.star_eq_conjTranspose] using hstar (Complex.I • (1 : Matrix n n ℂ))
  rw [map_neg] at h
  exact eq_zero_of_neg_eq h

end LinearMap

namespace Matrix

open TauCeti

/-- When `rePart` is cyclic (`∀ a b : D, rePart (a * b) = rePart (b * a)`), characterization of
`IsRosatiPositive (rePart.comp (Matrix.traceLinearMap n ℝ D))` via Hermitian matrices and strict
positivity of `v ↦ rePart (star v ⬝ᵥ (S *ᵥ v))`. -/
theorem isRosatiPositive_comp_traceLinearMap_iff {D : Type*} [NonUnitalNonAssocSemiring D]
    [Module ℝ D] [StarRing D] {n : Type*} [Fintype n] (S : Matrix n n D)
    {rePart : D →ₗ[ℝ] ℝ} (hre_cyclic : ∀ a b : D, rePart (a * b) = rePart (b * a)) :
    IsRosatiPositive (rePart.comp (Matrix.traceLinearMap n ℝ D)) S ↔
      S.IsHermitian ∧ ∀ v : n → D, v ≠ 0 → 0 < rePart (star v ⬝ᵥ (S *ᵥ v)) := by
  classical
  rw [isRosatiPositive_iff, Matrix.isHermitian_iff_isSelfAdjoint]
  refine and_congr_right fun _ ↦ ⟨fun h v hv ↦ ?_, fun h X hX ↦ ?_⟩
  · obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv
    let X : Matrix n n D := Matrix.of fun i m ↦ if m = i₀ then v i else 0
    have hpos := h X fun h0 ↦ hi₀ (by simpa [X] using congrFun (congrFun h0 i₀) i₀)
    have hcol {m : n} (hm : m ≠ i₀) : (fun j ↦ X j m) = 0 := funext fun j ↦ by simp [X, hm]
    rw [LinearMap.comp_traceLinearMap_mul_mul_star_eq_sum hre_cyclic, Finset.sum_eq_single i₀
      (fun m _ hm ↦ by simp [hcol hm])
      (fun h0 ↦ absurd (Finset.mem_univ i₀) h0)] at hpos
    simpa [X] using hpos
  · rw [LinearMap.comp_traceLinearMap_mul_mul_star_eq_sum hre_cyclic]
    obtain ⟨m₀, hm₀⟩ : ∃ m : n, (fun j ↦ X j m) ≠ 0 := by
      by_contra hall; push Not at hall; exact hX (Matrix.ext fun j m ↦ congrFun (hall m) j)
    refine Finset.sum_pos' (fun m _ ↦ ?_) ⟨m₀, Finset.mem_univ m₀, h _ hm₀⟩
    rcases eq_or_ne (fun j ↦ X j m) 0 with h0 | hne <;> [simp [h0]; exact (h _ hne).le]

/-- Over `ℝ`, `IsRosatiPositive` for `Matrix.traceLinearMap n ℝ ℝ` agrees with `Matrix.PosDef`. -/
@[simp] theorem isRosatiPositive_traceLinearMap_real_iff {n : Type*} [Fintype n]
    (S : Matrix n n ℝ) :
    IsRosatiPositive (Matrix.traceLinearMap n ℝ ℝ) S ↔ S.PosDef := by
  rw [← (LinearMap.id_comp (Matrix.traceLinearMap n ℝ ℝ) :
      (LinearMap.id : ℝ →ₗ[ℝ] ℝ).comp _ = _),
    isRosatiPositive_comp_traceLinearMap_iff S mul_comm, Matrix.posDef_iff_dotProduct_mulVec]
  simp only [LinearMap.id_apply, star_trivial]

/-- Over `ℂ`, `IsRosatiPositive` for `Complex.reLm.comp (Matrix.traceLinearMap n ℝ ℂ)` agrees
with `Matrix.PosDef`. -/
@[simp] theorem isRosatiPositive_comp_traceLinearMap_complex_iff {n : Type*} [Fintype n]
    (S : Matrix n n ℂ) :
    IsRosatiPositive (Complex.reLm.comp (Matrix.traceLinearMap n ℝ ℂ)) S ↔ S.PosDef := by
  rw [isRosatiPositive_comp_traceLinearMap_iff S (fun _ _ ↦ congrArg Complex.reLm (mul_comm _ _)),
    Matrix.posDef_iff_dotProduct_mulVec]
  refine and_congr_right fun hS ↦ forall_congr' fun v ↦ imp_congr_right fun _ ↦ ?_
  have him : (star v ⬝ᵥ (S *ᵥ v)).im = 0 := by
    simpa using Matrix.IsHermitian.im_star_dotProduct_mulVec_self hS v
  rw [Complex.pos_iff]; exact ⟨fun h ↦ ⟨h, him.symm⟩, fun h ↦ h.1⟩

/-- Over `ℍ[ℝ]`, `IsRosatiPositive` for
`(QuaternionAlgebra.reₗ (-1) 0 (-1)).comp (Matrix.traceLinearMap n ℝ ℍ[ℝ])` (half the
quaternionic reduced trace) agrees with `Matrix.QuatPosDef`. -/
@[simp] theorem isRosatiPositive_comp_traceLinearMap_quaternion_iff {n : Type*} [Fintype n]
    (S : Matrix n n ℍ[ℝ]) :
    IsRosatiPositive ((QuaternionAlgebra.reₗ (-1) 0 (-1)).comp (Matrix.traceLinearMap n ℝ ℍ[ℝ]))
      S ↔ S.QuatPosDef := by
  rw [isRosatiPositive_comp_traceLinearMap_iff S Quaternion.re_mul_comm, Matrix.quatPosDef_iff]
  simp only [QuaternionAlgebra.reₗ_apply]

end Matrix
