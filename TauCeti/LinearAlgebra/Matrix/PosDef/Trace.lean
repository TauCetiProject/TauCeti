/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Trace normalization of positive definite matrices

Every positive definite matrix `G` on a nonempty finite index type over `ℝ` or `ℂ` has strictly
positive real trace, as does `G⁻¹`. Rescaling `G` by `√(Tr G⁻¹ / Tr G)` therefore produces a
positive definite scalar multiple `c • G` satisfying `(c • G).trace = (c • G)⁻¹.trace`. This is the
normalization that fixes the Woronowicz matrix in weighted Schur orthogonality.

## References

* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*, SMF,
  2013, Theorem 1.4.2.
-/

public section

open scoped ComplexOrder

namespace Matrix.PosDef

/-- Every positive definite matrix on a nonempty finite index type over `ℝ` or `ℂ` can be rescaled
by a positive scalar `c` so that `(c • G).trace = (c • G)⁻¹.trace`. -/
theorem exists_pos_smul_trace_eq_inv_trace {K ι : Type*} [RCLike K] [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {G : Matrix ι ι K} (hG : G.PosDef) :
    ∃ c : K, 0 < c ∧ (c • G).PosDef ∧ (c • G)⁻¹ = c⁻¹ • G⁻¹ ∧
      (c • G).trace = (c • G)⁻¹.trace := by
  obtain ⟨g, hg_pos, hg_eq⟩ := RCLike.pos_iff_exists_ofReal.mp hG.trace_pos
  obtain ⟨gi, hgi_pos, hgi_eq⟩ := RCLike.pos_iff_exists_ofReal.mp hG.inv.trace_pos
  set r : ℝ := Real.sqrt (gi / g)
  set c : K := (r : K) with hc_def
  have hr_pos : 0 < r := Real.sqrt_pos_of_pos (div_pos hgi_pos hg_pos)
  have hc_pos : 0 < c := RCLike.ofReal_pos.mpr hr_pos
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hFt_inv : (c • G)⁻¹ = c⁻¹ • G⁻¹ := by
    simpa [Units.smul_def] using
      G.inv_smul' (Units.mk0 c hc_ne) ((isUnit_iff_isUnit_det _).mp hG.isUnit)
  have hG_smul : (c • G).PosDef := by
    rw [hc_def, ← RCLike.real_smul_eq_coe_smul]
    exact hG.smul hr_pos
  refine ⟨c, hc_pos, hG_smul, hFt_inv, ?_⟩
  have hsq_r : r * r * g = gi := (congrArg (· * g)
    (Real.mul_self_sqrt (div_nonneg hgi_pos.le hg_pos.le))).trans (div_mul_cancel₀ _ hg_pos.ne')
  have hsq : c * c * G.trace = G⁻¹.trace := by
    rw [← hg_eq, ← hgi_eq]
    simpa [c] using congrArg (fun x : ℝ ↦ (x : K)) hsq_r
  rw [hFt_inv, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, ← hsq,
    ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hc_ne, one_mul]

end Matrix.PosDef
