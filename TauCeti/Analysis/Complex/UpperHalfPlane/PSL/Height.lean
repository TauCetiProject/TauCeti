/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Heights after moving a real boundary point to `∞`

If `g ∈ PSL(2, ℝ)` carries the real boundary point `ξ` to `∞`, then a lift of `g` has lower row
proportional to `(1, -ξ)`, so `g` acts as `z ↦ (az + b) / (c (z - ξ))`. Its effect on heights is
therefore `Im (g • z) = Im z / (c² |z - ξ|²)`. For `A > 0` the set `{z | A < Im (g • z)}` is a
horodisc at `ξ`, a Euclidean disc tangent to `ℝ` at `ξ` (for `A ≤ 0` it is all of `ℍ`), and this
formula is how a horodisc at a real point is compared with Euclidean distances to that point.

## Main result

* `TauCeti.UpperHalfPlane.exists_im_smul_eq_div_of_smul_coe_eq_infty`: the height formula above.
-/

public section

open Matrix Matrix.ProjectiveSpecialLinearGroup OnePoint UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane

/-- If `g ∈ PSL(2, ℝ)` carries the real boundary point `ξ` to `∞`, then there is `c > 0` such that
`Im (g • z) = Im z / (c |z - ξ|²)` for every `z ∈ ℍ`; here `c` is the square of the lower-left
entry of a lift of `g`. -/
theorem exists_im_smul_eq_div_of_smul_coe_eq_infty {g : PSL(2, ℝ)} {ξ : ℝ}
    (hg : g • (ξ : OnePoint ℝ) = ∞) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℍ, (g • z).im = z.im / (c * Complex.normSq ((z : ℂ) - ξ)) := by
  induction g using QuotientGroup.induction_on with | H a => ?_
  rw [OnePoint.pslMk_smul, OnePoint.smul_some_eq_ite] at hg
  split_ifs at hg with h
  · simp only [SpecialLinearGroup.coe_GL_coe_matrix] at h
    have hdet : a 0 0 * a 1 1 - a 0 1 * a 1 0 = 1 := by
      rw [← Matrix.det_fin_two]
      exact a.det_coe
    -- the lower-left entry is nonzero, since otherwise the lower row would vanish
    have hc : a 1 0 ≠ 0 := by
      intro hc
      rw [hc, zero_mul, zero_add] at h
      rw [h, hc] at hdet
      simp at hdet
    refine ⟨a 1 0 ^ 2, by positivity, fun z ↦ ?_⟩
    have hd : a 1 1 = -(a 1 0 * ξ) := by linear_combination h
    have hdenom : denom (SpecialLinearGroup.mapGL ℝ a) z = a 1 0 * ((z : ℂ) - ξ) := by
      simp [denom, hd]
      ring
    rw [UpperHalfPlane.pslMk_smul, MulAction.compHom_smul_def, im_smul_eq_div_normSq, hdenom,
      Complex.normSq_mul, Complex.normSq_ofReal]
    simp [sq]
  · exact absurd hg (OnePoint.coe_ne_infty _)

end TauCeti.UpperHalfPlane
