/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.Schoenflies
public import TauCeti.Analysis.Contour.Winding.Number.Homotopy
import TauCeti.Analysis.Contour.Winding.Number.Translate

/-!
# Winding of differences of loops on a Jordan curve

Let `p` and `q` be two closed piecewise `C¹` loops on the same planar Jordan curve `C` with
`p t ≠ q t` for every `t`. The winding number of the difference loop `p - q` about `0` equals the
winding number of `p` about any point `z` of the inside `filledHull C \ C`
(`TauCeti.Contour.windingNumber_sub_eq_of_isJordanCurve`). Contracting `q` to `z` through the
inside, along the radii of a Schoenflies homeomorphism, is a homotopy of `p - q` to `p - z` in
`ℂ \ {0}`.

This is the topological input of Hopf's proof of the theorem of turning tangents: `p` and `q` are
the two endpoints of the secants of a simple closed curve, and the secant loop is compared with
the winding of the curve about a point of its inside.

## References

* H. Hopf, *Über die Drehung der Tangenten und Sehnen ebener Kurven*, Compositio Math. 2 (1935),
  50–62.
-/

public section

open Metric Set
open scoped unitInterval

noncomputable section

namespace TauCeti.Contour

/-- **Winding of the difference of two loops on a Jordan curve.** If `p` and `q` are closed
piecewise `C¹` loops on a Jordan curve `C` with `p t ≠ q t` for all `t`, then the winding number
of `p - q` about `0` is the winding number of `p` about any point `z` of the inside
`filledHull C \ C`. -/
theorem windingNumber_sub_eq_of_isJordanCurve {C : Set ℂ} (hC : IsJordanCurve C)
    {x y z : ℂ} {p : Path x x} {q : Path y y}
    (hpC : ∀ t, p t ∈ C) (hqC : ∀ t, q t ∈ C) (hpq : ∀ t, p t ≠ q t)
    (hz : z ∈ filledHull C \ C)
    (hp : IsPiecewiseC1On p.extend 0 1) (hq : IsPiecewiseC1On q.extend 0 1) :
    windingNumber (fun t ↦ p.extend t - q.extend t) 0 1 0 = windingNumber p.extend 0 1 z := by
  obtain ⟨e, he₀, heS, heB, -⟩ := hC.exists_homeomorph_image_sphere_of_mem hz
  have hnorm (t : I) : ‖e.symm (q t)‖ = 1 := by
    obtain ⟨v, hv, hev⟩ := heS ▸ hqC t
    rw [← hev, e.symm_apply_apply]
    exact mem_sphere_zero_iff_norm.mp hv
  let P : Path (x - y) (x - y) :=
    { toFun t := p t - q t
      continuous_toFun := p.continuous.sub q.continuous
      source' := by simp
      target' := by simp }
  let Q : Path (x - z) (x - z) :=
    { toFun t := p t - z
      continuous_toFun := p.continuous.sub continuous_const
      source' := by simp
      target' := by simp }
  let F : C(I × I, ℂ) :=
    ⟨fun st ↦ p st.2 - e ((1 - (st.1 : ℝ)) • e.symm (q st.2)), by fun_prop⟩
  have havoid (st : I × I) : F st ≠ 0 := by
    rw [ContinuousMap.coe_mk, sub_ne_zero]
    rcases eq_or_ne st.1 0 with hs | hs
    · simpa [hs] using hpq st.2
    have hpos : 0 < (st.1 : ℝ) := lt_of_le_of_ne st.1.2.1 fun h ↦ hs (Subtype.ext h.symm)
    have hball : (1 - (st.1 : ℝ)) • e.symm (q st.2) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr st.1.2.2), hnorm,
        mul_one]
      linarith
    have hin : e ((1 - (st.1 : ℝ)) • e.symm (q st.2)) ∈ filledHull C \ C :=
      heB ▸ mem_image_of_mem e hball
    exact fun h ↦ hin.2 (h ▸ hpC st.2)
  have hw := windingNumber_eq_of_homotopy F (p := P) (q := Q) (w := 0)
    (fun t ↦ by simp [F, P]) (fun t ↦ by simp [F, Q, he₀]) (fun s ↦ by simp [F]) havoid
    (hp.sub hq) (hp.sub (.of_contDiffOn contDiffOn_const))
  -- `P` and `Q` are evaluated through `Path.extend_apply` on the parameter interval.
  have hI {t : ℝ} (ht : t ∈ uIoo 0 1) : t ∈ Icc (0 : ℝ) 1 :=
    Ioo_subset_Icc_self <| by rwa [uIoo_of_le zero_le_one] at ht
  have hP : EqOn P.extend (fun t ↦ p.extend t - q.extend t) (uIoo 0 1) := fun t ht ↦ by
    simp only [Path.extend_apply _ (hI ht), P, Path.coe_mk_mk]
  have hQ : EqOn Q.extend (fun t ↦ p.extend t - z) (uIoo 0 1) := fun t ht ↦ by
    simp only [Path.extend_apply _ (hI ht), Q, Path.coe_mk_mk]
  rw [windingNumber_congr_curve hP, windingNumber_congr_curve hQ] at hw
  refine hw.trans ?_
  simpa only [sub_eq_add_neg, add_neg_cancel] using windingNumber_translate (γ := p.extend)
    (a := 0) (b := 1) (z₀ := z) (-z)

end TauCeti.Contour
