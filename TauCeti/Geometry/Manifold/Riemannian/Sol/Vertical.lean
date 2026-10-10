/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sol.Height

/-!
# Vertical lines under isometries of Sol

Every Riemannian isometry of Sol sends vertical lines to vertical lines. Its restriction to
each such line is translation followed by one global choice of sign. Consequently the two
horizontal coordinates of its value depend only on the two horizontal coordinates of its
argument. This separates the horizontal map from the height variable in the classification
of Sol isometries.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  401–487, Section 4, pp. 470–471 (Sol and its isometry group).
* `TauCeti.Sol.exists_mfderiv_height_eq`: the height rigidity used here.
-/

public noncomputable section

open Bundle Manifold Real
open scoped Manifold ContDiff

namespace TauCeti.Sol

local notation "P" => ℝ × ℝ × ℝ
local notation "J" => 𝓘(ℝ, P)

/-- The differential of a Sol isometry sends the unit vertical vector to itself or its
negative, with the same sign at every point. Tangent vectors are read in global coordinates. -/
theorem exists_mfderiv_vertical_eq (Φ : Isom J Sol) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ p : Sol,
      tangentSpaceCastModel J (Φ p)
        (mfderiv J J Φ p ((tangentSpaceCastModel J p).symm (0, 0, 1))) = (0, 0, ε) := by
  obtain ⟨ε, hε, hd⟩ := exists_mfderiv_height_eq Φ
  refine ⟨ε, hε, fun p => ?_⟩
  let u := (tangentSpaceCastModel J p).symm (0, 0, 1)
  let w := tangentSpaceCastModel J (Φ p) (mfderiv J J Φ p u)
  have hz : w.2.2 = ε := by
    simpa only [u, w, ContinuousLinearEquiv.apply_symm_apply, mul_one] using hd p u
  have hn := Φ.inner_mfderiv p u u
  rw [inner_def, inner_def] at hn
  simp only [u, ContinuousLinearEquiv.apply_symm_apply, mul_zero, mul_one, zero_add] at hn
  have he : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hn' : exp (2 * (Φ p).z) * w.1 * w.1 + exp (-2 * (Φ p).z) * w.2.1 * w.2.1 +
      w.2.2 * w.2.2 = 1 := hn
  rw [hz, he] at hn'
  have hsum : exp (2 * (Φ p).z) * w.1 ^ 2 + exp (-2 * (Φ p).z) * w.2.1 ^ 2 = 0 := by
    nlinarith only [hn']
  obtain ⟨hx, hy⟩ := (add_eq_zero_iff_of_nonneg
    (mul_nonneg (exp_pos (2 * (Φ p).z)).le (sq_nonneg w.1))
    (mul_nonneg (exp_pos (-2 * (Φ p).z)).le (sq_nonneg w.2.1))).mp hsum
  have hx : w.1 = 0 := by simpa only [mul_eq_zero, exp_ne_zero, false_or, sq_eq_zero_iff] using hx
  have hy : w.2.1 = 0 := by simpa only [mul_eq_zero, exp_ne_zero, false_or, sq_eq_zero_iff] using hy
  exact Prod.ext hx (Prod.ext hy hz)

private theorem hasDerivAt_vertical_coordinates (Φ : Isom J Sol) {ε : ℝ}
    (hd : ∀ p : Sol, tangentSpaceCastModel J (Φ p)
      (mfderiv J J Φ p ((tangentSpaceCastModel J p).symm (0, 0, 1))) = (0, 0, ε))
    (x y t : ℝ) :
    HasDerivAt (fun s => toProd (Φ (mk x y s))) (0, 0, ε) t := by
  let f : P → P := (toProd ∘ Φ) ∘ toProd.symm
  have hf : ContDiff ℝ ∞ f := contDiff_toProd_isometry Φ
  have hc : HasDerivAt (fun s : ℝ => (x, y, s)) (0, 0, 1) t :=
    (hasDerivAt_const t x).prodMk ((hasDerivAt_const t y).prodMk (hasDerivAt_id t))
  have he : fderiv ℝ f (x, y, t) (0, 0, 1) = (0, 0, ε) := by
    simpa only [f, toProd_mk, ContinuousLinearEquiv.apply_symm_apply] using
      (fderiv_toProd_isometry_apply Φ (mk x y t)
        ((tangentSpaceCastModel J (mk x y t)).symm (0, 0, 1))).trans (hd _)
  have h := (hf.differentiable (by simp) (x, y, t)).hasFDerivAt.comp_hasDerivAt t hc
  rw [he] at h
  convert h using 1
  funext s
  simp only [Function.comp_apply, f]
  rw [← toProd_mk x y s, Equiv.symm_apply_apply]

/-- A Sol isometry acts on every vertical line by a translation and one global sign.
In particular, the horizontal coordinates of the image are constant along that line. -/
theorem exists_apply_mk_height_eq (Φ : Isom J Sol) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ (p : Sol) (t : ℝ),
      Φ (mk p.x p.y (p.z + t)) = mk (Φ p).x (Φ p).y ((Φ p).z + ε * t) := by
  obtain ⟨ε, hε, hd⟩ := exists_mfderiv_vertical_eq Φ
  refine ⟨ε, hε, fun p t => ?_⟩
  let f : ℝ → P := fun s => toProd (Φ (mk p.x p.y (p.z + s)))
  let g : ℝ → P := fun s => ((Φ p).x, (Φ p).y, (Φ p).z + ε * s)
  have hf (s : ℝ) : HasDerivAt f (0, 0, ε) s := by
    have hs : HasDerivAt (fun r : ℝ => p.z + r) (1 : ℝ) s := by
      simpa only [id_eq] using (hasDerivAt_id s).const_add p.z
    simpa only [f, Function.comp_def, one_smul] using
      (hasDerivAt_vertical_coordinates Φ hd p.x p.y (p.z + s)).scomp s
        hs
  have hg (s : ℝ) : HasDerivAt g (0, 0, ε) s := by
    have hh : HasDerivAt (fun s : ℝ => (Φ p).z + ε * s) ε s := by
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id s).const_mul ε).const_add (Φ p).z)
    exact (hasDerivAt_const s (Φ p).x).prodMk ((hasDerivAt_const s (Φ p).y).prodMk hh)
  have heq : f = g := eq_of_fderiv_eq (fun s => (hf s).differentiableAt)
    (fun s => (hg s).differentiableAt) (fun s => (hf s).hasFDerivAt.fderiv.trans
      (hg s).hasFDerivAt.fderiv.symm) 0 (by
        simp only [f, g, add_zero, mk_x_y_z, mul_zero]
        exact (congrArg toProd (mk_x_y_z (Φ p))).symm.trans
          (toProd_mk (Φ p).x (Φ p).y (Φ p).z))
  apply toProd.injective
  simpa only [f, g, toProd_mk] using congrFun heq t

end TauCeti.Sol
