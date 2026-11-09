/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sol.Height

import TauCeti.Analysis.Calculus.FDeriv.ConstantDirection

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

/-- A Sol isometry acts on every vertical line by a translation and one global sign.
In particular, the horizontal coordinates of the image are constant along that line. -/
theorem exists_apply_mk_height_eq (Φ : Isom J Sol) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ (p : Sol) (t : ℝ),
      Φ (mk p.x p.y (p.z + t)) = mk (Φ p).x (Φ p).y ((Φ p).z + ε * t) := by
  obtain ⟨ε, hε, hd⟩ := exists_mfderiv_vertical_eq Φ
  refine ⟨ε, hε, fun p t => toProd.injective ?_⟩
  have hder (q : P) : fderiv ℝ ((toProd ∘ Φ) ∘ toProd.symm) q (0, 0, 1) = (0, 0, ε) := by
    simpa only [Equiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply] using
      (fderiv_toProd_isometry_apply Φ (toProd.symm q)
        ((tangentSpaceCastModel J (toProd.symm q)).symm (0, 0, 1))).trans (hd _)
  have h := apply_add_smul_eq_of_fderiv_apply_eq
    ((contDiff_toProd_isometry Φ).differentiable (by simp)) hder (toProd p) t
  have hq : toProd.symm (toProd p + t • ((0, 0, 1) : P)) = mk p.x p.y (p.z + t) := by
    rw [Equiv.symm_apply_eq, toProd_mk]
    ext <;> simp [fst_toProd, fst_snd_toProd, snd_snd_toProd]
  simp only [Function.comp_apply, hq, Equiv.symm_apply_apply] at h
  rw [h]
  ext <;> simp [fst_toProd, fst_snd_toProd, snd_snd_toProd, mul_comm]

end TauCeti.Sol
