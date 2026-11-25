/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic
import TauCeti.Topology.MetricSpace.IsometricSMul

/-!
# The isometry group of the upper half-plane is `PGL(2, ℝ)`

Mathlib's action `UpperHalfPlane.glAction` of `GL(2, ℝ)` on `ℍ` sends `z` to `(az + b)/(cz + d)`
when `det g > 0` and to `(a conj z + b)/(c conj z + d)` when `det g < 0`. Mathlib proves that
`SL(2, ℝ)` acts by isometries of the hyperbolic distance. This file extends that to the whole of
`GL(2, ℝ)`, including the orientation-reversing, antiholomorphic elements of negative
determinant, and to `PGL(2, ℝ)`.

A matrix of positive determinant acts as its determinant-normalized class in `PSL(2, ℝ)`
(`UpperHalfPlane.glPosToPSL2R_smul`), which is an isometry. A matrix `g` of negative determinant
is `J * (J * g)`, where `UpperHalfPlane.J = diag(-1, 1)` acts by the reflection `z ↦ -conj z` in the
imaginary axis and `J * g` has positive determinant.

Conversely, every map `f : ℍ → ℍ` preserving the hyperbolic distance, with no differentiability or
surjectivity assumed, is the action of exactly one element of `PGL(2, ℝ)`. Composing with an element
of `PSL(2, ℝ)` that moves `f i` and `f (2i)` back to `i` and `2i`, one obtains an isometry fixing
both points. By `UpperHalfPlane.cosh_dist`, the distances from a point `x + iy` to `i` and to `2i`
determine `y` and `x²`, so this isometry is `z ↦ z` or `z ↦ -conj z` at each point. After
composing with `J` if necessary, it also fixes `1 + i`, and the distance to `1 + i` then determines
the sign of `x`. Uniqueness is the faithfulness of the action. Hence the action identifies
`PGL(2, ℝ)` with the group `ℍ ≃ᵢ ℍ` of distance-preserving bijections of `ℍ`.

## Main declarations

* `TauCeti.UpperHalfPlane.isometry_J_smul`: the action of `UpperHalfPlane.J` is an isometry.
* `TauCeti.UpperHalfPlane.instIsIsometricSMulGL`: every element of `GL(2, ℝ)` acts on `ℍ` by an
  isometry.
* `TauCeti.UpperHalfPlane.instIsIsometricSMulPGL`: every element of `PGL(2, ℝ)` acts on `ℍ` by an
  isometry.
* `Isometry.exists_pgl_smul_eq` and `Isometry.existsUnique_pgl_smul_eq`: every isometry
  `ℍ → ℍ` is the action of exactly one element of `PGL(2, ℝ)`.
* `TauCeti.UpperHalfPlane.pglEquivIsometryEquiv`: the group isomorphism `PGL(2, ℝ) ≃* (ℍ ≃ᵢ ℍ)`.

## References

* Svetlana Katok, *Fuchsian Groups*, §1.1.
* Alan Beardon, *The Geometry of Discrete Groups*, §7.2.
* John Voight, *Quaternion Algebras*, Springer GTM 288 (2021), Lemma 33.4.11 and
  Theorem 33.5.5.
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane

/-- The orientation-reversing involution `UpperHalfPlane.J : z ↦ -conj z` acts on `ℍ` by an
isometry. -/
theorem isometry_J_smul : Isometry (J • · : ℍ → ℍ) :=
  Isometry.of_dist_eq fun z w ↦ by
    rw [UpperHalfPlane.dist_eq, UpperHalfPlane.dist_eq, coe_J_smul, coe_J_smul, dist_neg_neg,
      Complex.dist_conj_conj, J_smul_im, J_smul_im]

/-- Every element of `GL(2, ℝ)` acts on the upper half-plane by an isometry of the hyperbolic
distance, including the elements of negative determinant, which act antiholomorphically by
`z ↦ (a conj z + b)/(c conj z + d)`. -/
instance instIsIsometricSMulGL : IsIsometricSMul (GL (Fin 2) ℝ) ℍ where
  isometry_smul g := by
    -- a matrix of positive determinant acts as its determinant-normalized class in `PSL(2, ℝ)`
    have hpos {h : GL (Fin 2) ℝ} (hh : 0 < (h.det : ℝ)) : Isometry (h • · : ℍ → ℍ) := by
      have e (z : ℍ) : glPosToPSL2R ⟨h, hh⟩ • z = h • z := glPosToPSL2R_smul ⟨h, hh⟩ z
      simpa only [e] using isometry_smul ℍ (glPosToPSL2R ⟨h, hh⟩)
    rcases g.det.ne_zero.lt_or_gt with hg | hg
    · -- `g = J * (J * g)` and `J * g` has positive determinant
      have hJg : 0 < ((J * g).det : ℝ) := by simpa using hg
      have hcomp : (g • · : ℍ → ℍ) = (J • ·) ∘ ((J * g) • ·) := by
        funext z
        simp [smul_smul, ← mul_assoc, ← sq]
      rw [hcomp]
      exact isometry_J_smul.comp (hpos hJg)
    · exact hpos hg

/-- Every element of `PGL(2, ℝ)` acts on the upper half-plane by an isometry of the hyperbolic
distance. -/
instance instIsIsometricSMulPGL : IsIsometricSMul PGL(2, ℝ) ℍ where
  isometry_smul q := by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
    simpa only [pglMk_smul] using isometry_smul ℍ g

/-- For a fixed point `p`, the hyperbolic distance from `p` determines
`((re - p.re)² + im² + p.im²) / im`, by `UpperHalfPlane.cosh_dist'`. -/
private lemma sq_div_im_eq_of_dist_eq {p z w : ℍ} (h : dist w p = dist z p) :
    ((w.re - p.re) ^ 2 + w.im ^ 2 + p.im ^ 2) / w.im =
      ((z.re - p.re) ^ 2 + z.im ^ 2 + p.im ^ 2) / z.im := by
  have hc := congrArg Real.cosh h
  rw [cosh_dist', cosh_dist'] at hc
  field_simp at hc ⊢
  linarith

/-- The point `2i`. -/
private def twoI : ℍ := ⟨⟨0, 2⟩, two_pos⟩

/-- The point `1 + i`. -/
private def oneAddI : ℍ := ⟨⟨1, 1⟩, one_pos⟩

@[simp] private lemma twoI_re : twoI.re = 0 := rfl
@[simp] private lemma twoI_im : twoI.im = 2 := rfl
@[simp] private lemma oneAddI_re : oneAddI.re = 1 := rfl
@[simp] private lemma oneAddI_im : oneAddI.im = 1 := rfl

/-- The hyperbolic distances from a point `x + iy` to `i` and to `2i` determine `y` and `x²`. -/
private lemma im_eq_and_re_sq_eq_of_dist_eq {z w : ℍ} (hI : dist w I = dist z I)
    (h2 : dist w twoI = dist z twoI) : w.im = z.im ∧ w.re ^ 2 = z.re ^ 2 := by
  have h₁ := sq_div_im_eq_of_dist_eq hI
  have h₂ := sq_div_im_eq_of_dist_eq h2
  simp only [I_re, I_im, twoI_re, twoI_im] at h₁ h₂
  have hz := z.im_pos
  field_simp at h₁ h₂
  have him : w.im = z.im := by linear_combination (h₁ - h₂) / 3
  refine ⟨him, ?_⟩
  rw [him] at h₁
  have h : (w.re ^ 2 - z.re ^ 2) * z.im = 0 := by linear_combination h₁
  linear_combination (mul_eq_zero.1 h).resolve_right hz.ne'

/-- A point of `ℍ` is determined by its hyperbolic distances to `i`, `2i` and `1 + i`. -/
private lemma eq_of_dist_eq {z w : ℍ} (hI : dist w I = dist z I)
    (h2 : dist w twoI = dist z twoI) (h11 : dist w oneAddI = dist z oneAddI) : w = z := by
  obtain ⟨him, hre⟩ := im_eq_and_re_sq_eq_of_dist_eq hI h2
  have h₃ := sq_div_im_eq_of_dist_eq h11
  simp only [oneAddI_re, oneAddI_im, him] at h₃
  field_simp at h₃
  have hre' : w.re = z.re := by nlinarith
  exact ext_re_im hre' him

private lemma dist_I_twoI : dist I twoI = Real.log 2 := by
  rw [dist_of_re_eq (by simp [I_re]), I_im, twoI_im, Real.log_one, Real.dist_eq, zero_sub,
    abs_neg, abs_of_pos (Real.log_pos one_lt_two)]

private lemma geodesicLine_one_log_two : geodesicLine 1 (Real.log 2) = twoI :=
  coe_injective (coe_geodesicLine_one_log two_pos)

open Matrix.ProjectiveSpecialLinearGroup in
/-- Every map of the upper half-plane preserving the hyperbolic distance is the action of an
element of `PGL(2, ℝ)`. Neither surjectivity nor differentiability is assumed. -/
theorem _root_.Isometry.exists_pgl_smul_eq {f : ℍ → ℍ} (hf : Isometry f) :
    ∃ c : PGL(2, ℝ), ∀ z, c • z = f z := by
  -- move `f i` and `f (2i)` back to `i` and `2i` by an element `h` of `PSL(2, ℝ)`
  obtain ⟨g, hg₀, hg⟩ := exists_geodesicLine_zero_eq_and_dist_eq (f I) (f twoI)
  set h := toPGL g
  have hFI : h⁻¹ • f I = I := by
    rw [← map_inv, toPGL_smul, ← hg₀, smul_geodesicLine, inv_mul_cancel, geodesicLine_zero,
      one_smul]
  have hF2 : h⁻¹ • f twoI = twoI := by
    rw [← map_inv, toPGL_smul, ← hg, smul_geodesicLine, inv_mul_cancel, hf.dist_eq, dist_I_twoI,
      geodesicLine_one_log_two]
  have hF : Isometry fun z ↦ h⁻¹ • f z := (isometry_smul ℍ h⁻¹).comp hf
  -- the result sends `1 + i` to `±1 + i`; if needed, `J` corrects the sign and keeps `i`, `2i`
  obtain ⟨c₀, hc₀I, hc₀2, hc₀⟩ : ∃ c₀ : PGL(2, ℝ),
      c₀ • I = I ∧ c₀ • twoI = twoI ∧ c₀ • h⁻¹ • f oneAddI = oneAddI := by
    obtain ⟨him, hre⟩ := im_eq_and_re_sq_eq_of_dist_eq (z := oneAddI) (w := h⁻¹ • f oneAddI)
      (by simpa only [hFI] using hF.dist_eq oneAddI I)
      (by simpa only [hF2] using hF.dist_eq oneAddI twoI)
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hre with hre | hre
    · exact ⟨1, one_smul _ _, one_smul _ _, by rw [one_smul]; exact ext_re_im hre him⟩
    · refine ⟨Matrix.ProjGenLinGroup.mk J, ?_, ?_, ?_⟩ <;> rw [pglMk_smul] <;>
        apply ext_re_im <;> simp [hre, him, I_re, I_im]
  -- the isometry `z ↦ c₀ • h⁻¹ • f z` fixes `i`, `2i` and `1 + i`, so it is the identity
  refine ⟨h * c₀⁻¹, fun z ↦ ?_⟩
  have hG : Isometry fun z ↦ c₀ • h⁻¹ • f z := (isometry_smul ℍ c₀).comp hF
  have hdist (p : ℍ) (hp : c₀ • h⁻¹ • f p = p) : dist (c₀ • h⁻¹ • f z) p = dist z p := by
    simpa only [hp] using hG.dist_eq z p
  have key : c₀ • h⁻¹ • f z = z :=
    eq_of_dist_eq (hdist I (by rw [hFI, hc₀I])) (hdist twoI (by rw [hF2, hc₀2])) (hdist _ hc₀)
  conv_lhs => rw [← key]
  simp [smul_smul]

/-- Every map of the upper half-plane preserving the hyperbolic distance is the action of exactly
one element of `PGL(2, ℝ)`. -/
theorem _root_.Isometry.existsUnique_pgl_smul_eq {f : ℍ → ℍ} (hf : Isometry f) :
    ∃! c : PGL(2, ℝ), ∀ z, c • z = f z := by
  obtain ⟨c, hc⟩ := hf.exists_pgl_smul_eq
  exact ⟨c, hc, fun c' hc' ↦ eq_of_smul_eq_smul fun z ↦ (hc' z).trans (hc z).symm⟩

/-- The isometry group `ℍ ≃ᵢ ℍ` of the upper half-plane, for the hyperbolic distance, is
`PGL(2, ℝ)` acting by `UpperHalfPlane.glAction`: Möbius transformations for positive determinant
and their compositions with `z ↦ -conj z` for negative determinant. -/
def pglEquivIsometryEquiv : PGL(2, ℝ) ≃* (ℍ ≃ᵢ ℍ) :=
  MulEquiv.ofBijective (IsometryEquiv.constSMulHom PGL(2, ℝ) ℍ)
    -- stated as `Function.Bijective` so that `MulEquiv.ofBijective_apply` applies by `simp`
    (show Function.Bijective (IsometryEquiv.constSMulHom PGL(2, ℝ) ℍ) from
      ⟨IsometryEquiv.constSMulHom_injective PGL(2, ℝ) ℍ,
        fun f ↦ f.isometry.exists_pgl_smul_eq.imp fun _ hc ↦ IsometryEquiv.ext fun z ↦ by
          simpa using hc z⟩)

/-- `pglEquivIsometryEquiv c` is the action of `c` on `ℍ`. -/
@[simp]
theorem pglEquivIsometryEquiv_apply (c : PGL(2, ℝ)) (z : ℍ) :
    pglEquivIsometryEquiv c z = c • z := by
  simp [pglEquivIsometryEquiv]

/-- The inverse of the isometry `pglEquivIsometryEquiv c` is the action of `c⁻¹` on `ℍ`. -/
@[simp]
theorem pglEquivIsometryEquiv_symm_apply (c : PGL(2, ℝ)) (z : ℍ) :
    (pglEquivIsometryEquiv c).symm z = c⁻¹ • z := by
  rw [IsometryEquiv.symm_apply_eq, pglEquivIsometryEquiv_apply, smul_inv_smul]

/-- The element of `PGL(2, ℝ)` attached to an isometry acts on `ℍ` as that isometry. -/
@[simp]
theorem pglEquivIsometryEquiv_symm_smul (f : ℍ ≃ᵢ ℍ) (z : ℍ) :
    pglEquivIsometryEquiv.symm f • z = f z := by
  rw [← pglEquivIsometryEquiv_apply, MulEquiv.apply_symm_apply]

end TauCeti.UpperHalfPlane
