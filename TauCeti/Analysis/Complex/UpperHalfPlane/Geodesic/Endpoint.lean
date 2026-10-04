/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.HalfPlane
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Affine
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import TauCeti.Analysis.Complex.UpperHalfPlane.Stabilizer

/-!
# The ideal endpoints of a geodesic line

The geodesic line `geodesicLine g` is the `g`-translate of the upward imaginary axis, which runs
from the boundary point `0` to the boundary point `∞`. Its ideal endpoints are therefore
`g • 0` (backward) and `g • ∞` (forward), for the action of `PSL(2, ℝ)` on `OnePoint ℝ`
(`OnePoint.instMulActionPSL`). This file describes the arc of ideal points on each side of a
geodesic line, and determines from the endpoints the side form `sideForm g` of `HalfPlane.lean`,
whose sign on `ℍ` is the side of the line. The open arc of ideal points to the left of the line,
`boundaryLeftHalfPlane g = g • {x : ℝ | x < 0}`, is described on its finite part by the same form
(`coe_mem_boundaryLeftHalfPlane_iff`).

In terms of the endpoints: a geodesic line from `∞` down to the real point `e` has
`sideForm g z = e - Re z` (`sideForm_eq_of_smul_zero_eq_infty`), one from `e` up to `∞` has
`sideForm g z = Re z - e` (`sideForm_eq_of_smul_infty_eq_infty`), and one between two real
points `e₀` and `e₁` is the semicircle on the diameter `[e₀, e₁]`, with `sideForm g` a positive
multiple of `(e₁ - e₀) (ρ² - |z - m|²)` for the midpoint `m` and the half-length `ρ`
(`exists_sideForm_eq_of_smul_zero_of_smul_infty`); its left side contains `∞` exactly when
`e₀ < e₁` (`infty_mem_boundaryLeftHalfPlane_iff`).

Finally, the endpoints determine the oriented geodesic up to reparametrisation: two elements with
the same backward and forward endpoints differ by a dilation on the right
(`exists_eq_mul_dilation_of_smul_zero_eq_of_smul_infty_eq`), and an element is determined by the
point at parameter `0` and the forward endpoint
(`eq_of_geodesicLine_zero_eq_of_smul_infty_eq`).

## Main declarations

* `TauCeti.UpperHalfPlane.sideForm_eq_of_smul_zero_eq_infty`,
  `sideForm_eq_of_smul_infty_eq_infty`, `exists_sideForm_eq_of_smul_zero_of_smul_infty`: the side
  form of a geodesic line in terms of its endpoints.
* `TauCeti.UpperHalfPlane.boundaryLeftHalfPlane g`: the open arc of ideal points to the left of
  `geodesicLine g`, with `coe_mem_boundaryLeftHalfPlane_iff` and
  `infty_mem_boundaryLeftHalfPlane_iff`.
* `TauCeti.UpperHalfPlane.exists_smul_zero_eq_and_smul_infty_eq`: every ordered pair of distinct
  ideal points are the endpoints of a geodesic line.
* `TauCeti.UpperHalfPlane.exists_geodesicLine_zero_eq_and_smul_infty_eq`: a geodesic line from any
  point of `ℍ` to any ideal point.
* `TauCeti.UpperHalfPlane.strictMono_re_geodesicLine`: along a semicircle from `e₀` to `e₁ > e₀`,
  the real part increases strictly, between `e₀` and `e₁`.

## Source

Walkden, *Hyperbolic geometry* (MATH32051 lecture notes, Manchester 2019), §4.1 (the action of a
Möbius transformation on `∂ℍ`, `γ(∞) = a/c`, `γ(-d/c) = ∞`) and §4.3 (geodesics are determined by
their endpoints; Lemma 4.3.1, the semicircle with endpoints `ζ₋ < ζ₊` is carried to the imaginary
axis by `z ↦ (z - ζ₊)/(z - ζ₋)`); Katok, *Fuchsian groups, geodesic flows on surfaces of
constant negative curvature and symbolic coding of geodesics*, Clay Math. Proc. 10 (2010),
Theorem 3.1 p. 10 (geodesics are semicircles and vertical lines).
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Pointwise OnePoint

namespace TauCeti.UpperHalfPlane

open Matrix.ProjectiveSpecialLinearGroup (upperRightHom upperRightHom_smul_coe
  upperRightHom_smul_infty mk_smul_zero_eq_infty_iff mk_smul_infty_eq_infty_iff
  mk_smul_zero_eq_coe_iff mk_smul_infty_eq_coe_iff)
open Matrix.SpecialLinearGroup (dilation eq_dilation_two_mul_log)

/-! ### Dilations and `pslS` on the ideal boundary -/

-- Not `@[simp]`: `OnePoint.pslMk_smul` rewrites the left-hand sides of these three lemmas, a
-- class of a matrix acting, into the `GL` action first.
/-- A dilation fixes the ideal point `0`. -/
theorem dilation_smul_zero (s : ℝ) :
    ((dilation s : SL(2, ℝ)) : PSL(2, ℝ)) • ((0 : ℝ) : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ) := by
  simp [OnePoint.smul_some_eq_ite, Real.exp_ne_zero]

/-- A dilation fixes the ideal point `∞`. -/
theorem dilation_smul_infty (s : ℝ) :
    ((dilation s : SL(2, ℝ)) : PSL(2, ℝ)) • (∞ : OnePoint ℝ) = ∞ := by
  simp [OnePoint.smul_infty_eq_self_iff]

/-- A dilation acts on the real ideal points as multiplication by `exp s`. -/
theorem dilation_smul_coe (s x : ℝ) :
    ((dilation s : SL(2, ℝ)) : PSL(2, ℝ)) • (x : OnePoint ℝ) =
      ((Real.exp s * x : ℝ) : OnePoint ℝ) := by
  have h : Real.exp (s / 2) * x / Real.exp (-(s / 2)) = Real.exp s * x := by
    rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg, mul_right_comm, ← Real.exp_add, add_halves]
  simp [OnePoint.smul_some_eq_ite, Real.exp_ne_zero, h]

private theorem pslS_eq_mk :
    pslS = ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S : SL(2, ℝ)) :
      PSL(2, ℝ)) := by
  rw [pslS_def, psl2zToPSL2R_mk, sl2zToPSL2R_apply]

/-- `pslS`, the class of `z ↦ -1/z`, sends the ideal point `0` to `∞`. -/
@[simp]
theorem pslS_smul_zero : pslS • ((0 : ℝ) : OnePoint ℝ) = ∞ := by
  simp [pslS_eq_mk, ModularGroup.coe_S]

/-- `pslS`, the class of `z ↦ -1/z`, sends the ideal point `∞` to `0`. -/
@[simp]
theorem pslS_smul_infty : pslS • (∞ : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ) := by
  simp [pslS_eq_mk, ModularGroup.coe_S, OnePoint.smul_infty_eq_ite]

/-- Conjugating a dilation by `pslS` inverts it. -/
theorem pslS_mul_dilation_mul_pslS (s : ℝ) :
    pslS * ((dilation s : SL(2, ℝ)) : PSL(2, ℝ)) * pslS =
      ((dilation (-s) : SL(2, ℝ)) : PSL(2, ℝ)) := by
  rw [pslS_eq_mk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ←
    Matrix.ProjectiveSpecialLinearGroup.mk_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_S, neg_div]

/-! ### The endpoints of a representative -/

private theorem det_mk (A : SL(2, ℝ)) : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  rw [← Matrix.det_fin_two]
  exact A.det_coe

/-! ### The ideal arc on the left of a geodesic line -/

/-- The open arc of ideal points to the left of `geodesicLine g`: the `g`-translate of the
negative real numbers. -/
def boundaryLeftHalfPlane (g : PSL(2, ℝ)) : Set (OnePoint ℝ) :=
  g • (((↑) : ℝ → OnePoint ℝ) '' Set.Iio 0)

-- The body of `boundaryLeftHalfPlane` is not `@[expose]`d, so downstream modules rewrite with
-- this.
/-- Restatement of the body of `boundaryLeftHalfPlane`, unfolded from the `def`. -/
theorem boundaryLeftHalfPlane_def (g : PSL(2, ℝ)) :
    boundaryLeftHalfPlane g = g • (((↑) : ℝ → OnePoint ℝ) '' Set.Iio 0) := by
  rfl

/-- Translating the left ideal arc of `g` by `h` gives the left ideal arc of `h * g`. -/
@[simp]
theorem smul_boundaryLeftHalfPlane (h g : PSL(2, ℝ)) :
    h • boundaryLeftHalfPlane g = boundaryLeftHalfPlane (h * g) := by
  rw [boundaryLeftHalfPlane, boundaryLeftHalfPlane, smul_smul]

/-- Reparametrising a geodesic line by a dilation does not change its left ideal arc. -/
@[simp]
theorem boundaryLeftHalfPlane_mul_dilation (g : PSL(2, ℝ)) (s : ℝ) :
    boundaryLeftHalfPlane (g * ↑(dilation s)) = boundaryLeftHalfPlane g := by
  rw [boundaryLeftHalfPlane, boundaryLeftHalfPlane, ← smul_smul]
  congr 1
  rw [← Set.image_smul, Set.image_image]
  simp only [dilation_smul_coe]
  ext p
  simp only [Set.mem_image, Set.mem_Iio]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, mul_neg_of_pos_of_neg (Real.exp_pos s) hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Real.exp (-s) * x, mul_neg_of_pos_of_neg (Real.exp_pos _) hx, ?_⟩
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- A real ideal point lies on the left ideal arc of `g` exactly when the side form is negative
there. -/
theorem coe_mem_boundaryLeftHalfPlane_iff (g : PSL(2, ℝ)) (x : ℝ) :
    (x : OnePoint ℝ) ∈ boundaryLeftHalfPlane g ↔ sideForm g x < 0 := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  rw [boundaryLeftHalfPlane, Set.mem_smul_set_iff_inv_smul_mem, ← QuotientGroup.mk_inv,
    OnePoint.pslMk_smul, OnePoint.smul_some_eq_ite, sideForm_mk_ofReal]
  simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, ← sub_eq_add_neg, neg_mul]
  by_cases h : -(A 1 0 * x) + A 0 0 = 0
  · simp [h]
  · simp only [h, ↓reduceIte, Set.mem_image, OnePoint.coe_eq_coe, Set.mem_Iio, exists_eq_right]
    rw [div_neg_iff, mul_neg_iff]

/-- The backward endpoint of a geodesic line is not on its left ideal arc. -/
@[simp]
theorem smul_zero_notMem_boundaryLeftHalfPlane (g : PSL(2, ℝ)) :
    g • ((0 : ℝ) : OnePoint ℝ) ∉ boundaryLeftHalfPlane g := by
  rw [boundaryLeftHalfPlane, Set.smul_mem_smul_set_iff]
  rintro ⟨x, hx, hx₀⟩
  exact (Set.mem_Iio.1 hx).ne (OnePoint.coe_injective hx₀)

/-- The forward endpoint of a geodesic line is not on its left ideal arc. -/
@[simp]
theorem smul_infty_notMem_boundaryLeftHalfPlane (g : PSL(2, ℝ)) :
    g • (∞ : OnePoint ℝ) ∉ boundaryLeftHalfPlane g := by
  rw [boundaryLeftHalfPlane, Set.smul_mem_smul_set_iff]
  rintro ⟨x, -, hx⟩
  exact OnePoint.coe_ne_infty x hx

/-- The backward endpoint of a geodesic line is a zero of its side form. -/
theorem sideForm_eq_zero_of_smul_zero_eq {g : PSL(2, ℝ)} {e : ℝ}
    (h : g • ((0 : ℝ) : OnePoint ℝ) = e) : sideForm g e = 0 := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  rw [sideForm_mk_ofReal, (mk_smul_zero_eq_coe_iff.1 h).2]
  ring

/-- The forward endpoint of a geodesic line is a zero of its side form. -/
theorem sideForm_eq_zero_of_smul_infty_eq {g : PSL(2, ℝ)} {e : ℝ}
    (h : g • (∞ : OnePoint ℝ) = e) : sideForm g e = 0 := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  rw [sideForm_mk_ofReal, (mk_smul_infty_eq_coe_iff.1 h).2]
  ring

/-! ### The side form in terms of the endpoints -/

/-- A geodesic line running from `∞` down to the real point `e` is the vertical line `Re z = e`,
with side form `e - Re z`: its left half-plane is `{Re z > e}`. -/
theorem sideForm_eq_of_smul_zero_eq_infty {g : PSL(2, ℝ)} {e : ℝ}
    (h₀ : g • ((0 : ℝ) : OnePoint ℝ) = ∞) (h₁ : g • (∞ : OnePoint ℝ) = e) (z : ℂ) :
    sideForm g z = e - z.re := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  rw [mk_smul_zero_eq_infty_iff] at h₀
  obtain ⟨-, ha⟩ := mk_smul_infty_eq_coe_iff.1 h₁
  have hdet := det_mk A
  rw [sideForm_mk, h₀, ha]
  rw [h₀, ha] at hdet
  linear_combination (e - z.re) * hdet

/-- A geodesic line running from the real point `e` up to `∞` is the vertical line `Re z = e`,
with side form `Re z - e`: its left half-plane is `{Re z < e}`. -/
theorem sideForm_eq_of_smul_infty_eq_infty {g : PSL(2, ℝ)} {e : ℝ}
    (h₀ : g • ((0 : ℝ) : OnePoint ℝ) = e) (h₁ : g • (∞ : OnePoint ℝ) = ∞) (z : ℂ) :
    sideForm g z = z.re - e := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  rw [mk_smul_infty_eq_infty_iff] at h₁
  obtain ⟨-, hb⟩ := mk_smul_zero_eq_coe_iff.1 h₀
  have hdet := det_mk A
  rw [sideForm_mk, h₁, hb]
  rw [h₁, hb] at hdet
  linear_combination (z.re - e) * hdet

/-- A geodesic line running from the real point `e₀` to the real point `e₁` is the semicircle on
the diameter `[e₀, e₁]`: its side form is a positive multiple of `(e₁ - e₀) (ρ² - |z - m|²)`, for
the midpoint `m = (e₀ + e₁) / 2` and the half-length `ρ = (e₁ - e₀) / 2`. -/
theorem exists_sideForm_eq_of_smul_zero_of_smul_infty {g : PSL(2, ℝ)} {e₀ e₁ : ℝ}
    (h₀ : g • ((0 : ℝ) : OnePoint ℝ) = e₀) (h₁ : g • (∞ : OnePoint ℝ) = e₁) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ z : ℂ, sideForm g z =
      κ * (e₁ - e₀) * (((e₁ - e₀) / 2) ^ 2 - Complex.normSq (z - ((e₀ + e₁) / 2 : ℝ))) := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  obtain ⟨hd, hb⟩ := mk_smul_zero_eq_coe_iff.1 h₀
  obtain ⟨hc, ha⟩ := mk_smul_infty_eq_coe_iff.1 h₁
  have hdet := det_mk A
  rw [ha, hb] at hdet
  refine ⟨(A 1 0 * A 1 1) ^ 2, by positivity, fun z ↦ ?_⟩
  rw [sideForm_mk, ha, hb, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  linear_combination (-(A 1 0 * A 1 1) * (((e₁ - e₀) / 2) ^ 2 - ((z.re - (e₀ + e₁) / 2) *
    (z.re - (e₀ + e₁) / 2) + z.im * z.im))) * hdet

/-- The ideal point `∞` lies on the left of the semicircle from `e₀` to `e₁` exactly when the
semicircle runs from left to right, `e₀ < e₁`. -/
theorem infty_mem_boundaryLeftHalfPlane_iff {g : PSL(2, ℝ)} {e₀ e₁ : ℝ}
    (h₀ : g • ((0 : ℝ) : OnePoint ℝ) = e₀) (h₁ : g • (∞ : OnePoint ℝ) = e₁) :
    (∞ : OnePoint ℝ) ∈ boundaryLeftHalfPlane g ↔ e₀ < e₁ := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  obtain ⟨-, hb⟩ := mk_smul_zero_eq_coe_iff.1 h₀
  obtain ⟨hc, ha⟩ := mk_smul_infty_eq_coe_iff.1 h₁
  have hdet := det_mk A
  rw [ha, hb] at hdet
  rw [boundaryLeftHalfPlane, Set.mem_smul_set_iff_inv_smul_mem, ← QuotientGroup.mk_inv,
    OnePoint.pslMk_smul, OnePoint.smul_infty_eq_ite]
  simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, neg_eq_zero, hc, ↓reduceIte, Set.mem_image,
    OnePoint.coe_eq_coe, Set.mem_Iio, exists_eq_right]
  have hcd : (e₁ - e₀) * (A 1 0 * A 1 1) = 1 := by linear_combination hdet
  rw [div_neg, neg_lt_zero, div_pos_iff, ← mul_pos_iff, mul_comm]
  exact (pos_iff_pos_of_mul_pos (hcd.symm ▸ one_pos)).symm.trans sub_pos

/-- The real part along the geodesic line of a matrix. -/
private theorem re_geodesicLine_mk (A : SL(2, ℝ)) (t : ℝ) :
    (geodesicLine (A : PSL(2, ℝ)) t).re = (A 0 0 * A 1 0 * Real.exp t ^ 2 + A 0 1 * A 1 1) /
      (A 1 0 ^ 2 * Real.exp t ^ 2 + A 1 1 ^ 2) := by
  rw [geodesicLine_def, UpperHalfPlane.pslMk_smul, UpperHalfPlane.re,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Complex.div_re, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, mul_zero, Complex.ofReal_im, zero_mul, sub_self, zero_add,
    Complex.normSq_apply, Complex.add_im, Complex.mul_im, add_zero]
  rw [← add_div]
  congr 1 <;> ring

/-- Along the geodesic line from `e₀` to `e₁`, the real part is the weighted mean of `e₀` and `e₁`
with weights `d²` and `c² exp (2 t)`. -/
private theorem re_geodesicLine_eq_of_smul_zero_of_smul_infty {A : SL(2, ℝ)} {e₀ e₁ : ℝ}
    (h₀ : (A : PSL(2, ℝ)) • ((0 : ℝ) : OnePoint ℝ) = e₀)
    (h₁ : (A : PSL(2, ℝ)) • (∞ : OnePoint ℝ) = e₁)
    (t : ℝ) : (geodesicLine (A : PSL(2, ℝ)) t).re =
      (e₁ * (A 1 0 ^ 2 * Real.exp t ^ 2) + e₀ * A 1 1 ^ 2) /
        (A 1 0 ^ 2 * Real.exp t ^ 2 + A 1 1 ^ 2) := by
  obtain ⟨-, hb⟩ := mk_smul_zero_eq_coe_iff.1 h₀
  obtain ⟨-, ha⟩ := mk_smul_infty_eq_coe_iff.1 h₁
  rw [re_geodesicLine_mk, ha, hb]
  ring

/-- Along a semicircle running from `e₀` to `e₁ > e₀`, the real part increases strictly. -/
theorem strictMono_re_geodesicLine {g : PSL(2, ℝ)} {e₀ e₁ : ℝ}
    (h₀ : g • ((0 : ℝ) : OnePoint ℝ) = e₀) (h₁ : g • (∞ : OnePoint ℝ) = e₁) (h : e₀ < e₁) :
    StrictMono fun t ↦ (geodesicLine g t).re := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  have hd := (mk_smul_zero_eq_coe_iff.1 h₀).1
  have hc := (mk_smul_infty_eq_coe_iff.1 h₁).1
  intro s t hst
  simp only [re_geodesicLine_eq_of_smul_zero_of_smul_infty h₀ h₁]
  have hu : Real.exp s ^ 2 < Real.exp t ^ 2 := by gcongr
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have key : 0 < A 1 0 ^ 2 * A 1 1 ^ 2 * (e₁ - e₀) * (Real.exp t ^ 2 - Real.exp s ^ 2) := by
    have := sub_pos.2 h
    have := sub_pos.2 hu
    positivity
  linear_combination key

/-- Along a semicircle running from `e₀` to `e₁ > e₀`, the real part stays above `e₀`. -/
theorem lt_re_geodesicLine {g : PSL(2, ℝ)} {e₀ e₁ : ℝ}
    (h₀ : g • ((0 : ℝ) : OnePoint ℝ) = e₀) (h₁ : g • (∞ : OnePoint ℝ) = e₁) (h : e₀ < e₁)
    (t : ℝ) : e₀ < (geodesicLine g t).re := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  have hc := (mk_smul_infty_eq_coe_iff.1 h₁).1
  rw [re_geodesicLine_eq_of_smul_zero_of_smul_infty h₀ h₁, lt_div_iff₀ (by positivity)]
  have key : 0 < (e₁ - e₀) * (A 1 0 ^ 2 * Real.exp t ^ 2) := by
    have := sub_pos.2 h
    positivity
  linear_combination key

/-- Along a semicircle running from `e₀` to `e₁ > e₀`, the real part stays below `e₁`. -/
theorem re_geodesicLine_lt {g : PSL(2, ℝ)} {e₀ e₁ : ℝ}
    (h₀ : g • ((0 : ℝ) : OnePoint ℝ) = e₀) (h₁ : g • (∞ : OnePoint ℝ) = e₁) (h : e₀ < e₁)
    (t : ℝ) : (geodesicLine g t).re < e₁ := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  have hd := (mk_smul_zero_eq_coe_iff.1 h₀).1
  rw [re_geodesicLine_eq_of_smul_zero_of_smul_infty h₀ h₁, div_lt_iff₀ (by positivity)]
  have key : 0 < (e₁ - e₀) * A 1 1 ^ 2 := by
    have := sub_pos.2 h
    positivity
  linear_combination key

/-! ### Existence and uniqueness from the endpoints -/

/-- Every ordered pair of distinct ideal points are the backward and forward endpoints of a
geodesic line. -/
theorem exists_smul_zero_eq_and_smul_infty_eq {ξ η : OnePoint ℝ} (h : ξ ≠ η) :
    ∃ g : PSL(2, ℝ), g • ((0 : ℝ) : OnePoint ℝ) = ξ ∧ g • (∞ : OnePoint ℝ) = η := by
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq PSL(2, ℝ) (∞ : OnePoint ℝ) η
  have hne : k⁻¹ • ξ ≠ ∞ := by
    rw [ne_eq, inv_smul_eq_iff, hk]
    exact h
  obtain ⟨x, hx⟩ := OnePoint.ne_infty_iff_exists.1 hne
  refine ⟨k * upperRightHom x, ?_, ?_⟩
  · rw [mul_smul, upperRightHom_smul_coe, zero_add, hx, smul_inv_smul]
  · rw [mul_smul, upperRightHom_smul_infty, hk]

/-- An element of `PSL(2, ℝ)` fixing the ideal points `0` and `∞` is a dilation. -/
theorem exists_eq_dilation_of_smul_zero_of_smul_infty {k : PSL(2, ℝ)}
    (h₀ : k • ((0 : ℝ) : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ)) (h₁ : k • (∞ : OnePoint ℝ) = ∞) :
    ∃ s : ℝ, k = ((dilation s : SL(2, ℝ)) : PSL(2, ℝ)) := by
  induction k using QuotientGroup.induction_on with | H A => ?_
  rw [mk_smul_infty_eq_infty_iff] at h₁
  have h₀₁ : A 0 1 = 0 := by simpa using (mk_smul_zero_eq_coe_iff.1 h₀).2
  have hdet := det_mk A
  rw [h₁, h₀₁] at hdet
  have h₀₀ : A 0 0 ≠ 0 := by
    rintro h
    simp [h] at hdet
  rcases lt_or_gt_of_ne h₀₀ with hneg | hpos
  · refine ⟨2 * Real.log (-A 0 0), ?_⟩
    rw [← Matrix.ProjectiveSpecialLinearGroup.mk_neg A, eq_dilation_two_mul_log (A := -A)
      (by simp [h₁]) (by simp [h₀₁]) (by simpa using hneg)]
    simp
  · exact ⟨_, congrArg _ (eq_dilation_two_mul_log h₁ h₀₁ hpos)⟩

/-- Two elements with the same backward and the same forward endpoint differ by a dilation on the
right: their geodesic lines are reparametrisations of each other. -/
theorem exists_eq_mul_dilation_of_smul_zero_eq_of_smul_infty_eq {g g' : PSL(2, ℝ)}
    (h₀ : g • ((0 : ℝ) : OnePoint ℝ) = g' • ((0 : ℝ) : OnePoint ℝ))
    (h₁ : g • (∞ : OnePoint ℝ) = g' • (∞ : OnePoint ℝ)) :
    ∃ s : ℝ, g' = g * ((dilation s : SL(2, ℝ)) : PSL(2, ℝ)) := by
  obtain ⟨s, hs⟩ := exists_eq_dilation_of_smul_zero_of_smul_infty (k := g⁻¹ * g')
    (by rw [mul_smul, ← h₀, inv_smul_smul]) (by rw [mul_smul, ← h₁, inv_smul_smul])
  exact ⟨s, by rw [← hs, mul_inv_cancel_left]⟩

/-- A geodesic line from any point of `ℍ` to any ideal point, starting at parameter `0`. -/
theorem exists_geodesicLine_zero_eq_and_smul_infty_eq (z : ℍ) (ξ : OnePoint ℝ) :
    ∃ g : PSL(2, ℝ), geodesicLine g 0 = z ∧ g • (∞ : OnePoint ℝ) = ξ := by
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq PSL(2, ℝ) (∞ : OnePoint ℝ) ξ
  set w : ℍ := k⁻¹ • z
  refine ⟨k * (upperRightHom w.re * ↑(dilation (Real.log w.im))), ?_, ?_⟩
  · have hw : w.re +ᵥ dilation (Real.log w.im) • UpperHalfPlane.I = w := by
      apply UpperHalfPlane.coe_injective
      rw [UpperHalfPlane.coe_vadd, coe_dilation_smul, Real.exp_log w.im_pos, UpperHalfPlane.coe_I]
      apply Complex.ext <;> simp
    rw [geodesicLine_zero, mul_smul, mul_smul, UpperHalfPlane.pslMk_smul, upperRightHom_smul, hw,
      smul_inv_smul]
  · rw [mul_smul, mul_smul, dilation_smul_infty, upperRightHom_smul_infty, hk]

/-- An element of `PSL(2, ℝ)` is determined by the point of its geodesic line at parameter `0`
together with its forward endpoint. -/
theorem eq_of_geodesicLine_zero_eq_of_smul_infty_eq {g g' : PSL(2, ℝ)}
    (h₀ : geodesicLine g 0 = geodesicLine g' 0) (h₁ : g • (∞ : OnePoint ℝ) = g' • ∞) :
    g = g' := by
  rw [geodesicLine_zero, geodesicLine_zero, ← inv_smul_eq_iff, ← mul_smul] at h₀
  obtain ⟨θ, hθ⟩ := Matrix.ProjectiveSpecialLinearGroup.exists_rotation_eq_of_smul_I_eq_I h₀
  have h₁' : (g'⁻¹ * g) • (∞ : OnePoint ℝ) = ∞ := by rw [mul_smul, h₁, inv_smul_smul]
  rw [hθ, mk_smul_infty_eq_infty_iff] at h₁'
  simp only [Matrix.SpecialLinearGroup.coe_rotation, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    neg_eq_zero] at h₁'
  have hcos : Real.cos θ ^ 2 = 1 := by
    linear_combination Real.cos_sq_add_sin_sq θ - Real.sin θ * h₁'
  rw [← inv_mul_eq_one, ← inv_inv g', ← mul_inv_rev, inv_eq_one, hθ]
  -- `sin θ = 0`, so `cos θ = ±1` and the rotation is `±1`, trivial in `PSL(2, ℝ)`
  rcases sq_eq_one_iff.1 hcos with h | h
  · have hrot : Matrix.SpecialLinearGroup.rotation θ = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h, h₁']
    rw [hrot, QuotientGroup.mk_one]
  · have hrot : Matrix.SpecialLinearGroup.rotation θ = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h, h₁']
    rw [hrot, Matrix.ProjectiveSpecialLinearGroup.mk_neg, QuotientGroup.mk_one]

end TauCeti.UpperHalfPlane
