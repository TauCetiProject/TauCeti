/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Topology.Algebra.Group.Quotient
public import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.MatrixFinTwo.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The Möbius action of `GL(2, ℝ)` on `ℍ^± = ℂ ∖ ℝ`

Mathlib's action `UpperHalfPlane.glAction` of `GL(2, ℝ)` on the upper half-plane `ℍ` lets a
matrix of negative determinant act by a Möbius transformation followed by complex conjugation.
This file sets up the raw Möbius action `z ↦ (a z + b) / (c z + d)` on the union of the upper
and lower half-planes, `ℍ^± = ℂ ∖ ℝ`, and relates the two: folding the lower half-plane onto
the upper one by conjugation is equivariant from the raw action to `glAction`, and for positive
determinant the raw and folded formulas agree on `ℍ`.

The raw action is transitive. The stabilizer of `i` consists of the matrices `!![a, b; -b, a]`,
equivalently of the nonzero real multiples of the rotations `!![cos θ, sin θ; -sin θ, cos θ]`,
that is the group `ℝ^× SO(2)`. The map `x + i y ↦ !![y, x; 0, 1]` is a continuous section of
`g ↦ g • i`, so the orbit map at `i` induces a `GL(2, ℝ)`-equivariant homeomorphism
`GL(2, ℝ) ⧸ ℝ^× SO(2) ≃ₜ ℍ^±`. On the upper half-plane the section has positive determinant,
so `GL(2, ℝ)^+` acts transitively on `ℍ` with stabilizer `ℝ^× SO(2) ∩ GL(2, ℝ)^+` at `i`.

## Main declarations

* `TauCeti.UpperLowerHalfPlane`: the space `ℍ^± = ℂ ∖ ℝ`, with the raw Möbius action
  `TauCeti.UpperLowerHalfPlane.instMulAction`.
* `TauCeti.UpperLowerHalfPlane.fold` and `TauCeti.UpperLowerHalfPlane.fold_smul`: folding onto
  `ℍ` intertwines the raw action with `UpperHalfPlane.glAction`.
* `TauCeti.UpperLowerHalfPlane.ofUpperHalfPlane_smul_of_det_pos`: for positive determinant the
  raw action restricts to `glAction` on `ℍ`.
* `TauCeti.UpperLowerHalfPlane.smul_I_eq_I_iff` and
  `TauCeti.UpperLowerHalfPlane.smul_I_eq_I_iff_exists_rotation`: the stabilizer of `i` is
  `ℝ^× SO(2)`.
* `TauCeti.UpperLowerHalfPlane.sectionGL`: the continuous section `x + i y ↦ !![y, x; 0, 1]`.
* `TauCeti.UpperLowerHalfPlane.quotientStabilizerHomeomorph`: the equivariant homeomorphism
  `GL(2, ℝ) ⧸ stabilizer i ≃ₜ ℍ^±`.
* `TauCeti.UpperLowerHalfPlane.exists_det_pos_smul_I_eq` and
  `TauCeti.UpperLowerHalfPlane.gl_smul_I_eq_I_iff_smul_I_eq_I_of_det_pos`: transitivity of
  `GL(2, ℝ)^+` on `ℍ` and its stabilizer of `i`.
-/

public section

noncomputable section

open UpperHalfPlane Matrix ComplexConjugate

namespace TauCeti

/-- The union `ℍ^± = ℂ ∖ ℝ` of the upper and lower half-planes, with the subspace topology. -/
@[expose] def UpperLowerHalfPlane : Type := {z : ℂ // z.im ≠ 0}
deriving TopologicalSpace

namespace UpperLowerHalfPlane

/-- The complex number underlying a point of `ℍ^±`. -/
@[coe, expose] def coe (z : UpperLowerHalfPlane) : ℂ := z.val

instance instCoeOut : CoeOut UpperLowerHalfPlane ℂ := ⟨coe⟩

/-- The point of `ℍ^±` given by a complex number with nonzero imaginary part. -/
@[expose] def mk (z : ℂ) (hz : z.im ≠ 0) : UpperLowerHalfPlane := ⟨z, hz⟩

@[simp]
theorem coe_mk (z : ℂ) (hz : z.im ≠ 0) : ((mk z hz : UpperLowerHalfPlane) : ℂ) = z := rfl

@[ext]
theorem ext {z w : UpperLowerHalfPlane} (h : (z : ℂ) = w) : z = w := Subtype.ext h

theorem im_ne_zero (z : UpperLowerHalfPlane) : (z : ℂ).im ≠ 0 := z.property

theorem isEmbedding_coe : Topology.IsEmbedding ((↑) : UpperLowerHalfPlane → ℂ) :=
  Topology.IsEmbedding.subtypeVal

@[fun_prop]
theorem continuous_coe : Continuous ((↑) : UpperLowerHalfPlane → ℂ) := continuous_subtypeVal

/-- The raw Möbius transformation `z ↦ (a z + b) / (c z + d)` of `ℍ^±` by `g ∈ GL(2, ℝ)`.
Unlike `UpperHalfPlane.glAction`, a matrix of negative determinant exchanges the two
half-planes. -/
instance instSMul : SMul (GL (Fin 2) ℝ) UpperLowerHalfPlane where
  smul g z := mk (num g z / denom g z) (moebius_im_ne_zero g z.im_ne_zero)

theorem coe_smul (g : GL (Fin 2) ℝ) (z : UpperLowerHalfPlane) :
    ((g • z : UpperLowerHalfPlane) : ℂ) = num g z / denom g z := rfl

/-- The raw Möbius action `z ↦ (a z + b) / (c z + d)` of `GL(2, ℝ)` on `ℍ^±`. -/
instance instMulAction : MulAction (GL (Fin 2) ℝ) UpperLowerHalfPlane where
  one_smul z := ext (by simp [coe_smul, num, denom])
  mul_smul g h z := ext (by rw [coe_smul, coe_smul, coe_smul, moebius_mul g h z.im_ne_zero])

theorem im_smul (g : GL (Fin 2) ℝ) (z : UpperLowerHalfPlane) :
    ((g • z : UpperLowerHalfPlane) : ℂ).im =
      g.det.val * (z : ℂ).im / Complex.normSq (denom g z) :=
  moebius_im g z

/-- A raw Möbius image lies in the upper half-plane exactly when `det g * Im z > 0`. -/
theorem im_smul_pos_iff (g : GL (Fin 2) ℝ) (z : UpperLowerHalfPlane) :
    0 < ((g • z : UpperLowerHalfPlane) : ℂ).im ↔ 0 < g.det.val * (z : ℂ).im := by
  rw [im_smul, div_pos_iff_of_pos_right (normSq_denom_pos g z.im_ne_zero)]

/-- A raw Möbius image lies in the lower half-plane exactly when `det g * Im z < 0`. -/
theorem im_smul_neg_iff (g : GL (Fin 2) ℝ) (z : UpperLowerHalfPlane) :
    ((g • z : UpperLowerHalfPlane) : ℂ).im < 0 ↔ g.det.val * (z : ℂ).im < 0 := by
  rw [im_smul, div_lt_iff₀ (normSq_denom_pos g z.im_ne_zero), zero_mul]

/-- The raw action of `GL(2, ℝ)` on `ℍ^±` is jointly continuous. -/
instance instContinuousSMul : ContinuousSMul (GL (Fin 2) ℝ) UpperLowerHalfPlane where
  continuous_smul := by
    refine isEmbedding_coe.continuous_iff.2 ?_
    simp only [Function.comp_def, coe_smul]
    exact ((num_continuous.comp (continuous_fst.prodMk (continuous_coe.comp continuous_snd))).div
      (denom_continuous.comp (continuous_fst.prodMk (continuous_coe.comp continuous_snd)))
      fun p ↦ denom_ne_zero_of_im p.1 p.2.im_ne_zero)

/-- The orbit map `g ↦ g • z` of the raw action is continuous. -/
theorem continuous_smul_left (z : UpperLowerHalfPlane) :
    Continuous fun g : GL (Fin 2) ℝ ↦ g • z :=
  continuous_id.smul continuous_const

/-- The point of `ℍ^±` given by a point of the upper half-plane. -/
def ofUpperHalfPlane (τ : ℍ) : UpperLowerHalfPlane := mk τ τ.im_ne_zero

@[simp]
theorem coe_ofUpperHalfPlane (τ : ℍ) : ((ofUpperHalfPlane τ : UpperLowerHalfPlane) : ℂ) = τ :=
  (rfl)

theorem ofUpperHalfPlane_injective : Function.Injective ofUpperHalfPlane :=
  fun _ _ h ↦ UpperHalfPlane.ext (congrArg coe h)

/-- For positive determinant the raw action agrees with `UpperHalfPlane.glAction` on `ℍ`. -/
theorem ofUpperHalfPlane_smul_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (τ : ℍ) :
    ofUpperHalfPlane (g • τ) = g • ofUpperHalfPlane τ :=
  ext (coe_smul_of_det_pos hg τ)

/-- Folding `ℍ^±` onto the upper half-plane: the identity on `ℍ`, complex conjugation on the
lower half-plane. -/
def fold (z : UpperLowerHalfPlane) : ℍ :=
  if h : 0 < (z : ℂ).im then ⟨z, h⟩
  else ⟨conj (z : ℂ), by simpa using lt_of_le_of_ne (not_lt.1 h) z.im_ne_zero⟩

theorem coe_fold_of_im_pos {z : UpperLowerHalfPlane} (hz : 0 < (z : ℂ).im) :
    (fold z : ℂ) = z := by
  simp [fold, hz]

theorem coe_fold_of_im_neg {z : UpperLowerHalfPlane} (hz : (z : ℂ).im < 0) :
    (fold z : ℂ) = conj (z : ℂ) := by
  simp [fold, hz.not_gt]

@[simp]
theorem fold_ofUpperHalfPlane (τ : ℍ) : fold (ofUpperHalfPlane τ) = τ :=
  UpperHalfPlane.ext (coe_fold_of_im_pos τ.im_pos)

/-- Folding is equivariant from the raw Möbius action on `ℍ^±` to Mathlib's
`UpperHalfPlane.glAction` on `ℍ`. -/
theorem fold_smul (g : GL (Fin 2) ℝ) (z : UpperLowerHalfPlane) : fold (g • z) = g • fold z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul]
  have hconj : ∀ w : ℂ, num g (conj w) / denom g (conj w) = conj (num g w / denom g w) := by
    intro w
    simp [num, denom]
  rcases g.det.ne_zero.lt_or_gt with hdet | hdet <;>
    rcases z.im_ne_zero.lt_or_gt with hz | hz
  · rw [coe_fold_of_im_pos ((im_smul_pos_iff g z).2 (mul_pos_of_neg_of_neg hdet hz)),
      coe_fold_of_im_neg hz, σ_apply_of_det_neg hdet, hconj, Complex.conj_conj, coe_smul]
  · rw [coe_fold_of_im_neg ((im_smul_neg_iff g z).2 (mul_neg_of_neg_of_pos hdet hz)),
      coe_fold_of_im_pos hz, σ_apply_of_det_neg hdet, coe_smul]
  · rw [coe_fold_of_im_neg ((im_smul_neg_iff g z).2 (mul_neg_of_pos_of_neg hdet hz)),
      coe_fold_of_im_neg hz, σ_apply_of_det_pos hdet, hconj, coe_smul]
  · rw [coe_fold_of_im_pos ((im_smul_pos_iff g z).2 (mul_pos hdet hz)), coe_fold_of_im_pos hz,
      σ_apply_of_det_pos hdet, coe_smul]

/-- The point `i` of `ℍ^±`. -/
def I : UpperLowerHalfPlane := ofUpperHalfPlane UpperHalfPlane.I

@[simp]
theorem coe_I : ((I : UpperLowerHalfPlane) : ℂ) = Complex.I := (rfl)

@[simp]
theorem fold_I : fold I = UpperHalfPlane.I := fold_ofUpperHalfPlane _

/-- An element of `GL(2, ℝ)` fixes `i` in the raw action exactly when it has the form
`!![a, b; -b, a]`. -/
theorem smul_I_eq_I_iff (g : GL (Fin 2) ℝ) : g • I = I ↔ g 0 0 = g 1 1 ∧ g 0 1 = -g 1 0 := by
  have hd := denom_ne_zero_of_im g (z := Complex.I) (by simp)
  rw [UpperLowerHalfPlane.ext_iff, coe_smul, coe_I, div_eq_iff hd]
  simp [num, denom, Complex.ext_iff, and_comm]

/-- The stabilizer of `i` in the raw action is `ℝ^× SO(2)`: its elements are the nonzero real
multiples of the rotations `!![cos θ, sin θ; -sin θ, cos θ]`. -/
theorem smul_I_eq_I_iff_exists_rotation (g : GL (Fin 2) ℝ) :
    g • I = I ↔ ∃ r : ℝ, r ≠ 0 ∧ ∃ θ : ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = r • (SpecialLinearGroup.rotation θ : Matrix _ _ ℝ) := by
  rw [smul_I_eq_I_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    set w : ℂ := ⟨g 0 0, g 0 1⟩
    have hw : w ≠ 0 := by
      intro hw
      have h00 : g 0 0 = 0 := congrArg Complex.re hw
      have h01 : g 0 1 = 0 := congrArg Complex.im hw
      apply g.det_ne_zero
      rw [det_fin_two, h00, h01]
      ring
    refine ⟨‖w‖, norm_ne_zero_iff.2 hw, Complex.arg w, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.coe_rotation, Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg,
        w] <;>
      linarith
  · rintro ⟨r, -, θ, h⟩
    simp [h, SpecialLinearGroup.coe_rotation]

/-- The matrix `!![y, x; 0, 1]` attached to `z = x + i y` in `ℍ^±`. -/
def sectionGL (z : UpperLowerHalfPlane) : GL (Fin 2) ℝ where
  val := !![(z : ℂ).im, (z : ℂ).re; 0, 1]
  inv := !![((z : ℂ).im)⁻¹, -(z : ℂ).re * ((z : ℂ).im)⁻¹; 0, 1]
  val_inv := by
    have := z.im_ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, this]
    field_simp
    ring
  inv_val := by
    have := z.im_ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, this]
    field_simp
    ring

@[simp]
theorem coe_sectionGL (z : UpperLowerHalfPlane) :
    (sectionGL z : Matrix (Fin 2) (Fin 2) ℝ) = !![(z : ℂ).im, (z : ℂ).re; 0, 1] := (rfl)

theorem coe_sectionGL_inv (z : UpperLowerHalfPlane) :
    (((sectionGL z)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((z : ℂ).im)⁻¹, -(z : ℂ).re * ((z : ℂ).im)⁻¹; 0, 1] :=
  (rfl)

theorem det_sectionGL (z : UpperLowerHalfPlane) : (sectionGL z).det.val = (z : ℂ).im := by
  simp [GeneralLinearGroup.val_det_apply, det_fin_two]

@[simp]
theorem sectionGL_smul_I (z : UpperLowerHalfPlane) : sectionGL z • I = z := by
  ext
  simp [coe_smul, num, denom, Complex.ext_iff]

theorem continuous_sectionGL : Continuous sectionGL := by
  have him : Continuous fun z : UpperLowerHalfPlane ↦ (z : ℂ).im := by fun_prop
  have hre : Continuous fun z : UpperLowerHalfPlane ↦ (z : ℂ).re := by fun_prop
  have hinv : Continuous fun z : UpperLowerHalfPlane ↦ ((z : ℂ).im)⁻¹ :=
    him.inv₀ fun z ↦ z.im_ne_zero
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · simp only [Function.comp_def, coe_sectionGL]
    refine continuous_matrix fun i j ↦ ?_
    fin_cases i <;> fin_cases j
    exacts [him, hre, continuous_const, continuous_const]
  · simp only [coe_sectionGL_inv]
    refine continuous_matrix fun i j ↦ ?_
    fin_cases i <;> fin_cases j
    exacts [hinv, hre.neg.mul hinv, continuous_const, continuous_const]

/-- The raw action of `GL(2, ℝ)` on `ℍ^±` is transitive. -/
instance instIsPretransitive : MulAction.IsPretransitive (GL (Fin 2) ℝ) UpperLowerHalfPlane :=
  .of_orbit fun z ↦ ⟨sectionGL z, sectionGL_smul_I z⟩

/-- `GL(2, ℝ) ⧸ ℝ^× SO(2)` is homeomorphic to `ℍ^±` through `g ↦ g • i`. Here `ℝ^× SO(2)` is
the stabilizer of `i` (`smul_I_eq_I_iff_exists_rotation`); the inverse is induced by the
continuous section `sectionGL`. -/
def quotientStabilizerHomeomorph :
    GL (Fin 2) ℝ ⧸ MulAction.stabilizer (GL (Fin 2) ℝ) I ≃ₜ UpperLowerHalfPlane where
  toFun := MulAction.ofQuotientStabilizer (GL (Fin 2) ℝ) I
  invFun z := (sectionGL z : GL (Fin 2) ℝ ⧸ MulAction.stabilizer (GL (Fin 2) ℝ) I)
  left_inv q := by
    induction q using QuotientGroup.induction_on with | H g => ?_
    apply MulAction.injective_ofQuotientStabilizer
    simp [MulAction.ofQuotientStabilizer_mk]
  right_inv z := by simp [MulAction.ofQuotientStabilizer_mk]
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_smul_left I)
  continuous_invFun := QuotientGroup.continuous_mk.comp continuous_sectionGL

@[simp]
theorem quotientStabilizerHomeomorph_mk (g : GL (Fin 2) ℝ) :
    quotientStabilizerHomeomorph (g : GL (Fin 2) ℝ ⧸ MulAction.stabilizer (GL (Fin 2) ℝ) I) =
      g • I :=
  (rfl)

/-- The homeomorphism `GL(2, ℝ) ⧸ ℝ^× SO(2) ≃ₜ ℍ^±` is `GL(2, ℝ)`-equivariant. -/
theorem quotientStabilizerHomeomorph_smul (g : GL (Fin 2) ℝ)
    (q : GL (Fin 2) ℝ ⧸ MulAction.stabilizer (GL (Fin 2) ℝ) I) :
    quotientStabilizerHomeomorph (g • q) = g • quotientStabilizerHomeomorph q :=
  MulAction.ofQuotientStabilizer_smul _ _ g q

@[simp]
theorem quotientStabilizerHomeomorph_symm_apply (z : UpperLowerHalfPlane) :
    quotientStabilizerHomeomorph.symm z =
      (sectionGL z : GL (Fin 2) ℝ ⧸ MulAction.stabilizer (GL (Fin 2) ℝ) I) :=
  (rfl)

/-- `GL(2, ℝ)^+` acts transitively on the upper half-plane: the section `x + i y ↦
!![y, x; 0, 1]` has positive determinant on `ℍ`. -/
theorem exists_det_pos_smul_I_eq (τ : ℍ) :
    ∃ g : GL (Fin 2) ℝ, 0 < g.det.val ∧ g • UpperHalfPlane.I = τ := by
  have hpos : 0 < (sectionGL (ofUpperHalfPlane τ)).det.val := by
    simpa [det_sectionGL] using τ.im_pos
  refine ⟨_, hpos, ofUpperHalfPlane_injective ?_⟩
  rw [ofUpperHalfPlane_smul_of_det_pos hpos]
  exact sectionGL_smul_I _

/-- The stabilizer of `i` in `GL(2, ℝ)^+` for `UpperHalfPlane.glAction` is the positive
determinant part of the raw stabilizer `ℝ^× SO(2)`. -/
theorem gl_smul_I_eq_I_iff_smul_I_eq_I_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    g • UpperHalfPlane.I = UpperHalfPlane.I ↔ g • I = I := by
  rw [I, ← ofUpperHalfPlane_smul_of_det_pos hg]
  exact ofUpperHalfPlane_injective.eq_iff.symm

end UpperLowerHalfPlane

end TauCeti
