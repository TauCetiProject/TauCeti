/-
Copyright (c) 2026 The Tau Ceti authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti authors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.ProperAction
public import TauCeti.Topology.Algebra.ConstMulAction
public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.RingTheory.IntegralDomain

/-!
# Stabilizers of Fuchsian groups

The stabilizer of a point of the upper half-plane in a discrete subgroup of `PSL(2, ℝ)` is
finite cyclic. Its faithful character into the multiplicative monoid of `ℂ` is the complex
derivative of the Möbius action at the fixed point. This identifies the order of every stabilizer
element with the order of its
derivative, and a nonidentity element is represented by an elliptic matrix.

The derivative is first defined for the whole projective action. Its representative formula is
independent of the sign of an `SL(2, ℝ)` representative because the denominator is squared. The
denominator cocycle proves the chain rule directly, avoiding any extension of the upper-half-plane
action outside its natural domain. At a fixed point the imaginary-part formula shows that the
derivative has norm one.

## Main results

* `UpperHalfPlane.pslDerivative_mul`: the derivative cocycle for the `PSL(2, ℝ)` action.
* `TauCeti.stabilizerDerivative`: the derivative as a character of a point stabilizer.
* `TauCeti.stabilizerDerivative_injective`: faithfulness of that character.
* `TauCeti.orderOf_stabilizerDerivative`: equality of the elliptic and derivative orders.
* `TauCeti.isCyclic_stabilizer`: point stabilizers in Fuchsian groups are cyclic.
* `TauCeti.isElliptic_of_smul_eq_self_of_mk_ne_one`: nonidentity stabilizer elements have elliptic
  matrix representatives.

## References

* [S. Katok, *Fuchsian Groups*, Chapter 2][katok1992]
-/

public section

open scoped MatrixGroups
open Matrix.SpecialLinearGroup

noncomputable section

namespace UpperHalfPlane

/-- The complex derivative of the action of a projective special linear transformation. -/
def pslDerivative (g : PSL(2, ℝ)) (τ : ℍ) : ℂ :=
  deriv (fun z : ℂ ↦ ↑(g • ofComplex z)) τ

/-- The derivative of an `SL(2, ℝ)` representative is the reciprocal square of its Möbius
denominator. In particular, it is unchanged when the representative is multiplied by `-1`. -/
@[simp]
theorem pslDerivative_mk (g : SL(2, ℝ)) (τ : ℍ) :
    pslDerivative (↑g : PSL(2, ℝ)) τ = 1 / denom (mapGL ℝ g) τ ^ 2 := by
  have hfun : (fun z : ℂ ↦ (↑((↑g : PSL(2, ℝ)) • ofComplex z) : ℂ)) =
      fun z : ℂ ↦ (↑(g • ofComplex z) : ℂ) := by
    funext z
    rw [pslMk_smul]
  rw [pslDerivative, hfun]
  have hfun' : (fun z : ℂ ↦ (↑(g • ofComplex z) : ℂ)) =
      fun z : ℂ ↦ (↑((mapGL ℝ g) • ofComplex z) : ℂ) := rfl
  rw [hfun']
  rw [deriv_smul (by
    rw [← Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.SpecialLinearGroup.det_mapGL]
    exact zero_lt_one)]
  rw [← Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.SpecialLinearGroup.det_mapGL]
  simp

/-- The derivative of a projective Möbius transformation never vanishes on the upper
half-plane. -/
theorem pslDerivative_ne_zero (g : PSL(2, ℝ)) (τ : ℍ) : pslDerivative g τ ≠ 0 := by
  refine QuotientGroup.induction_on g fun a ↦ ?_
  rw [pslDerivative_mk]
  exact div_ne_zero one_ne_zero (pow_ne_zero _ (denom_ne_zero _ τ))

/-- The derivative is a multiplicative cocycle for the projective action. -/
theorem pslDerivative_mul (g h : PSL(2, ℝ)) (τ : ℍ) :
    pslDerivative (g * h) τ = pslDerivative g (h • τ) * pslDerivative h τ := by
  refine QuotientGroup.induction_on g fun a ↦ ?_
  refine QuotientGroup.induction_on h fun b ↦ ?_
  simp only [← QuotientGroup.mk_mul, pslDerivative_mk, pslMk_smul, map_mul]
  rw [denom_cocycle_σ]
  have hb : 0 < (mapGL ℝ b).det.val := by
    rw [Matrix.SpecialLinearGroup.det_mapGL]
    exact zero_lt_one
  simp only [σ, ite_eq_left hb]
  change 1 / (denom (mapGL ℝ a) (↑((mapGL ℝ b) • τ) : ℂ) *
      denom (mapGL ℝ b) τ) ^ 2 = _
  field_simp
  simp only [MulAction.compHom_smul_def]

/-- The identity projective transformation has derivative one. -/
@[simp]
theorem pslDerivative_one (τ : ℍ) : pslDerivative (1 : PSL(2, ℝ)) τ = 1 := by
  change pslDerivative (↑(1 : SL(2, ℝ)) : PSL(2, ℝ)) τ = 1
  rw [pslDerivative_mk]
  simp [denom]

/-- At a fixed point, the derivative has complex norm one. -/
theorem norm_pslDerivative_eq_one_of_smul_eq_self {g : PSL(2, ℝ)} {τ : ℍ}
    (hfix : g • τ = τ) : ‖pslDerivative g τ‖ = 1 := by
  revert hfix
  refine QuotientGroup.induction_on g fun a hfix ↦ ?_
  rw [pslDerivative_mk, norm_div, norm_one, norm_pow]
  have hact : (↑a : PSL(2, ℝ)) • τ = (mapGL ℝ a) • τ := by
    rw [pslMk_smul]
    rfl
  have him : ((mapGL ℝ a) • τ).im = τ.im := by
    rw [← hact]
    exact congrArg UpperHalfPlane.im hfix
  rw [τ.im_smul_eq_div_normSq] at him
  have hdet : |(mapGL ℝ a).det.val| = 1 := by
    rw [Matrix.SpecialLinearGroup.det_mapGL]
    simp
  rw [hdet, one_mul] at him
  have hsq : Complex.normSq (denom (mapGL ℝ a) τ) = 1 := by
    have hpos := τ.im_pos
    have hden := normSq_denom_pos (mapGL ℝ a) τ.im_ne_zero
    field_simp at him
    nlinarith
  rw [Complex.normSq_eq_norm_sq] at hsq
  have hnorm : ‖denom (mapGL ℝ a) τ‖ = 1 := by nlinarith [norm_nonneg (denom (mapGL ℝ a) τ)]
  rw [hnorm]
  simp

private theorem mem_center_of_smul_eq_self_of_derivative_eq_one (a : SL(2, ℝ)) (τ : ℍ)
    (hfix : a • τ = τ) (hderiv : 1 / denom (mapGL ℝ a) τ ^ 2 = 1) :
    a ∈ Subgroup.center SL(2, ℝ) := by
  let A : GL (Fin 2) ℝ := mapGL ℝ a
  have hden_ne : denom A τ ≠ 0 := denom_ne_zero A τ
  have hsq : denom A τ ^ 2 = 1 := by
    change 1 / denom A τ ^ 2 = 1 at hderiv
    field_simp at hderiv
    exact hderiv.symm
  have hAfix : A • τ = τ := hfix
  have hApos : 0 < A.det.val := by
    dsimp [A]
    rw [Matrix.SpecialLinearGroup.det_mapGL]
    exact zero_lt_one
  have hAeq : A = Matrix.SpecialLinearGroup.toGL a := by
    ext i j
    simp [A, Matrix.SpecialLinearGroup.mapGL_coe_matrix, Algebra.algebraMap_self]
  rw [sq_eq_one_iff] at hsq
  apply (Matrix.SpecialLinearGroup.toGL_mem_center_iff a).mp
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  rcases hsq with hden | hden
  · have hc : A 1 0 = 0 := by
      simpa [denom, τ.im_ne_zero] using congrArg Complex.im hden
    have hd : A 1 1 = 1 := by simpa [denom, hc] using hden
    have hnum := gl_smul_eq_iff_num_eq.mp hAfix
    simp only [σ, ite_eq_left hApos] at hnum
    have ha : A 0 0 = 1 := by
      simpa [num, denom, hc, hd, τ.im_ne_zero] using congrArg Complex.im hnum
    have hb : A 0 1 = 0 := by
      simpa [num, denom, hc, hd, ha] using congrArg Complex.re hnum
    refine ⟨1, ?_⟩
    rw [← hAeq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar, ha, hb, hc, hd]
  · have hc : A 1 0 = 0 := by
      simpa [denom, τ.im_ne_zero] using congrArg Complex.im hden
    have hdC : (A 1 1 : ℂ) = -1 := by simpa [denom, hc] using hden
    have hd : A 1 1 = -1 := by exact_mod_cast hdC
    have hnum := gl_smul_eq_iff_num_eq.mp hAfix
    simp only [σ, ite_eq_left hApos] at hnum
    have ha : A 0 0 = -1 := by
      have hi : A 0 0 * τ.im = -τ.im := by
        simpa [num, denom, hc, hd] using congrArg Complex.im hnum
      nlinarith [τ.im_pos]
    have hb : A 0 1 = 0 := by
      simpa [num, denom, hc, hd, ha] using congrArg Complex.re hnum
    refine ⟨-1, ?_⟩
    rw [← hAeq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar, ha, hb, hc, hd]

/-- A projective transformation fixing a point is determined by its derivative there. -/
theorem eq_one_of_smul_eq_self_of_pslDerivative_eq_one {g : PSL(2, ℝ)} {τ : ℍ}
    (hfix : g • τ = τ) (hderiv : pslDerivative g τ = 1) : g = 1 := by
  revert hfix hderiv
  refine QuotientGroup.induction_on g fun a hfix hderiv ↦ ?_
  rw [pslDerivative_mk] at hderiv
  rw [QuotientGroup.eq_one_iff]
  apply mem_center_of_smul_eq_self_of_derivative_eq_one a τ
  · simpa only [pslMk_smul] using hfix
  · exact hderiv

end UpperHalfPlane

namespace TauCeti

open MulAction

open _root_.UpperHalfPlane

/-- The derivative character of the stabilizer of a point in a subgroup of `PSL(2, ℝ)`. -/
@[expose]
def stabilizerDerivative (G : Subgroup PSL(2, ℝ)) (τ : ℍ) : stabilizer G τ →* ℂ where
  toFun g := pslDerivative (g.1.1 : PSL(2, ℝ)) τ
  map_one' := pslDerivative_one τ
  map_mul' g h := by
    change pslDerivative ((g.1.1 : PSL(2, ℝ)) * (h.1.1 : PSL(2, ℝ))) τ = _
    rw [pslDerivative_mul]
    rw [show (h.1.1 : PSL(2, ℝ)) • τ = τ from h.property]

/-- Evaluating the stabilizer derivative character is evaluating the projective derivative of the
underlying element. -/
@[simp]
theorem stabilizerDerivative_apply (G : Subgroup PSL(2, ℝ)) (τ : ℍ)
    (g : stabilizer G τ) :
    stabilizerDerivative G τ g = pslDerivative (g.1.1 : PSL(2, ℝ)) τ := rfl

/-- The derivative character takes values in the nonzero complex numbers. -/
theorem stabilizerDerivative_ne_zero (G : Subgroup PSL(2, ℝ)) (τ : ℍ)
    (g : stabilizer G τ) : stabilizerDerivative G τ g ≠ 0 :=
  pslDerivative_ne_zero _ _

/-- The derivative character takes values on the complex unit circle. -/
theorem norm_stabilizerDerivative (G : Subgroup PSL(2, ℝ)) (τ : ℍ)
    (g : stabilizer G τ) : ‖stabilizerDerivative G τ g‖ = 1 :=
  norm_pslDerivative_eq_one_of_smul_eq_self g.property

/-- The derivative character of a point stabilizer is injective. -/
theorem stabilizerDerivative_injective (G : Subgroup PSL(2, ℝ)) (τ : ℍ) :
    Function.Injective (stabilizerDerivative G τ) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext g
  simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hg
    apply Subtype.ext
    apply Subtype.ext
    exact eq_one_of_smul_eq_self_of_pslDerivative_eq_one g.property hg
  · rintro rfl
    exact map_one (stabilizerDerivative G τ)

/-- The order of a stabilizer element equals the order of its derivative. -/
theorem orderOf_stabilizerDerivative (G : Subgroup PSL(2, ℝ)) (τ : ℍ)
    (g : stabilizer G τ) : orderOf (stabilizerDerivative G τ g) = orderOf g :=
  orderOf_injective (stabilizerDerivative G τ) (stabilizerDerivative_injective G τ) g

/-- Every point stabilizer in a Fuchsian group is cyclic. -/
theorem isCyclic_stabilizer (G : Subgroup PSL(2, ℝ)) [DiscreteTopology G] (τ : ℍ) :
    IsCyclic (stabilizer G τ) :=
  isCyclic_of_injective_ringHom (stabilizerDerivative G τ)
    (stabilizerDerivative_injective G τ)

/-- A representative of a nonidentity projective transformation fixing a point is elliptic. -/
theorem isElliptic_of_smul_eq_self_of_mk_ne_one (a : SL(2, ℝ)) (τ : ℍ)
    (hfix : (↑a : PSL(2, ℝ)) • τ = τ) (hne : (↑a : PSL(2, ℝ)) ≠ 1) :
    (mapGL ℝ a : GL (Fin 2) ℝ).IsElliptic := by
  apply _root_.UpperHalfPlane.isElliptic_of_exists_smul_eq_self
  · rw [← Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.SpecialLinearGroup.det_mapGL]
    exact zero_lt_one
  · intro hcenter
    apply hne
    rw [QuotientGroup.eq_one_iff]
    exact (Matrix.SpecialLinearGroup.toGL_mem_center_iff a).mp hcenter
  · refine ⟨τ, ?_⟩
    have ha : a • τ = τ := by simpa only [UpperHalfPlane.pslMk_smul] using hfix
    exact ha

end TauCeti
