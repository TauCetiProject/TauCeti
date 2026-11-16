/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Analysis.Normed.Operator.Conformal
public import TauCeti.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.LinearAlgebra.Orientation.Basic

/-!
# The oriented Jacobian of a linear map

For real inner product spaces `V` and `W` of the same finite dimension `n`, equipped with
orientations `oV` and `oW`, a linear map `A : V →ₗ[ℝ] W` pulls the target oriented volume form
`oW.volumeForm` back to a scalar multiple of `oV.volumeForm`. That scalar is the **oriented
Jacobian** `oV.orientedJacobian oW A` (`J_{oV, oW}(A)`): for every `n`-tuple `v : Fin n → V`,
$$
  \mathrm{vol}_{o_W}(A v_0, \dots, A v_{n-1})
    = J_{o_V, o_W}(A) \, \mathrm{vol}_{o_V}(v_0, \dots, v_{n-1}).
$$
Equivalently, `oV.orientedJacobian oW A = oW.volumeForm (A ∘ v) / oV.volumeForm v` on any linearly
independent `n`-tuple `v : Fin n → V` (in particular, on any basis `b` of `V`); when `0 < n`, this
simplifies to `oW.volumeForm (A ∘ b)` on any positively oriented orthonormal basis `b` of `V`. In
dimension `0`, it takes value `1` when the two zero-dimensional orientations have the same sign
relative to `Module.Oriented.positiveOrientation`, and `-1` otherwise.

Unlike `LinearMap.det`, the oriented Jacobian applies between *distinct* inner product spaces of
equal dimension, such as the tangent spaces `T_x M` and `T_{f(x)} N` along a map `f : M → N`
between oriented Riemannian `n`-manifolds. Unlike `LinearMap.normDet`, it retains the orientation
sign needed for degree formulas and pullback of top-degree differential forms.

## Main definitions and results

* `Orientation.orientedJacobian`: the signed volume factor `J_{oV, oW}(A) : ℝ` of `A : V →ₗ[ℝ] W`.
* `Orientation.volumeForm_comp_eq`, `Orientation.volumeForm_compLinearMap`,
  `Orientation.volumeFormL_compContinuousLinearMap`: pullback of the oriented volume form by `A`
  multiplies it by `oV.orientedJacobian oW A`, and this property characterizes the scalar uniquely
  (`Orientation.eq_orientedJacobian_of_volumeForm_compLinearMap`,
  `Orientation.eq_orientedJacobian_of_volumeForm_comp_eq`).
* `Orientation.orientedJacobian_eq_div`,
  `Orientation.orientedJacobian_eq_volumeForm_of_orthonormal`,
  `Orientation.orientedJacobian_eq_det_toMatrix_mul_div`,
  `Orientation.orientedJacobian_eq_det_toMatrix`: evaluation in arbitrary bases and in oriented
  orthonormal frames.
* `Orientation.orientedJacobian_fin_zero_eq_ite`, `Orientation.orientedJacobian_fin_zero_self`,
  `Orientation.abs_orientedJacobian_fin_zero`, `Orientation.orientedJacobian_fin_one_eq_inner`,
  `Orientation.areaForm_comp_eq`: explicit formulas in dimensions `0`, `1`, and `2`.
* `Orientation.orientedJacobian_comp`, `Orientation.orientedJacobian_id`,
  `Orientation.orientedJacobian_neg_left`, `Orientation.orientedJacobian_neg_right`,
  `Orientation.orientedJacobian_smul`: multiplicativity under composition, reversal of either
  orientation, and homogeneity of degree `n`.
* `Orientation.orientedJacobian_self`, `Orientation.orientedJacobian_eq_neg_det_of_ne`,
  `Orientation.orientedJacobian_eq_det_comp_mul_div_volumeForm`,
  `Orientation.orientedJacobian_eq_det_comp_mul_div_abs_volumeForm_of_map_eq_of_linearIndependent`,
  `Orientation.orientedJacobian_eq_det_comp_mul_div_abs_volumeForm_of_map_eq`,
  `Orientation.orientedJacobian_eq_det_comp_mul_div`,
  `Orientation.orientedJacobian_comp_eq_div_mul_of_volumeForm_compLinearMap`: recovery of
  `LinearMap.det` on a single oriented space, expression in terms of reference linear equivalences
  (coordinate charts) over arbitrary real vector spaces or oriented inner product spaces, and
  transformation under rescaling of the volume forms (changes of metric).
* `Orientation.abs_orientedJacobian`, `Orientation.orientedJacobian_sq_eq_det_gram`,
  `Orientation.orientedJacobian_sq`, `Orientation.orientedJacobian_adjoint`: agreement of
  `|oV.orientedJacobian oW A|` with `LinearMap.normDet A`, Gram-determinant square formula, and
  invariance under taking the adjoint.
* `Orientation.abs_orientedJacobian_toLinearMap_le`, `Orientation.abs_orientedJacobian_le`,
  `Orientation.norm_apply_eq_of_abs_orientedJacobian_eq_norm_pow`,
  `Orientation.abs_orientedJacobian_toLinearMap_eq_norm_pow_iff`: Hadamard's inequality
  `|J(A)| ≤ ‖A‖ ^ n`, together with its sharp equality case (`A = 0` or `IsConformalMap A`).
* `Orientation.contDiff_orientedJacobian`, `Orientation.continuous_orientedJacobian`: smoothness
  and continuity of `A ↦ oV.orientedJacobian oW A.toLinearMap` on `V →L[ℝ] W`.
* `Orientation.orientedJacobian_ne_zero_iff`, `Orientation.orientedJacobian_pos_iff`,
  `Orientation.orientedJacobian_neg_iff`: characterizations of nonvanishing by bijectivity and of
  positivity (negativity) by orientation preservation (reversal) along `Orientation.map`.

## Implementation notes

Following `Orientation.volumeForm` in Mathlib, the algebraic core assumes only
`[Fact (Module.finrank ℝ V = n)]` and `[Fact (Module.finrank ℝ W = n)]` without separate
`[FiniteDimensional]` typeclasses: when `n = m + 1`, finite-dimensionality is automatic via
`FiniteDimensional.of_fact_finrank_eq_succ`, while in degree `0` the `Fin 0` volume forms are
nonzero constants regardless of the ambient space. Hypotheses `[FiniteDimensional ℝ V]` and
`[FiniteDimensional ℝ W]` are added only where `LinearMap.normDet`,
`LinearMap.toContinuousLinearMap`, `LinearMap.adjoint`, the zero-dimensional Hadamard equality
rigidity characterization (where `finrank ℝ V = 0` only implies `Subsingleton V` under
`FiniteDimensional ℝ V`), or zero-dimensional bijectivity genuinely require them.

## References

* O. Martio, S. Rickman, J. Väisälä, *Definitions for quasiregular mappings*, Ann. Acad. Sci.
  Fenn. Ser. A I 448 (1969), p. 6.
* T. Iwaniec, G. Martin, *Geometric Function Theory and Non-linear Analysis*, Oxford University
  Press, 2001, Chapters 4–6.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2012, Chapter 15.
-/

public section

noncomputable section

open Module
open scoped ContDiff RealInnerProductSpace

namespace Orientation

/-! ### Definition and volume-form characterization -/

section TwoSpaces

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {n : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)]

/-- The **oriented Jacobian** `J_{oV, oW}(A)` of a linear map `A : V →ₗ[ℝ] W` between oriented real
inner product spaces of the same dimension `n`: the unique scalar multiplying `oV.volumeForm` into
the pullback `oW.volumeForm.compLinearMap A`. -/
def orientedJacobian (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) : ℝ :=
  if hn : 0 < n then
    oW.volumeForm (A ∘ oV.finOrthonormalBasis hn Fact.out)
  else
    oW.volumeForm 0 / oV.volumeForm 0

/-- Evaluating `oW.volumeForm` on the image of any `n`-tuple under `A` multiplies `oV.volumeForm`
by `oV.orientedJacobian oW A`. -/
theorem volumeForm_comp_eq (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) (v : Fin n → V) :
    oW.volumeForm (A ∘ v) = oV.orientedJacobian oW A * oV.volumeForm v := by
  rcases n with - | m
  · have hne : oV.volumeForm 0 ≠ 0 :=
      oV.volumeForm_apply_ne_zero_iff.mpr linearIndependent_empty_type
    have hJ : oV.orientedJacobian oW A = oW.volumeForm 0 / oV.volumeForm 0 := by
      simp [orientedJacobian]
    rw [Subsingleton.elim (A ∘ v) 0, Subsingleton.elim v 0, hJ, div_mul_cancel₀ _ hne]
  · let b := oV.finOrthonormalBasis m.succ_pos Fact.out
    have hb : b.toBasis.orientation = oV := oV.finOrthonormalBasis_orientation m.succ_pos Fact.out
    have hpull := congrArg (· v)
      ((oW.volumeForm.compLinearMap A).eq_smul_basis_det b.toBasis)
    have hJ : oV.orientedJacobian oW A = oW.volumeForm (A ∘ b) := by
      simp [orientedJacobian, b]
    simpa only [AlternatingMap.compLinearMap_apply, ← Function.comp_def, smul_apply, smul_eq_mul,
      OrthonormalBasis.coe_toBasis, ← oV.volumeForm_robust b hb, hJ] using hpull

/-- Pulling `oW.volumeForm` back along a linear map `A` multiplies `oV.volumeForm` by
`oV.orientedJacobian oW A`. -/
theorem volumeForm_compLinearMap (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) :
    oW.volumeForm.compLinearMap A = oV.orientedJacobian oW A • oV.volumeForm := by
  ext v
  simp only [AlternatingMap.compLinearMap_apply, ← Function.comp_def, smul_apply, smul_eq_mul]
  exact oV.volumeForm_comp_eq oW A v

/-- Pulling the continuous volume form `oW.volumeFormL` back along a continuous linear map `A`
multiplies `oV.volumeFormL` by `oV.orientedJacobian oW A.toLinearMap`. -/
theorem volumeFormL_compContinuousLinearMap (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →L[ℝ] W) :
    oW.volumeFormL.compContinuousLinearMap A =
      oV.orientedJacobian oW A.toLinearMap • oV.volumeFormL := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply, volumeFormL_apply, smul_eq_mul,
    ← ContinuousLinearMap.coe_coe]
  exact oV.volumeForm_comp_eq oW A.toLinearMap v

/-- Uniqueness of the oriented Jacobian from evaluation on a single linearly independent `n`-tuple.
-/
theorem eq_orientedJacobian_of_volumeForm_comp_eq (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W) {c : ℝ} {v : Fin n → V}
    (hv : LinearIndependent ℝ v) (hc : oW.volumeForm (A ∘ v) = c * oV.volumeForm v) :
    c = oV.orientedJacobian oW A :=
  mul_right_cancel₀ (oV.volumeForm_apply_ne_zero_iff.mpr hv)
    (hc.symm.trans (oV.volumeForm_comp_eq oW A v))

/-- Uniqueness of the oriented Jacobian as the pullback multiplier on volume forms. -/
theorem eq_orientedJacobian_of_volumeForm_compLinearMap (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W) {c : ℝ}
    (hc : oW.volumeForm.compLinearMap A = c • oV.volumeForm) :
    c = oV.orientedJacobian oW A := by
  rcases n with - | m
  · exact oV.eq_orientedJacobian_of_volumeForm_comp_eq oW A linearIndependent_empty_type
      (by simpa only [AlternatingMap.compLinearMap_apply, ← Function.comp_def, smul_apply,
        smul_eq_mul] using congrArg (· ![]) hc)
  · let b := oV.finOrthonormalBasis m.succ_pos Fact.out
    exact oV.eq_orientedJacobian_of_volumeForm_comp_eq oW A b.toBasis.linearIndependent
      (by simpa only [AlternatingMap.compLinearMap_apply, ← Function.comp_def, smul_apply,
        smul_eq_mul, OrthonormalBasis.coe_toBasis] using congrArg (· b) hc)

/-- On any linearly independent `n`-tuple `v`, the oriented Jacobian is the ratio of the target
volume of `A ∘ v` to the source volume of `v`. -/
theorem orientedJacobian_eq_div_of_linearIndependent (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W) {v : Fin n → V} (hv : LinearIndependent ℝ v) :
    oV.orientedJacobian oW A = oW.volumeForm (A ∘ v) / oV.volumeForm v := by
  rw [oV.volumeForm_comp_eq oW A v,
    mul_div_cancel_right₀ _ (oV.volumeForm_apply_ne_zero_iff.mpr hv)]

/-- On any basis `b` of `V`, `oV.orientedJacobian oW A = oW.volumeForm (A ∘ b) / oV.volumeForm b`.
-/
theorem orientedJacobian_eq_div (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) (b : Basis (Fin n) ℝ V) :
    oV.orientedJacobian oW A = oW.volumeForm (A ∘ b) / oV.volumeForm b :=
  oV.orientedJacobian_eq_div_of_linearIndependent oW A b.linearIndependent

/-- On a positively oriented orthonormal basis `b` of `V`, the oriented Jacobian is
`oW.volumeForm (A ∘ b)`. -/
theorem orientedJacobian_eq_volumeForm_of_orthonormal (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W) (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = oV) :
    oV.orientedJacobian oW A = oW.volumeForm (A ∘ b) := by
  have hb1 : oV.volumeForm b = 1 := by
    rw [← oV.volumeFormL_apply, oV.volumeFormL_apply_orthonormal b hb]
  rw [oV.orientedJacobian_eq_div oW A b.toBasis, OrthonormalBasis.coe_toBasis, hb1, div_one]

/-- On a negatively oriented orthonormal basis `b` of `V`, the oriented Jacobian is
`-oW.volumeForm (A ∘ b)`. -/
theorem orientedJacobian_eq_neg_volumeForm_of_orthonormal (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W) (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation ≠ oV) :
    oV.orientedJacobian oW A = -oW.volumeForm (A ∘ b) := by
  have hb_neg : oV.volumeForm b = -1 := by
    rw [oV.volumeForm_robust_neg b hb, neg_apply]
    simpa only [OrthonormalBasis.coe_toBasis] using congrArg Neg.neg b.toBasis.det_self
  rw [oV.orientedJacobian_eq_div oW A b.toBasis, OrthonormalBasis.coe_toBasis, hb_neg, div_neg,
    div_one]

/-- In arbitrary bases `bV` of `V` and `bW` of `W`, the oriented Jacobian of `A` is the determinant
of its matrix `A.toMatrix bV bW` multiplied by the ratio of target and source basis volumes
`oW.volumeForm bW / oV.volumeForm bV`. -/
theorem orientedJacobian_eq_det_toMatrix_mul_div (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W)
    (bV : Basis (Fin n) ℝ V) (bW : Basis (Fin n) ℝ W) :
    oV.orientedJacobian oW A =
      (A.toMatrix bV bW).det * (oW.volumeForm bW / oV.volumeForm bV) := by
  have hW : oW.volumeForm (A ∘ bV) = oW.volumeForm bW * bW.det (A ∘ bV) := by
    simpa only [smul_apply, smul_eq_mul] using
      congrArg (· (A ∘ bV)) (oW.volumeForm.eq_smul_basis_det bW)
  rw [oV.orientedJacobian_eq_div oW A bV, hW, Basis.det_apply,
    ← LinearMap.toMatrix_eq_basisToMatrix]
  ring

/-- In positively oriented orthonormal bases `bV` of `V` and `bW` of `W`, the oriented Jacobian of
`A` is the determinant of its matrix `A.toMatrix bV.toBasis bW.toBasis`. -/
theorem orientedJacobian_eq_det_toMatrix (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W)
    (bV : OrthonormalBasis (Fin n) ℝ V) (hbV : bV.toBasis.orientation = oV)
    (bW : OrthonormalBasis (Fin n) ℝ W) (hbW : bW.toBasis.orientation = oW) :
    oV.orientedJacobian oW A = (A.toMatrix bV.toBasis bW.toBasis).det := by
  have hV : oV.volumeForm bV.toBasis = 1 := by
    rw [OrthonormalBasis.coe_toBasis, ← oV.volumeFormL_apply,
      oV.volumeFormL_apply_orthonormal bV hbV]
  have hW : oW.volumeForm bW.toBasis = 1 := by
    rw [OrthonormalBasis.coe_toBasis, ← oW.volumeFormL_apply,
      oW.volumeFormL_apply_orthonormal bW hbW]
  rw [oV.orientedJacobian_eq_det_toMatrix_mul_div oW A bV.toBasis bW.toBasis, hV, hW, div_one,
    mul_one]

end TwoSpaces

/-! ### Explicit formulas in dimensions `0`, `1`, and `2` -/

section ZeroDim

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ V = 0)] [Fact (finrank ℝ W = 0)]

/-- Between zero-dimensional spaces carrying `positiveOrientation`, the oriented Jacobian is `1`. -/
@[simp]
theorem orientedJacobian_fin_zero_pos_pos {A : V →ₗ[ℝ] W} :
    (positiveOrientation : Orientation ℝ V (Fin 0)).orientedJacobian positiveOrientation A = 1 := by
  simp [orientedJacobian]

open Classical in
/-- In dimension `0`, `oV.orientedJacobian oW A` is `1` if `oV` and `oW` have the same sign
relative to `positiveOrientation`, and `-1` otherwise. -/
theorem orientedJacobian_fin_zero_eq_ite (oV : Orientation ℝ V (Fin 0))
    (oW : Orientation ℝ W (Fin 0)) (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian oW A =
      if (oV = positiveOrientation ↔ oW = positiveOrientation) then 1 else -1 := by
  have hneV : (positiveOrientation : Orientation ℝ V (Fin 0)) ≠ -positiveOrientation :=
    Module.Ray.ne_neg_self _
  have hneW : (positiveOrientation : Orientation ℝ W (Fin 0)) ≠ -positiveOrientation :=
    Module.Ray.ne_neg_self _
  rcases oV.eq_or_eq_neg_of_isEmpty with rfl | rfl <;>
    rcases oW.eq_or_eq_neg_of_isEmpty with rfl | rfl <;>
    simp [orientedJacobian, hneV.symm, hneW.symm]

/-- In dimension `0`, the oriented Jacobian has absolute value `1`. -/
@[simp]
theorem abs_orientedJacobian_fin_zero (oV : Orientation ℝ V (Fin 0))
    (oW : Orientation ℝ W (Fin 0)) (A : V →ₗ[ℝ] W) :
    |oV.orientedJacobian oW A| = 1 := by
  rw [oV.orientedJacobian_fin_zero_eq_ite oW A]
  split_ifs <;> norm_num

/-- In dimension `0`, `oV.orientedJacobian oW A = 1` iff `oV` and `oW` have the same sign relative
to `positiveOrientation` (`oV = positiveOrientation ↔ oW = positiveOrientation`). -/
theorem orientedJacobian_fin_zero_eq_one_iff (oV : Orientation ℝ V (Fin 0))
    (oW : Orientation ℝ W (Fin 0)) (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian oW A = 1 ↔ (oV = positiveOrientation ↔ oW = positiveOrientation) := by
  rw [oV.orientedJacobian_fin_zero_eq_ite oW A]
  split_ifs with h <;> norm_num [h]

/-- In dimension `0`, `oV.orientedJacobian oW A = -1` iff exactly one of `oV`, `oW` equals
`positiveOrientation`. -/
theorem orientedJacobian_fin_zero_eq_neg_one_iff (oV : Orientation ℝ V (Fin 0))
    (oW : Orientation ℝ W (Fin 0)) (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian oW A = -1 ↔ ¬(oV = positiveOrientation ↔ oW = positiveOrientation) := by
  rw [oV.orientedJacobian_fin_zero_eq_ite oW A]
  split_ifs with h <;> norm_num [h]

open Classical in
/-- For two orientations on the same zero-dimensional space, `o₁.orientedJacobian o₂ A` is `1` if
`o₁ = o₂` and `-1` otherwise. -/
theorem orientedJacobian_fin_zero_eq_ite' (o₁ o₂ : Orientation ℝ V (Fin 0)) (A : V →ₗ[ℝ] V) :
    o₁.orientedJacobian o₂ A = if o₁ = o₂ then 1 else -1 := by
  rw [o₁.orientedJacobian_fin_zero_eq_ite o₂ A]
  congr 1
  exact propext ⟨fun h ↦ by
    rcases o₁.eq_or_eq_neg_of_isEmpty with rfl | rfl <;>
      rcases o₂.eq_or_eq_neg_of_isEmpty with rfl | rfl <;>
      simp_all [(Module.Ray.ne_neg_self _).symm],
    fun h ↦ h ▸ Iff.rfl⟩

/-- For a single orientation on a zero-dimensional space, the oriented Jacobian of any endomorphism
is `1`. -/
@[simp]
theorem orientedJacobian_fin_zero_self (o : Orientation ℝ V (Fin 0)) (A : V →ₗ[ℝ] V) :
    o.orientedJacobian o A = 1 := by
  rw [o.orientedJacobian_fin_zero_eq_ite' o A]
  simp only [↓reduceIte]

end ZeroDim

section OneDim

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ V = 1)] [Fact (finrank ℝ W = 1)]

/-- Between oriented one-dimensional real inner product spaces with positively oriented unit basis
vectors `bV 0` and `bW 0`, the oriented Jacobian of `A` is `⟪bW 0, A (bV 0)⟫`. -/
theorem orientedJacobian_fin_one_eq_inner (oV : Orientation ℝ V (Fin 1))
    (oW : Orientation ℝ W (Fin 1)) (A : V →ₗ[ℝ] W)
    (bV : OrthonormalBasis (Fin 1) ℝ V) (hbV : bV.toBasis.orientation = oV)
    (bW : OrthonormalBasis (Fin 1) ℝ W) (hbW : bW.toBasis.orientation = oW) :
    oV.orientedJacobian oW A = ⟪bW 0, A (bV 0)⟫ := by
  rw [oV.orientedJacobian_eq_det_toMatrix oW A bV hbV bW hbW, Matrix.det_fin_one]
  simp [LinearMap.toMatrix_apply, bW.repr_apply_apply]

end OneDim

section TwoDim

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ V = 2)] [Fact (finrank ℝ W = 2)]

/-- Between oriented Euclidean planes, `A` scales the area form `Orientation.areaForm` by
`oV.orientedJacobian oW A`. -/
theorem areaForm_comp_eq (oV : Orientation ℝ V (Fin 2))
    (oW : Orientation ℝ W (Fin 2)) (A : V →ₗ[ℝ] W) (x y : V) :
    oW.areaForm (A x) (A y) = oV.orientedJacobian oW A * oV.areaForm x y := by
  have hxy : ![A x, A y] = A ∘ ![x, y] := by ext i; fin_cases i <;> simp
  rw [areaForm_to_volumeForm, areaForm_to_volumeForm, hxy, oV.volumeForm_comp_eq oW A]

end TwoDim

/-! ### Functoriality, orientation reversal, and linear operations -/

section ThreeSpaces

variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {n : ℕ} [Fact (finrank ℝ U = n)] [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)]

/-- **Multiplicativity of the oriented Jacobian**: for three oriented spaces of dimension `n`,
`J_{oU, oW}(B ∘ A) = J_{oV, oW}(B) * J_{oU, oV}(A)`. -/
theorem orientedJacobian_comp (oU : Orientation ℝ U (Fin n)) (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : U →ₗ[ℝ] V) (B : V →ₗ[ℝ] W) :
    oU.orientedJacobian oW (B ∘ₗ A) = oV.orientedJacobian oW B * oU.orientedJacobian oV A := by
  symm
  refine oU.eq_orientedJacobian_of_volumeForm_compLinearMap oW (B ∘ₗ A) ?_
  ext v
  have hcomp : (fun i ↦ (B ∘ₗ A) (v i)) = B ∘ (A ∘ v) := by ext i; simp
  rw [AlternatingMap.compLinearMap_apply, hcomp, oV.volumeForm_comp_eq oW B (A ∘ v),
    oU.volumeForm_comp_eq oV A v, smul_apply, smul_eq_mul, mul_assoc]

end ThreeSpaces

section TwoSpacesOps

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {n : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)]

/-- Reversing the source orientation negates the oriented Jacobian. -/
@[simp]
theorem orientedJacobian_neg_left (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) :
    (-oV).orientedJacobian oW A = -oV.orientedJacobian oW A := by
  symm
  refine (-oV).eq_orientedJacobian_of_volumeForm_compLinearMap oW A ?_
  rw [oV.volumeForm_compLinearMap oW A, volumeForm_neg_orientation, smul_neg, neg_smul, neg_neg]

/-- Reversing the target orientation negates the oriented Jacobian. -/
@[simp]
theorem orientedJacobian_neg_right (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian (-oW) A = -oV.orientedJacobian oW A := by
  symm
  refine oV.eq_orientedJacobian_of_volumeForm_compLinearMap (-oW) A ?_
  ext v
  simp only [AlternatingMap.compLinearMap_apply, volumeForm_neg_orientation, neg_apply,
    smul_apply, smul_eq_mul, neg_mul]
  rw [← Function.comp_def, oV.volumeForm_comp_eq oW A v]

/-- Scaling `A` by `c : ℝ` multiplies its oriented Jacobian by `c ^ n`. -/
@[simp]
theorem orientedJacobian_smul (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (c : ℝ) (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian oW (c • A) = c ^ n * oV.orientedJacobian oW A := by
  symm
  refine oV.eq_orientedJacobian_of_volumeForm_compLinearMap oW (c • A) ?_
  ext v
  have hsmul : (fun i ↦ (c • A) (v i)) = fun i ↦ c • (A ∘ v) i := by ext i; simp
  rw [AlternatingMap.compLinearMap_apply, hsmul, oW.volumeForm.map_smul_univ]
  simp [oV.volumeForm_comp_eq oW A v, mul_assoc]

/-- Negating `A` multiplies its oriented Jacobian by `(-1) ^ n`. -/
theorem orientedJacobian_neg (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian oW (-A) = (-1) ^ n * oV.orientedJacobian oW A := by
  simpa only [neg_one_smul] using oV.orientedJacobian_smul oW (-1) A

/-- In positive dimension, the zero linear map has oriented Jacobian `0`. -/
@[simp]
theorem orientedJacobian_zero_of_pos (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (hn : 0 < n) :
    oV.orientedJacobian oW 0 = 0 := by
  simpa [zero_pow hn.ne'] using oV.orientedJacobian_smul oW 0 0

/-! ### Endomorphisms, inverses, and coordinate expressions -/

/-- For a single orientation on `V`, the oriented Jacobian of an endomorphism `A` is
`LinearMap.det A`. -/
@[simp low]
theorem orientedJacobian_self (oV : Orientation ℝ V (Fin n)) (A : V →ₗ[ℝ] V) :
    oV.orientedJacobian oV A = A.det := by
  rcases n with - | m
  · rw [oV.orientedJacobian_fin_zero_self A, LinearMap.det_eq_one_of_finrank_eq_zero Fact.out A]
  · let b := oV.finOrthonormalBasis m.succ_pos Fact.out
    have hb : b.toBasis.orientation = oV := oV.finOrthonormalBasis_orientation m.succ_pos Fact.out
    rw [oV.orientedJacobian_eq_det_toMatrix oV A b hb b hb, LinearMap.det_toMatrix]

/-- The identity map has oriented Jacobian `1` with respect to a single orientation. -/
theorem orientedJacobian_id (oV : Orientation ℝ V (Fin n)) :
    oV.orientedJacobian oV LinearMap.id = 1 := by
  simp

/-- For two distinct orientations on `V`, the oriented Jacobian of an endomorphism `A` is
`-LinearMap.det A`. -/
theorem orientedJacobian_eq_neg_det_of_ne (o₁ o₂ : Orientation ℝ V (Fin n)) (h : o₁ ≠ o₂)
    (A : V →ₗ[ℝ] V) :
    o₁.orientedJacobian o₂ A = -A.det := by
  have hcard : Fintype.card (Fin n) = finrank ℝ V := (Fintype.card_fin n).trans (Eq.symm Fact.out)
  rw [(o₂.ne_iff_eq_neg_of_card_eq_finrank o₁ hcard).mp h.symm]
  simp

/-- For two distinct orientations on `V`, the identity map has oriented Jacobian `-1`. -/
theorem orientedJacobian_id_of_ne (o₁ o₂ : Orientation ℝ V (Fin n)) (h : o₁ ≠ o₂) :
    o₁.orientedJacobian o₂ LinearMap.id = -1 := by
  rw [o₁.orientedJacobian_eq_neg_det_of_ne o₂ h, LinearMap.det_id]

/-- The oriented Jacobians of a linear equivalence and its inverse multiply to `1`. -/
@[simp]
theorem orientedJacobian_symm_mul (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (e : V ≃ₗ[ℝ] W) :
    oW.orientedJacobian oV e.symm.toLinearMap * oV.orientedJacobian oW e.toLinearMap = 1 := by
  have hcomp : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id := by ext x; simp
  rw [← oV.orientedJacobian_comp oW oV e.toLinearMap e.symm.toLinearMap, hcomp,
    oV.orientedJacobian_id]

/-- The oriented Jacobians of a linear equivalence and its inverse multiply to `1` in either order.
-/
@[simp]
theorem orientedJacobian_mul_symm (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (e : V ≃ₗ[ℝ] W) :
    oV.orientedJacobian oW e.toLinearMap * oW.orientedJacobian oV e.symm.toLinearMap = 1 := by
  rw [mul_comm, oV.orientedJacobian_symm_mul oW e]

/-- The oriented Jacobian of a linear equivalence is nonzero. -/
theorem orientedJacobian_linearEquiv_ne_zero (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (e : V ≃ₗ[ℝ] W) :
    oV.orientedJacobian oW e.toLinearMap ≠ 0 :=
  right_ne_zero_of_mul_eq_one (oV.orientedJacobian_symm_mul oW e)

/-- The oriented Jacobian of the inverse of a linear equivalence is the reciprocal of its oriented
Jacobian. -/
theorem orientedJacobian_symm (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (e : V ≃ₗ[ℝ] W) :
    oW.orientedJacobian oV e.symm.toLinearMap = (oV.orientedJacobian oW e.toLinearMap)⁻¹ :=
  eq_inv_of_mul_eq_one_left (oV.orientedJacobian_symm_mul oW e)

/-- **Coordinate expression of the oriented Jacobian over an arbitrary real vector space**: given
linear equivalences `eV : V ≃ₗ[ℝ] U` and `eW : W ≃ₗ[ℝ] U` to a common model space `U` with a basis
`b`, `oV.orientedJacobian oW A` is the determinant of `eW ∘ A ∘ eV⁻¹` multiplied by the ratio of
target and source volume forms on the transported frames `b.map eW.symm` and `b.map eV.symm`. -/
theorem orientedJacobian_eq_det_comp_mul_div_volumeForm
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (b : Basis (Fin n) ℝ U) (eV : V ≃ₗ[ℝ] U) (eW : W ≃ₗ[ℝ] U) (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian oW A =
      (eW.toLinearMap ∘ₗ A ∘ₗ eV.symm.toLinearMap).det *
        (oW.volumeForm (b.map eW.symm) / oV.volumeForm (b.map eV.symm)) := by
  rw [oV.orientedJacobian_eq_det_toMatrix_mul_div oW A (b.map eV.symm) (b.map eW.symm),
    LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right, LinearEquiv.symm_symm,
    LinearMap.det_toMatrix]

/-- **Coordinate expression of the oriented Jacobian on any linearly independent tuple**: given
linear equivalences `eV : V ≃ₗ[ℝ] U` and `eW : W ≃ₗ[ℝ] U` to a common real vector space `U` and a
linearly independent `n`-tuple `v : Fin n → U`, `oV.orientedJacobian oW A` is
`(eW ∘ A ∘ eV⁻¹).det * (oW.volumeForm (eW⁻¹ ∘ v) / oV.volumeForm (eV⁻¹ ∘ v))`. -/
theorem orientedJacobian_eq_det_comp_mul_div_volumeForm_of_linearIndependent
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (eV : V ≃ₗ[ℝ] U) (eW : W ≃ₗ[ℝ] U) (A : V →ₗ[ℝ] W)
    {v : Fin n → U} (hv : LinearIndependent ℝ v) :
    oV.orientedJacobian oW A =
      (eW.toLinearMap ∘ₗ A ∘ₗ eV.symm.toLinearMap).det *
        (oW.volumeForm (eW.symm ∘ v) / oV.volumeForm (eV.symm ∘ v)) := by
  rcases n with - | m
  · have hdet : (eW.toLinearMap ∘ₗ A ∘ₗ eV.symm.toLinearMap).det = 1 :=
      LinearMap.det_eq_one_of_finrank_eq_zero (eV.finrank_eq.symm.trans Fact.out) _
    rw [hdet, one_mul, Subsingleton.elim (eW.symm ∘ v) 0, Subsingleton.elim (eV.symm ∘ v) 0,
      oV.orientedJacobian_eq_div_of_linearIndependent oW A linearIndependent_empty_type,
      Subsingleton.elim (A ∘ ![]) 0, Subsingleton.elim (![] : Fin 0 → V) 0]
  · have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ m
    have hcard : Fintype.card (Fin (m + 1)) = finrank ℝ U := by
      rw [Fintype.card_fin, ← eV.finrank_eq, Fact.out (p := finrank ℝ V = m + 1)]
    let b := basisOfLinearIndependentOfCardEqFinrank hv hcard
    have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank hv hcard
    rw [oV.orientedJacobian_eq_det_comp_mul_div_volumeForm oW b eV eW A, b.coe_map, b.coe_map, hb]

/-- When `eV : V ≃ₗ[ℝ] U` and `eW : W ≃ₗ[ℝ] U` transport `oV` and `oW` to the same orientation on
`U`, the signs of the coordinate volume forms cancel on any linearly independent `n`-tuple
`v : Fin n → U`, and `oV.orientedJacobian oW A` equals
`(eW ∘ A ∘ eV⁻¹).det * (|oW.volumeForm (eW⁻¹ ∘ v)| / |oV.volumeForm (eV⁻¹ ∘ v)|)`. -/
theorem orientedJacobian_eq_det_comp_mul_div_abs_volumeForm_of_map_eq_of_linearIndependent
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (eV : V ≃ₗ[ℝ] U) (eW : W ≃ₗ[ℝ] U)
    (h : Orientation.map (Fin n) eV oV = Orientation.map (Fin n) eW oW)
    (A : V →ₗ[ℝ] W) {v : Fin n → U} (hv : LinearIndependent ℝ v) :
    oV.orientedJacobian oW A =
      (eW.toLinearMap ∘ₗ A ∘ₗ eV.symm.toLinearMap).det *
        (|oW.volumeForm (eW.symm ∘ v)| / |oV.volumeForm (eV.symm ∘ v)|) := by
  rw [oV.orientedJacobian_eq_det_comp_mul_div_volumeForm_of_linearIndependent oW eV eW A hv]
  congr 1
  have hmap : Orientation.map (Fin n) (eV.trans eW.symm) oV = oW := by
    rw [Orientation.map_trans, h, ← Orientation.map_symm, Equiv.symm_apply_apply]
  have hcomp : (eV.trans eW.symm) ∘ (eV.symm ∘ v) = eW.symm ∘ v := by
    ext i
    simp
  have hpos : 0 < oW.volumeForm (eW.symm ∘ v) ↔ 0 < oV.volumeForm (eV.symm ∘ v) := by
    simpa only [hmap, hcomp] using oV.volumeForm_map_comp_pos_iff (eV.trans eW.symm) (eV.symm ∘ v)
  have hWne : oW.volumeForm (eW.symm ∘ v) ≠ 0 :=
    oW.volumeForm_apply_ne_zero_iff.mpr
      (by simpa only [LinearEquiv.coe_coe] using hv.map' eW.symm.toLinearMap eW.symm.ker)
  have hVne : oV.volumeForm (eV.symm ∘ v) ≠ 0 :=
    oV.volumeForm_apply_ne_zero_iff.mpr
      (by simpa only [LinearEquiv.coe_coe] using hv.map' eV.symm.toLinearMap eV.symm.ker)
  by_cases hWpos : 0 < oW.volumeForm (eW.symm ∘ v)
  · rw [abs_of_pos hWpos, abs_of_pos (hpos.mp hWpos)]
  · have hWneg : oW.volumeForm (eW.symm ∘ v) < 0 :=
      lt_of_le_of_ne (not_lt.mp hWpos) hWne
    have hVneg : oV.volumeForm (eV.symm ∘ v) < 0 :=
      lt_of_le_of_ne (not_lt.mp (mt hpos.mpr hWpos)) hVne
    rw [abs_of_neg hWneg, abs_of_neg hVneg, neg_div_neg_eq]

/-- When `eV : V ≃ₗ[ℝ] U` and `eW : W ≃ₗ[ℝ] U` transport `oV` and `oW` to the same orientation on
`U`, the signs of the coordinate volume forms cancel and `oV.orientedJacobian oW A` equals
`(eW ∘ A ∘ eV⁻¹).det * (|oW.volumeForm (b.map eW.symm)| / |oV.volumeForm (b.map eV.symm)|)`. -/
theorem orientedJacobian_eq_det_comp_mul_div_abs_volumeForm_of_map_eq
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (b : Basis (Fin n) ℝ U) (eV : V ≃ₗ[ℝ] U) (eW : W ≃ₗ[ℝ] U)
    (h : Orientation.map (Fin n) eV oV = Orientation.map (Fin n) eW oW)
    (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian oW A =
      (eW.toLinearMap ∘ₗ A ∘ₗ eV.symm.toLinearMap).det *
        (|oW.volumeForm (b.map eW.symm)| / |oV.volumeForm (b.map eV.symm)|) := by
  rw [b.coe_map eW.symm, b.coe_map eV.symm]
  exact oV.orientedJacobian_eq_det_comp_mul_div_abs_volumeForm_of_map_eq_of_linearIndependent
    oW eV eW h A b.linearIndependent

end TwoSpacesOps

section ModelInnerProduct

variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {n : ℕ} [Fact (finrank ℝ U = n)] [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)]

/-- **Coordinate expression of the oriented Jacobian over an oriented inner product model space**:
given linear equivalences `eV : V ≃ₗ[ℝ] U` and `eW : W ≃ₗ[ℝ] U` to `(U, oU)`,
`oV.orientedJacobian oW A` is the determinant of `eW ∘ A ∘ eV⁻¹` multiplied by the ratio of the
oriented Jacobians of `eV` and `eW`. -/
theorem orientedJacobian_eq_det_comp_mul_div (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (oU : Orientation ℝ U (Fin n))
    (eV : V ≃ₗ[ℝ] U) (eW : W ≃ₗ[ℝ] U) (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian oW A =
      (eW.toLinearMap ∘ₗ A ∘ₗ eV.symm.toLinearMap).det *
        (oV.orientedJacobian oU eV.toLinearMap / oW.orientedJacobian oU eW.toLinearMap) := by
  have hA : A = (eW.symm.toLinearMap ∘ₗ (eW.toLinearMap ∘ₗ A ∘ₗ eV.symm.toLinearMap)) ∘ₗ
      eV.toLinearMap := by ext x; simp
  conv_lhs => rw [hA]
  rw [oV.orientedJacobian_comp oU oW eV.toLinearMap,
    oU.orientedJacobian_comp oU oW _ eW.symm.toLinearMap,
    oU.orientedJacobian_self, oW.orientedJacobian_symm oU eW, div_eq_mul_inv]
  ring

end ModelInnerProduct

section MetricRescaling

variable {V V' W W' : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [NormedAddCommGroup W'] [InnerProductSpace ℝ W']
  {n : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ V' = n)]
  [Fact (finrank ℝ W = n)] [Fact (finrank ℝ W' = n)]

/-- **Metric-rescaling formula**: if linear maps `iV : V' →ₗ[ℝ] V` and `jW : W →ₗ[ℝ] W'` rescale
volume forms by `ρV` and `ρW` (`vol_{oV'} = ρV • iV^* vol_{oV}` and
`jW^* vol_{oW'} = ρW • vol_{oW}`), then the oriented Jacobian of `jW ∘ A ∘ iV` equals
`(ρW / ρV) * oV.orientedJacobian oW A`. -/
theorem orientedJacobian_comp_eq_div_mul_of_volumeForm_compLinearMap
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (oV' : Orientation ℝ V' (Fin n)) (oW' : Orientation ℝ W' (Fin n))
    (iV : V' →ₗ[ℝ] V) (jW : W →ₗ[ℝ] W') {ρV ρW : ℝ}
    (hV : oV'.volumeForm = ρV • oV.volumeForm.compLinearMap iV)
    (hW : oW'.volumeForm.compLinearMap jW = ρW • oW.volumeForm)
    (A : V →ₗ[ℝ] W) :
    oV'.orientedJacobian oW' (jW ∘ₗ A ∘ₗ iV) =
      (ρW / ρV) * oV.orientedJacobian oW A := by
  have hρW : ρW = oW.orientedJacobian oW' jW :=
    oW.eq_orientedJacobian_of_volumeForm_compLinearMap oW' jW hW
  have hid : oV'.volumeForm.compLinearMap LinearMap.id =
      (ρV * oV'.orientedJacobian oV iV) • oV'.volumeForm := by
    rw [AlternatingMap.compLinearMap_id]
    simpa only [oV'.volumeForm_compLinearMap oV iV, smul_smul] using hV
  have hmul : ρV * oV'.orientedJacobian oV iV = 1 :=
    (oV'.eq_orientedJacobian_of_volumeForm_compLinearMap oV' LinearMap.id hid).trans
      oV'.orientedJacobian_id
  have hiV : oV'.orientedJacobian oV iV = ρV⁻¹ := eq_inv_of_mul_eq_one_right hmul
  rw [oV'.orientedJacobian_comp oW oW' (A ∘ₗ iV) jW,
    oV'.orientedJacobian_comp oV oW iV A, hiV, ← hρW, div_eq_mul_inv]
  ring

end MetricRescaling

/-! ### Norm determinant, Gram matrix, adjoints, isometries, and Hadamard's inequality -/

section MetricProperties

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {n : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)]

/-- The absolute value of `oV.orientedJacobian oW A` is `LinearMap.normDet A`. -/
theorem abs_orientedJacobian [FiniteDimensional ℝ V] (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W) :
    |oV.orientedJacobian oW A| = A.normDet := by
  rcases n with - | m
  · have : Subsingleton V := (finrank_zero_iff (R := ℝ) (M := V)).mp Fact.out
    simp
  · let b := oV.finOrthonormalBasis m.succ_pos Fact.out
    have hb : b.toBasis.orientation = oV := oV.finOrthonormalBasis_orientation m.succ_pos Fact.out
    have hsq : A.normDet ^ 2 = (Matrix.gram ℝ (A ∘ b)).det := by
      simpa only [RCLike.ofReal_real_eq_id, id, Function.comp_def] using A.normDet_sq_eq_det_gram b
    rw [oV.orientedJacobian_eq_volumeForm_of_orthonormal oW A b hb,
      oW.abs_volumeForm_apply_eq_sqrt_det_gram, ← hsq, Real.sqrt_sq A.normDet_nonneg]

/-- On any orthonormal basis `b` of `V`, the square of `oV.orientedJacobian oW A` is the Gram
determinant `(Matrix.gram ℝ (A ∘ b)).det`. -/
theorem orientedJacobian_sq_eq_det_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W)
    (b : OrthonormalBasis ι ℝ V) :
    oV.orientedJacobian oW A ^ 2 = (Matrix.gram ℝ (A ∘ b)).det := by
  have : FiniteDimensional ℝ V := Module.Finite.of_basis b.toBasis
  rw [← sq_abs, oV.abs_orientedJacobian oW A]
  simpa only [RCLike.ofReal_real_eq_id, id, Function.comp_def] using A.normDet_sq_eq_det_gram b

/-- The square of `oV.orientedJacobian oW A` equals `(A.adjoint ∘ₗ A).det`. -/
theorem orientedJacobian_sq [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian oW A ^ 2 = (A.adjoint ∘ₗ A).det := by
  rw [← sq_abs, oV.abs_orientedJacobian oW A]
  simpa only [RCLike.ofReal_real_eq_id, id] using A.normDet_sq

/-- Taking the adjoint reverses the roles of the two oriented spaces without changing the signed
oriented Jacobian: `J_{oW, oV}(A†) = J_{oV, oW}(A)`. -/
@[simp]
theorem orientedJacobian_adjoint [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W) :
    oW.orientedJacobian oV A.adjoint = oV.orientedJacobian oW A := by
  rcases n with - | m
  · rw [oW.orientedJacobian_fin_zero_eq_ite oV A.adjoint, oV.orientedJacobian_fin_zero_eq_ite oW A]
    congr 1
    exact propext Iff.comm
  · let bV := oV.finOrthonormalBasis m.succ_pos Fact.out
    let bW := oW.finOrthonormalBasis m.succ_pos Fact.out
    have hbV : bV.toBasis.orientation = oV := oV.finOrthonormalBasis_orientation m.succ_pos Fact.out
    have hbW : bW.toBasis.orientation = oW := oW.finOrthonormalBasis_orientation m.succ_pos Fact.out
    rw [oW.orientedJacobian_eq_det_toMatrix oV A.adjoint bW hbW bV hbV,
      oV.orientedJacobian_eq_det_toMatrix oW A bV hbV bW hbW,
      LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose, star_trivial]

/-- Every linear isometry between `n`-dimensional real inner product spaces has oriented Jacobian
of absolute value `1`. -/
theorem abs_orientedJacobian_linearIsometry (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (f : V →ₗᵢ[ℝ] W) :
    |oV.orientedJacobian oW f.toLinearMap| = 1 := by
  rcases n with - | m
  · simp
  · have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ m
    rw [oV.abs_orientedJacobian oW f.toLinearMap, f.normDet_eq_one]

/-- A linear isometric equivalence has oriented Jacobian `1` when the target carries the
transported orientation `Orientation.map (Fin n) φ.toLinearEquiv oV`. -/
@[simp]
theorem orientedJacobian_map_linearIsometryEquiv (oV : Orientation ℝ V (Fin n))
    (φ : V ≃ₗᵢ[ℝ] W) :
    oV.orientedJacobian (Orientation.map (Fin n) φ.toLinearEquiv oV) φ.toLinearMap = 1 := by
  symm
  refine oV.eq_orientedJacobian_of_volumeForm_compLinearMap _ φ.toLinearMap ?_
  ext v
  simp [oV.volumeForm_map, Function.comp_def]

/-- An orientation-preserving linear isometric equivalence has oriented Jacobian `1`. -/
theorem orientedJacobian_linearIsometryEquiv_of_map_eq (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (φ : V ≃ₗᵢ[ℝ] W)
    (h : Orientation.map (Fin n) φ.toLinearEquiv oV = oW) :
    oV.orientedJacobian oW φ.toLinearMap = 1 := by
  subst h
  exact oV.orientedJacobian_map_linearIsometryEquiv φ

/-- An orientation-reversing linear isometric equivalence has oriented Jacobian `-1`. -/
theorem orientedJacobian_linearIsometryEquiv_of_map_ne (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (φ : V ≃ₗᵢ[ℝ] W)
    (h : Orientation.map (Fin n) φ.toLinearEquiv oV ≠ oW) :
    oV.orientedJacobian oW φ.toLinearMap = -1 := by
  have hcard : Fintype.card (Fin n) = finrank ℝ W := (Fintype.card_fin n).trans (Eq.symm Fact.out)
  rw [(oW.ne_iff_eq_neg_of_card_eq_finrank _ hcard).mp h.symm]
  simp

/-- **Basis-wise Hadamard inequality**: on any orthonormal basis `b` of `V`,
`|oV.orientedJacobian oW A| ≤ ∏ i, ‖A (b i)‖`. -/
theorem abs_orientedJacobian_le_prod_norm {ι : Type*} [Fintype ι]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W)
    (b : OrthonormalBasis ι ℝ V) :
    |oV.orientedJacobian oW A| ≤ ∏ i : ι, ‖A (b i)‖ := by
  have : FiniteDimensional ℝ V := Module.Finite.of_basis b.toBasis
  rw [oV.abs_orientedJacobian oW A]
  exact A.normDet_le_prod_norm b

/-- **Hadamard's inequality** for a continuous linear map: `|J(A)| ≤ ‖A‖ ^ n`. -/
theorem abs_orientedJacobian_toLinearMap_le (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →L[ℝ] W) :
    |oV.orientedJacobian oW A.toLinearMap| ≤ ‖A‖ ^ n := by
  rcases n with - | m
  · simp
  · have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ m
    rw [oV.abs_orientedJacobian oW A.toLinearMap, ← Fact.out (p := finrank ℝ V = m + 1)]
    exact A.normDet_le_norm_pow

/-- **Hadamard's inequality** for a linear map on a finite-dimensional domain:
`|oV.orientedJacobian oW A| ≤ ‖A.toContinuousLinearMap‖ ^ n`. -/
theorem abs_orientedJacobian_le [FiniteDimensional ℝ V] (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W) :
    |oV.orientedJacobian oW A| ≤ ‖A.toContinuousLinearMap‖ ^ n := by
  simpa using oV.abs_orientedJacobian_toLinearMap_le oW A.toContinuousLinearMap

/-- A conformal continuous linear map achieves equality in Hadamard's inequality:
`|oV.orientedJacobian oW A.toLinearMap| = ‖A‖ ^ n`. -/
theorem abs_orientedJacobian_of_isConformalMap (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) {A : V →L[ℝ] W} (hA : IsConformalMap A) :
    |oV.orientedJacobian oW A.toLinearMap| = ‖A‖ ^ n := by
  rcases n with - | m
  · simp
  · have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ m
    rw [oV.abs_orientedJacobian oW A.toLinearMap, ← Fact.out (p := finrank ℝ V = m + 1)]
    exact hA.normDet_eq_norm_pow

/-- On a finite-dimensional domain `V`, equality `|J(A)| = ‖A‖ ^ n` in Hadamard's inequality
forces `A` to scale the norm of every vector by `‖A‖`. -/
theorem norm_apply_eq_of_abs_orientedJacobian_eq_norm_pow [FiniteDimensional ℝ V]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n)) {A : V →L[ℝ] W}
    (heq : |oV.orientedJacobian oW A.toLinearMap| = ‖A‖ ^ n) (x : V) :
    ‖A x‖ = ‖A‖ * ‖x‖ := by
  rw [oV.abs_orientedJacobian oW A.toLinearMap, ← Fact.out (p := finrank ℝ V = n)] at heq
  exact A.norm_apply_eq_of_normDet_eq_norm_pow heq x

/-- **Equality case of Hadamard's inequality**: on a finite-dimensional domain `V`,
`|oV.orientedJacobian oW A.toLinearMap| = ‖A‖ ^ n` holds if and only if `A = 0` or `A` is
conformal (`IsConformalMap A`). -/
theorem abs_orientedJacobian_toLinearMap_eq_norm_pow_iff [FiniteDimensional ℝ V]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n)) (A : V →L[ℝ] W) :
    |oV.orientedJacobian oW A.toLinearMap| = ‖A‖ ^ n ↔ A = 0 ∨ IsConformalMap A := by
  rw [oV.abs_orientedJacobian oW A.toLinearMap, ← Fact.out (p := finrank ℝ V = n)]
  exact A.normDet_eq_norm_pow_iff

/-- The map `A ↦ oV.orientedJacobian oW A.toLinearMap` on `V →L[ℝ] W` is `C^k` for every
`k : ℕ∞ω` (in particular smooth and analytic). -/
theorem contDiff_orientedJacobian (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    {k : ℕ∞ω} :
    ContDiff ℝ k (fun A : V →L[ℝ] W ↦ oV.orientedJacobian oW A.toLinearMap) := by
  rcases n with - | m
  · simp only [orientedJacobian_fin_zero_eq_ite]
    exact contDiff_const
  · let b := oV.finOrthonormalBasis m.succ_pos Fact.out
    have hb : b.toBasis.orientation = oV := oV.finOrthonormalBasis_orientation m.succ_pos Fact.out
    have heq : (fun A : V →L[ℝ] W ↦ oV.orientedJacobian oW A.toLinearMap) =
        fun A ↦ oW.volumeFormL.toContinuousMultilinearMap (fun i ↦ A (b i)) := by
      ext A
      rw [oV.orientedJacobian_eq_volumeForm_of_orthonormal oW A.toLinearMap b hb,
        ← oW.volumeFormL_apply]
      simp only [ContinuousAlternatingMap.coe_toContinuousMultilinearMap, Function.comp_def,
        ContinuousLinearMap.coe_coe]
    rw [heq]
    exact oW.volumeFormL.toContinuousMultilinearMap.contDiff.comp
      (contDiff_pi.mpr fun i ↦ (ContinuousLinearMap.apply ℝ W (b i)).contDiff)

/-- The oriented Jacobian `A ↦ oV.orientedJacobian oW A.toLinearMap` depends continuously on
`A : V →L[ℝ] W`. -/
theorem continuous_orientedJacobian (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) :
    Continuous (fun A : V →L[ℝ] W ↦ oV.orientedJacobian oW A.toLinearMap) :=
  (oV.contDiff_orientedJacobian oW (k := ∞)).continuous

/-! ### Invertibility and orientation-preservation criteria -/

/-- A linear equivalence `e : V ≃ₗ[ℝ] W` has positive oriented Jacobian if and only if it
transports `oV` to `oW`. -/
theorem orientedJacobian_linearEquiv_pos_iff (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (e : V ≃ₗ[ℝ] W) :
    0 < oV.orientedJacobian oW e.toLinearMap ↔ Orientation.map (Fin n) e oV = oW := by
  rcases n with - | m
  · have hneV : (positiveOrientation : Orientation ℝ V (Fin 0)) ≠ -positiveOrientation :=
      Module.Ray.ne_neg_self _
    have hneW : (positiveOrientation : Orientation ℝ W (Fin 0)) ≠ -positiveOrientation :=
      Module.Ray.ne_neg_self _
    rcases oV.eq_or_eq_neg_of_isEmpty with rfl | rfl <;>
      rcases oW.eq_or_eq_neg_of_isEmpty with rfl | rfl <;>
      simp [orientedJacobian_fin_zero_eq_ite, map_positiveOrientation_of_isEmpty,
        hneV.symm, hneW, hneW.symm]
  · let b := oV.finOrthonormalBasis m.succ_pos Fact.out
    have hb : b.toBasis.orientation = oV := oV.finOrthonormalBasis_orientation m.succ_pos Fact.out
    have hmap : ⇑(b.toBasis.map e) = e.toLinearMap ∘ b := by ext i; simp
    rw [oV.orientedJacobian_eq_volumeForm_of_orthonormal oW e.toLinearMap b hb, ← hmap,
      oW.volumeForm_apply_pos_iff, Basis.orientation_map, hb]

/-- A linear equivalence `e : V ≃ₗ[ℝ] W` has negative oriented Jacobian if and only if it
transports `oV` to `-oW`. -/
theorem orientedJacobian_linearEquiv_neg_iff (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (e : V ≃ₗ[ℝ] W) :
    oV.orientedJacobian oW e.toLinearMap < 0 ↔ Orientation.map (Fin n) e oV = -oW := by
  rw [← neg_pos, ← oV.orientedJacobian_neg_right oW e.toLinearMap,
    oV.orientedJacobian_linearEquiv_pos_iff (-oW) e]

/-- An orientation-preserving linear equivalence has oriented Jacobian equal to its `normDet`. -/
theorem orientedJacobian_linearEquiv_eq_normDet [FiniteDimensional ℝ V]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n)) (e : V ≃ₗ[ℝ] W)
    (h : Orientation.map (Fin n) e oV = oW) :
    oV.orientedJacobian oW e.toLinearMap = e.toLinearMap.normDet := by
  rw [← oV.abs_orientedJacobian oW e.toLinearMap,
    abs_of_pos ((oV.orientedJacobian_linearEquiv_pos_iff oW e).mpr h)]

/-- An orientation-reversing linear equivalence has oriented Jacobian equal to `-normDet`. -/
theorem orientedJacobian_linearEquiv_eq_neg_normDet [FiniteDimensional ℝ V]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n)) (e : V ≃ₗ[ℝ] W)
    (h : Orientation.map (Fin n) e oV ≠ oW) :
    oV.orientedJacobian oW e.toLinearMap = -e.toLinearMap.normDet := by
  have hcard : Fintype.card (Fin n) = finrank ℝ W := (Fintype.card_fin n).trans (Eq.symm Fact.out)
  rw [← oV.abs_orientedJacobian oW e.toLinearMap,
    abs_of_neg ((oV.orientedJacobian_linearEquiv_neg_iff oW e).mpr
      ((ne_iff_eq_neg_of_card_eq_finrank _ _ hcard).mp h)), neg_neg]

/-- Between finite-dimensional real inner product spaces of the same dimension `n`, the oriented
Jacobian vanishes if and only if `A` is not bijective. -/
theorem orientedJacobian_eq_zero_iff [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n)) {A : V →ₗ[ℝ] W} :
    oV.orientedJacobian oW A = 0 ↔ ¬Function.Bijective A := by
  have hdim : finrank ℝ V = finrank ℝ W :=
    (Fact.out : finrank ℝ V = n).trans (Fact.out : finrank ℝ W = n).symm
  have hbij : Function.Injective A ↔ Function.Bijective A :=
    ⟨fun h ↦ ⟨h, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp h⟩,
      Function.Bijective.injective⟩
  rw [← abs_eq_zero, oV.abs_orientedJacobian oW A, LinearMap.normDet_eq_zero_iff_ker_ne_bot,
    ne_eq, LinearMap.ker_eq_bot, hbij]

/-- Between finite-dimensional real inner product spaces of the same dimension `n`, the oriented
Jacobian is nonzero if and only if `A` is bijective. -/
theorem orientedJacobian_ne_zero_iff [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n)) {A : V →ₗ[ℝ] W} :
    oV.orientedJacobian oW A ≠ 0 ↔ Function.Bijective A :=
  (oV.orientedJacobian_eq_zero_iff oW).not_left

/-- Between finite-dimensional real inner product spaces of the same dimension `n`, the oriented
Jacobian of `A` is positive if and only if `A` is invertible (`e : V ≃ₗ[ℝ] W` with
`e.toLinearMap = A`) and transports `oV` to `oW`. -/
theorem orientedJacobian_pos_iff [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n)) {A : V →ₗ[ℝ] W} :
    0 < oV.orientedJacobian oW A ↔
      ∃ e : V ≃ₗ[ℝ] W, e.toLinearMap = A ∧ Orientation.map (Fin n) e oV = oW := by
  refine ⟨fun hpos ↦ ?_, ?_⟩
  · have hbij : Function.Bijective A := (oV.orientedJacobian_ne_zero_iff oW).mp hpos.ne'
    let e : V ≃ₗ[ℝ] W := LinearEquiv.ofBijective A hbij
    have he : e.toLinearMap = A := by ext x; simp [e]
    exact ⟨e, he, (oV.orientedJacobian_linearEquiv_pos_iff oW e).mp (he.symm ▸ hpos)⟩
  · rintro ⟨e, rfl, hmap⟩
    exact (oV.orientedJacobian_linearEquiv_pos_iff oW e).mpr hmap

/-- Between finite-dimensional real inner product spaces of the same dimension `n`, the oriented
Jacobian of `A` is negative if and only if `A` is invertible and transports `oV` to `-oW`. -/
theorem orientedJacobian_neg_iff [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n)) {A : V →ₗ[ℝ] W} :
    oV.orientedJacobian oW A < 0 ↔
      ∃ e : V ≃ₗ[ℝ] W, e.toLinearMap = A ∧ Orientation.map (Fin n) e oV = -oW := by
  rw [← neg_pos, ← oV.orientedJacobian_neg_right oW A, oV.orientedJacobian_pos_iff (-oW)]

end MetricProperties

/-! ### Worked planar examples -/

section PlanarExamples

open scoped EuclideanSpace Matrix.Norms.L2Operator

-- Anisotropic scaling `diag(2, 1)` on `ℝ²` has `J = 2` and `‖A‖² = 4`, witnessing strictness in
-- Hadamard's inequality.
example (o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)) :
    let A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal ![2, 1])
    o.orientedJacobian o A.toLinearMap = 2 ∧
      ‖A‖ ^ 2 = 4 ∧ |o.orientedJacobian o A.toLinearMap| < ‖A‖ ^ 2 := by
  intro A
  have hJ : o.orientedJacobian o A.toLinearMap = 2 := by
    simp [A, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  have hnorm : ‖A‖ = 2 := by
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal, Pi.norm_def]
    have hsup : (Finset.univ : Finset (Fin 2)).sup (fun i ↦ ‖(![2, 1] : Fin 2 → ℝ) i‖₊) = 2 := by
      rw [Fin.univ_succ]; simp
    exact congrArg NNReal.toReal hsup
  refine ⟨hJ, by rw [hnorm]; norm_num, by rw [hJ, hnorm]; norm_num⟩

-- The planar reflection `diag(-1, 1)` has `J = -1` when both sides carry `o` and `J = 1` from
-- `(ℝ², o)` to `(ℝ², -o)`.
example (o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)) :
    let R : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1])
    o.orientedJacobian o R = -1 ∧ o.orientedJacobian (-o) R = 1 := by
  intro R; constructor <;> simp [R]

-- The rank-one projection `diag(1, 0)` on `ℝ²` has `J = 0` while `‖P‖ = 1 > 0`.
example (o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)) :
    let P : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal ![1, 0])
    o.orientedJacobian o P.toLinearMap = 0 ∧ 0 < ‖P‖ := by
  intro P
  have hJ : o.orientedJacobian o P.toLinearMap = 0 := by
    simp [P, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  have hnorm : ‖P‖ = 1 := by
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal, Pi.norm_def]
    have hsup : (Finset.univ : Finset (Fin 2)).sup (fun i ↦ ‖(![1, 0] : Fin 2 → ℝ) i‖₊) = 1 := by
      rw [Fin.univ_succ]; simp
    exact congrArg NNReal.toReal hsup
  exact ⟨hJ, by rw [hnorm]; exact zero_lt_one⟩

end PlanarExamples

end Orientation
