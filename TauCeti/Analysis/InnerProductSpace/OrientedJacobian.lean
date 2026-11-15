/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.ConformalLinearMap
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import TauCeti.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
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
Equivalently, `oV.orientedJacobian oW A = oW.volumeForm (A ∘ b)` on any positively oriented
orthonormal basis `b` of `V`, and `oW.volumeForm (A ∘ b) / oV.volumeForm b` on any basis `b` of
`V`. In dimension `0`, it takes value `1` when the two zero-dimensional orientations agree with
`Orientation.positiveOrientation` in the same way, and `-1` when they disagree.

Unlike `LinearMap.det`, the oriented Jacobian applies between *distinct* inner product spaces of
equal dimension, such as the tangent spaces `T_x M` and `T_{f(x)} N` along a map `f : M → N`
between oriented Riemannian `n`-manifolds. Unlike `LinearMap.normDet`, it retains the orientation
sign needed for degree formulas and pullback of top-degree differential forms.

## Main definitions and results

* `Orientation.orientedJacobian`: the signed volume factor `J_{oV, oW}(A) : ℝ` of `A : V →ₗ[ℝ] W`.
* `Orientation.volumeForm_comp_eq`, `Orientation.compLinearMap_volumeForm`,
  `Orientation.compContinuousLinearMap_volumeFormL`: pullback of the oriented volume form by `A`
  multiplies it by `oV.orientedJacobian oW A`, and this property characterizes the scalar uniquely
  (`Orientation.eq_orientedJacobian_of_compLinearMap_volumeForm`,
  `Orientation.eq_orientedJacobian_of_volumeForm_comp_eq`).
* `Orientation.orientedJacobian_eq_div`,
  `Orientation.orientedJacobian_eq_volumeForm_of_orthonormal`,
  `Orientation.orientedJacobian_eq_det_toMatrix`: evaluation in arbitrary bases and in oriented
  orthonormal frames.
* `Orientation.orientedJacobian_zero_eq_ite`, `Orientation.orientedJacobian_one_eq_inner`,
  `Orientation.areaForm_apply_eq_orientedJacobian_mul`: explicit formulas in dimensions `0`, `1`,
  and `2`.
* `Orientation.orientedJacobian_comp`, `Orientation.orientedJacobian_id`,
  `Orientation.orientedJacobian_neg_left`, `Orientation.orientedJacobian_neg_right`,
  `Orientation.orientedJacobian_smul`: multiplicativity under composition, reversal of either
  orientation, and homogeneity of degree `n`.
* `Orientation.orientedJacobian_self`, `Orientation.orientedJacobian_eq_det_conj_mul_div`,
  `Orientation.orientedJacobian_conj_of_compLinearMap_volumeForm`: recovery of `LinearMap.det` on a
  single oriented space, expression in terms of reference linear equivalences (coordinate charts),
  and transformation under rescaling of the volume forms (changes of metric).
* `Orientation.abs_orientedJacobian`, `Orientation.orientedJacobian_sq_eq_det_gram`,
  `Orientation.orientedJacobian_sq`, `Orientation.orientedJacobian_adjoint`: agreement of
  `|oV.orientedJacobian oW A|` with `LinearMap.normDet A`, Gram-determinant square formula, and
  invariance under taking the adjoint.
* `Orientation.abs_orientedJacobian_coe_le`, `Orientation.abs_orientedJacobian_le`,
  `Orientation.norm_apply_eq_of_abs_orientedJacobian_eq_norm_pow`,
  `Orientation.abs_orientedJacobian_coe_eq_norm_pow_iff`: Hadamard's inequality
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
`LinearMap.toContinuousLinearMap`, or zero-dimensional bijectivity genuinely require them.

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
theorem compLinearMap_volumeForm (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) :
    oW.volumeForm.compLinearMap A = oV.orientedJacobian oW A • oV.volumeForm := by
  ext v
  exact oV.volumeForm_comp_eq oW A v

/-- Pulling the continuous volume form `oW.volumeFormL` back along a continuous linear map `A`
multiplies `oV.volumeFormL` by `oV.orientedJacobian oW A.toLinearMap`. -/
theorem compContinuousLinearMap_volumeFormL (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →L[ℝ] W) :
    oW.volumeFormL.compContinuousLinearMap A =
      oV.orientedJacobian oW A.toLinearMap • oV.volumeFormL := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply, volumeFormL_apply, smul_eq_mul]
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
theorem eq_orientedJacobian_of_compLinearMap_volumeForm (oV : Orientation ℝ V (Fin n))
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

/-- In positively oriented orthonormal bases `bV` of `V` and `bW` of `W`, the oriented Jacobian of
`A` is the determinant of its matrix `A.toMatrix bV.toBasis bW.toBasis`. -/
theorem orientedJacobian_eq_det_toMatrix (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W)
    (bV : OrthonormalBasis (Fin n) ℝ V) (hbV : bV.toBasis.orientation = oV)
    (bW : OrthonormalBasis (Fin n) ℝ W) (hbW : bW.toBasis.orientation = oW) :
    oV.orientedJacobian oW A = (A.toMatrix bV.toBasis bW.toBasis).det := by
  rw [oV.orientedJacobian_eq_volumeForm_of_orthonormal oW A bV hbV, oW.volumeForm_robust bW hbW,
    Basis.det_apply]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply]

end TwoSpaces

/-! ### Explicit formulas in dimensions `0`, `1`, and `2` -/

section ZeroDim

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ V = 0)] [Fact (finrank ℝ W = 0)]

/-- Between zero-dimensional spaces carrying `positiveOrientation`, the oriented Jacobian is `1`. -/
@[simp]
theorem orientedJacobian_zero_pos_pos {A : V →ₗ[ℝ] W} :
    (positiveOrientation : Orientation ℝ V (Fin 0)).orientedJacobian positiveOrientation A = 1 := by
  simp [orientedJacobian]

open Classical in
/-- In dimension `0`, `oV.orientedJacobian oW A` is `1` if `oV` and `oW` have the same sign
relative to `positiveOrientation`, and `-1` otherwise. -/
theorem orientedJacobian_zero_eq_ite (oV : Orientation ℝ V (Fin 0))
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

/-- In dimension `0`, `oV.orientedJacobian oW A = 1` iff `oV` and `oW` agree with
`positiveOrientation` simultaneously. -/
theorem orientedJacobian_zero_eq_one_iff (oV : Orientation ℝ V (Fin 0))
    (oW : Orientation ℝ W (Fin 0)) (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian oW A = 1 ↔ (oV = positiveOrientation ↔ oW = positiveOrientation) := by
  rw [oV.orientedJacobian_zero_eq_ite oW A]
  split_ifs with h <;> norm_num [h]

/-- In dimension `0`, `oV.orientedJacobian oW A = -1` iff exactly one of `oV`, `oW` equals
`positiveOrientation`. -/
theorem orientedJacobian_zero_eq_neg_one_iff (oV : Orientation ℝ V (Fin 0))
    (oW : Orientation ℝ W (Fin 0)) (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian oW A = -1 ↔ ¬(oV = positiveOrientation ↔ oW = positiveOrientation) := by
  rw [oV.orientedJacobian_zero_eq_ite oW A]
  split_ifs with h <;> norm_num [h]

end ZeroDim

section ZeroDimSelf

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 0)]

open Classical in
/-- For two orientations on the same zero-dimensional space, `o₁.orientedJacobian o₂ A` is `1` if
`o₁ = o₂` and `-1` otherwise. -/
theorem orientedJacobian_zero_self_eq_ite (o₁ o₂ : Orientation ℝ V (Fin 0)) (A : V →ₗ[ℝ] V) :
    o₁.orientedJacobian o₂ A = if o₁ = o₂ then 1 else -1 := by
  rw [o₁.orientedJacobian_zero_eq_ite o₂ A]
  congr 1
  exact propext ⟨fun h ↦ by
    rcases o₁.eq_or_eq_neg_of_isEmpty with rfl | rfl <;>
      rcases o₂.eq_or_eq_neg_of_isEmpty with rfl | rfl <;>
      simp_all [(Module.Ray.ne_neg_self _).symm],
    fun h ↦ h ▸ Iff.rfl⟩

end ZeroDimSelf

section OneDim

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ V = 1)] [Fact (finrank ℝ W = 1)]

/-- Between oriented one-dimensional real inner product spaces with positively oriented unit basis
vectors `bV 0` and `bW 0`, the oriented Jacobian of `A` is `⟪bW 0, A (bV 0)⟫`. -/
theorem orientedJacobian_one_eq_inner (oV : Orientation ℝ V (Fin 1))
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
theorem areaForm_apply_eq_orientedJacobian_mul (oV : Orientation ℝ V (Fin 2))
    (oW : Orientation ℝ W (Fin 2)) (A : V →ₗ[ℝ] W) (x y : V) :
    oW.areaForm (A x) (A y) = oV.orientedJacobian oW A * oV.areaForm x y := by
  have hxy : ![A x, A y] = A ∘ ![x, y] := by
    ext i
    fin_cases i <;> rfl
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
  refine oU.eq_orientedJacobian_of_compLinearMap_volumeForm oW (B ∘ₗ A) ?_
  ext v
  have hcomp : (fun i ↦ (B ∘ₗ A) (v i)) = B ∘ (A ∘ v) := rfl
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
  refine (-oV).eq_orientedJacobian_of_compLinearMap_volumeForm oW A ?_
  rw [oV.compLinearMap_volumeForm oW A, volumeForm_neg_orientation, smul_neg, neg_smul, neg_neg]

/-- Reversing the target orientation negates the oriented Jacobian. -/
@[simp]
theorem orientedJacobian_neg_right (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian (-oW) A = -oV.orientedJacobian oW A := by
  symm
  refine oV.eq_orientedJacobian_of_compLinearMap_volumeForm (-oW) A ?_
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
  refine oV.eq_orientedJacobian_of_compLinearMap_volumeForm oW (c • A) ?_
  ext v
  have hsmul : (fun i ↦ (c • A) (v i)) = fun i ↦ c • (A ∘ v) i := rfl
  rw [AlternatingMap.compLinearMap_apply, hsmul, oW.volumeForm.map_smul_univ]
  simp [oV.volumeForm_comp_eq oW A v, mul_assoc]

/-- Negating `A` multiplies its oriented Jacobian by `(-1) ^ n`. -/
@[simp]
theorem orientedJacobian_neg (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian oW (-A) = (-1) ^ n * oV.orientedJacobian oW A := by
  simpa only [neg_one_smul] using oV.orientedJacobian_smul oW (-1) A

/-- In positive dimension, the zero linear map has oriented Jacobian `0`. -/
theorem orientedJacobian_zero_of_pos (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (hn : 0 < n) :
    oV.orientedJacobian oW 0 = 0 := by
  simpa [zero_pow hn.ne'] using oV.orientedJacobian_smul oW 0 0

end TwoSpacesOps

/-! ### Endomorphisms, inverses, and coordinate conjugation -/

section Self

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)]

/-- For a single orientation on `V`, the oriented Jacobian of an endomorphism `A` is
`LinearMap.det A`. -/
@[simp]
theorem orientedJacobian_self (oV : Orientation ℝ V (Fin n)) (A : V →ₗ[ℝ] V) :
    oV.orientedJacobian oV A = A.det := by
  rcases n with - | m
  · rw [oV.orientedJacobian_zero_self_eq_ite oV A]
    simp only [↓reduceIte]
    by_cases hfd : FiniteDimensional ℝ V
    · have : Subsingleton V := (finrank_zero_iff (R := ℝ) (M := V)).mp Fact.out
      exact (LinearMap.det_eq_one_of_subsingleton A).symm
    · exact (LinearMap.det_eq_one_of_not_module_finite hfd A).symm
  · let b := oV.finOrthonormalBasis m.succ_pos Fact.out
    have hb : b.toBasis.orientation = oV := oV.finOrthonormalBasis_orientation m.succ_pos Fact.out
    rw [oV.orientedJacobian_eq_det_toMatrix oV A b hb b hb, LinearMap.det_toMatrix]

/-- The identity map has oriented Jacobian `1` with respect to a single orientation. -/
theorem orientedJacobian_id (oV : Orientation ℝ V (Fin n)) :
    oV.orientedJacobian oV LinearMap.id = 1 := by
  simp

/-- For two distinct orientations on `V`, the oriented Jacobian of an endomorphism `A` is
`-LinearMap.det A`. -/
theorem orientedJacobian_self_of_ne (o₁ o₂ : Orientation ℝ V (Fin n)) (h : o₁ ≠ o₂)
    (A : V →ₗ[ℝ] V) :
    o₁.orientedJacobian o₂ A = -A.det := by
  have hcard : Fintype.card (Fin n) = finrank ℝ V := by
    simp [Fact.out (p := finrank ℝ V = n)]
  rcases eq_or_eq_neg_of_card_eq_finrank o₂ o₁ hcard with rfl | rfl
  · exact absurd rfl h
  · simp

/-- For two distinct orientations on `V`, the identity map has oriented Jacobian `-1`. -/
theorem orientedJacobian_id_of_ne (o₁ o₂ : Orientation ℝ V (Fin n)) (h : o₁ ≠ o₂) :
    o₁.orientedJacobian o₂ LinearMap.id = -1 := by
  rw [o₁.orientedJacobian_self_of_ne o₂ h, LinearMap.det_id]

end Self

section LinearEquivAlgebra

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {n : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)]

/-- The oriented Jacobians of a linear equivalence and its inverse multiply to `1`. -/
theorem orientedJacobian_symm_mul (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (e : V ≃ₗ[ℝ] W) :
    oW.orientedJacobian oV e.symm.toLinearMap * oV.orientedJacobian oW e.toLinearMap = 1 := by
  have hcomp : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id := by
    ext x
    simp
  rw [← oV.orientedJacobian_comp oW oV e.toLinearMap e.symm.toLinearMap, hcomp,
    oV.orientedJacobian_id]

/-- The oriented Jacobian of a linear equivalence is nonzero. -/
theorem orientedJacobian_ne_zero_of_linearEquiv (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (e : V ≃ₗ[ℝ] W) :
    oV.orientedJacobian oW e.toLinearMap ≠ 0 :=
  right_ne_zero_of_mul_eq_one (oV.orientedJacobian_symm_mul oW e)

/-- The oriented Jacobian of the inverse of a linear equivalence is the reciprocal of its oriented
Jacobian. -/
@[simp]
theorem orientedJacobian_symm (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (e : V ≃ₗ[ℝ] W) :
    oW.orientedJacobian oV e.symm.toLinearMap = (oV.orientedJacobian oW e.toLinearMap)⁻¹ :=
  eq_inv_of_mul_eq_one_left (oV.orientedJacobian_symm_mul oW e)

end LinearEquivAlgebra

section Conjugation

variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {n : ℕ} [Fact (finrank ℝ U = n)] [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)]

/-- **Coordinate expression of the oriented Jacobian**: given linear equivalences `eV : V ≃ₗ[ℝ] U`
and `eW : W ≃ₗ[ℝ] U` to a common model inner product space `(U, oU)`, `oV.orientedJacobian oW A`
is the determinant of the model endomorphism `eW ∘ A ∘ eV⁻¹` multiplied by the ratio of the
oriented Jacobians of `eV` and `eW`. -/
theorem orientedJacobian_eq_det_conj_mul_div (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (oU : Orientation ℝ U (Fin n))
    (eV : V ≃ₗ[ℝ] U) (eW : W ≃ₗ[ℝ] U) (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian oW A =
      (eW.toLinearMap ∘ₗ A ∘ₗ eV.symm.toLinearMap).det *
        (oV.orientedJacobian oU eV.toLinearMap / oW.orientedJacobian oU eW.toLinearMap) := by
  have hA : A = (eW.symm.toLinearMap ∘ₗ (eW.toLinearMap ∘ₗ A ∘ₗ eV.symm.toLinearMap)) ∘ₗ
      eV.toLinearMap := by
    ext x
    simp
  conv_lhs => rw [hA]
  rw [oV.orientedJacobian_comp oU oW eV.toLinearMap,
    oU.orientedJacobian_comp oU oW _ eW.symm.toLinearMap,
    oU.orientedJacobian_self, oW.orientedJacobian_symm oU eW, div_eq_mul_inv]
  ring

end Conjugation

section MetricRescaling

variable {V V' W W' : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [NormedAddCommGroup W'] [InnerProductSpace ℝ W']
  {n : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ V' = n)]
  [Fact (finrank ℝ W = n)] [Fact (finrank ℝ W' = n)]

/-- **Metric-rescaling formula**: if linear equivalences `iV : V' ≃ₗ[ℝ] V` and `iW : W' ≃ₗ[ℝ] W`
relate a second pair of oriented inner product structures to `(V, oV)` and `(W, oW)` with volume
ratios `ρV` and `ρW` (`(iV⁻¹)^* vol_{oV'} = ρV • vol_{oV}` and likewise on `W`), then the oriented
Jacobian of `iW⁻¹ ∘ A ∘ iV` equals `(ρW / ρV) * oV.orientedJacobian oW A`. -/
theorem orientedJacobian_conj_of_compLinearMap_volumeForm
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (oV' : Orientation ℝ V' (Fin n)) (oW' : Orientation ℝ W' (Fin n))
    (iV : V' ≃ₗ[ℝ] V) (iW : W' ≃ₗ[ℝ] W) {ρV ρW : ℝ}
    (hV : oV'.volumeForm.compLinearMap iV.symm.toLinearMap = ρV • oV.volumeForm)
    (hW : oW'.volumeForm.compLinearMap iW.symm.toLinearMap = ρW • oW.volumeForm)
    (A : V →ₗ[ℝ] W) :
    oV'.orientedJacobian oW' (iW.symm.toLinearMap ∘ₗ A ∘ₗ iV.toLinearMap) =
      (ρW / ρV) * oV.orientedJacobian oW A := by
  have hρV : ρV = oV.orientedJacobian oV' iV.symm.toLinearMap :=
    oV.eq_orientedJacobian_of_compLinearMap_volumeForm oV' iV.symm.toLinearMap hV
  have hρW : ρW = oW.orientedJacobian oW' iW.symm.toLinearMap :=
    oW.eq_orientedJacobian_of_compLinearMap_volumeForm oW' iW.symm.toLinearMap hW
  have hiV : oV'.orientedJacobian oV iV.toLinearMap = ρV⁻¹ := by
    simpa only [LinearEquiv.symm_symm, hρV] using oV.orientedJacobian_symm oV' iV.symm
  rw [oV'.orientedJacobian_comp oW oW' (A ∘ₗ iV.toLinearMap) iW.symm.toLinearMap,
    oV'.orientedJacobian_comp oV oW iV.toLinearMap A, hiV, ← hρW, div_eq_mul_inv]
  ring

end MetricRescaling

/-! ### Norm determinant, Gram matrix, adjoints, isometries, and Hadamard's inequality -/

section MetricProperties

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {n : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)]

/-- The absolute value of `oV.orientedJacobian oW A` is `LinearMap.normDet A`. -/
@[simp]
theorem abs_orientedJacobian [FiniteDimensional ℝ V] (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W) :
    |oV.orientedJacobian oW A| = A.normDet := by
  rcases n with - | m
  · have : Subsingleton V := (finrank_zero_iff (R := ℝ) (M := V)).mp Fact.out
    rw [oV.orientedJacobian_zero_eq_ite oW A, A.normDet_of_subsingleton]
    split_ifs <;> simp
  · let b := oV.finOrthonormalBasis m.succ_pos Fact.out
    have hb : b.toBasis.orientation = oV := oV.finOrthonormalBasis_orientation m.succ_pos Fact.out
    have hsq : A.normDet ^ 2 = (Matrix.gram ℝ (A ∘ b)).det := by
      simpa only [RCLike.ofReal_real_eq_id, id, Function.comp_def] using A.normDet_sq_eq_det_gram b
    rw [oV.orientedJacobian_eq_volumeForm_of_orthonormal oW A b hb,
      oW.abs_volumeForm_apply_eq_sqrt_det_gram, ← hsq, Real.sqrt_sq A.normDet_nonneg]

/-- On any orthonormal basis `b` of `V`, the square of `oV.orientedJacobian oW A` is the Gram
determinant `(Matrix.gram ℝ (A ∘ b)).det`. -/
theorem orientedJacobian_sq_eq_det_gram (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W) (b : OrthonormalBasis (Fin n) ℝ V) :
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
theorem orientedJacobian_adjoint [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W) :
    oW.orientedJacobian oV A.adjoint = oV.orientedJacobian oW A := by
  rcases n with - | m
  · rw [oW.orientedJacobian_zero_eq_ite oV A.adjoint, oV.orientedJacobian_zero_eq_ite oW A]
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
  · rw [oV.orientedJacobian_zero_eq_ite oW f.toLinearMap]
    split_ifs <;> simp
  · have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ m
    rw [oV.abs_orientedJacobian oW f.toLinearMap, f.normDet_eq_one]

/-- A linear isometric equivalence has oriented Jacobian `1` when the target carries the
transported orientation `Orientation.map (Fin n) φ.toLinearEquiv oV`. -/
@[simp]
theorem orientedJacobian_map_linearIsometryEquiv (oV : Orientation ℝ V (Fin n))
    (φ : V ≃ₗᵢ[ℝ] W) :
    oV.orientedJacobian (Orientation.map (Fin n) φ.toLinearEquiv oV) φ.toLinearMap = 1 := by
  symm
  refine oV.eq_orientedJacobian_of_compLinearMap_volumeForm _ φ.toLinearMap ?_
  ext v
  have hcomp : ⇑φ.symm ∘ (fun i ↦ φ.toLinearEquiv (v i)) = v := by
    ext i
    simp
  rw [AlternatingMap.compLinearMap_apply, oV.volumeForm_map φ, smul_apply, one_smul]
  exact congrArg oV.volumeForm hcomp

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
  have hcard : Fintype.card (Fin n) = finrank ℝ W := by
    simp [Fact.out (p := finrank ℝ W = n)]
  rcases eq_or_eq_neg_of_card_eq_finrank oW (Orientation.map (Fin n) φ.toLinearEquiv oV) hcard with
    rfl | rfl
  · exact absurd rfl h
  · simp

/-- **Basis-wise Hadamard inequality**: on any orthonormal basis `b` of `V`,
`|oV.orientedJacobian oW A| ≤ ∏ i, ‖A (b i)‖`. -/
theorem abs_orientedJacobian_le_prod_norm (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W) (b : OrthonormalBasis (Fin n) ℝ V) :
    |oV.orientedJacobian oW A| ≤ ∏ i : Fin n, ‖A (b i)‖ := by
  by_cases hb : b.toBasis.orientation = oV
  · rw [oV.orientedJacobian_eq_volumeForm_of_orthonormal oW A b hb]
    exact oW.abs_volumeForm_apply_le (A ∘ b)
  · rw [oV.orientedJacobian_eq_neg_volumeForm_of_orthonormal oW A b hb, abs_neg]
    exact oW.abs_volumeForm_apply_le (A ∘ b)

/-- **Hadamard's inequality** for a continuous linear map: `|J(A)| ≤ ‖A‖ ^ n`. -/
theorem abs_orientedJacobian_coe_le (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →L[ℝ] W) :
    |oV.orientedJacobian oW A.toLinearMap| ≤ ‖A‖ ^ n := by
  rcases n with - | m
  · rw [oV.orientedJacobian_zero_eq_ite oW A.toLinearMap, pow_zero]
    split_ifs <;> simp
  · let b := oV.finOrthonormalBasis m.succ_pos Fact.out
    refine (oV.abs_orientedJacobian_le_prod_norm oW A.toLinearMap b).trans ?_
    calc
      ∏ i : Fin (m + 1), ‖A (b i)‖ ≤ ∏ _i : Fin (m + 1), ‖A‖ := by
        gcongr with i
        simpa [b.orthonormal.1 i] using A.le_opNorm (b i)
      _ = ‖A‖ ^ (m + 1) := by simp

/-- **Hadamard's inequality** for a linear map on a finite-dimensional domain:
`|oV.orientedJacobian oW A| ≤ ‖A.toContinuousLinearMap‖ ^ n`. -/
theorem abs_orientedJacobian_le [FiniteDimensional ℝ V] (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W) :
    |oV.orientedJacobian oW A| ≤ ‖A.toContinuousLinearMap‖ ^ n :=
  oV.abs_orientedJacobian_coe_le oW A.toContinuousLinearMap

/-- A conformal continuous linear map achieves equality in Hadamard's inequality:
`|oV.orientedJacobian oW A.toLinearMap| = ‖A‖ ^ n`. -/
theorem abs_orientedJacobian_of_isConformalMap (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) {A : V →L[ℝ] W} (hA : IsConformalMap A) :
    |oV.orientedJacobian oW A.toLinearMap| = ‖A‖ ^ n := by
  rcases n with - | m
  · rw [oV.orientedJacobian_zero_eq_ite oW A.toLinearMap, pow_zero]
    split_ifs <;> simp
  · obtain ⟨c, _, li, rfl⟩ := hA
    have : Nontrivial V := by
      have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ m
      have hpos : 0 < finrank ℝ V := by
        rw [Fact.out (p := finrank ℝ V = m + 1)]
        exact m.succ_pos
      exact Module.nontrivial_of_finrank_pos hpos
    have hcoe : (c • li.toContinuousLinearMap).toLinearMap = c • li.toLinearMap := rfl
    rw [hcoe, oV.orientedJacobian_smul oW c li.toLinearMap, abs_mul, abs_pow,
      oV.abs_orientedJacobian_linearIsometry oW li, mul_one, norm_smul,
      li.norm_toContinuousLinearMap, mul_one, Real.norm_eq_abs]

/-- On a finite-dimensional domain `V`, equality `|J(A)| = ‖A‖ ^ n` in Hadamard's inequality
forces `A` to scale the norm of every vector by `‖A‖`. -/
theorem norm_apply_eq_of_abs_orientedJacobian_eq_norm_pow [FiniteDimensional ℝ V]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n)) {A : V →L[ℝ] W}
    (heq : |oV.orientedJacobian oW A.toLinearMap| = ‖A‖ ^ n) (x : V) :
    ‖A x‖ = ‖A‖ * ‖x‖ := by
  rcases eq_or_ne A 0 with rfl | hA0
  · simp
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases n with - | m
  · have : Subsingleton V := (finrank_zero_iff (R := ℝ) (M := V)).mp Fact.out
    exact absurd (Subsingleton.elim x 0) hx
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA0
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let u : V := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, inv_mul_cancel₀ hx0]
  have horth : Orthonormal ℝ (({0} : Set (Fin (m + 1))).domRestrict (fun _ ↦ u)) :=
    orthonormal_iff_ite.mpr fun ⟨i, hi⟩ ⟨j, hj⟩ ↦ by
      simp only [Set.mem_singleton_iff] at hi hj
      subst hi hj
      simp [Set.domRestrict, hu]
  obtain ⟨b, hb0⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (by simp [Fact.out (p := finrank ℝ V = m + 1)])
  have hprod : ‖A‖ ^ (m + 1) ≤ ∏ j : Fin (m + 1), ‖A (b j)‖ :=
    heq ▸ oV.abs_orientedJacobian_le_prod_norm oW A.toLinearMap b
  have hAu : ‖A u‖ = ‖A‖ := by
    by_contra hne
    have hlt : ‖A u‖ < ‖A‖ := lt_of_le_of_ne (by simpa [hu] using A.le_opNorm u) hne
    have hrest : ∏ j ∈ Finset.univ.erase (0 : Fin (m + 1)), ‖A (b j)‖ ≤ ‖A‖ ^ m := by
      calc
        ∏ j ∈ Finset.univ.erase (0 : Fin (m + 1)), ‖A (b j)‖ ≤
            ∏ _j ∈ Finset.univ.erase (0 : Fin (m + 1)), ‖A‖ := by
          gcongr with j
          simpa [b.orthonormal.1 j] using A.le_opNorm (b j)
        _ = ‖A‖ ^ m := by simp
    have hstrict : ∏ j : Fin (m + 1), ‖A (b j)‖ < ‖A‖ ^ (m + 1) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ 0), hb0 0 rfl, pow_succ']
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hrest (norm_nonneg _))
        (mul_lt_mul_of_pos_right hlt (pow_pos hApos m))
    exact hstrict.not_ge hprod
  simpa [u, map_smul, norm_smul, inv_mul_eq_iff_eq_mul₀ hx0, mul_comm ‖x‖ ‖A‖] using hAu

/-- **Equality case of Hadamard's inequality**: on a finite-dimensional domain `V`,
`|oV.orientedJacobian oW A.toLinearMap| = ‖A‖ ^ n` holds if and only if `A = 0` or `A` is
conformal (`IsConformalMap A`). -/
theorem abs_orientedJacobian_coe_eq_norm_pow_iff [FiniteDimensional ℝ V]
    (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n)) (A : V →L[ℝ] W) :
    |oV.orientedJacobian oW A.toLinearMap| = ‖A‖ ^ n ↔ A = 0 ∨ IsConformalMap A := by
  refine ⟨fun heq ↦ ?_, ?_⟩
  · rcases eq_or_ne A 0 with rfl | hA0
    · exact .inl rfl
    have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA0
    refine .inr ⟨‖A‖, hApos.ne', ⟨‖A‖⁻¹ • A.toLinearMap, fun x ↦ ?_⟩, ?_⟩
    · simp [norm_smul, oV.norm_apply_eq_of_abs_orientedJacobian_eq_norm_pow oW heq x,
        inv_mul_cancel_left₀ hApos.ne']
    · ext x
      simp [smul_inv_smul₀ hApos.ne']
  · rintro (rfl | hconf)
    · rcases n with - | m
      · rw [ContinuousLinearMap.toLinearMap_zero, oV.orientedJacobian_zero_eq_ite oW 0, pow_zero]
        split_ifs <;> simp
      · simp [oV.orientedJacobian_zero_of_pos oW m.succ_pos, zero_pow m.succ_ne_zero]
    · exact oV.abs_orientedJacobian_of_isConformalMap oW hconf

/-- The map `A ↦ oV.orientedJacobian oW A.toLinearMap` on `V →L[ℝ] W` is smooth (indeed
polynomial, hence `C^k` for every `k : ℕ∞ω`). -/
theorem contDiff_orientedJacobian (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    {k : ℕ∞ω} :
    ContDiff ℝ k (fun A : V →L[ℝ] W ↦ oV.orientedJacobian oW A.toLinearMap) := by
  rcases n with - | m
  · exact contDiff_const
  · let b := oV.finOrthonormalBasis m.succ_pos Fact.out
    have hb : b.toBasis.orientation = oV := oV.finOrthonormalBasis_orientation m.succ_pos Fact.out
    have heq : (fun A : V →L[ℝ] W ↦ oV.orientedJacobian oW A.toLinearMap) =
        fun A ↦ oW.volumeFormL.toContinuousMultilinearMap (fun i ↦ A (b i)) := by
      ext A
      rw [oV.orientedJacobian_eq_volumeForm_of_orthonormal oW A.toLinearMap b hb,
        ← oW.volumeFormL_apply]
      rfl
    rw [heq]
    exact oW.volumeFormL.toContinuousMultilinearMap.contDiff.comp
      (contDiff_pi.mpr fun i ↦ (ContinuousLinearMap.apply ℝ W (b i)).contDiff)

/-- The oriented Jacobian `A ↦ oV.orientedJacobian oW A.toLinearMap` depends continuously on
`A : V →L[ℝ] W`. -/
theorem continuous_orientedJacobian (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) :
    Continuous (fun A : V →L[ℝ] W ↦ oV.orientedJacobian oW A.toLinearMap) :=
  (oV.contDiff_orientedJacobian oW (k := ∞)).continuous

end MetricProperties

/-! ### Invertibility and orientation-preservation criteria -/

section SignAndInvertibility

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {n : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)]

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
      simp [orientedJacobian_zero_eq_ite, map_positiveOrientation_of_isEmpty,
        hneV.symm, hneW, hneW.symm]
  · let b := oV.finOrthonormalBasis m.succ_pos Fact.out
    have hb : b.toBasis.orientation = oV := oV.finOrthonormalBasis_orientation m.succ_pos Fact.out
    have hmap : ⇑(b.toBasis.map e) = e.toLinearMap ∘ b := by
      ext i
      simp
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
  have hcard : Fintype.card (Fin n) = finrank ℝ W := by
    simp [Fact.out (p := finrank ℝ W = n)]
  have hneg : Orientation.map (Fin n) e oV = -oW := by
    rcases eq_or_eq_neg_of_card_eq_finrank (Orientation.map (Fin n) e oV) oW hcard with h' | h'
    · exact absurd h' h
    · exact h'
  rw [← oV.abs_orientedJacobian oW e.toLinearMap,
    abs_of_neg ((oV.orientedJacobian_linearEquiv_neg_iff oW e).mpr hneg), neg_neg]

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
    have he : e.toLinearMap = A := rfl
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

end SignAndInvertibility

/-! ### Worked planar examples -/

section PlanarExamples

open scoped EuclideanSpace Matrix.Norms.L2Operator

-- Anisotropic scaling `diag(2, 1)` on `ℝ²` has `J = 2` and `‖A‖² = 4`, witnessing strictness in
-- Hadamard's inequality.
example (o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)) :
    let A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal ![2, 1])
    o.orientedJacobian o A.toLinearMap = 2 ∧
      ‖A‖ ^ 2 = 4 ∧
      |o.orientedJacobian o A.toLinearMap| < ‖A‖ ^ 2 := by
  intro A
  have hJ : o.orientedJacobian o A.toLinearMap = 2 := by
    simp [A, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  have hnorm : ‖A‖ = 2 := by
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal, Pi.norm_def]
    have hsup : (Finset.univ : Finset (Fin 2)).sup (fun i ↦ ‖(![2, 1] : Fin 2 → ℝ) i‖₊) = 2 := by
      rw [Fin.univ_succ]
      simp
    exact congrArg NNReal.toReal hsup
  refine ⟨hJ, by rw [hnorm]; norm_num, by rw [hJ, hnorm]; norm_num⟩

-- The planar reflection `diag(-1, 1)` has `J = -1` when both sides carry `o` and `J = 1` from
-- `(ℝ², o)` to `(ℝ², -o)`.
example (o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)) :
    let R : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1])
    o.orientedJacobian o R = -1 ∧ o.orientedJacobian (-o) R = 1 := by
  intro R
  constructor <;> simp [R]

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
      rw [Fin.univ_succ]
      simp
    exact congrArg NNReal.toReal hsup
  exact ⟨hJ, by rw [hnorm]; exact zero_lt_one⟩

end PlanarExamples

end Orientation
