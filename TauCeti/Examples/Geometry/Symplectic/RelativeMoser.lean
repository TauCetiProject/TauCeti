/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Relative.Basic
public import TauCeti.Geometry.Symplectic.Liouville.Plane
public import TauCeti.Geometry.Symplectic.Manifold.Plane
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import Mathlib.Analysis.Calculus.Deriv.Pow
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.LinearAlgebra.Determinant.Prod

/-!
# Examples: relative Poincaré and relative Moser along the `x`-axis

Let `Q` be the `x`-axis `ℝ × {0}` of the plane `ℝ × ℝ`. Three explicit computations test what
the relative Poincaré lemma and the relative Moser theorems say along `Q`, and which hypotheses
they need.

* **The relative primitive of `dx ∧ dy`.** The area form `dx ∧ dy` restricts to zero on `Q`.
  The relative Poincaré operator `TauCeti.fiberwisePoincareHomotopy`, which contracts along the
  fibre scaling `(x, y) ↦ (x, t y)`, turns it into the primitive `-y dx`
  (`fiberwisePoincareHomotopy_realPlaneDx_wedge_realPlaneDy`), which vanishes along `Q`
  (`neg_realPlaneYDx_mk_zero`). The form `x dy` is also a primitive of `dx ∧ dy`
  (`Prod.extDeriv_realPlaneXDy`), but it does not vanish along `Q`
  (`realPlaneXDy_mk_zero_ne_zero`): among the primitives, fibre scaling selects one vanishing
  along `Q`.
* **Forms agreeing along `Q`.** The forms `dx ∧ dy` and `(1 + y²) dx ∧ dy`
  (`oneAddSqAreaForm`) agree as full ambient tensors at every point of `Q`
  (`oneAddSqAreaForm_val_eq`). Let `g` be the inverse of the homeomorphism `u ↦ u + u³ / 3`
  (`cubicHomeomorph`), so that `(1 + g²) g' = 1` (`hasDerivAt_cubicHomeomorph_symm`). The
  diffeomorphism `φ(x, y) = (x, g y)` (`cubicReparamSnd`) pulls `(1 + y²) dx ∧ dy` back to
  `dx ∧ dy` (`mpullback_cubicReparamSnd_oneAddSqAreaForm`), fixes `Q` pointwise
  (`cubicReparamSnd_mk_zero`) and has differential the identity along `Q`
  (`mfderiv_cubicReparamSnd_mk_zero`). This is the conclusion of the relative Moser theorem with
  prescribed first jet,
  `TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq`, made explicit
  along the noncompact axis `Q`.
* **Forms agreeing only after restriction to `Q`.** The forms `dx ∧ dy` and `2 dx ∧ dy` both
  restrict to zero on `Q` (`mpullback_inclX_two_smul_constSmooth`), but differ at every point
  (`two_smul_constSmooth_val_ne`). The diffeomorphism `(x, y) ↦ (x, y / 2)` (`halfScaleSnd`) pulls
  `2 dx ∧ dy` back to `dx ∧ dy` (`mpullback_halfScaleSnd_two_smul_constSmooth`) and fixes `Q`
  (`halfScaleSnd_mk_zero`), with differential `diag(1, 1 / 2)` (`mfderiv_halfScaleSnd_apply`).
  Every smooth map pulling `2 dx ∧ dy` back to `dx ∧ dy` at a point has Jacobian determinant `1 / 2`
  there (`det_fderiv_eq_of_mpullback_two_smul_constSmooth`), so none has differential the identity
  (`fderiv_ne_id_of_mpullback_two_smul_constSmooth`). When two forms agree only after restriction
  to `Q`, a diffeomorphism fixing `Q` can still exist, but its first jet along `Q` cannot be
  prescribed: the full ambient agreement along the submanifold assumed by
  `TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq` cannot be
  weakened to agreement of the restrictions.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Proposition 6.8 (the relative Poincaré lemma) and Theorem 7.4 (relative Moser).
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti.Examples.RelativeMoser

/-! ### The relative primitive of `dx ∧ dy` -/

/-- **Fibre scaling turns `dx ∧ dy` into `-y dx`.** The relative Poincaré operator of the area
form `dx ∧ dy`, which integrates its contraction along the fibre scaling `(x, y) ↦ (x, t y)`
towards the `x`-axis, is the one-form `-y dx`. -/
theorem fiberwisePoincareHomotopy_realPlaneDx_wedge_realPlaneDy :
    fiberwisePoincareHomotopy (fun p : ℝ × ℝ ↦ (Prod.realPlaneDx p).wedge (Prod.realPlaneDy p)) =
      -Prod.realPlaneYDx := by
  funext p
  rw [fiberwisePoincareHomotopy_apply]
  have h (t : ℝ) : (((Prod.realPlaneDx (p.1, t • p.2)).wedge
      (Prod.realPlaneDy (p.1, t • p.2))).curryLeft ((0 : ℝ), p.2)).compContinuousLinearMap
        ((ContinuousLinearMap.id ℝ ℝ).prodMap (t • ContinuousLinearMap.id ℝ ℝ)) =
      -Prod.realPlaneYDx p := by
    ext v
    obtain ⟨a, rfl⟩ : ∃ a, v = ![a] := ⟨v 0, funext fun i ↦ by fin_cases i; rfl⟩
    -- The contracted tuple is `![(0, y), (a.1, t a.2)]`, on which the wedge evaluates.
    have hv : Matrix.vecCons ((0 : ℝ), p.2) (Prod.map id (t • id) ∘ ![a]) =
        ![((0 : ℝ), p.2), (a.1, t * a.2)] :=
      funext fun i ↦ by fin_cases i <;> rfl
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousLinearMap.coe_prodMap',
      ContinuousLinearMap.coe_id', FunLike.coe_smul]
    rw [hv]
    simp [mul_comm]
  simp only [h, intervalIntegral.integral_const, sub_zero, one_smul, Pi.neg_apply]

/-- **The relative primitive `-y dx` vanishes along the `x`-axis**, and its exterior derivative is
`dx ∧ dy` (`Prod.extDeriv_realPlaneYDx`), as the relative Poincaré lemma asserts for a closed form
restricting to zero on the `x`-axis. -/
theorem neg_realPlaneYDx_mk_zero (x : ℝ) : -Prod.realPlaneYDx (x, 0) = 0 := by
  rw [← Pi.neg_apply, ← fiberwisePoincareHomotopy_realPlaneDx_wedge_realPlaneDy,
    fiberwisePoincareHomotopy_zeroSection]

/-- **The primitive `x dy` of `dx ∧ dy` does not vanish along the `x`-axis**: it is nonzero at
every point `(x, 0)` with `x ≠ 0`. So the primitive is not determined by `d β = dx ∧ dy`, and
fibre scaling selects one vanishing along the axis. That `x dy` is a primitive of `dx ∧ dy` is
`Prod.extDeriv_realPlaneXDy`. -/
theorem realPlaneXDy_mk_zero_ne_zero {x : ℝ} (hx : x ≠ 0) : Prod.realPlaneXDy (x, 0) ≠ 0 := by
  intro h
  have := congrArg (fun α : (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ ↦ α ![(0, 1)]) h
  simp [hx] at this

/-! ### Forms agreeing along the `x`-axis: `(1 + y²) dx ∧ dy` and `dx ∧ dy` -/

/-- The smooth function `(x, y) ↦ 1 + y²` on the plane. -/
private def oneAddSq : C^∞⟮𝓘(ℝ, ℝ × ℝ), ℝ × ℝ; ℝ⟯ :=
  ⟨fun p ↦ 1 + p.2 ^ 2, (by fun_prop : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ 1 + p.2 ^ 2).contMDiff⟩

private theorem oneAddSq_apply (p : ℝ × ℝ) : oneAddSq p = 1 + p.2 ^ 2 :=
  (rfl)

/-- The two-form `(1 + y²) dx ∧ dy` on the plane. -/
def oneAddSqAreaForm : SmoothTwoForm 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) :=
  SmoothForm.funSMulₗ oneAddSq (stdSymplecticForm (V := ℝ)).constSmooth

/-- The form `(1 + y²) dx ∧ dy` evaluates as `(v, w) ↦ (1 + y²) (v₁ w₂ - v₂ w₁)` at `(x, y)`. -/
theorem eval₂_oneAddSqAreaForm (x : ℝ × ℝ) (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ) x) :
    oneAddSqAreaForm.eval₂ x v w = (1 + x.2 ^ 2) * (v.1 * w.2 - v.2 * w.1) := by
  rw [SmoothBundleForm.eval₂_apply, oneAddSqAreaForm, SmoothForm.coe_funSMulₗ]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [oneAddSq_apply, ← SmoothBundleForm.eval₂_apply, eval₂_constSmooth_stdSymplecticForm]

/-- **`(1 + y²) dx ∧ dy` and `dx ∧ dy` agree along the `x`-axis**, as full ambient tensors. -/
theorem oneAddSqAreaForm_val_eq (x : ℝ) :
    oneAddSqAreaForm.val (x, 0) = (stdSymplecticForm (V := ℝ)).constSmooth.val (x, 0) :=
  SmoothBundleForm.apply_eq_of_eval₂_eq fun v w ↦ by
    rw [eval₂_oneAddSqAreaForm, eval₂_constSmooth_stdSymplecticForm]
    simp

/-- The homeomorphism `u ↦ u + u³ / 3` of the real line, strictly increasing with derivative
`1 + u² > 0`. -/
def cubicHomeomorph : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective (fun u : ℝ ↦ u + u ^ 3 / 3)
    (strictMono_id.add ((Odd.strictMono_pow (by decide)).div_const (by norm_num)))
    ((by fun_prop : Continuous fun u : ℝ ↦ u + u ^ 3 / 3).surjective
      (Filter.tendsto_atTop_mono' _ (Filter.eventually_ge_atTop 0 |>.mono fun u hu ↦ by
        dsimp; nlinarith [pow_nonneg hu 3]) Filter.tendsto_id)
      (Filter.tendsto_atBot_mono' _ (Filter.eventually_le_atBot 0 |>.mono fun u hu ↦ by
        dsimp; nlinarith [Odd.pow_nonpos (n := 3) (by decide) hu]) Filter.tendsto_id))).toHomeomorph

/-- The homeomorphism `cubicHomeomorph` is `u ↦ u + u³ / 3`. -/
@[simp]
theorem cubicHomeomorph_apply (u : ℝ) : cubicHomeomorph u = u + u ^ 3 / 3 :=
  (rfl)

/-- The derivative of `u ↦ u + u³ / 3` is `1 + u²`. -/
theorem hasDerivAt_cubicHomeomorph (u : ℝ) : HasDerivAt cubicHomeomorph (1 + u ^ 2) u := by
  have h := (hasDerivAt_id u).add ((hasDerivAt_pow 3 u).div_const 3)
  convert h using 1
  · ext; simp
  · simp

/-- The inverse `g` of `u ↦ u + u³ / 3` is smooth. -/
theorem contDiff_cubicHomeomorph_symm : ContDiff ℝ ∞ cubicHomeomorph.symm :=
  cubicHomeomorph.contDiff_symm_deriv (fun u ↦ by positivity) hasDerivAt_cubicHomeomorph
    (by fun_prop : ContDiff ℝ ∞ fun u : ℝ ↦ u + u ^ 3 / 3)

/-- **The inverse `g` of `u ↦ u + u³ / 3` satisfies `(1 + g²) g' = 1`.** -/
theorem hasDerivAt_cubicHomeomorph_symm (y : ℝ) :
    HasDerivAt cubicHomeomorph.symm (1 + cubicHomeomorph.symm y ^ 2)⁻¹ y :=
  HasDerivAt.of_local_left_inverse cubicHomeomorph.symm.continuous.continuousAt
    (hasDerivAt_cubicHomeomorph _) (by positivity)
    (Filter.Eventually.of_forall cubicHomeomorph.apply_symm_apply)

/-- The diffeomorphism `φ(x, y) = (x, g y)` of the plane, where `g` is the inverse of
`u ↦ u + u³ / 3`. -/
def cubicReparamSnd : (ℝ × ℝ) ≃ₘ⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ (ℝ × ℝ) where
  toFun p := (p.1, cubicHomeomorph.symm p.2)
  invFun p := (p.1, cubicHomeomorph p.2)
  left_inv p := Prod.ext rfl (cubicHomeomorph.apply_symm_apply p.2)
  right_inv p := Prod.ext rfl (cubicHomeomorph.symm_apply_apply p.2)
  contMDiff_toFun :=
    (contDiff_fst.prodMk (contDiff_cubicHomeomorph_symm.comp contDiff_snd)).contMDiff
  contMDiff_invFun := (by fun_prop : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦
    (p.1, p.2 + p.2 ^ 3 / 3)).contMDiff

/-- The diffeomorphism `cubicReparamSnd` is `(x, y) ↦ (x, g y)`. -/
@[simp]
theorem cubicReparamSnd_apply (p : ℝ × ℝ) : cubicReparamSnd p = (p.1, cubicHomeomorph.symm p.2) :=
  (rfl)

/-- The inverse `g` of `u ↦ u + u³ / 3` fixes `0`. -/
@[simp]
theorem cubicHomeomorph_symm_zero : cubicHomeomorph.symm 0 = 0 :=
  cubicHomeomorph.symm_apply_eq.2 (by simp)

/-- `φ(x, y) = (x, g y)` fixes the `x`-axis pointwise. -/
theorem cubicReparamSnd_mk_zero (x : ℝ) : cubicReparamSnd (x, 0) = (x, 0) := by
  simp

/-- The differential of `φ(x, y) = (x, g y)` at `(x, y)` is `v ↦ (v₁, v₂ / (1 + g(y)²))`. -/
theorem mfderiv_cubicReparamSnd_apply (p : ℝ × ℝ) (v : TangentSpace 𝓘(ℝ, ℝ × ℝ) p) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) cubicReparamSnd p v =
      (v.1, (1 + cubicHomeomorph.symm p.2 ^ 2)⁻¹ * v.2) := by
  have h : HasFDerivAt (fun p : ℝ × ℝ ↦ (p.1, cubicHomeomorph.symm p.2))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        ((1 + cubicHomeomorph.symm p.2 ^ 2)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    hasFDerivAt_fst.prodMk ((hasDerivAt_cubicHomeomorph_symm p.2).comp_hasFDerivAt p
      hasFDerivAt_snd)
  have hc : ⇑cubicReparamSnd = fun p : ℝ × ℝ ↦ (p.1, cubicHomeomorph.symm p.2) :=
    funext cubicReparamSnd_apply
  rw [hc, h.mfderiv_apply, NormedSpace.fromTangentSpace_symm_apply]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    smul_apply, ContinuousLinearMap.coe_snd', smul_eq_mul]
  rw [NormedSpace.fromTangentSpace_apply]

/-- **`φ` has differential the identity along the `x`-axis.** -/
theorem mfderiv_cubicReparamSnd_mk_zero (x : ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) cubicReparamSnd (x, 0) =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ × ℝ) (x, 0)) := by
  ext v
  rw [mfderiv_cubicReparamSnd_apply]
  simp only [cubicHomeomorph_symm_zero, zero_pow two_ne_zero, add_zero, inv_one, one_mul]
  -- A tangent vector of the plane is a pair of reals, so it is the pair of its components.
  exact Prod.mk.eta.trans (ContinuousLinearMap.id_apply v).symm

/-- **`φ(x, y) = (x, g y)` pulls `(1 + y²) dx ∧ dy` back to `dx ∧ dy`**, since
`(1 + g²) g' = 1`. -/
theorem mpullback_cubicReparamSnd_oneAddSqAreaForm :
    SmoothForm.mpullback cubicReparamSnd cubicReparamSnd.contMDiff oneAddSqAreaForm =
      (stdSymplecticForm (V := ℝ)).constSmooth :=
  SmoothBundleForm.ext_eval₂ fun p v w ↦ by
    rw [SmoothForm.eval₂_mpullback, eval₂_oneAddSqAreaForm, eval₂_constSmooth_stdSymplecticForm,
      mfderiv_cubicReparamSnd_apply, mfderiv_cubicReparamSnd_apply, cubicReparamSnd_apply]
    have : (1 + cubicHomeomorph.symm p.2 ^ 2) ≠ 0 := by positivity
    field_simp

/-! ### Forms agreeing only after restriction: `2 dx ∧ dy` and `dx ∧ dy` -/

/-- The inclusion `x ↦ (x, 0)` of the `x`-axis into the plane. -/
def inclX (x : ℝ) : ℝ × ℝ := (x, 0)

/-- The inclusion of the `x`-axis is smooth. -/
theorem contMDiff_inclX : ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ inclX :=
  (contDiff_id.prodMk contDiff_const).contMDiff

/-- `dx ∧ dy` restricts to zero on the `x`-axis. -/
theorem mpullback_inclX_constSmooth :
    SmoothForm.mpullback inclX contMDiff_inclX (stdSymplecticForm (V := ℝ)).constSmooth = 0 :=
  SmoothBundleForm.ext_eval₂ fun x v w ↦ by
    have hd : HasFDerivAt inclX ((ContinuousLinearMap.id ℝ ℝ).prod 0) x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const 0 x)
    have h (u : TangentSpace 𝓘(ℝ) x) : (mfderiv 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) inclX x u).2 = 0 := by
      rw [hd.mfderiv_apply, NormedSpace.fromTangentSpace_symm_apply]
      simp only [ContinuousLinearMap.prod_apply, zero_apply]
    rw [SmoothForm.eval₂_mpullback, eval₂_constSmooth_stdSymplecticForm, h, h]
    simp

/-- **`2 dx ∧ dy` and `dx ∧ dy` have the same restriction to the `x`-axis**, namely zero. -/
theorem mpullback_inclX_two_smul_constSmooth :
    SmoothForm.mpullback inclX contMDiff_inclX
        ((2 : ℝ) • (stdSymplecticForm (V := ℝ)).constSmooth) =
      SmoothForm.mpullback inclX contMDiff_inclX (stdSymplecticForm (V := ℝ)).constSmooth := by
  rw [map_smul, mpullback_inclX_constSmooth, smul_zero]

/-- The constant form `2 dx ∧ dy` evaluates as `(v, w) ↦ 2 (v₁ w₂ - v₂ w₁)`. -/
theorem eval₂_two_smul_constSmooth (x : ℝ × ℝ) (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ) x) :
    ((2 : ℝ) • (stdSymplecticForm (V := ℝ)).constSmooth).eval₂ x v w =
      2 * (v.1 * w.2 - v.2 * w.1) := by
  rw [SmoothBundleForm.eval₂_apply, SetLike.val_smul, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, ← SmoothBundleForm.eval₂_apply,
    eval₂_constSmooth_stdSymplecticForm, smul_eq_mul]

/-- **`2 dx ∧ dy` and `dx ∧ dy` differ at every point**, in particular along the `x`-axis. -/
theorem two_smul_constSmooth_val_ne (p : ℝ × ℝ) :
    ((2 : ℝ) • (stdSymplecticForm (V := ℝ)).constSmooth).val p ≠
      (stdSymplecticForm (V := ℝ)).constSmooth.val p := by
  intro h
  have h2 (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ) p) :
      2 * (v.1 * w.2 - v.2 * w.1) = v.1 * w.2 - v.2 * w.1 := by
    rw [← eval₂_two_smul_constSmooth, ← eval₂_constSmooth_stdSymplecticForm,
      SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply, h]
  have := h2 (1, 0) (0, 1)
  norm_num at this

/-- The linear diffeomorphism `(x, y) ↦ (x, y / 2)` of the plane. -/
def halfScaleSnd : (ℝ × ℝ) ≃ₘ⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ (ℝ × ℝ) where
  toFun p := (p.1, p.2 / 2)
  invFun p := (p.1, 2 * p.2)
  left_inv p := by simp [mul_div_cancel₀]
  right_inv p := by simp
  contMDiff_toFun := (by fun_prop : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ (p.1, p.2 / 2)).contMDiff
  contMDiff_invFun := (by fun_prop : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ (p.1, 2 * p.2)).contMDiff

/-- The diffeomorphism `halfScaleSnd` is `(x, y) ↦ (x, y / 2)`. -/
@[simp]
theorem halfScaleSnd_apply (p : ℝ × ℝ) : halfScaleSnd p = (p.1, p.2 / 2) :=
  (rfl)

/-- `(x, y) ↦ (x, y / 2)` fixes the `x`-axis pointwise. -/
theorem halfScaleSnd_mk_zero (x : ℝ) : halfScaleSnd (x, 0) = (x, 0) := by
  simp

/-- The differential of `(x, y) ↦ (x, y / 2)` is `v ↦ (v₁, v₂ / 2)` at every point. -/
theorem mfderiv_halfScaleSnd_apply (p : ℝ × ℝ) (v : TangentSpace 𝓘(ℝ, ℝ × ℝ) p) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) halfScaleSnd p v = (v.1, v.2 / 2) := by
  have h : HasFDerivAt (fun p : ℝ × ℝ ↦ (p.1, p.2 / 2))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((2⁻¹ : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    hasFDerivAt_fst.prodMk ((hasFDerivAt_snd.mul_const (2⁻¹ : ℝ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q ↦ div_eq_mul_inv q.2 2))
  have hc : ⇑halfScaleSnd = fun p : ℝ × ℝ ↦ (p.1, p.2 / 2) := funext halfScaleSnd_apply
  rw [hc, h.mfderiv_apply, NormedSpace.fromTangentSpace_symm_apply]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    smul_apply, ContinuousLinearMap.coe_snd', smul_eq_mul, div_eq_inv_mul]
  rw [NormedSpace.fromTangentSpace_apply]

/-- **`(x, y) ↦ (x, y / 2)` pulls `2 dx ∧ dy` back to `dx ∧ dy`.** -/
theorem mpullback_halfScaleSnd_two_smul_constSmooth :
    SmoothForm.mpullback halfScaleSnd halfScaleSnd.contMDiff
        ((2 : ℝ) • (stdSymplecticForm (V := ℝ)).constSmooth) =
      (stdSymplecticForm (V := ℝ)).constSmooth :=
  SmoothBundleForm.ext_eval₂ fun p v w ↦ by
    rw [SmoothForm.eval₂_mpullback, eval₂_two_smul_constSmooth,
      eval₂_constSmooth_stdSymplecticForm, mfderiv_halfScaleSnd_apply, mfderiv_halfScaleSnd_apply]
    ring

/-- **A map pulling `2 dx ∧ dy` back to `dx ∧ dy` has Jacobian determinant `1 / 2`.** If the
pullback of `2 dx ∧ dy` along a smooth map `f` of the plane agrees with `dx ∧ dy` at `p`, then the
differential of `f` at `p` has determinant `1 / 2`. -/
theorem det_fderiv_eq_of_mpullback_two_smul_constSmooth {f : ℝ × ℝ → ℝ × ℝ}
    (hf : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ f) {p : ℝ × ℝ}
    (h : (SmoothForm.mpullback f hf ((2 : ℝ) • (stdSymplecticForm (V := ℝ)).constSmooth)).val p =
      (stdSymplecticForm (V := ℝ)).constSmooth.val p) :
    (fderiv ℝ f p).det = 1 / 2 := by
  have h2 (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ) p) :
      2 * ((fderiv ℝ f p v).1 * (fderiv ℝ f p w).2 - (fderiv ℝ f p v).2 * (fderiv ℝ f p w).1) =
        v.1 * w.2 - v.2 * w.1 := by
    rw [← eval₂_constSmooth_stdSymplecticForm, SmoothBundleForm.eval₂_apply, ← h,
      ← SmoothBundleForm.eval₂_apply, SmoothForm.eval₂_mpullback, eval₂_two_smul_constSmooth,
      mfderiv_eq_fderiv]
    simp [NormedSpace.fromTangentSpace_apply, NormedSpace.fromTangentSpace_symm_apply]
  have := h2 (1, 0) (0, 1)
  rw [ContinuousLinearMap.det, LinearMap.det_finTwoProd, ContinuousLinearMap.coe_coe]
  norm_num at this
  linarith

/-- **No map pulling `2 dx ∧ dy` back to `dx ∧ dy` has differential the identity.** At a point
where the pullback of `2 dx ∧ dy` along a smooth map `f` agrees with `dx ∧ dy`, the differential
of `f` has determinant `1 / 2` and so is not the identity. Hence the conclusion
`mfderiv Φ = id` along the `x`-axis of the relative Moser theorem with prescribed first jet fails
for these two forms, which agree only after restriction to the `x`-axis. -/
theorem fderiv_ne_id_of_mpullback_two_smul_constSmooth {f : ℝ × ℝ → ℝ × ℝ}
    (hf : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ f) {p : ℝ × ℝ}
    (h : (SmoothForm.mpullback f hf ((2 : ℝ) • (stdSymplecticForm (V := ℝ)).constSmooth)).val p =
      (stdSymplecticForm (V := ℝ)).constSmooth.val p) :
    fderiv ℝ f p ≠ ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  intro hid
  have := det_fderiv_eq_of_mpullback_two_smul_constSmooth hf h
  rw [hid] at this
  norm_num [ContinuousLinearMap.det] at this

end TauCeti.Examples.RelativeMoser
