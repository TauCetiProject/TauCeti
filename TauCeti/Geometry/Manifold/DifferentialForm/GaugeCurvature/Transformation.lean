/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.Geometry.Manifold.DifferentialForm.GaugeCurvature
import TauCeti.Geometry.Manifold.DifferentialForm.Squared
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Gauge transformations of connections on a trivial bundle

Let `𝔄` be a complete normed real algebra, for instance a matrix algebra, and let
`P = M × 𝔄ˣ` be the trivial principal bundle over a manifold `M` with structure group the Lie
group of units `𝔄ˣ`. The connections on `P` are the operators `d + A` for the `𝔄`-valued
`1`-forms `A`, and the gauge group is the group `C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯` of smooth maps
`M → 𝔄ˣ`. The statements below apply in particular to gauge transformations with values in a
subgroup `K` of `𝔄ˣ`, such as a unitary group, but the connections stay `𝔄`-valued: the theory of
connections with values in the Lie algebra of `K` is not developed here. This file defines the
action of the gauge group on connections with the left convention

`g · A = g A g⁻¹ - (dg) g⁻¹`

(`TauCeti.SmoothForm.gaugeAction`), and proves that it is a group action
(`TauCeti.SmoothForm.gaugeAction_one`, `TauCeti.SmoothForm.gaugeAction_mul`) that transforms the
curvature by conjugation.

* The pointwise conjugation `φ ↦ g φ g⁻¹` of `𝔄`-valued forms of any degree
  (`TauCeti.gaugeConj`) is linear, and is itself an action of the gauge group
  (`TauCeti.gaugeConj_one`, `TauCeti.gaugeConj_mul`), so conjugation by `g⁻¹` undoes it
  (`TauCeti.gaugeConj_inv_gaugeConj`, `TauCeti.gaugeConj_gaugeConj_inv`).
* The gauge action is affine over this conjugation: `g · (A + b) = g · A + g b g⁻¹`
  (`TauCeti.SmoothForm.gaugeAction_add`). So its differential in the direction of a tangent vector
  `b` of the affine space of connections is `b ↦ g b g⁻¹`.
* Inversion is differentiated by `d(g⁻¹) = -g⁻¹ (dg) g⁻¹`
  (`TauCeti.mvfderiv_units_inv_apply`), from the product rule for `g g⁻¹ = 1`.
* **Covariant derivative.** For the commutator bracket `[a, b] = a b - b a` of `𝔄`, the covariant
  derivative `d_A ξ = dξ + [A, ξ]` (`TauCeti.gaugeCovariantDeriv`) is equivariant,
  `d_(g · A) (g ξ g⁻¹) = g (d_A ξ) g⁻¹` (`TauCeti.gaugeCovariantDeriv_gaugeAction`).
* **Curvature.** For the commutator bracket `[a, b] = a b - b a` of `𝔄`, the curvature
  `F_A = dA + ½ [A ∧ A]` (`TauCeti.gaugeCurvature`) transforms by conjugation,
  `F_(g · A) = g F_A g⁻¹` (`TauCeti.gaugeCurvature_gaugeAction`). In particular the gauge action
  preserves the flat connections (`TauCeti.gaugeCurvature_gaugeAction_eq_zero_iff`).

This is the counterpart, for differential forms on a manifold, of the pointwise gauge calculus of
`TauCeti.Analysis.PDE.YangMills.GaugeIdentities` for connections `E → E →L[𝕜] 𝔸` on a normed
space, with the same convention: there `TauCeti.gaugeAction` is the gauge action of a map
`O : E → 𝔸` with invertible values, `TauCeti.gaugeAction_gaugeAction` the action law,
`TauCeti.connectionCovariantDerivative_gaugeAction` the transformation law of the covariant
derivative and `TauCeti.connectionCurvature_gaugeAction` that of the curvature. Here the gauge
transformations are smooth maps into `𝔄ˣ`, so no invertibility hypotheses appear.

The conventions are those of the Atiyah–Bott description of the infinitesimal gauge action in
`TauCeti.Geometry.Symplectic.AtiyahBott.TrivialBundle`: for `g = exp (t ξ)` the velocity of
`g · A` at `t = 0` is `[ξ, A] - dξ = -d_A ξ`, the generator used there. That computation of the
velocity is not formalized here.

## Main definitions

* `TauCeti.gaugeConj`: the conjugation `φ ↦ g φ g⁻¹` of `𝔄`-valued forms.
* `TauCeti.SmoothForm.gaugeAction`: the gauge action `g · A = g A g⁻¹ - (dg) g⁻¹` on
  connections.

## Main results

* `TauCeti.SmoothForm.gaugeAction_one`, `TauCeti.SmoothForm.gaugeAction_mul`: the gauge action
  is an action of the gauge group.
* `TauCeti.SmoothForm.gaugeAction_add`: the gauge action is affine over the conjugation.
* `TauCeti.gaugeCovariantDeriv_gaugeAction`: `d_(g · A) (g ξ g⁻¹) = g (d_A ξ) g⁻¹`.
* `TauCeti.gaugeCurvature_gaugeAction`: `F_(g · A) = g F_A g⁻¹`.

## References

* M. F. Atiyah and R. Bott, *The Yang–Mills equations over Riemann surfaces*, Philos. Trans.
  Roy. Soc. London Ser. A 308 (1983), 523–615 (the gauge group and its action on connections).
* E. Meinrenken, *Symplectic geometry*, lecture notes (2000), Theorem 7.46 (the trivial bundle).
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M 𝔄 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]

variable [IsManifold I 1 M] [CompleteSpace 𝔄]

/-! ### Conjugation of forms -/

omit [IsManifold I 1 M] in
/-- The values of the gauge transformation `g⁻¹` are the inverses of those of `g`. -/
private theorem units_inv_val_eq (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) :
    (fun y ↦ (g⁻¹ y).val) = fun y ↦ ((g y)⁻¹ : 𝔄ˣ).val := by
  funext y
  rw [ContMDiffMap.coe_inv, Pi.inv_apply]

omit [IsManifold I 1 M] in
/-- The pointwise inverse of a gauge transformation, read in `𝔄`, is differentiable. -/
private theorem mdifferentiableAt_units_inv_val (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, 𝔄) (fun y ↦ ((g y)⁻¹ : 𝔄ˣ).val) x :=
  units_inv_val_eq g ▸ g⁻¹.mdifferentiableAt_units_val (by simp) x

/-- The `𝔄`-valued `0`-form `x ↦ g x` of a smooth map into the units of `𝔄`. -/
private def unitsValForm (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) : SmoothForm I M 𝔄 0 :=
  SmoothForm.ofFunction
    (⟨fun x ↦ (g x).val, (Units.contMDiff_val (𝕜 := ℝ)).comp g.contMDiff⟩ : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄⟯)

@[simp]
private theorem unitsValForm_val (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (x : M)
    (v : Fin 0 → TangentSpace I x) :
    (unitsValForm g).val x v = (g x).val := by
  rw [Subsingleton.elim v 0]
  exact congrFun (SmoothForm.ofFunction_apply_zero _) x

/-- The **conjugation** `φ ↦ g φ g⁻¹` of `𝔄`-valued `k`-forms by a gauge transformation `g`,
pointwise in the values of the form. On the curvature it is the transformation law of
`TauCeti.gaugeCurvature_gaugeAction`, and on tangent vectors of the affine space of connections it
is the differential of the gauge action (`TauCeti.SmoothForm.gaugeAction_add`). -/
def gaugeConj {k : ℕ} (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) :
    SmoothForm I M 𝔄 k →ₗ[ℝ] SmoothForm I M 𝔄 k :=
  (SmoothForm.wedgeWith (ContinuousLinearMap.mul ℝ 𝔄)).flip (unitsValForm g⁻¹) ∘ₗ
    (SmoothForm.wedgeWith (ContinuousLinearMap.mul ℝ 𝔄).flip).flip (unitsValForm g)

private theorem gaugeConj_apply {k : ℕ} (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (φ : SmoothForm I M 𝔄 k) :
    gaugeConj g φ = SmoothForm.wedgeWith (ContinuousLinearMap.mul ℝ 𝔄)
      (SmoothForm.wedgeWith (ContinuousLinearMap.mul ℝ 𝔄).flip φ (unitsValForm g))
      (unitsValForm g⁻¹) :=
  (rfl)

/-- The conjugate of a form evaluated on tangent vectors: `(g φ g⁻¹)(v) = g φ(v) g⁻¹`. -/
@[simp]
theorem gaugeConj_val {k : ℕ} (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (φ : SmoothForm I M 𝔄 k) (x : M)
    (v : Fin k → TangentSpace I x) :
    (gaugeConj g φ).val x v = (g x).val * φ.val x v * ((g x)⁻¹ : 𝔄ˣ).val := by
  simp [gaugeConj, SmoothForm.wedgeWith_apply_zero_right, ContMDiffMap.coe_inv]

/-- The identity gauge transformation conjugates trivially. -/
@[simp]
theorem gaugeConj_one {k : ℕ} (φ : SmoothForm I M 𝔄 k) :
    gaugeConj (1 : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) φ = φ :=
  Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ by
    simp [ContMDiffMap.coe_one]

/-- Conjugation is an action of the gauge group: `(g h) φ (g h)⁻¹ = g (h φ h⁻¹) g⁻¹`. -/
theorem gaugeConj_mul {k : ℕ} (g h : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (φ : SmoothForm I M 𝔄 k) :
    gaugeConj (g * h) φ = gaugeConj g (gaugeConj h φ) :=
  Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ by
    simp [ContMDiffMap.coe_mul, mul_assoc]

/-- Conjugation by `g⁻¹` undoes conjugation by `g`. -/
@[simp]
theorem gaugeConj_inv_gaugeConj {k : ℕ} (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯)
    (φ : SmoothForm I M 𝔄 k) : gaugeConj g⁻¹ (gaugeConj g φ) = φ := by
  rw [← gaugeConj_mul, inv_mul_cancel, gaugeConj_one]

/-- Conjugation by `g` undoes conjugation by `g⁻¹`. -/
@[simp]
theorem gaugeConj_gaugeConj_inv {k : ℕ} (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯)
    (φ : SmoothForm I M 𝔄 k) : gaugeConj g (gaugeConj g⁻¹ φ) = φ := by
  rw [← gaugeConj_mul, mul_inv_cancel, gaugeConj_one]

/-- A conjugate of a form vanishes exactly when the form does. -/
@[simp]
theorem gaugeConj_eq_zero_iff {k : ℕ} {g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯} {φ : SmoothForm I M 𝔄 k} :
    gaugeConj g φ = 0 ↔ φ = 0 :=
  ⟨fun h ↦ by rw [← gaugeConj_inv_gaugeConj g φ, h, map_zero], fun h ↦ by rw [h, map_zero]⟩

/-! ### The gauge action -/

variable [IsManifold I 2 M]

/-- The derivative of the `0`-form of a gauge transformation `g` is `dg`. -/
private theorem mextDeriv_unitsValForm_apply (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (x : M)
    (u : TangentSpace I x) :
    mextDeriv (unitsValForm g).val x ![u] = mvfderiv I (fun y ↦ (g y).val) x u := by
  rw [← mextDerivₗ_apply, mextDerivₗ_zero_apply]
  simp only [unitsValForm_val]

/-- The derivative of the `0`-form of `g⁻¹` is `d(g⁻¹) = -g⁻¹ (dg) g⁻¹`. -/
private theorem mextDeriv_unitsValForm_inv_apply (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (x : M)
    (u : TangentSpace I x) :
    mextDeriv (unitsValForm g⁻¹).val x ![u] =
      -(((g x)⁻¹ : 𝔄ˣ).val * mvfderiv I (fun y ↦ (g y).val) x u * ((g x)⁻¹ : 𝔄ˣ).val) := by
  rw [mextDeriv_unitsValForm_apply, ← mvfderiv_units_inv_apply
    (g.mdifferentiableAt_units_val (by simp) x) (mdifferentiableAt_units_inv_val g x),
    units_inv_val_eq]

/-- The **gauge action** `g · A = g A g⁻¹ - (dg) g⁻¹` of a gauge transformation
`g : M → 𝔄ˣ` on the connection `d + A` of the trivial bundle, given by an `𝔄`-valued `1`-form
`A`. This is the left convention: `(g h) · A = g · (h · A)`
(`TauCeti.SmoothForm.gaugeAction_mul`). It is the counterpart for forms on a manifold of the
pointwise `TauCeti.gaugeAction` on a normed space. -/
def SmoothForm.gaugeAction (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (A : SmoothForm I M 𝔄 1) :
    SmoothForm I M 𝔄 1 :=
  gaugeConj g A -
    SmoothForm.wedgeWith (ContinuousLinearMap.mul ℝ 𝔄) (mextDerivₗ I 0 (unitsValForm g))
      (unitsValForm g⁻¹)

/-- The gauge action evaluated at a tangent vector:
`(g · A)(v) = g A(v) g⁻¹ - dg(v) g⁻¹`. -/
theorem SmoothForm.gaugeAction_val (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (A : SmoothForm I M 𝔄 1)
    (x : M) (v : TangentSpace I x) :
    (SmoothForm.gaugeAction g A).val x ![v] = (g x).val * A.val x ![v] * ((g x)⁻¹ : 𝔄ˣ).val -
      mvfderiv I (fun y ↦ (g y).val) x v * ((g x)⁻¹ : 𝔄ˣ).val := by
  rw [SmoothForm.gaugeAction, Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
    gaugeConj_val, SmoothForm.wedgeWith_apply_zero_right, mextDerivₗ_zero_apply]
  simp only [unitsValForm_val, ContMDiffMap.coe_inv, Pi.inv_apply,
    ContinuousLinearMap.mul_apply']

/-- The identity gauge transformation acts trivially. -/
@[simp]
theorem SmoothForm.gaugeAction_one (A : SmoothForm I M 𝔄 1) :
    SmoothForm.gaugeAction (1 : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) A = A :=
  SmoothBundleForm.ext_eval₁ fun x v ↦ by
    rw [SmoothForm.gaugeAction_val]
    simp [ContMDiffMap.coe_one, mvfderiv_const]

/-- **The gauge action is a left action**: `(g h) · A = g · (h · A)`. -/
theorem SmoothForm.gaugeAction_mul (g h : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (A : SmoothForm I M 𝔄 1) :
    SmoothForm.gaugeAction (g * h) A =
      SmoothForm.gaugeAction g (SmoothForm.gaugeAction h A) :=
  SmoothBundleForm.ext_eval₁ fun x v ↦ by
    -- The Leibniz rule for the product `g h` of the two `𝔄`-valued functions.
    have hgh : (fun y ↦ ((g * h) y).val) =
        (fun y ↦ (g y).val) • fun y ↦ (h y).val := by
      funext y
      rw [ContMDiffMap.coe_mul, Pi.mul_apply, Units.val_mul, Pi.smul_apply', smul_eq_mul]
    rw [SmoothForm.gaugeAction_val, SmoothForm.gaugeAction_val, SmoothForm.gaugeAction_val, hgh,
      mvfderiv_smul_algebra (F := 𝔄) (g.mdifferentiableAt_units_val (by simp) x)
        (h.mdifferentiableAt_units_val (by simp) x)]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
      ContMDiffMap.coe_mul, Pi.mul_apply, mul_inv_rev, Units.val_mul, mul_sub, sub_mul, add_mul,
      mul_assoc, Units.mul_inv_cancel_left]
    abel

/-- **The gauge action is affine over the conjugation**: `g · (A + b) = g · A + g b g⁻¹`. -/
theorem SmoothForm.gaugeAction_add (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (A b : SmoothForm I M 𝔄 1) :
    SmoothForm.gaugeAction g (A + b) = SmoothForm.gaugeAction g A + gaugeConj g b := by
  rw [SmoothForm.gaugeAction, SmoothForm.gaugeAction, map_add]
  abel

/-! ### The covariant derivative -/

/-- **The covariant derivative transforms by conjugation.** For the commutator bracket
`[a, b] = a b - b a` of `𝔄`, the covariant derivative of the gauge transformed connection on the
conjugated function is `d_(g · A) (g ξ g⁻¹) = g (d_A ξ) g⁻¹`. This is the counterpart for forms
on a manifold of the pointwise `TauCeti.connectionCovariantDerivative_gaugeAction`. -/
theorem gaugeCovariantDeriv_gaugeAction {β : 𝔄 →L[ℝ] 𝔄 →L[ℝ] 𝔄}
    (hβ : ∀ a b, β a b = a * b - b * a) (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (A : SmoothForm I M 𝔄 1)
    (ξ : SmoothForm I M 𝔄 0) :
    gaugeCovariantDeriv β (SmoothForm.gaugeAction g A) (gaugeConj g ξ) =
      gaugeConj g (gaugeCovariantDeriv β A ξ) :=
  SmoothBundleForm.ext_eval₁ fun x v ↦ by
    have hG := g.mdifferentiableAt_units_val (by simp) x
    have hGi := mdifferentiableAt_units_inv_val g x
    have hξ := (SmoothForm.contMDiff_apply_zero ξ).mdifferentiableAt (x := x) (by simp)
    have hξGi : MDifferentiableAt I 𝓘(ℝ, 𝔄)
        ((fun y ↦ ξ.val y 0) • fun y ↦ ((g y)⁻¹ : 𝔄ˣ).val) x :=
      hξ.mul hGi
    -- The function underlying `g ξ g⁻¹` is a product of three `𝔄`-valued functions.
    have hfun : (fun y ↦ (gaugeConj g ξ).val y 0) = (fun y ↦ (g y).val) •
        ((fun y ↦ ξ.val y 0) • fun y ↦ ((g y)⁻¹ : 𝔄ˣ).val) := by
      funext y
      simp [mul_assoc]
    rw [gaugeCovariantDeriv_val, gaugeConj_val g (gaugeCovariantDeriv β A ξ),
      gaugeCovariantDeriv_val, gaugeConj_val g ξ x 0, SmoothForm.gaugeAction_val,
      ← mextDerivₗ_apply, mextDerivₗ_zero_apply, ← mextDerivₗ_apply, mextDerivₗ_zero_apply, hfun,
      mvfderiv_smul_algebra (F := 𝔄) hG hξGi, mvfderiv_smul_algebra (F := 𝔄) hξ hGi]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
      Pi.smul_apply', mvfderiv_units_inv_apply hG hGi, hβ, mul_add, add_mul, mul_sub, sub_mul,
      mul_neg, mul_assoc, Units.inv_mul_cancel_left]
    abel

/-! ### The curvature -/

/-- **The curvature transforms by conjugation.** For the commutator bracket `[a, b] = a b - b a`
of `𝔄`, the curvature of the gauge transformed connection is `F_(g · A) = g F_A g⁻¹`. -/
theorem gaugeCurvature_gaugeAction {β : 𝔄 →L[ℝ] 𝔄 →L[ℝ] 𝔄} (hβ : ∀ a b, β a b = a * b - b * a)
    (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (A : SmoothForm I M 𝔄 1) :
    gaugeCurvature β (SmoothForm.gaugeAction g A) = gaugeConj g (gaugeCurvature β A) := by
  have hskew : ∀ a b, β a b = -β b a := fun a b ↦ by rw [hβ, hβ, neg_sub]
  refine SmoothBundleForm.ext_eval₂ fun x v w ↦ ?_
  have hdd : mextDeriv (mextDerivₗ I 0 (unitsValForm g)).val x ![v, w] = 0 := by
    have h0 := LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ (I := I) (M := M) (F := 𝔄) 0)
      (unitsValForm g)
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at h0
    -- The zero form evaluates to zero. Its values lie in the fibres `Trivial M 𝔄 x` of the
    -- trivial bundle, where `zero_apply` does not apply, so this is closed by `rfl`.
    rw [← mextDerivₗ_apply, h0]
    rfl
  simp only [SmoothBundleForm.eval₂_apply]
  rw [gaugeCurvature_val β hskew, gaugeConj_val, gaugeCurvature_val β hskew,
    SmoothForm.gaugeAction_val, SmoothForm.gaugeAction_val, ← mextDerivₗ_apply,
    SmoothForm.gaugeAction, map_sub, Submodule.coe_sub, Pi.sub_apply,
    ContinuousAlternatingMap.sub_apply, mextDerivₗ_apply, mextDerivₗ_apply, gaugeConj_apply,
    SmoothForm.coe_wedgeWith, SmoothForm.mextDeriv_wedgeWith_apply_one_zero,
    SmoothForm.coe_wedgeWith, SmoothForm.mextDeriv_wedgeWith_apply_one_zero,
    SmoothForm.coe_wedgeWith, SmoothForm.mextDeriv_wedgeWith_apply_one_zero]
  simp only [mextDeriv_unitsValForm_inv_apply]
  simp only [RoughForm.wedgeWith_apply_zero_right, hdd, mextDeriv_unitsValForm_apply,
    mextDerivₗ_zero_apply, unitsValForm_val, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply', hβ, ContMDiffMap.coe_inv, Pi.inv_apply, mul_sub, sub_mul,
    mul_add, add_mul, mul_neg, zero_mul, mul_assoc, Units.inv_mul_cancel_left]
  abel

/-- The gauge action preserves the flat connections. -/
theorem gaugeCurvature_gaugeAction_eq_zero_iff {β : 𝔄 →L[ℝ] 𝔄 →L[ℝ] 𝔄}
    (hβ : ∀ a b, β a b = a * b - b * a) (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯)
    (A : SmoothForm I M 𝔄 1) :
    gaugeCurvature β (SmoothForm.gaugeAction g A) = 0 ↔ gaugeCurvature β A = 0 := by
  rw [gaugeCurvature_gaugeAction hβ, gaugeConj_eq_zero_iff]

end TauCeti
