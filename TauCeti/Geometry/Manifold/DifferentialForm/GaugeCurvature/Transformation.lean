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
group of units `𝔄ˣ`; a closed subgroup `K` of `𝔄ˣ`, such as a unitary group, is treated by
restricting to gauge transformations with values in `K`. The connections on `P` are the operators
`d + A` for the `𝔄`-valued `1`-forms `A`, and the gauge group is the group
`C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯` of smooth maps `M → 𝔄ˣ`. This file defines its action on connections
with the left convention

`g · A = g A g⁻¹ - (dg) g⁻¹`

(`TauCeti.gaugeAction`), and proves that it is a group action
(`TauCeti.gaugeAction_one`, `TauCeti.gaugeAction_mul`) that transforms the curvature by
conjugation.

* The pointwise conjugation `φ ↦ g φ g⁻¹` of `𝔄`-valued forms of any degree
  (`TauCeti.gaugeConj`) is linear, and is itself an action of the gauge group
  (`TauCeti.gaugeConj_one`, `TauCeti.gaugeConj_mul`).
* The gauge action is affine over this conjugation: `g · (A + b) = g · A + g b g⁻¹`
  (`TauCeti.gaugeAction_add`). So its differential in the direction of a tangent vector `b` of the
  affine space of connections is `b ↦ g b g⁻¹`.
* Inversion is differentiated by `d(g⁻¹) = -g⁻¹ (dg) g⁻¹`
  (`TauCeti.mvfderiv_units_inv_apply`), from the product rule for `g g⁻¹ = 1`.
* **Curvature.** For the commutator bracket `[a, b] = a b - b a` of `𝔄`, the curvature
  `F_A = dA + ½ [A ∧ A]` (`TauCeti.gaugeCurvature`) transforms by conjugation,
  `F_(g · A) = g F_A g⁻¹` (`TauCeti.gaugeCurvature_gaugeAction`). In particular the gauge action
  preserves the flat connections (`TauCeti.gaugeCurvature_gaugeAction_eq_zero_iff`).

The conventions are those of the Atiyah–Bott description of the infinitesimal gauge action in
`TauCeti.Geometry.Symplectic.AtiyahBott.TrivialBundle`: for `g = exp (t ξ)` the velocity of
`g · A` at `t = 0` is `[ξ, A] - dξ = -d_A ξ`, the generator used there. That computation of the
velocity is not formalized here.

## Main definitions

* `TauCeti.gaugeConj`: the conjugation `φ ↦ g φ g⁻¹` of `𝔄`-valued forms.
* `TauCeti.gaugeAction`: the gauge action `g · A = g A g⁻¹ - (dg) g⁻¹` on connections.

## Main results

* `TauCeti.gaugeAction_one`, `TauCeti.gaugeAction_mul`: the gauge action is an action of the
  gauge group.
* `TauCeti.gaugeAction_add`: the gauge action is affine over the conjugation.
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

variable [IsManifold I 1 M]

/-- Two `1`-forms agree when they agree on every tangent vector. -/
private theorem smoothForm_ext_one {φ ψ : SmoothForm I M 𝔄 1}
    (h : ∀ x (v : TangentSpace I x), φ.val x ![v] = ψ.val x ![v]) : φ = ψ :=
  Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ by
    have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
    rw [hv]
    exact h x (v 0)

variable [CompleteSpace 𝔄]

/-! ### Conjugation of forms -/

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
is the differential of the gauge action (`TauCeti.gaugeAction_add`). -/
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

/-! ### The gauge action -/

variable [IsManifold I 2 M]

/-- The **gauge action** `g · A = g A g⁻¹ - (dg) g⁻¹` of a gauge transformation
`g : M → 𝔄ˣ` on the connection `d + A` of the trivial bundle, given by an `𝔄`-valued `1`-form
`A`. This is the left convention: `(g h) · A = g · (h · A)` (`TauCeti.gaugeAction_mul`). -/
def gaugeAction (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (A : SmoothForm I M 𝔄 1) :
    SmoothForm I M 𝔄 1 :=
  gaugeConj g A -
    SmoothForm.wedgeWith (ContinuousLinearMap.mul ℝ 𝔄) (mextDerivₗ I 0 (unitsValForm g))
      (unitsValForm g⁻¹)

/-- The gauge action evaluated at a tangent vector:
`(g · A)(v) = g A(v) g⁻¹ - dg(v) g⁻¹`. -/
theorem gaugeAction_val (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (A : SmoothForm I M 𝔄 1) (x : M)
    (v : TangentSpace I x) :
    (gaugeAction g A).val x ![v] = (g x).val * A.val x ![v] * ((g x)⁻¹ : 𝔄ˣ).val -
      mvfderiv I (fun y ↦ (g y).val) x v * ((g x)⁻¹ : 𝔄ˣ).val := by
  rw [gaugeAction, Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
    gaugeConj_val, SmoothForm.wedgeWith_apply_zero_right, mextDerivₗ_zero_apply]
  simp only [unitsValForm_val, ContMDiffMap.coe_inv, Pi.inv_apply,
    ContinuousLinearMap.mul_apply']

/-- The identity gauge transformation acts trivially. -/
@[simp]
theorem gaugeAction_one (A : SmoothForm I M 𝔄 1) :
    gaugeAction (1 : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) A = A :=
  smoothForm_ext_one fun x v ↦ by
    rw [gaugeAction_val]
    simp [ContMDiffMap.coe_one, mvfderiv_const]

/-- **The gauge action is a left action**: `(g h) · A = g · (h · A)`. -/
theorem gaugeAction_mul (g h : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (A : SmoothForm I M 𝔄 1) :
    gaugeAction (g * h) A = gaugeAction g (gaugeAction h A) :=
  smoothForm_ext_one fun x v ↦ by
    have hg : MDifferentiableAt I 𝓘(ℝ, 𝔄) (fun y ↦ (g y).val) x :=
      ((Units.contMDiff_val (𝕜 := ℝ)).comp g.contMDiff).mdifferentiableAt (by simp)
    have hh : MDifferentiableAt I 𝓘(ℝ, 𝔄) (fun y ↦ (h y).val) x :=
      ((Units.contMDiff_val (𝕜 := ℝ)).comp h.contMDiff).mdifferentiableAt (by simp)
    -- The Leibniz rule for the product `g h` of the two `𝔄`-valued functions.
    have hgh : (fun y ↦ ((g * h) y).val) =
        (fun y ↦ (g y).val) • fun y ↦ (h y).val := by
      funext y
      rw [ContMDiffMap.coe_mul, Pi.mul_apply, Units.val_mul, Pi.smul_apply', smul_eq_mul]
    rw [gaugeAction_val, gaugeAction_val, gaugeAction_val, hgh,
      mvfderiv_smul_algebra (F := 𝔄) hg hh,
      add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, smul_eq_mul,
      ContMDiffMap.coe_mul, Pi.mul_apply, mul_inv_rev, Units.val_mul, Units.val_mul]
    simp only [mul_sub, sub_mul, add_mul, mul_assoc, Units.mul_inv_cancel_left]
    abel

/-- **The gauge action is affine over the conjugation**: `g · (A + b) = g · A + g b g⁻¹`. -/
theorem gaugeAction_add (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (A b : SmoothForm I M 𝔄 1) :
    gaugeAction g (A + b) = gaugeAction g A + gaugeConj g b := by
  rw [gaugeAction, gaugeAction, map_add]
  abel

/-! ### The curvature -/

omit [CompleteSpace 𝔄] [IsManifold I 2 M] in
/-- The Leibniz rule for the exterior derivative of the pairing of an `𝔄`-valued `1`-form with an
`𝔄`-valued `0`-form, stated for the smooth paired wedge. -/
private theorem mextDeriv_wedgeWith_one_zero (μ : 𝔄 →L[ℝ] 𝔄 →L[ℝ] 𝔄)
    (φ : SmoothForm I M 𝔄 1) (ψ : SmoothForm I M 𝔄 0) (x : M) (v w : TangentSpace I x) :
    mextDeriv (SmoothForm.wedgeWith μ φ ψ).val x ![v, w] =
      μ (mextDeriv φ.val x ![v, w]) (ψ.val x 0) -
        (μ (φ.val x ![v]) (mextDeriv ψ.val x ![w]) -
          μ (φ.val x ![w]) (mextDeriv ψ.val x ![v])) := by
  rw [SmoothForm.coe_wedgeWith]
  exact SmoothForm.mextDeriv_wedgeWith_apply_one_zero μ φ ψ x v w

/-- **The curvature transforms by conjugation.** For the commutator bracket `[a, b] = a b - b a`
of `𝔄`, the curvature of the gauge transformed connection is `F_(g · A) = g F_A g⁻¹`. -/
theorem gaugeCurvature_gaugeAction {β : 𝔄 →L[ℝ] 𝔄 →L[ℝ] 𝔄} (hβ : ∀ a b, β a b = a * b - b * a)
    (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯) (A : SmoothForm I M 𝔄 1) :
    gaugeCurvature β (gaugeAction g A) = gaugeConj g (gaugeCurvature β A) := by
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
  have hG : ∀ u : TangentSpace I x, mextDeriv (unitsValForm g).val x ![u] =
      mvfderiv I (fun y ↦ (g y).val) x u := fun u ↦ by
    rw [← mextDerivₗ_apply, mextDerivₗ_zero_apply]
    simp only [unitsValForm_val]
  have hGi : ∀ u : TangentSpace I x, mextDeriv (unitsValForm g⁻¹).val x ![u] =
      -(((g x)⁻¹ : 𝔄ˣ).val * mvfderiv I (fun y ↦ (g y).val) x u * ((g x)⁻¹ : 𝔄ˣ).val) :=
    fun u ↦ by
      have hgi : (fun y ↦ (g⁻¹ y).val) = fun y ↦ ((g y)⁻¹ : 𝔄ˣ).val := by
        funext y
        rw [ContMDiffMap.coe_inv, Pi.inv_apply]
      have hg : MDifferentiableAt I 𝓘(ℝ, 𝔄) (fun y ↦ (g y).val) x :=
        ((Units.contMDiff_val (𝕜 := ℝ)).comp g.contMDiff).mdifferentiableAt (by simp)
      have hg' : MDifferentiableAt I 𝓘(ℝ, 𝔄) (fun y ↦ (g⁻¹ y).val) x :=
        ((Units.contMDiff_val (𝕜 := ℝ)).comp g⁻¹.contMDiff).mdifferentiableAt (by simp)
      rw [← mextDerivₗ_apply, mextDerivₗ_zero_apply,
        ← mvfderiv_units_inv_apply hg (hgi ▸ hg')]
      simp only [unitsValForm_val, hgi]
  simp only [SmoothBundleForm.eval₂_apply]
  rw [gaugeCurvature_val β hskew, gaugeConj_val, gaugeCurvature_val β hskew,
    gaugeAction_val, gaugeAction_val, ← mextDerivₗ_apply, gaugeAction, map_sub,
    Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply, mextDerivₗ_apply,
    mextDerivₗ_apply, gaugeConj_apply, mextDeriv_wedgeWith_one_zero,
    mextDeriv_wedgeWith_one_zero, mextDeriv_wedgeWith_one_zero]
  simp only [SmoothForm.wedgeWith_apply_zero_right, hdd, hG, hGi, mextDerivₗ_zero_apply,
    unitsValForm_val, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', hβ,
    ContMDiffMap.coe_inv, Pi.inv_apply]
  simp only [mul_sub, sub_mul, mul_add, add_mul, mul_neg, zero_mul, mul_assoc,
    Units.inv_mul_cancel_left]
  abel

/-- The gauge action preserves the flat connections. -/
theorem gaugeCurvature_gaugeAction_eq_zero_iff {β : 𝔄 →L[ℝ] 𝔄 →L[ℝ] 𝔄}
    (hβ : ∀ a b, β a b = a * b - b * a) (g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯)
    (A : SmoothForm I M 𝔄 1) :
    gaugeCurvature β (gaugeAction g A) = 0 ↔ gaugeCurvature β A = 0 := by
  rw [gaugeCurvature_gaugeAction hβ]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  rw [← gaugeConj_one (gaugeCurvature β A), ← inv_mul_cancel g, gaugeConj_mul, h, map_zero]

end TauCeti
