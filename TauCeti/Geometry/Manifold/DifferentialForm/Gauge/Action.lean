/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Gauge.Curvature
public import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.Analysis.Normed.Algebra.Exponential
import TauCeti.Geometry.Manifold.DifferentialForm.Squared
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The gauge action on connections of a trivial bundle

Let `𝔸` be a normed real algebra, for instance the matrix algebra `Mₙ(ℝ)` or `Mₙ(ℂ)`, and let
`M` be a manifold. The connections of the trivial bundle over `M` whose structure group is
contained in the units of `𝔸` are the operators `d + A` for the `𝔸`-valued `1`-forms `A`, and
the gauge group is the group `C^∞(M, 𝔸)ˣ` of units of the algebra of smooth `𝔸`-valued
functions: the smooth maps `g : M → 𝔸` whose values are invertible, with `g⁻¹` the pointwise
inverse. The bracket of `𝔸` is the commutator `[a, b] = a b - b a`, which enters the curvature
`F_A = dA + ½ [A ∧ A]` (`TauCeti.gaugeCurvature`) as the continuous bilinear map
`ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip`.

This file defines the action of the gauge group on connections, with the left convention

`g · A = g A g⁻¹ - (dg) g⁻¹`

(`TauCeti.mgaugeAction`), and proves its basic properties.

* **Conjugation.** `g` acts on `𝔸`-valued forms of every degree by the pointwise conjugation
  `Ad_g φ = g φ g⁻¹` (`TauCeti.gaugeConj`), a group action by linear maps
  (`TauCeti.gaugeConj_one`, `TauCeti.gaugeConj_mul`, with inverse conjugation by `g⁻¹`,
  `TauCeti.gaugeConj_gaugeConj_inv`) that commutes with brackets of `1`-forms
  (`TauCeti.wedgeWith_gaugeConj_gaugeConj`).
* **The Maurer–Cartan form.** The right Maurer–Cartan form `θ_g = (dg) g⁻¹`
  (`TauCeti.mrightMaurerCartan`) satisfies the cocycle law `θ_(g h) = θ_g + Ad_g θ_h`
  (`TauCeti.mrightMaurerCartan_mul`) and the Maurer–Cartan equation `dθ_g = ½ [θ_g ∧ θ_g]`
  (`TauCeti.mextDerivₗ_mrightMaurerCartan`). The derivative of a conjugated `1`-form is
  `d(Ad_g φ) = Ad_g dφ + [θ_g ∧ Ad_g φ]` (`TauCeti.mextDerivₗ_gaugeConj`).
* **The gauge action.** `g · A = Ad_g A - θ_g` is a left action of the gauge group
  (`TauCeti.mgaugeAction_one`, `TauCeti.mgaugeAction_mul`), bundled as the `MulAction`
  `TauCeti.gaugeMulAction`, by affine maps whose linear part is
  `Ad_g` (`TauCeti.mgaugeAction_add`), and the curvature transforms by conjugation,
  `F_(g · A) = Ad_g F_A` (`TauCeti.gaugeCurvature_mgaugeAction`). In particular the gauge group
  preserves the flat connections, and the pure gauge connections `g · 0 = -θ_g` are flat.
  The covariant derivative is equivariant, `d_(g · A) (g ξ g⁻¹) = g (d_A ξ) g⁻¹`
  (`TauCeti.gaugeCovariantDeriv_mgaugeAction`).
* **The infinitesimal action.** For a complete `𝔸`, a smooth function `ξ : M → 𝔸` generates the
  gauge transformations `exp (t ξ)` (`TauCeti.gaugeExp`), and
  `d/dt|_(t=0) exp (t ξ) · A = [ξ, A] - dξ = -d_A ξ`
  (`TauCeti.hasDerivAt_mgaugeAction_gaugeExp_smul_apply`), where `d_A ξ = dξ + [A, ξ]` is the
  covariant derivative `TauCeti.gaugeCovariantDeriv`. So the infinitesimal generator of `ξ` at
  `A` is `-d_A ξ`, the generator used for the Atiyah–Bott moment map in
  `TauCeti.Geometry.Symplectic.AtiyahBott.TrivialBundle`.

The function-level versions of these identities on a normed space, for connections with values
in a normed algebra, are `TauCeti.gaugeAction`, `TauCeti.rightMaurerCartan` and
`TauCeti.connectionCurvature_gaugeAction`; here the connections are differential forms on a
manifold.

## Main definitions

* `TauCeti.gaugeConj`: conjugation `φ ↦ g φ g⁻¹` of `𝔸`-valued forms by a gauge transformation.
* `TauCeti.mrightMaurerCartan`: the right Maurer–Cartan form `(dg) g⁻¹`.
* `TauCeti.mgaugeAction`: the gauge action `g · A = g A g⁻¹ - (dg) g⁻¹` on connections.
* `TauCeti.gaugeMulAction`: the gauge action bundled as a `MulAction` (not an instance).
* `TauCeti.gaugeExp`: the gauge transformation `exp ξ` of a smooth function `ξ`.

## Main results

* `TauCeti.mgaugeAction_one`, `TauCeti.mgaugeAction_mul`: the gauge action is a left action.
* `TauCeti.gaugeCurvature_mgaugeAction`: `F_(g · A) = g F_A g⁻¹`.
* `TauCeti.gaugeCovariantDeriv_mgaugeAction`: `d_(g · A) (g ξ g⁻¹) = g (d_A ξ) g⁻¹`.
* `TauCeti.hasDerivAt_mgaugeAction_gaugeExp_smul_apply`: the infinitesimal gauge action is
  `ξ ↦ -d_A ξ`.

## References

* M. F. Atiyah and R. Bott, *The Yang–Mills equations over Riemann surfaces*, Philos. Trans.
  Roy. Soc. London Ser. A 308 (1983), 523–615 (the gauge group and its action on connections).
* E. Meinrenken, *Symplectic geometry*, lecture notes, 2000, Theorem 7.46 (the gauge action on
  the connections of the trivial bundle over a surface).
* S.-J. Oh and D. Tataru, *The Yang–Mills heat flow and the caloric gauge*, Astérisque 436
  (2022), arXiv:1709.08599, Section 1 (the transformation laws of the Maurer–Cartan form and of
  the curvature under gauge transformations).
-/

public section

noncomputable section

open Bundle NormedSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M 𝔸 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [ContMDiffRing 𝓘(ℝ, 𝔸) ∞ 𝔸] {k : ℕ}

/-! ### Values of gauge transformations -/

section Values

variable (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) (x : M)

/-- The differential of the inverse of a gauge transformation:
`d(g⁻¹) = -g⁻¹ (dg) g⁻¹`. -/
private theorem mvfderiv_inv_apply (v : TangentSpace I x) :
    mvfderiv I ((g⁻¹ : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x v =
      -((↑g⁻¹ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x * mvfderiv I (g : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x v *
        (↑g⁻¹ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x) :=
  mvfderiv_apply_eq_neg_mul_mul_of_mul_eq_one
    ((g : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯).contMDiff.mdifferentiableAt (by simp))
    ((↑g⁻¹ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯).contMDiff.mdifferentiableAt (by simp))
    (.of_eq (by rw [← ContMDiffMap.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      ContMDiffMap.coe_one])) (by
      simp only [← ContMDiffMap.coe_evalUnitsHom_apply, map_inv, Units.inv_mul]) v

end Values

/-! ### Exponentials of smooth functions -/

section GaugeExp

variable [CompleteSpace 𝔸]

/-- The gauge transformation `exp ξ : x ↦ exp (ξ x)` of a smooth `𝔸`-valued function `ξ`, an
element of the Lie algebra `C^∞(M, 𝔸)` of the gauge group. Its inverse is `exp (-ξ)`. -/
def gaugeExp (ξ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ where
  val := ⟨fun x ↦ exp (ξ x), (contDiff_exp ℝ).comp_contMDiff ξ.contMDiff⟩
  inv := ⟨fun x ↦ exp (-ξ x), (contDiff_exp ℝ).comp_contMDiff ξ.contMDiff.neg⟩
  -- The anonymous constructors elaborate at the underlying subtype, so `ContMDiffMap.coe_mul`
  -- does not match the product; `change` unfolds it to the pointwise product by definition.
  val_inv := ContMDiffMap.ext fun x ↦ by
    change exp (ξ x) * exp (-ξ x) = 1
    simpa only [add_neg_cancel, zero_smul, exp_zero, one_smul, neg_smul] using
      (exp_add_smul (ξ x) (1 : ℝ) (-1)).symm
  inv_val := ContMDiffMap.ext fun x ↦ by
    change exp (-ξ x) * exp (ξ x) = 1
    simpa only [neg_add_cancel, zero_smul, exp_zero, one_smul, neg_smul] using
      (exp_add_smul (ξ x) (-1 : ℝ) 1).symm

/-- The values of `exp ξ` are the exponentials of the values of `ξ`. -/
@[simp]
theorem coe_gaugeExp_apply (ξ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) (x : M) :
    (gaugeExp ξ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x = exp (ξ x) :=
  (rfl)

/-- The inverse of `exp ξ` is `exp (-ξ)`. -/
@[simp]
theorem coe_gaugeExp_inv_apply (ξ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) (x : M) :
    (((gaugeExp ξ)⁻¹ : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x = exp (-ξ x) :=
  (rfl)

end GaugeExp

variable [IsManifold I 2 M]

/-! ### Conjugation -/

/-- **Conjugation** of `𝔸`-valued `k`-forms by a gauge transformation `g`, the pointwise adjoint
action `Ad_g φ = g φ g⁻¹`. -/
def gaugeConj (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) : SmoothForm I M 𝔸 k →ₗ[ℝ] SmoothForm I M 𝔸 k :=
  (SmoothForm.wedgeWith (ContinuousLinearMap.mul ℝ 𝔸)).flip
      (SmoothForm.ofFunction ↑g⁻¹) ∘ₗ
    (SmoothForm.wedgeWith (ContinuousLinearMap.mul ℝ 𝔸).flip).flip (SmoothForm.ofFunction ↑g)

private theorem gaugeConj_eq (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) (φ : SmoothForm I M 𝔸 k) :
    gaugeConj g φ = SmoothForm.wedgeWith (ContinuousLinearMap.mul ℝ 𝔸)
      (SmoothForm.wedgeWith (ContinuousLinearMap.mul ℝ 𝔸).flip φ (SmoothForm.ofFunction ↑g))
      (SmoothForm.ofFunction ↑g⁻¹) :=
  (rfl)

/-- Conjugation evaluated on tangent vectors: `(Ad_g φ)(v) = g φ(v) g⁻¹`. -/
theorem gaugeConj_val (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) (φ : SmoothForm I M 𝔸 k) (x : M)
    (v : Fin k → TangentSpace I x) :
    (gaugeConj g φ).val x v =
      (g : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x * φ.val x v *
        ((g⁻¹ : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x := by
  simp only [gaugeConj, LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
    SmoothForm.wedgeWith_apply_zero_right, SmoothForm.coe_ofFunction, RoughForm.ofFunction_apply,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply]

/-- Conjugation by the identity is the identity. -/
@[simp]
theorem gaugeConj_one : gaugeConj (1 : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) =
    (LinearMap.id : SmoothForm I M 𝔸 k →ₗ[ℝ] SmoothForm I M 𝔸 k) :=
  LinearMap.ext fun φ ↦ Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ by
    simp [gaugeConj_val]

/-- Conjugation is a left action of the gauge group: `Ad_(g h) = Ad_g ∘ Ad_h`. -/
theorem gaugeConj_mul (g h : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) :
    gaugeConj (g * h) = (gaugeConj g).comp (gaugeConj h : SmoothForm I M 𝔸 k →ₗ[ℝ] _) :=
  LinearMap.ext fun φ ↦ Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ by
    simp only [gaugeConj_val, LinearMap.comp_apply, mul_inv_rev, Units.val_mul,
      ContMDiffMap.coe_mul, Pi.mul_apply, mul_assoc]

/-- Conjugation by `g` undoes conjugation by `g⁻¹`. -/
@[simp]
theorem gaugeConj_gaugeConj_inv (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) (φ : SmoothForm I M 𝔸 k) :
    gaugeConj g (gaugeConj g⁻¹ φ) = φ := by
  rw [← LinearMap.comp_apply, ← gaugeConj_mul, mul_inv_cancel, gaugeConj_one, LinearMap.id_apply]

/-- Conjugation by `g⁻¹` undoes conjugation by `g`. -/
@[simp]
theorem gaugeConj_inv_gaugeConj (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) (φ : SmoothForm I M 𝔸 k) :
    gaugeConj g⁻¹ (gaugeConj g φ) = φ := by
  rw [← LinearMap.comp_apply, ← gaugeConj_mul, inv_mul_cancel, gaugeConj_one, LinearMap.id_apply]

/-- A conjugate of a form vanishes exactly when the form does. -/
@[simp]
theorem gaugeConj_eq_zero_iff {g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ} {φ : SmoothForm I M 𝔸 k} :
    gaugeConj g φ = 0 ↔ φ = 0 :=
  ⟨fun h ↦ by rw [← gaugeConj_inv_gaugeConj g φ, h, map_zero], fun h ↦ by rw [h, map_zero]⟩

/-- Conjugation commutes with the commutator bracket of `1`-forms:
`[Ad_g φ ∧ Ad_g ψ] = Ad_g [φ ∧ ψ]`. -/
theorem wedgeWith_gaugeConj_gaugeConj (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ)
    (φ ψ : SmoothForm I M 𝔸 1) :
    SmoothForm.wedgeWith (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip)
        (gaugeConj g φ) (gaugeConj g ψ) =
      gaugeConj g (SmoothForm.wedgeWith
        (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip) φ ψ) :=
  SmoothBundleForm.ext_eval₂ fun x v w ↦ by
    simp only [SmoothBundleForm.eval₂_apply, SmoothForm.wedgeWith_apply_one_one, gaugeConj_val,
      sub_apply, ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply]
    simp only [← ContMDiffMap.coe_evalUnitsHom_apply, map_inv, mul_sub, sub_mul, mul_assoc,
      Units.inv_mul_cancel_left]

/-! ### The Maurer–Cartan form -/

/-- The **right Maurer–Cartan form** `θ_g = (dg) g⁻¹` of a gauge transformation `g`. -/
def mrightMaurerCartan (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) : SmoothForm I M 𝔸 1 :=
  SmoothForm.wedgeWith (ContinuousLinearMap.mul ℝ 𝔸)
    (mextDerivₗ I 0 (SmoothForm.ofFunction ↑g)) (SmoothForm.ofFunction ↑g⁻¹)

/-- The right Maurer–Cartan form evaluated on a tangent vector: `θ_g(v) = dg(v) g⁻¹`. -/
theorem mrightMaurerCartan_val (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) (x : M)
    (v : Fin 1 → TangentSpace I x) :
    (mrightMaurerCartan g).val x v =
      mvfderiv I (g : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x (v 0) *
        ((g⁻¹ : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x := by
  simp only [mrightMaurerCartan, SmoothForm.wedgeWith_apply_zero_right, mextDerivₗ_apply,
    SmoothForm.coe_ofFunction, mextDeriv_ofFunction,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, RoughForm.ofFunction_apply,
    ContinuousLinearMap.mul_apply']

/-- The Maurer–Cartan form of the identity gauge transformation vanishes. -/
@[simp]
theorem mrightMaurerCartan_one :
    mrightMaurerCartan (1 : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) = 0 :=
  Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ by
    rw [mrightMaurerCartan_val, Units.val_one, ContMDiffMap.coe_one]
    simp [Pi.one_def, mvfderiv_const]

/-- The cocycle law of the right Maurer–Cartan form: `θ_(g h) = θ_g + g θ_h g⁻¹`. -/
theorem mrightMaurerCartan_mul (g h : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) :
    mrightMaurerCartan (g * h) = mrightMaurerCartan g + gaugeConj g (mrightMaurerCartan h) :=
  Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ by
    have hd := congrArg (fun L ↦ L (v 0)) (mvfderiv_smul_algebra (F := 𝔸)
      ((g : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯).contMDiff.mdifferentiableAt (by simp) (x := x))
      ((h : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯).contMDiff.mdifferentiableAt (by simp)))
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul] at hd
    simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
      mrightMaurerCartan_val, gaugeConj_val, Units.val_mul, mul_inv_rev, ContMDiffMap.coe_mul]
    rw [hd]
    simp only [Pi.mul_apply, ← ContMDiffMap.coe_evalUnitsHom_apply, map_inv, add_mul, mul_assoc,
      Units.mul_inv_cancel_left]
    abel

/-! ### Exterior derivatives -/

/-- The **Maurer–Cartan equation** for the right Maurer–Cartan form: `dθ_g = ½ [θ_g ∧ θ_g]`, that
is `dθ_g (v, w) = [θ_g v, θ_g w]`. -/
theorem mextDerivₗ_mrightMaurerCartan (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) :
    mextDerivₗ I 1 (mrightMaurerCartan g) = (2 : ℝ)⁻¹ • SmoothForm.wedgeWith
      (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip)
      (mrightMaurerCartan g) (mrightMaurerCartan g) :=
  SmoothBundleForm.ext_eval₂ fun x v w ↦ by
    rw [SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply]
    conv_lhs => rw [mrightMaurerCartan, SmoothForm.coe_wedgeWith,
      SmoothForm.mextDeriv_wedgeWith_apply_one_zero, mextDerivₗ_apply,
      SmoothForm.mextDeriv_mextDeriv]
    simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
      SmoothForm.wedgeWith_apply_one_one, sub_apply, ContinuousLinearMap.mul_apply',
      ContinuousLinearMap.flip_apply, mrightMaurerCartan_val, SmoothForm.coe_ofFunction,
      mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply, mvfderiv_inv_apply,
      ContinuousAlternatingMap.coe_zero, RoughForm.ofFunction_apply, Pi.zero_apply, zero_mul,
      zero_sub, Matrix.cons_val_fin_one, mul_neg, sub_neg_eq_add, mul_assoc]
    module

/-- The exterior derivative of a conjugated `1`-form: `d(Ad_g φ) = Ad_g dφ + [θ_g ∧ Ad_g φ]`. -/
theorem mextDerivₗ_gaugeConj (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) (φ : SmoothForm I M 𝔸 1) :
    mextDerivₗ I 1 (gaugeConj g φ) = gaugeConj g (mextDerivₗ I 1 φ) + SmoothForm.wedgeWith
      (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip)
      (mrightMaurerCartan g) (gaugeConj g φ) :=
  SmoothBundleForm.ext_eval₂ fun x v w ↦ by
    rw [SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply]
    conv_lhs => rw [gaugeConj_eq, SmoothForm.coe_wedgeWith,
      SmoothForm.mextDeriv_wedgeWith_apply_one_zero, SmoothForm.coe_wedgeWith,
      SmoothForm.mextDeriv_wedgeWith_apply_one_zero]
    simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
      SmoothForm.wedgeWith_apply_one_one, RoughForm.wedgeWith_apply_zero_right, gaugeConj_val,
      sub_apply, ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply,
      mrightMaurerCartan_val, SmoothForm.coe_ofFunction,
      mextDeriv_ofFunction, mextDerivₗ_apply, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
      mvfderiv_inv_apply, RoughForm.ofFunction_apply, Matrix.cons_val_fin_one]
    simp only [← ContMDiffMap.coe_evalUnitsHom_apply, map_inv, sub_mul, mul_neg, mul_assoc,
      Units.inv_mul_cancel_left]
    abel

/-! ### The gauge action -/

/-- The **gauge action** of a gauge transformation `g` on the connections `d + A` of the trivial
bundle, with the left convention `g · A = g A g⁻¹ - (dg) g⁻¹ = Ad_g A - θ_g`. -/
def mgaugeAction (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) (A : SmoothForm I M 𝔸 1) :
    SmoothForm I M 𝔸 1 :=
  gaugeConj g A - mrightMaurerCartan g

/-- The gauge action as conjugation followed by translation by the Maurer–Cartan form. -/
theorem mgaugeAction_def (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) (A : SmoothForm I M 𝔸 1) :
    mgaugeAction g A = gaugeConj g A - mrightMaurerCartan g :=
  (rfl)

/-- The gauge action evaluated on a tangent vector: `(g · A)(v) = g A(v) g⁻¹ - dg(v) g⁻¹`. -/
theorem mgaugeAction_val (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) (A : SmoothForm I M 𝔸 1) (x : M)
    (v : Fin 1 → TangentSpace I x) :
    (mgaugeAction g A).val x v =
      (g : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x * A.val x v *
          ((g⁻¹ : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x -
        mvfderiv I (g : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x (v 0) *
          ((g⁻¹ : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x := by
  simp only [mgaugeAction_def, Submodule.coe_sub, Pi.sub_apply,
    ContinuousAlternatingMap.sub_apply, gaugeConj_val, mrightMaurerCartan_val]

/-- The identity gauge transformation acts trivially. -/
@[simp]
theorem mgaugeAction_one (A : SmoothForm I M 𝔸 1) :
    mgaugeAction (1 : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) A = A := by
  rw [mgaugeAction_def, gaugeConj_one, mrightMaurerCartan_one, LinearMap.id_apply, sub_zero]

/-- The gauge action is a left action: `(g h) · A = g · (h · A)`. -/
theorem mgaugeAction_mul (g h : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) (A : SmoothForm I M 𝔸 1) :
    mgaugeAction (g * h) A = mgaugeAction g (mgaugeAction h A) := by
  rw [mgaugeAction_def, mgaugeAction_def, mgaugeAction_def, gaugeConj_mul,
    mrightMaurerCartan_mul, LinearMap.comp_apply, map_sub]
  abel

/-- The gauge action as a `MulAction` of the gauge group on the connections, `g • A = g · A`, so
that gauge orbits, stabilizers and orbit spaces are `MulAction.orbit`, `MulAction.stabilizer` and
`MulAction.orbitRel.Quotient`. It is not an instance: use it through
`letI := TauCeti.gaugeMulAction`. -/
abbrev gaugeMulAction : MulAction (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ (SmoothForm I M 𝔸 1) where
  smul := mgaugeAction
  one_smul := mgaugeAction_one
  mul_smul := mgaugeAction_mul

/-- The scalar action of `TauCeti.gaugeMulAction` is the gauge action. -/
theorem gaugeMulAction_smul_def (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) (A : SmoothForm I M 𝔸 1) :
    letI := gaugeMulAction (I := I) (M := M) (𝔸 := 𝔸)
    g • A = mgaugeAction g A :=
  (rfl)

/-- The gauge action is affine, with linear part the conjugation:
`g · (A + b) = g · A + g b g⁻¹`. -/
theorem mgaugeAction_add (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) (A b : SmoothForm I M 𝔸 1) :
    mgaugeAction g (A + b) = mgaugeAction g A + gaugeConj g b := by
  rw [mgaugeAction_def, mgaugeAction_def, map_add]
  abel

/-- The gauge transforms of the trivial connection are the pure gauge connections
`g · 0 = -θ_g`. -/
@[simp]
theorem mgaugeAction_zero (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) :
    mgaugeAction g 0 = -mrightMaurerCartan g := by
  rw [mgaugeAction_def, map_zero, zero_sub]

/-- **The curvature transforms by conjugation** under the gauge action:
`F_(g · A) = g F_A g⁻¹`. -/
theorem gaugeCurvature_mgaugeAction (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ) (A : SmoothForm I M 𝔸 1) :
    gaugeCurvature (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip)
        (mgaugeAction g A) =
      gaugeConj g
        (gaugeCurvature (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip) A) := by
  have hβ : ∀ a b : 𝔸, (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip) a b =
      -(ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip) b a := fun a b ↦ by
    simp only [sub_apply, ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply, neg_sub]
  rw [gaugeCurvature_def, gaugeCurvature_def, mgaugeAction_def, map_sub, mextDerivₗ_gaugeConj,
    mextDerivₗ_mrightMaurerCartan]
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, wedgeWith_gaugeConj_gaugeConj,
    SmoothForm.wedgeWith_comm_one_one_of_antisymm _ hβ (mrightMaurerCartan g) (gaugeConj g A)]
  module

/-- The gauge action preserves the flat connections. -/
theorem gaugeCurvature_mgaugeAction_eq_zero_iff (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ)
    (A : SmoothForm I M 𝔸 1) :
    gaugeCurvature (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip)
        (mgaugeAction g A) = 0 ↔
      gaugeCurvature (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip) A = 0 := by
  rw [gaugeCurvature_mgaugeAction, gaugeConj_eq_zero_iff]

/-! ### The covariant derivative -/

/-- **The covariant derivative transforms by conjugation** under the gauge action:
`d_(g · A) (g ξ g⁻¹) = g (d_A ξ) g⁻¹`. This is the counterpart for forms on a manifold of the
pointwise `TauCeti.connectionCovariantDerivative_gaugeAction`. -/
theorem gaugeCovariantDeriv_mgaugeAction (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ)
    (A : SmoothForm I M 𝔸 1) (ξ : SmoothForm I M 𝔸 0) :
    gaugeCovariantDeriv (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip)
        (mgaugeAction g A) (gaugeConj g ξ) =
      gaugeConj g (gaugeCovariantDeriv
        (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip) A ξ) :=
  SmoothBundleForm.ext_eval₁ fun x v ↦ by
    have hG : MDifferentiableAt I 𝓘(ℝ, 𝔸) (g : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x :=
      (g : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯).contMDiff.mdifferentiableAt (by simp)
    have hGi : MDifferentiableAt I 𝓘(ℝ, 𝔸) (↑g⁻¹ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x :=
      (↑g⁻¹ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯).contMDiff.mdifferentiableAt (by simp)
    have hξ := (SmoothForm.contMDiff_apply_zero ξ).mdifferentiableAt (x := x) (by simp)
    have hξGi : MDifferentiableAt I 𝓘(ℝ, 𝔸)
        ((fun y ↦ ξ.val y 0) • ⇑(↑g⁻¹ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)) x :=
      hξ.mul hGi
    -- The function underlying `g ξ g⁻¹` is a product of three `𝔸`-valued functions.
    have hfun : (fun y ↦ (gaugeConj g ξ).val y 0) = ⇑(g : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) •
        ((fun y ↦ ξ.val y 0) • ⇑(↑g⁻¹ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)) := by
      funext y
      simp only [gaugeConj_val, Pi.smul_apply', smul_eq_mul, Pi.mul_apply, mul_assoc]
    rw [gaugeCovariantDeriv_val, gaugeConj_val g (gaugeCovariantDeriv _ A ξ),
      gaugeCovariantDeriv_val, gaugeConj_val g ξ x 0, mgaugeAction_val, ← mextDerivₗ_apply,
      mextDerivₗ_zero_apply, ← mextDerivₗ_apply, mextDerivₗ_zero_apply, hfun,
      mvfderiv_smul_algebra (F := 𝔸) hG hξGi, mvfderiv_smul_algebra (F := 𝔸) hξ hGi]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
      Pi.smul_apply', mvfderiv_inv_apply, sub_apply, ContinuousLinearMap.mul_apply',
      ContinuousLinearMap.flip_apply, Matrix.cons_val_zero]
    simp only [← ContMDiffMap.coe_evalUnitsHom_apply, map_inv, mul_add, add_mul, mul_sub, sub_mul,
      mul_neg, mul_assoc, Units.inv_mul_cancel_left]
    abel

/-! ### The infinitesimal gauge action -/

section Exp

variable [CompleteSpace 𝔸]

/-- **The infinitesimal gauge action.** Along the gauge transformations `exp (t ξ)`, the
connection `A` moves with velocity `-d_A ξ = [ξ, A] - dξ` at `t = 0`:
`d/dt|_(t=0) (exp (t ξ) · A)(v) = -(d_A ξ)(v)`. -/
theorem hasDerivAt_mgaugeAction_gaugeExp_smul_apply (A : SmoothForm I M 𝔸 1)
    (ξ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) (x : M) (v : Fin 1 → TangentSpace I x) :
    HasDerivAt (fun t : ℝ ↦ (mgaugeAction (gaugeExp (t • ξ)) A).val x v)
      (-(gaugeCovariantDeriv (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip) A
        (SmoothForm.ofFunction ξ)).val x v) 0 := by
  have hξ : MDifferentiableAt I 𝓘(ℝ, 𝔸) ξ x := ξ.contMDiff.mdifferentiableAt (by simp)
  have hexp : ContDiff ℝ 2 (exp : 𝔸 → 𝔸) := contDiff_exp ℝ
  -- The derivative of `exp (t ξ)` in the manifold direction is `t (D exp)_(t ξ x) (dξ v)`.
  have hm : ∀ t : ℝ, mvfderiv I (gaugeExp (t • ξ) : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x (v 0) =
      t • fderiv ℝ exp (t • ξ x) (mvfderiv I ξ x (v 0)) := fun t ↦ by
    have he : ⇑(gaugeExp (t • ξ) : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) = exp ∘ fun y ↦ t • ξ y :=
      funext fun y ↦ by
        rw [coe_gaugeExp_apply, ContMDiffMap.coe_smul, Pi.smul_apply, Function.comp_apply]
    rw [he, mvfderiv_comp_apply_of_differentiableAt (g := fun y ↦ t • ξ y)
        (hexp.differentiable (by simp) _) (hξ.const_smul t), mvfderiv_const_smul hξ t,
      smul_apply, map_smul]
  -- Its velocity at `t = 0` is `dξ v`.
  have hL : HasDerivAt (fun t : ℝ ↦ t • fderiv ℝ exp (t • ξ x) (mvfderiv I ξ x (v 0)))
      (mvfderiv I ξ x (v 0)) 0 := by
    have hd : DifferentiableAt ℝ
        (fun t : ℝ ↦ fderiv ℝ exp (t • ξ x) (mvfderiv I ξ x (v 0))) 0 :=
      ((((hexp.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)).clm_apply
        (differentiable_const _)).comp (differentiable_id.smul_const (ξ x))).differentiableAt
    convert (hasDerivAt_id' (0 : ℝ)).smul hd.hasDerivAt using 1
    simp only [zero_smul, (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)).fderiv, one_smul,
      one_apply_eq_self, zero_add]
  have he : HasDerivAt (fun t : ℝ ↦ exp (t • ξ x)) (ξ x) 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) (ξ x) 0
  have he' : HasDerivAt (fun t : ℝ ↦ exp (-(t • ξ x))) (-ξ x) 0 := by
    simpa [smul_neg] using hasDerivAt_exp_smul_const (𝕂 := ℝ) (-ξ x) 0
  convert ((he.mul_const (A.val x v)).mul he').sub (hL.mul he') using 1
  · funext t
    rw [Pi.sub_apply, Pi.mul_apply, Pi.mul_apply, mgaugeAction_val, hm, coe_gaugeExp_apply,
      coe_gaugeExp_inv_apply, ContMDiffMap.coe_smul, Pi.smul_apply]
  · rw [gaugeCovariantDeriv_val, SmoothForm.coe_ofFunction, mextDeriv_ofFunction,
      ContinuousAlternatingMap.ofSubsingleton_apply_apply, RoughForm.ofFunction_apply]
    simp only [zero_smul, neg_zero, exp_zero, mul_one, one_mul, sub_apply,
      ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply, neg_add_rev]
    noncomm_ring

end Exp

end TauCeti
