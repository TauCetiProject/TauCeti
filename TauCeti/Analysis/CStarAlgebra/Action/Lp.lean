/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Basic
public import TauCeti.Analysis.CStarAlgebra.Hom
public import TauCeti.MeasureTheory.Function.Lp.LeftTranslation
public import TauCeti.MeasureTheory.Function.Lp.LinearIsometry

/-!
# Pointwise C⋆-actions and twisted left translation on Bochner `Lᵖ` spaces

Let `α : CStarAction G A` be a point-norm continuous action of a topological group `G` on a
possibly nonunital complex C⋆-algebra `A`. For any `1 ≤ p ≤ ∞` and measure `μ` on `G`, this file
constructs the pointwise and twisted group representations on `Lp A p μ` without requiring local
compactness, compactly supported approximations, or convolution completions:

* `TauCeti.CStarAction.actionLp`: pointwise isometric action `(r • u) s = α r (u s)` on
  `Lp A p μ` for `1 ≤ p ≤ ∞`, jointly continuous on `G × Lp A p μ` for `p < ∞`, and commuting
  with ordinary left translation `MeasureTheory.Lp.leftTranslation` when `μ` is left invariant.
* `TauCeti.CStarAction.translateLp`: twisted left translation `(r • f)(s) = α r (f (r⁻¹ * s))` on
  `Lp A p μ` for a left-invariant measure `μ`, defined as the product of `actionLp` and
  `MeasureTheory.Lp.leftTranslation`, and jointly continuous on `G × Lp A p μ` for `p < ∞`
  whenever `μ` is locally finite and inner regular on sets of finite measure.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti.CStarAction

section ActionLp

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [MeasurableSpace G] (α : CStarAction G A) (μ : Measure G) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Pointwise application `(r • u) s = α r (u s)` of a C⋆-action on `Lp A p μ`, as a group
homomorphism into linear isometric equivalences. -/
def actionLp : G →* (Lp A p μ ≃ₗᵢ[ℂ] Lp A p μ) where
  toFun r := (α r).toLinearIsometryEquiv.compLpₗᵢ p μ
  map_one' := by
    have h1 : (α 1).toLinearIsometryEquiv = LinearIsometryEquiv.refl ℂ A := by
      ext a; simp
    rw [h1, LinearIsometryEquiv.compLpₗᵢ_refl, LinearIsometryEquiv.one_def]
  map_mul' r t := by
    have hm : (α (r * t)).toLinearIsometryEquiv =
        (α t).toLinearIsometryEquiv.trans (α r).toLinearIsometryEquiv := by
      ext a; simp [mul_apply]
    rw [hm, LinearIsometryEquiv.compLpₗᵢ_trans, LinearIsometryEquiv.mul_def]

variable {μ p}

/-- `actionLp` acts by composing `Lp` classes with `(α r).toLinearIsometryEquiv`. -/
theorem actionLp_apply (r : G) (u : Lp A p μ) :
    α.actionLp μ p r u = (α r).toLinearIsometryEquiv.compLpₗᵢ p μ u :=
  (rfl)

/-- Pointwise almost-everywhere formula for `actionLp`. -/
theorem coeFn_actionLp (r : G) (u : Lp A p μ) :
    α.actionLp μ p r u =ᵐ[μ] fun s => α r (u s) := by
  filter_upwards [(α r).toLinearIsometryEquiv.coeFn_compLpₗᵢ (p := p) (μ := μ) u] with s hs
  simpa [actionLp_apply] using hs

/-- The inverse of `actionLp` at `r` is `actionLp` at `r⁻¹`. -/
@[simp]
theorem actionLp_symm (r : G) : (α.actionLp μ p r).symm = α.actionLp μ p r⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

/-- The trivial C⋆-action acts trivially on `Lp`. -/
@[simp]
theorem actionLp_trivial (r : G) : (trivial (G := G) (A := A)).actionLp μ p r = 1 := by
  have h1 : (trivial (G := G) (A := A) r).toLinearIsometryEquiv =
      LinearIsometryEquiv.refl ℂ A := by
    ext a; simp
  change (trivial (G := G) (A := A) r).toLinearIsometryEquiv.compLpₗᵢ p μ = 1
  rw [h1, LinearIsometryEquiv.compLpₗᵢ_refl, LinearIsometryEquiv.one_def]

/-- `actionLp` maps an indicator constant class by applying `α r` to its constant value. -/
theorem actionLp_indicatorConstLp (r : G) {s : Set G} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (c : A) :
    α.actionLp μ p r (indicatorConstLp p hs hμs c) = indicatorConstLp p hs hμs (α r c) := by
  rw [actionLp_apply, LinearIsometryEquiv.compLpₗᵢ_indicatorConstLp]
  simp

/-- For `p < ∞`, `actionLp` is jointly continuous on `G × Lp A p μ`. -/
@[fun_prop]
theorem continuous_actionLp (hp : p ≠ ∞) :
    Continuous fun q : G × Lp A p μ => α.actionLp μ p q.1 q.2 :=
  LinearIsometryEquiv.continuous_compLpₗᵢ hp (e := fun r => (α r).toLinearIsometryEquiv)
    fun c => by
      simp_rw [StarAlgEquiv.coe_toLinearIsometryEquiv]
      exact α.continuous_orbit c

/-- For `p < ∞`, every orbit `r ↦ α.actionLp μ p r u` is norm continuous in `Lp A p μ`. -/
@[fun_prop]
theorem continuous_actionLp_apply (hp : p ≠ ∞) (u : Lp A p μ) :
    Continuous fun r => α.actionLp μ p r u :=
  (α.continuous_actionLp hp).comp (continuous_id.prodMk continuous_const)

/-- Pointwise coefficient action and group left translation commute on `Lp A p μ`. -/
theorem actionLp_leftTranslation [MeasurableMul G] [μ.IsMulLeftInvariant] (r t : G)
    (u : Lp A p μ) :
    α.actionLp μ p r (Lp.leftTranslation μ p ℂ t u) =
      Lp.leftTranslation μ p ℂ t (α.actionLp μ p r u) := by
  refine Lp.ext ?_
  filter_upwards [α.coeFn_actionLp r (Lp.leftTranslation μ p ℂ t u),
    Lp.coeFn_leftTranslation (𝕜 := ℂ) t u,
    Lp.coeFn_leftTranslation (𝕜 := ℂ) t (α.actionLp μ p r u),
    (measurePreserving_mul_left μ t⁻¹).quasiMeasurePreserving.ae (α.coeFn_actionLp r u)]
    with s h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

end ActionLp

section TranslateLp

variable {G A : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] (α : CStarAction G A) (μ : Measure G) (p : ℝ≥0∞) [Fact (1 ≤ p)]
  [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- Twisted left translation `(r • f)(s) = α r (f (r⁻¹ * s))` on `Lp A p μ` for a left-invariant
measure `μ`, bundled as a group homomorphism into linear isometric equivalences. -/
def translateLp : G →* (Lp A p μ ≃ₗᵢ[ℂ] Lp A p μ) where
  toFun r := α.actionLp μ p r * Lp.leftTranslation μ p ℂ r
  map_one' := by simp
  map_mul' r t := by
    ext u : 1
    simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply]
    rw [α.actionLp_leftTranslation]

variable {μ p}

/-- `translateLp` factors as `actionLp` composed with `Lp.leftTranslation`. -/
theorem translateLp_eq_actionLp_mul_leftTranslation (r : G) :
    α.translateLp μ p r = α.actionLp μ p r * Lp.leftTranslation μ p ℂ r := by
  simp [translateLp]

/-- Twisted left translation on `Lp A p μ` is almost everywhere `s ↦ α r (f (r⁻¹ * s))`. -/
theorem coeFn_translateLp (r : G) (f : Lp A p μ) :
    α.translateLp μ p r f =ᵐ[μ] fun s => α r (f (r⁻¹ * s)) := by
  rw [translateLp_eq_actionLp_mul_leftTranslation, LinearIsometryEquiv.coe_mul,
    Function.comp_apply]
  filter_upwards [α.coeFn_actionLp r (Lp.leftTranslation μ p ℂ r f),
    Lp.coeFn_leftTranslation (𝕜 := ℂ) r f] with s hs₁ hs₂
  exact hs₁.trans (congrArg (α r) hs₂)

theorem translateLp_symm (r : G) :
    (α.translateLp μ p r).symm = α.translateLp μ p r⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

/-- For the trivial action, twisted left translation on `Lp A p μ` is ordinary left translation. -/
@[simp]
theorem translateLp_trivial (r : G) :
    (trivial (G := G) (A := A)).translateLp μ p r = Lp.leftTranslation μ p ℂ r := by
  rw [translateLp_eq_actionLp_mul_leftTranslation, actionLp_trivial, one_mul]

/-- Twisted left translation commutes with left multiplication by coefficients up to the action
twist. -/
theorem translateLp_compLp_mul (r : G) (a : A) (f : Lp A p μ) :
    α.translateLp μ p r ((ContinuousLinearMap.mul ℂ A a).compLp f) =
      (ContinuousLinearMap.mul ℂ A (α r a)).compLp (α.translateLp μ p r f) := by
  refine Lp.ext ?_
  filter_upwards [α.coeFn_translateLp r ((ContinuousLinearMap.mul ℂ A a).compLp f),
    (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae
      ((ContinuousLinearMap.mul ℂ A a).coeFn_compLp f),
    (ContinuousLinearMap.mul ℂ A (α r a)).coeFn_compLp (α.translateLp μ p r f),
    α.coeFn_translateLp r f] with s h₁ h₂ h₃ h₄
  simp only [ContinuousLinearMap.mul_apply'] at h₂
  rw [h₁, h₂, map_mul, h₃, ContinuousLinearMap.mul_apply', h₄]

end TranslateLp

section ContinuousTranslateLp

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  (α : CStarAction G A) {μ : Measure G} [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Twisted left translation on `Lp A p μ` is jointly continuous on `G × Lp A p μ` for `p < ∞`. -/
@[fun_prop]
theorem continuous_translateLp (hp : p ≠ ∞) :
    Continuous fun q : G × Lp A p μ => α.translateLp μ p q.1 q.2 := by
  have : Fact (p ≠ ∞) := ⟨hp⟩
  simp_rw [translateLp_eq_actionLp_mul_leftTranslation, LinearIsometryEquiv.coe_mul,
    Function.comp_apply, Lp.leftTranslation_apply]
  exact (α.continuous_actionLp hp).comp
    (continuous_fst.prodMk ((DomMulAct.continuous_mk.comp continuous_fst.inv).smul continuous_snd))

/-- Every orbit of twisted left translation in `Lp A p μ` is norm-continuous for `p < ∞`. -/
@[fun_prop]
theorem continuous_translateLp_apply (hp : p ≠ ∞) (f : Lp A p μ) :
    Continuous fun r : G => α.translateLp μ p r f :=
  (α.continuous_translateLp hp).comp (continuous_id.prodMk continuous_const)

end ContinuousTranslateLp

end TauCeti.CStarAction
