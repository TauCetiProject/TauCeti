/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Postcomposition on `Lᵖ` by linear isometries and linear isometry equivalences

Mathlib defines `ContinuousLinearMap.compLpL` for postcomposing `Lp E p μ` classes with a
continuous linear map `E →SL[σ] F`, giving a continuous linear map `Lp E p μ →SL[σ] Lp F p μ`.
When the map is a linear isometry `f : E →ₛₗᵢ[σ] F` or a linear isometry equivalence
`e : E ≃ₛₗᵢ[σ] F`, pointwise postcomposition preserves `eLpNorm` identically (over any normed
rings, without requiring a nontrivially normed field) and therefore lifts to a linear isometry
`LinearIsometry.compLpₗᵢ` or linear isometry equivalence `LinearIsometryEquiv.compLpₗᵢ` between
`Lp E p μ` and `Lp F p μ`.

Moreover, for `1 ≤ p < ∞`, any strongly (pointwise) continuous family of linear isometries
`f : X → (E →ₛₗᵢ[σ] F)` induces a jointly continuous map
`(x, u) ↦ (f x).compLpₗᵢ p μ u` on `X × Lp E p μ`, proved by density of `Lᵖ` simple functions
and uniform 1-Lipschitzness in the `Lᵖ` variable.

## Main definitions

* `LinearIsometry.compLpₗᵢ`: postcomposition on `Lp E p μ` with a semilinear isometry
  `f : E →ₛₗᵢ[σ] F`, bundled as `Lp E p μ →ₛₗᵢ[σ] Lp F p μ`.
* `LinearIsometryEquiv.compLpₗᵢ`: postcomposition on `Lp E p μ` with a semilinear isometric
  equivalence `e : E ≃ₛₗᵢ[σ] F`, bundled as `Lp E p μ ≃ₛₗᵢ[σ] Lp F p μ`.

## Main results

* `LinearIsometry.coeFn_compLpₗᵢ` and `LinearIsometryEquiv.coeFn_compLpₗᵢ`: almost-everywhere
  pointwise formulas for postcomposition on `Lᵖ`.
* `LinearIsometry.compLpₗᵢ_id`, `LinearIsometry.compLpₗᵢ_comp`,
  `LinearIsometryEquiv.compLpₗᵢ_symm`, `LinearIsometryEquiv.compLpₗᵢ_refl`, and
  `LinearIsometryEquiv.compLpₗᵢ_trans`: functoriality and inverse compatibility.
* `LinearIsometry.compLpₗᵢ_indicatorConstLp` and
  `LinearIsometryEquiv.compLpₗᵢ_indicatorConstLp`: action on indicator `Lᵖ` classes.
* `LinearIsometry.continuous_compLpₗᵢ` and `LinearIsometryEquiv.continuous_compLpₗᵢ`: joint
  continuity on `X × Lp E p μ` for `1 ≤ p < ∞` from pointwise continuity in `X`.
* `ContinuousLinearMap.norm_apply_one_compLp`: evaluating an `Lᵖ` family of linear maps
  `𝕜 →L[𝕜] E` at `1` preserves its `Lᵖ` norm.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LinearIsometry

variable {α 𝕜 𝕜' 𝕜'' E F G : Type*} [MeasurableSpace α]
  [NormedRing 𝕜] [NormedRing 𝕜'] [NormedRing 𝕜'']
  [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  [NormedAddCommGroup F] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
  [NormedAddCommGroup G] [Module 𝕜'' G] [IsBoundedSMul 𝕜'' G]
  {σ : 𝕜 →+* 𝕜'} {τ : 𝕜' →+* 𝕜''} {ρ : 𝕜 →+* 𝕜''}

/-- Postcomposing `Lᵖ` classes with a semilinear isometry `f : E →ₛₗᵢ[σ] F`, bundled as a
semilinear isometry `Lp E p μ →ₛₗᵢ[σ] Lp F p μ`. -/
def compLpₗᵢ (f : E →ₛₗᵢ[σ] F) (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α) :
    Lp E p μ →ₛₗᵢ[σ] Lp F p μ where
  toFun u := f.isometry.lipschitzWith.compLp (map_zero f) u
  map_add' u v := by
    refine Lp.ext ?_
    filter_upwards [f.isometry.lipschitzWith.coeFn_compLp (map_zero f) (u + v),
      Lp.coeFn_add u v,
      Lp.coeFn_add (f.isometry.lipschitzWith.compLp (map_zero f) u)
        (f.isometry.lipschitzWith.compLp (map_zero f) v),
      f.isometry.lipschitzWith.coeFn_compLp (map_zero f) u,
      f.isometry.lipschitzWith.coeFn_compLp (map_zero f) v] with x h₁ h₂ h₃ h₄ h₅
    simp only [h₁, h₂, h₃, h₄, h₅, Function.comp_apply, Pi.add_apply, map_add]
  map_smul' c u := by
    refine Lp.ext ?_
    filter_upwards [f.isometry.lipschitzWith.coeFn_compLp (map_zero f) (c • u),
      Lp.coeFn_smul c u,
      Lp.coeFn_smul (σ c) (f.isometry.lipschitzWith.compLp (map_zero f) u),
      f.isometry.lipschitzWith.coeFn_compLp (map_zero f) u] with x h₁ h₂ h₃ h₄
    simp only [h₁, h₂, h₃, h₄, Function.comp_apply, Pi.smul_apply, map_smulₛₗ]
  norm_map' u := by
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Lp.norm_def, Lp.norm_def,
      eLpNorm_congr_ae (f.isometry.lipschitzWith.coeFn_compLp (map_zero f) u),
      eLpNorm_congr_norm_ae (f := ⇑f ∘ ↑↑u)
        (f.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u))
        (Lp.aestronglyMeasurable u) (.of_forall fun x => f.norm_map (u x))]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

/-- Pointwise a.e. formula for `LinearIsometry.compLpₗᵢ`. -/
theorem coeFn_compLpₗᵢ (f : E →ₛₗᵢ[σ] F) (u : Lp E p μ) :
    f.compLpₗᵢ p μ u =ᵐ[μ] fun x => f (u x) :=
  f.isometry.lipschitzWith.coeFn_compLp (map_zero f) u

@[simp]
theorem compLpₗᵢ_id :
    (LinearIsometry.id : E →ₗᵢ[𝕜] E).compLpₗᵢ p μ = LinearIsometry.id := by
  ext1 u
  refine Lp.ext ?_
  filter_upwards [(LinearIsometry.id : E →ₗᵢ[𝕜] E).coeFn_compLpₗᵢ u] with x hx
  exact hx

theorem compLpₗᵢ_comp [RingHomCompTriple σ τ ρ] (g : F →ₛₗᵢ[τ] G) (f : E →ₛₗᵢ[σ] F) :
    (g.comp f).compLpₗᵢ p μ = (g.compLpₗᵢ p μ).comp (f.compLpₗᵢ p μ) := by
  ext1 u
  refine Lp.ext ?_
  filter_upwards [(g.comp f).coeFn_compLpₗᵢ u, g.coeFn_compLpₗᵢ (f.compLpₗᵢ p μ u),
    f.coeFn_compLpₗᵢ u] with x h₁ h₂ h₃
  simp only [h₁, h₂, h₃, coe_comp, Function.comp_apply]

/-- Postcomposition with a linear isometry commutes with `indicatorConstLp`. -/
@[simp]
theorem compLpₗᵢ_indicatorConstLp (f : E →ₛₗᵢ[σ] F) {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : E) :
    f.compLpₗᵢ p μ (indicatorConstLp p hs hμs c) = indicatorConstLp p hs hμs (f c) := by
  refine Lp.ext ?_
  filter_upwards [f.coeFn_compLpₗᵢ (indicatorConstLp p hs hμs c),
    (indicatorConstLp_coeFn : ⇑(indicatorConstLp p hs hμs c) =ᵐ[μ] _),
    (indicatorConstLp_coeFn : ⇑(indicatorConstLp p hs hμs (f c)) =ᵐ[μ] _)]
    with x hx₁ hx₂ hx₃
  rw [hx₁, hx₂, hx₃]
  exact (congrFun (Set.indicator_comp_of_zero (f := fun _ => c) (map_zero f)) x).symm

/-- A pointwise continuous family of linear isometries acts jointly continuously on `X × Lp E p μ`
for `1 ≤ p < ∞`. -/
theorem continuous_compLpₗᵢ {X : Type*} [TopologicalSpace X] (hp : p ≠ ∞)
    {f : X → E →ₛₗᵢ[σ] F} (hf : ∀ c : E, Continuous fun x => f x c) :
    Continuous fun q : X × Lp E p μ => (f q.1).compLpₗᵢ p μ q.2 := by
  refine continuous_prod_of_dense_continuous_lipschitzWith' _ 1
    (Lp.simpleFunc.denseRange hp)
    (fun x => ((f x).compLpₗᵢ p μ).isometry.lipschitzWith) ?_
  rintro _ ⟨φ, rfl⟩
  induction φ using Lp.simpleFunc.induction (one_pos.trans_le Fact.out).ne' hp with
  | indicatorConst c hs hμs =>
    simp_rw [Lp.simpleFunc.coe_indicatorConst, compLpₗᵢ_indicatorConstLp]
    have hlip : LipschitzWith (Real.toNNReal (μ.real _ ^ (1 / p.toReal)))
        (fun d : F => indicatorConstLp p hs hμs.ne d) :=
      LipschitzWith.of_dist_le_mul fun d₁ d₂ => by
        rw [dist_eq_norm, dist_eq_norm, indicatorConstLp_sub]
        exact norm_indicatorConstLp_le.trans
          (by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _))
    exact hlip.continuous.comp (hf c)
  | add _ _ _ hu hv =>
    simpa only [AddSubgroup.coe_add, map_add, Pi.add_def] using hu.add hv

end LinearIsometry

namespace LinearIsometryEquiv

variable {α 𝕜 𝕜' 𝕜'' E F G : Type*} [MeasurableSpace α]
  [NormedRing 𝕜] [NormedRing 𝕜'] [NormedRing 𝕜'']
  [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  [NormedAddCommGroup F] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
  [NormedAddCommGroup G] [Module 𝕜'' G] [IsBoundedSMul 𝕜'' G]
  {σ : 𝕜 →+* 𝕜'} {σ' : 𝕜' →+* 𝕜} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  {τ : 𝕜' →+* 𝕜''} {τ' : 𝕜'' →+* 𝕜'} [RingHomInvPair τ τ'] [RingHomInvPair τ' τ]
  {ρ : 𝕜 →+* 𝕜''} {ρ' : 𝕜'' →+* 𝕜} [RingHomInvPair ρ ρ'] [RingHomInvPair ρ' ρ]

/-- Postcomposing `Lᵖ` classes with a semilinear isometric equivalence `e : E ≃ₛₗᵢ[σ] F`, bundled
as a semilinear isometric equivalence `Lp E p μ ≃ₛₗᵢ[σ] Lp F p μ`. -/
def compLpₗᵢ (e : E ≃ₛₗᵢ[σ] F) (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α) :
    Lp E p μ ≃ₛₗᵢ[σ] Lp F p μ :=
  LinearIsometryEquiv.ofLinearIsometry
    (e.toLinearIsometry.compLpₗᵢ p μ)
    (e.symm.toLinearIsometry.compLpₗᵢ p μ).toLinearMap
    (LinearMap.ext fun v => by
      refine Lp.ext ?_
      filter_upwards [e.toLinearIsometry.coeFn_compLpₗᵢ (e.symm.toLinearIsometry.compLpₗᵢ p μ v),
        e.symm.toLinearIsometry.coeFn_compLpₗᵢ v] with x h₁ h₂
      simp only [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap, LinearMap.id_apply,
        h₁, h₂, coe_toLinearIsometry, apply_symm_apply])
    (LinearMap.ext fun u => by
      refine Lp.ext ?_
      filter_upwards [e.symm.toLinearIsometry.coeFn_compLpₗᵢ (e.toLinearIsometry.compLpₗᵢ p μ u),
        e.toLinearIsometry.coeFn_compLpₗᵢ u] with x h₁ h₂
      simp only [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap, LinearMap.id_apply,
        h₁, h₂, coe_toLinearIsometry, symm_apply_apply])

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

@[simp]
theorem toLinearIsometry_compLpₗᵢ (e : E ≃ₛₗᵢ[σ] F) :
    (e.compLpₗᵢ p μ).toLinearIsometry = e.toLinearIsometry.compLpₗᵢ p μ :=
  (rfl)

/-- Pointwise a.e. formula for `LinearIsometryEquiv.compLpₗᵢ`. -/
theorem coeFn_compLpₗᵢ (e : E ≃ₛₗᵢ[σ] F) (u : Lp E p μ) :
    e.compLpₗᵢ p μ u =ᵐ[μ] fun x => e (u x) :=
  e.toLinearIsometry.coeFn_compLpₗᵢ u

@[simp]
theorem compLpₗᵢ_symm (e : E ≃ₛₗᵢ[σ] F) :
    (e.compLpₗᵢ p μ).symm = e.symm.compLpₗᵢ p μ := by
  ext1 v
  exact (rfl)

@[simp]
theorem compLpₗᵢ_refl :
    (LinearIsometryEquiv.refl 𝕜 E).compLpₗᵢ p μ = LinearIsometryEquiv.refl 𝕜 (Lp E p μ) := by
  ext1 u
  refine Lp.ext ?_
  filter_upwards [(LinearIsometryEquiv.refl 𝕜 E).coeFn_compLpₗᵢ u] with x hx
  exact hx

theorem compLpₗᵢ_trans [RingHomCompTriple σ τ ρ] [RingHomCompTriple τ' σ' ρ']
    (e : E ≃ₛₗᵢ[σ] F) (e' : F ≃ₛₗᵢ[τ] G) :
    (e.trans e').compLpₗᵢ p μ = (e.compLpₗᵢ p μ).trans (e'.compLpₗᵢ p μ) := by
  ext1 u
  refine Lp.ext ?_
  filter_upwards [(e.trans e').coeFn_compLpₗᵢ u, e'.coeFn_compLpₗᵢ (e.compLpₗᵢ p μ u),
    e.coeFn_compLpₗᵢ u] with x h₁ h₂ h₃
  rw [h₁, trans_apply, trans_apply, h₂, h₃]

/-- Postcomposition with a linear isometric equivalence commutes with `indicatorConstLp`. -/
@[simp]
theorem compLpₗᵢ_indicatorConstLp (e : E ≃ₛₗᵢ[σ] F) {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : E) :
    e.compLpₗᵢ p μ (indicatorConstLp p hs hμs c) = indicatorConstLp p hs hμs (e c) :=
  e.toLinearIsometry.compLpₗᵢ_indicatorConstLp hs hμs c

/-- A pointwise continuous family of linear isometric equivalences acts jointly continuously on
`X × Lp E p μ` for `1 ≤ p < ∞`. -/
theorem continuous_compLpₗᵢ {X : Type*} [TopologicalSpace X] (hp : p ≠ ∞)
    {e : X → E ≃ₛₗᵢ[σ] F} (he : ∀ c : E, Continuous fun x => e x c) :
    Continuous fun q : X × Lp E p μ => (e q.1).compLpₗᵢ p μ q.2 :=
  LinearIsometry.continuous_compLpₗᵢ hp (f := fun x => (e x).toLinearIsometry) he

end LinearIsometryEquiv

namespace ContinuousLinearMap

variable {α 𝕜 E : Type*} {_ : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Pointwise evaluation at `1 : 𝕜` on `Lp (𝕜 →L[𝕜] E) p μ` preserves the `Lᵖ` norm, since it is
the isometry `(toSpanSingletonLIE 𝕜 E).symm`. -/
@[simp]
theorem norm_apply_one_compLp (f : Lp (𝕜 →L[𝕜] E) p μ) :
    ‖(ContinuousLinearMap.apply 𝕜 E (1 : 𝕜)).compLp f‖ = ‖f‖ :=
  norm_compLp_of_isometry (toSpanSingletonLIE 𝕜 E).symm.isometry f

end ContinuousLinearMap
