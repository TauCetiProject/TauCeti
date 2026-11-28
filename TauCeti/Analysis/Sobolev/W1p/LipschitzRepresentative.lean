/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed
public import TauCeti.Analysis.Sobolev.W1p.Convex
public import TauCeti.Analysis.Sobolev.W1p.Zero
import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.Analysis.Sobolev.W1p.InteriorMorrey
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Topology.MetricSpace.Holder

/-!
# Lipschitz representatives of `W^{1,∞}` functions

Let `Ω` be a convex open subset of a finite-dimensional real inner product space. A function
`u ∈ W^{1,∞}(Ω)` has a representative that is Lipschitz on `Ω` with constant `‖∇u‖_∞`
(`TauCeti.W1p.lipschitzOnWith_preciseRepresentative_of_convex`). Being uniformly continuous, it
extends to `closure Ω`, with the same Lipschitz constant and the same supremum bound `‖u‖_∞`.
This defines a bounded linear map

`W^{1,∞}(Ω) → C^{0,1}(closure Ω)` (`TauCeti.W1p.lipschitzRepresentativeL`),

characterised by agreeing almost everywhere on `Ω` with `u`
(`TauCeti.W1p.lipschitzRepresentativeL_eq_iff`). Neither boundedness nor boundary regularity of
`Ω` is needed; convexity is what makes the local Lipschitz bound global. The higher-order
consequence `W^{k,∞} ⊆ C^{k-1,1}` is in `TauCeti.Analysis.Sobolev.Wkp.LipschitzRepresentative`.

Near a boundary point the same local bound gives Lipschitz representatives of zero-trace functions
that vanish at the point. If `u ∈ W^{1,p}_0(Ω)` has essentially bounded gradient near `x`, and `x`
is a limit of points outside a closed set containing `Ω`, then the precise representative of the
extension of `u` by zero is Lipschitz near `x` and vanishes at `x`
(`TauCeti.W1p0.exists_lipschitzOnWith_ae_eq_of_ae_norm_gradient_le`).

## Main declarations

* `TauCeti.W1p.lipschitzRepresentativeL`: the Lipschitz representative on `closure Ω` as a
  continuous linear map `W^{1,∞}(Ω) → C^{0,1}(closure Ω)`, with
  `TauCeti.W1p.lipschitzRepresentativeL_apply` (it is the precise representative on `Ω`),
  `TauCeti.W1p.ae_lipschitzRepresentativeL_eq`, `TauCeti.W1p.lipschitzRepresentativeL_eq_iff`,
  `TauCeti.W1p.lipschitzWith_lipschitzRepresentativeL` (the sharp constant `‖∇u‖_∞`) and
  `TauCeti.W1p.norm_lipschitzRepresentativeL_apply_le`.
* `TauCeti.W1p0.exists_lipschitzOnWith_ae_eq_of_ae_norm_gradient_le`: a function of
  `W^{1,p}_0(Ω)` with essentially bounded gradient near a point `x` that is a limit of points
  outside a closed set `F ⊇ Ω` has a representative that is Lipschitz near `x` and vanishes at
  `x`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.2.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} (hΩ : Convex ℝ (Ω : Set E))
include hΩ

/-- **The Lipschitz representative on the closure.** On a convex domain, the precise
representative of `u ∈ W^{1,∞}(Ω)` extends to a function on `closure Ω` bounded by `‖u‖_∞` and
Lipschitz with constant `‖∇u‖_∞`. -/
private theorem W1p.exists_lipschitzRepresentative (u : W1p μ Ω ∞) :
    ∃ G : HolderSpace 1 (closure (Ω : Set E)) ℝ,
      (∀ x (hx : x ∈ Ω), G ⟨x, subset_closure hx⟩ = preciseRepresentative μ (W1p.value u) x) ∧
        LipschitzWith ‖W1p.gradient u‖₊ G ∧ ∀ x, ‖G x‖ ≤ ‖W1p.value u‖ := by
  set f := preciseRepresentative μ (W1p.value u)
  set s : Set (closure (Ω : Set E)) := {x | (x : E) ∈ Ω}
  -- The points of `Ω` are dense in `closure Ω`.
  have hd : Dense s := by
    rw [show s = range (inclusion subset_closure) from (range_inclusion _).symm]
    exact (denseRange_inclusion_iff _).2 subset_rfl
  -- On the points of `Ω`, the representative is Lipschitz with constant `‖∇u‖_∞`.
  have hL : HolderOnWith ‖W1p.gradient u‖₊ 1 (fun x : closure (Ω : Set E) ↦ f x) s := by
    rw [holderOnWith_one]
    have h := (W1p.lipschitzOnWith_preciseRepresentative_of_convex u hΩ subset_rfl).comp
      (LipschitzWith.subtypeVal (closure (Ω : Set E))).lipschitzOnWith
      (fun _ hx ↦ hx : MapsTo Subtype.val s (Ω : Set E))
    rw [mul_one] at h
    exact h
  obtain ⟨g, hg, hgf⟩ := hL.extend_of_dense hd
  have hgc : Continuous g := (holderWith_one.1 hg).continuous
  -- The bound by `‖u‖_∞` holds on the dense set `s`, hence everywhere.
  have hbd : ∀ x, ‖g x‖ ≤ ‖W1p.value u‖ := by
    have hcl : IsClosed {x | ‖g x‖ ≤ ‖W1p.value u‖} := isClosed_le hgc.norm continuous_const
    have hsub : s ⊆ {x | ‖g x‖ ≤ ‖W1p.value u‖} := fun x (hx : (x : E) ∈ Ω) ↦ by
      simpa [← hgf hx] using W1p.norm_preciseRepresentative_le u hx
    intro x
    exact hcl.closure_subset_iff.2 hsub (hd.closure_eq ▸ mem_univ x)
  let G : HolderSpace 1 (closure (Ω : Set E)) ℝ :=
    HolderSpace.ofBoundedContinuousFunction
      (BoundedContinuousFunction.ofNormedAddCommGroup g hgc _ hbd) ⟨_, hg⟩
  have hG : ⇑G = g := funext fun x ↦ HolderSpace.ofBoundedContinuousFunction_apply _ _ x
  refine ⟨G, fun x hx ↦ ?_, hG ▸ holderWith_one.1 hg, hG ▸ hbd⟩
  rw [hG]
  exact (hgf (x := ⟨x, subset_closure hx⟩) hx).symm

/-- The Lipschitz representative of `u` on `closure Ω`, chosen by
`W1p.exists_lipschitzRepresentative`. -/
private def W1p.lipschitzRepresentative (u : W1p μ Ω ∞) : HolderSpace 1 (closure (Ω : Set E)) ℝ :=
  (W1p.exists_lipschitzRepresentative hΩ u).choose

private theorem W1p.lipschitzRepresentative_spec (u : W1p μ Ω ∞) :
    (∀ x (hx : x ∈ Ω), W1p.lipschitzRepresentative hΩ u ⟨x, subset_closure hx⟩ =
        preciseRepresentative μ (W1p.value u) x) ∧
      LipschitzWith ‖W1p.gradient u‖₊ (W1p.lipschitzRepresentative hΩ u) ∧
        ∀ x, ‖W1p.lipschitzRepresentative hΩ u x‖ ≤ ‖W1p.value u‖ :=
  (W1p.exists_lipschitzRepresentative hΩ u).choose_spec

/-- The Lipschitz representative agrees almost everywhere on `Ω` with `u`. -/
private theorem W1p.ae_lipschitzRepresentative_eq (u : W1p μ Ω ∞) :
    ∀ᵐ x ∂μ, ∀ hx : x ∈ Ω, W1p.lipschitzRepresentative hΩ u ⟨x, subset_closure hx⟩ =
      W1p.value u x := by
  have h := W1p.ae_eq_preciseRepresentative u
  rw [EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet] at h
  filter_upwards [h] with x hx hxΩ
  rw [(W1p.lipschitzRepresentative_spec hΩ u).1 x hxΩ, hx hxΩ]

/-- The Lipschitz representative is the only element of `C^{0,1}(closure Ω)` that agrees almost
everywhere on `Ω` with `u`. -/
private theorem W1p.lipschitzRepresentative_eq_of_ae_eq (u : W1p μ Ω ∞)
    {G : HolderSpace 1 (closure (Ω : Set E)) ℝ}
    (h : ∀ᵐ x ∂μ, ∀ hx : x ∈ Ω, G ⟨x, subset_closure hx⟩ = W1p.value u x) :
    W1p.lipschitzRepresentative hΩ u = G :=
  HolderSpace.ext <| congrFun <| Ω.isOpen.ext_closure_of_ae_eq (μ := μ)
    (HolderSpace.continuous _) (HolderSpace.continuous _) <| by
    filter_upwards [W1p.ae_lipschitzRepresentative_eq hΩ u, h] with x h₁ h₂ hx
    rw [h₁ hx, h₂ hx]

/-- **The Lipschitz representative** of `W^{1,∞}` functions on a convex domain `Ω`, as a bounded
linear map `W^{1,∞}(Ω) → C^{0,1}(closure Ω)`. On `Ω` it is the precise representative
(`TauCeti.W1p.lipschitzRepresentativeL_apply`); it is the only element of `C^{0,1}(closure Ω)`
agreeing almost everywhere on `Ω` with `u` (`TauCeti.W1p.lipschitzRepresentativeL_eq_iff`). -/
def W1p.lipschitzRepresentativeL : W1p μ Ω ∞ →L[ℝ] HolderSpace 1 (closure (Ω : Set E)) ℝ :=
  LinearMap.mkContinuous
    { toFun := W1p.lipschitzRepresentative hΩ
      map_add' u v := W1p.lipschitzRepresentative_eq_of_ae_eq hΩ (u + v) <| by
        filter_upwards [W1p.ae_lipschitzRepresentative_eq hΩ u,
          W1p.ae_lipschitzRepresentative_eq hΩ v,
          (ae_restrict_iff' Ω.isOpen.measurableSet).1 (W1p.value_add_ae u v)]
          with x h₁ h₂ h₃ hx
        rw [HolderSpace.add_apply, h₁ hx, h₂ hx, h₃ hx, Pi.add_apply]
      map_smul' c u := W1p.lipschitzRepresentative_eq_of_ae_eq hΩ (c • u) <| by
        filter_upwards [W1p.ae_lipschitzRepresentative_eq hΩ u,
          (ae_restrict_iff' Ω.isOpen.measurableSet).1 (W1p.value_smul_ae c u)]
          with x h₁ h₂ hx
        rw [RingHom.id_apply, HolderSpace.smul_apply, h₁ hx, h₂ hx, Pi.smul_apply] }
    2 fun u ↦ by
      obtain ⟨-, hL, hbd⟩ := W1p.lipschitzRepresentative_spec hΩ u
      refine (HolderSpace.norm_le_of_norm_le_of_holderWith (norm_nonneg _) hbd
        (holderWith_one.2 hL)).trans ?_
      rw [coe_nnNorm, two_mul]
      exact add_le_add (W1p.norm_value_le u) (W1p.norm_gradient_le u)

/-- On `Ω`, the Lipschitz representative is the precise representative. -/
theorem W1p.lipschitzRepresentativeL_apply (u : W1p μ Ω ∞) {x : E} (hx : x ∈ Ω) :
    W1p.lipschitzRepresentativeL hΩ u ⟨x, subset_closure hx⟩ =
      preciseRepresentative μ (W1p.value u) x :=
  (W1p.lipschitzRepresentative_spec hΩ u).1 x hx

/-- The Lipschitz representative agrees almost everywhere on `Ω` with `u`. -/
theorem W1p.ae_lipschitzRepresentativeL_eq (u : W1p μ Ω ∞) :
    ∀ᵐ x ∂μ, ∀ hx : x ∈ Ω, W1p.lipschitzRepresentativeL hΩ u ⟨x, subset_closure hx⟩ =
      W1p.value u x :=
  W1p.ae_lipschitzRepresentative_eq hΩ u

/-- The Lipschitz representative is the only element of `C^{0,1}(closure Ω)` that agrees almost
everywhere on `Ω` with `u`. -/
theorem W1p.lipschitzRepresentativeL_eq_iff (u : W1p μ Ω ∞)
    {G : HolderSpace 1 (closure (Ω : Set E)) ℝ} :
    W1p.lipschitzRepresentativeL hΩ u = G ↔
      ∀ᵐ x ∂μ, ∀ hx : x ∈ Ω, G ⟨x, subset_closure hx⟩ = W1p.value u x :=
  ⟨fun h ↦ h ▸ W1p.ae_lipschitzRepresentativeL_eq hΩ u,
    W1p.lipschitzRepresentative_eq_of_ae_eq hΩ u⟩

/-- **The sharp Lipschitz constant.** The Lipschitz representative of `u` is Lipschitz on
`closure Ω` with constant the essential supremum `‖∇u‖_∞` of the weak gradient. -/
theorem W1p.lipschitzWith_lipschitzRepresentativeL (u : W1p μ Ω ∞) :
    LipschitzWith ‖W1p.gradient u‖₊ (W1p.lipschitzRepresentativeL hΩ u) :=
  (W1p.lipschitzRepresentative_spec hΩ u).2.1

/-- The Lipschitz representative of `u` is bounded by `‖u‖_∞`. -/
theorem W1p.norm_lipschitzRepresentativeL_apply_le (u : W1p μ Ω ∞)
    (x : closure (Ω : Set E)) : ‖W1p.lipschitzRepresentativeL hΩ u x‖ ≤ ‖W1p.value u‖ :=
  (W1p.lipschitzRepresentative_spec hΩ u).2.2 x


omit hΩ in
/-- **A representative vanishing at a boundary point.** Let `Ω` lie in a closed set `F` and let
`x` be a limit of points outside `F`. If the weak gradient of `u ∈ W^{1,p}_0(Ω)` is essentially
bounded by `M` on `Ω ∩ B(x, ρ)`, then `u` has a representative that is `M`-Lipschitz on `B(x, ρ)`
and vanishes at `x`: the precise representative of the extension of `u` by zero, which vanishes
outside `F`. -/
theorem W1p0.exists_lipschitzOnWith_ae_eq_of_ae_norm_gradient_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : Set E} (hF : IsClosed F) (hΩF : (Ω : Set E) ⊆ F) (u : W1p0 μ Ω p) {x : E}
    (hx : x ∈ closure Fᶜ) {ρ : ℝ} (hρ : 0 < ρ) {M : ℝ≥0}
    (hM : ∀ᵐ z ∂μ, z ∈ (Ω : Set E) ∩ Metric.ball x ρ → ‖W1p.gradient (u : W1p μ Ω p) z‖ ≤ M) :
    ∃ u' : E → ℝ, W1p.value (u : W1p μ Ω p) =ᵐ[μ.restrict Ω] u' ∧
      LipschitzOnWith M u' (Metric.ball x ρ) ∧ u' x = 0 := by
  set u₀ : W1p μ (⊤ : Opens E) p := (W1p0.extendByZeroL (Omega' := ⊤) le_top u).val
  have hval : W1p.value u₀ =ᵐ[μ] (Ω : Set E).indicator (W1p.value (u : W1p μ Ω p)) :=
    W1p0.value_extendByZeroL_top_ae u
  have hprec : W1p.value u₀ =ᵐ[μ] preciseRepresentative μ (W1p.value u₀) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using W1p.ae_eq_preciseRepresentative u₀
  -- Near `x` the gradient of the extension is bounded by `M`: it vanishes off `Ω`.
  have hgrad : ∀ᵐ z ∂μ.restrict (Metric.ball x ρ), ‖W1p.gradient u₀ z‖ ≤ M := by
    refine (ae_restrict_iff' Metric.isOpen_ball.measurableSet).2 ?_
    filter_upwards [W1p0.gradient_extendByZeroL_top_ae u, hM] with z h1 h2 hz
    rw [h1]
    by_cases hzΩ : z ∈ (Ω : Set E)
    · rw [indicator_of_mem hzΩ]
      exact h2 ⟨hzΩ, hz⟩
    · rw [indicator_of_notMem hzΩ, norm_zero]
      exact M.coe_nonneg
  set u' := preciseRepresentative μ (W1p.value u₀)
  have hL : LipschitzOnWith M u' (Metric.ball x ρ) :=
    W1p.lipschitzOnWith_preciseRepresentative_of_ae_norm_gradient_le u₀
      (V := ⟨Metric.ball x ρ, Metric.isOpen_ball⟩) le_top (convex_ball x ρ) subset_rfl hgrad
  refine ⟨u', ?_, hL, ?_⟩
  · refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 ?_
    filter_upwards [hval, hprec] with z h1 h2 hz
    rw [← h2, h1, indicator_of_mem hz]
  · -- Outside `F` the representative vanishes, and `x` is a limit of such points near `x`.
    set O : Set E := Metric.ball x ρ ∩ Fᶜ
    have hO : IsOpen O := Metric.isOpen_ball.inter hF.isOpen_compl
    have hzero : EqOn u' 0 O := by
      refine Measure.eqOn_open_of_ae_eq (μ := μ) ?_ hO (hL.continuousOn.mono inter_subset_left)
        continuousOn_const
      refine (ae_restrict_iff' hO.measurableSet).2 ?_
      filter_upwards [hval, hprec] with z h1 h2 hz
      rw [← h2, h1, indicator_of_notMem fun hzΩ => hz.2 (hΩF hzΩ), Pi.zero_apply]
    have hxO : x ∈ closure O := Metric.isOpen_ball.inter_closure ⟨Metric.mem_ball_self hρ, hx⟩
    exact hzero.of_subset_closure
      (hL.continuousOn.mono (insert_subset (Metric.mem_ball_self hρ) inter_subset_left))
      continuousOn_const (subset_insert _ _) (insert_subset hxO subset_closure) (mem_insert _ _)

end TauCeti
