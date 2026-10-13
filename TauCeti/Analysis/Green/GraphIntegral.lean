/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoxIntegral.Substitution
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.LeftRightNhds
import TauCeti.Analysis.Calculus.Deriv.CountableLevels

/-!
# Gauge integrals along graph arcs

For a graph continuous on an interval and differentiable except at countably many points,
the `P dx` integral along a vertical cell graph is the ordinary integral of `P` over the base
interval. A horizontal cell graph satisfies the corresponding `Q dy` formula. These statements
use the actual raw-curve derivative and the Henstock integral, without bounded graph speed or
absolute continuity. Constant-coordinate arcs have zero integral in the unused direction.
Graph reparametrization permits backtracking and unbounded speed, even when exceptional graph
levels have uncountable preimages under the parametrization.

-/

public section

open MeasureTheory Set

namespace TauCeti.Green

/-- The graph arc `t ↦ (t, graph t)` in a vertical cell. -/
def verticalGraph (graph : ℝ → ℝ) (t : ℝ) : ℂ := ⟨t, graph t⟩

/-- The graph arc `t ↦ (graph t, t)` in a horizontal cell. -/
def horizontalGraph (graph : ℝ → ℝ) (t : ℝ) : ℂ := ⟨graph t, t⟩

/-- Real coordinate of a vertical-cell graph. -/
@[simp]
theorem verticalGraph_re (graph : ℝ → ℝ) (t : ℝ) : (verticalGraph graph t).re = t := (rfl)

/-- Imaginary coordinate of a vertical-cell graph. -/
@[simp]
theorem verticalGraph_im (graph : ℝ → ℝ) (t : ℝ) :
    (verticalGraph graph t).im = graph t := (rfl)

/-- Real coordinate of a horizontal-cell graph. -/
@[simp]
theorem horizontalGraph_re (graph : ℝ → ℝ) (t : ℝ) :
    (horizontalGraph graph t).re = graph t := (rfl)

/-- Imaginary coordinate of a horizontal-cell graph. -/
@[simp]
theorem horizontalGraph_im (graph : ℝ → ℝ) (t : ℝ) : (horizontalGraph graph t).im = t := (rfl)

/-- A vertical-cell graph is continuous wherever its graph function is continuous. -/
theorem continuousOn_verticalGraph {s : Set ℝ} {graph : ℝ → ℝ} (h : ContinuousOn graph s) :
    ContinuousOn (verticalGraph graph) s :=
  Complex.equivRealProdCLM.symm.continuous.comp_continuousOn (continuousOn_id.prodMk h)

/-- A horizontal-cell graph is continuous wherever its graph function is continuous. -/
theorem continuousOn_horizontalGraph {s : Set ℝ} {graph : ℝ → ℝ} (h : ContinuousOn graph s) :
    ContinuousOn (horizontalGraph graph) s :=
  Complex.equivRealProdCLM.symm.continuous.comp_continuousOn (h.prodMk continuousOn_id)

/-- Derivative of a vertical-cell graph at a differentiability point. -/
theorem hasDerivAt_verticalGraph {graph : ℝ → ℝ} {graph' t : ℝ}
    (h : HasDerivAt graph graph' t) : HasDerivAt (verticalGraph graph) ⟨1, graph'⟩ t := by
  exact Complex.equivRealProdCLM.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk h)

/-- Derivative of a horizontal-cell graph at a differentiability point. -/
theorem hasDerivAt_horizontalGraph {graph : ℝ → ℝ} {graph' t : ℝ}
    (h : HasDerivAt graph graph' t) : HasDerivAt (horizontalGraph graph) ⟨graph', 1⟩ t := by
  exact Complex.equivRealProdCLM.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (h.prodMk (hasDerivAt_id t))

/-- Gauge `P dx` on a vertical-cell graph equals the base-interval integral. The graph may have
unbounded speed and need not be absolutely continuous. -/
theorem hasIntegral_verticalGraph_dx {a b : ℝ} (hab : a < b) {graph : ℝ → ℝ} {P : ℂ → ℝ}
    {s : Set ℝ} (hs : s.Countable) (hgraph : ContinuousOn graph (Icc a b))
    (hdgraph : ∀ t ∈ Ioo a b \ s, DifferentiableAt ℝ graph t)
    (hP : ContinuousOn P (verticalGraph graph '' Icc a b)) :
    BoxIntegral.HasIntegral (BoxIntegral.intervalBox a b hab) BoxIntegral.IntegrationParams.Henstock
      (fun x ↦ P (verticalGraph graph (x 0)) * (deriv (verticalGraph graph) (x 0)).re)
      BoxIntegral.BoxAdditiveMap.volume (∫ t in a..b, P (verticalGraph graph t)) := by
  have hc : ContinuousOn (P ∘ verticalGraph graph) (Icc a b) :=
    hP.comp (continuousOn_verticalGraph hgraph) (mapsTo_image _ _)
  apply (hc.intervalIntegrable_of_Icc hab.le).hasBoxIntegral hab _ rfl |>.congr_ae ?_ rfl
  apply BoxIntegral.ae_eq_intervalBox hab
    (f := P ∘ verticalGraph graph)
    (g := fun t ↦ P (verticalGraph graph t) * (deriv (verticalGraph graph) t).re)
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae ((hs.union (Set.toFinite ({a, b} : Set ℝ)).countable).ae_notMem volume)]
    with t ht hts
  have htb : t ≠ b := fun h ↦ hts (Or.inr (by simp [h]))
  have ht' : t ∈ Ioo a b \ s :=
    ⟨⟨ht.1, lt_of_le_of_ne ht.2 htb⟩, fun h ↦ hts (Or.inl h)⟩
  rw [(hasDerivAt_verticalGraph (hdgraph t ht').hasDerivAt).deriv]
  simp only [Function.comp_apply, mul_one]

/-- Gauge `Q dy` on a horizontal-cell graph equals the base-interval integral, even when the
speed is unbounded or the graph is not absolutely continuous. -/
theorem hasIntegral_horizontalGraph_dy {a b : ℝ} (hab : a < b) {graph : ℝ → ℝ} {Q : ℂ → ℝ}
    {s : Set ℝ} (hs : s.Countable) (hgraph : ContinuousOn graph (Icc a b))
    (hdgraph : ∀ t ∈ Ioo a b \ s, DifferentiableAt ℝ graph t)
    (hQ : ContinuousOn Q (horizontalGraph graph '' Icc a b)) :
    BoxIntegral.HasIntegral (BoxIntegral.intervalBox a b hab) BoxIntegral.IntegrationParams.Henstock
      (fun x ↦ Q (horizontalGraph graph (x 0)) * (deriv (horizontalGraph graph) (x 0)).im)
      BoxIntegral.BoxAdditiveMap.volume (∫ t in a..b, Q (horizontalGraph graph t)) := by
  have hc : ContinuousOn (Q ∘ horizontalGraph graph) (Icc a b) :=
    hQ.comp (continuousOn_horizontalGraph hgraph) (mapsTo_image _ _)
  apply (hc.intervalIntegrable_of_Icc hab.le).hasBoxIntegral hab _ rfl |>.congr_ae ?_ rfl
  apply BoxIntegral.ae_eq_intervalBox hab
    (f := Q ∘ horizontalGraph graph)
    (g := fun t ↦ Q (horizontalGraph graph t) * (deriv (horizontalGraph graph) t).im)
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae ((hs.union (Set.toFinite ({a, b} : Set ℝ)).countable).ae_notMem volume)]
    with t ht hts
  have htb : t ≠ b := fun h ↦ hts (Or.inr (by simp [h]))
  have ht' : t ∈ Ioo a b \ s :=
    ⟨⟨ht.1, lt_of_le_of_ne ht.2 htb⟩, fun h ↦ hts (Or.inl h)⟩
  rw [(hasDerivAt_horizontalGraph (hdgraph t ht').hasDerivAt).deriv]
  simp only [Function.comp_apply, mul_one]

private theorem deriv_verticalLine_re (c t : ℝ) (g : ℝ → ℝ) :
    (deriv (fun t ↦ (⟨c, g t⟩ : ℂ)) t).re = 0 := by
  by_cases hd : DifferentiableAt ℝ (fun t ↦ (⟨c, g t⟩ : ℂ)) t
  · exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt).unique
      (hasDerivAt_const t c)
  · rw [deriv_zero_of_not_differentiableAt hd]
    rfl

private theorem deriv_horizontalLine_im (c t : ℝ) (g : ℝ → ℝ) :
    (deriv (fun t ↦ (⟨g t, c⟩ : ℂ)) t).im = 0 := by
  by_cases hd : DifferentiableAt ℝ (fun t ↦ (⟨g t, c⟩ : ℂ)) t
  · exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt).unique
      (hasDerivAt_const t c)
  · rw [deriv_zero_of_not_differentiableAt hd]
    rfl

/-- An arbitrary arc on a vertical line contributes zero to `P dx`. -/
theorem hasIntegral_verticalLine_dx {a b : ℝ} (hab : a < b) (c : ℝ) (g : ℝ → ℝ) (P : ℂ → ℝ) :
    BoxIntegral.HasIntegral (BoxIntegral.intervalBox a b hab) BoxIntegral.IntegrationParams.Henstock
      (fun x ↦ P ⟨c, g (x 0)⟩ * (deriv (fun t ↦ (⟨c, g t⟩ : ℂ)) (x 0)).re)
      BoxIntegral.BoxAdditiveMap.volume 0 := by
  simpa only [deriv_verticalLine_re, mul_zero] using
    (BoxIntegral.hasIntegral_zero (I := BoxIntegral.intervalBox a b hab)
      (l := BoxIntegral.IntegrationParams.Henstock) (vol := BoxIntegral.BoxAdditiveMap.volume))

/-- An arbitrary arc on a horizontal line contributes zero to `Q dy`. -/
theorem hasIntegral_horizontalLine_dy {a b : ℝ} (hab : a < b) (c : ℝ) (g : ℝ → ℝ) (Q : ℂ → ℝ) :
    BoxIntegral.HasIntegral (BoxIntegral.intervalBox a b hab) BoxIntegral.IntegrationParams.Henstock
      (fun x ↦ Q ⟨g (x 0), c⟩ * (deriv (fun t ↦ (⟨g t, c⟩ : ℂ)) (x 0)).im)
      BoxIntegral.BoxAdditiveMap.volume 0 := by
  simpa only [deriv_horizontalLine_im, mul_zero] using
    (BoxIntegral.hasIntegral_zero (I := BoxIntegral.intervalBox a b hab)
      (l := BoxIntegral.IntegrationParams.Henstock) (vol := BoxIntegral.BoxAdditiveMap.volume))

-- At regular curve points, uniqueness gives the projected derivative. At irregular curve points,
-- the total derivative is zero; the parameter derivative also vanishes almost everywhere on the
-- countably many exceptional levels. Their preimages themselves need not be null or countable.
private theorem ae_deriv_projection {a b : ℝ} {θ θ' : ℝ → ℝ} {γ : ℝ → ℂ}
    (π : ℂ →L[ℝ] ℝ) (hπ : π ∘ γ = θ) {s S : Set ℝ} (hs : s.Countable) (hS : S.Countable)
    (hdθ : ∀ t ∈ Ioo a b \ s, HasDerivAt θ (θ' t) t)
    (hdγ : ∀ t ∈ Ioo a b \ s, θ t ∉ S → DifferentiableAt ℝ γ t) :
    (fun t ↦ π (deriv γ t)) =ᵐ[volume.restrict (Ioc a b)] θ' := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae ((hs.union (Set.toFinite ({a, b} : Set ℝ)).countable).ae_notMem volume),
    ae_restrict_of_ae ((countable_preimage_nonzero_deriv θ hS).ae_notMem volume)]
    with t ht hts hlevel
  have htb : t ≠ b := fun h ↦ hts (Or.inr (by simp [h]))
  have ht' : t ∈ Ioo a b \ s :=
    ⟨⟨ht.1, lt_of_le_of_ne ht.2 htb⟩, fun h ↦ hts (Or.inl h)⟩
  by_cases hγ : DifferentiableAt ℝ γ t
  · have hproj := π.hasFDerivAt.comp_hasDerivAt t hγ.hasDerivAt
    rw [hπ] at hproj
    exact hproj.unique (hdθ t ht')
  · have hmem : θ t ∈ S := by
      by_contra h
      exact hγ (hdγ t ht' h)
    have hzero : deriv θ t = 0 := by
      by_contra h
      exact hlevel ⟨hmem, h⟩
    rw [(hdθ t ht').deriv] at hzero
    rw [deriv_zero_of_not_differentiableAt hγ, map_zero, hzero]

/-- Gauge `P dx` is invariant under continuous graph reparametrization, including backtracking
and unbounded speed. Both the graph and parametrization may fail differentiability at countably
many points; no hypothesis on the size of the preimages of graph exceptions is needed. -/
theorem hasIntegral_verticalGraph_reparam_dx {a b c d : ℝ} (hab : a < b)
    {graph θ θ' : ℝ → ℝ} {P : ℂ → ℝ} {s S : Set ℝ} (hs : s.Countable) (hS : S.Countable)
    (hgraph : ContinuousOn graph (Icc c d))
    (hdgraph : ∀ t ∈ Ioo c d \ S, DifferentiableAt ℝ graph t)
    (hP : ContinuousOn P (verticalGraph graph '' Icc c d))
    (hθ : ContinuousOn θ (Icc a b)) (hdθ : ∀ t ∈ Ioo a b \ s, HasDerivAt θ (θ' t) t)
    (hmap : MapsTo θ (Icc a b) (Icc c d)) :
    BoxIntegral.HasIntegral (BoxIntegral.intervalBox a b hab) BoxIntegral.IntegrationParams.Henstock
      (fun x ↦ P (verticalGraph graph (θ (x 0))) * (deriv (verticalGraph graph ∘ θ) (x 0)).re)
      BoxIntegral.BoxAdditiveMap.volume (∫ t in θ a..θ b, P (verticalGraph graph t)) := by
  have hc : ContinuousOn (P ∘ verticalGraph graph) (Icc c d) :=
    hP.comp (continuousOn_verticalGraph hgraph) (mapsTo_image _ _)
  have hdγ : ∀ t ∈ Ioo a b \ s, θ t ∉ S ∪ {c, d} →
      DifferentiableAt ℝ (verticalGraph graph ∘ θ) t := by
    intro t ht havoid
    have hm := hmap (Ioo_subset_Icc_self ht.1)
    have htc : θ t ≠ c := fun h ↦ havoid (Or.inr (by simp [h]))
    have htd : θ t ≠ d := fun h ↦ havoid (Or.inr (by simp [h]))
    have htθ : θ t ∈ Ioo c d \ S :=
      ⟨⟨lt_of_le_of_ne hm.1 htc.symm, lt_of_le_of_ne hm.2 htd⟩,
        fun h ↦ havoid (Or.inl h)⟩
    exact ((hasDerivAt_verticalGraph (hdgraph (θ t) htθ).hasDerivAt).scomp t
      (hdθ t ht)).differentiableAt
  have hcoord : Complex.reCLM ∘ (verticalGraph graph ∘ θ) = θ := by
    ext t
    simp only [Function.comp_apply, Complex.reCLM_apply, verticalGraph_re]
  have he := ae_deriv_projection Complex.reCLM hcoord hs
    (hS.union (Set.toFinite ({c, d} : Set ℝ)).countable) hdθ hdγ
  have h := BoxIntegral.hasIntegral_Henstock_substitution hab hs hθ hdθ hc hmap
  apply h.congr_ae ?_ rfl
  apply BoxIntegral.ae_eq_intervalBox hab
    (f := fun t ↦ θ' t * P (verticalGraph graph (θ t)))
    (g := fun t ↦ P (verticalGraph graph (θ t)) * (deriv (verticalGraph graph ∘ θ) t).re)
  filter_upwards [he] with t ht
  simp only [Complex.reCLM_apply] at ht
  rw [ht, mul_comm]

/-- Gauge `Q dy` is invariant under continuous graph reparametrization, including backtracking
and unbounded speed. Both the graph and parametrization may fail differentiability at countably
many points; no hypothesis on the size of the preimages of graph exceptions is needed. -/
theorem hasIntegral_horizontalGraph_reparam_dy {a b c d : ℝ} (hab : a < b)
    {graph θ θ' : ℝ → ℝ} {Q : ℂ → ℝ} {s S : Set ℝ} (hs : s.Countable) (hS : S.Countable)
    (hgraph : ContinuousOn graph (Icc c d))
    (hdgraph : ∀ t ∈ Ioo c d \ S, DifferentiableAt ℝ graph t)
    (hQ : ContinuousOn Q (horizontalGraph graph '' Icc c d))
    (hθ : ContinuousOn θ (Icc a b)) (hdθ : ∀ t ∈ Ioo a b \ s, HasDerivAt θ (θ' t) t)
    (hmap : MapsTo θ (Icc a b) (Icc c d)) :
    BoxIntegral.HasIntegral (BoxIntegral.intervalBox a b hab) BoxIntegral.IntegrationParams.Henstock
      (fun x ↦ Q (horizontalGraph graph (θ (x 0))) * (deriv (horizontalGraph graph ∘ θ) (x 0)).im)
      BoxIntegral.BoxAdditiveMap.volume (∫ t in θ a..θ b, Q (horizontalGraph graph t)) := by
  have hc : ContinuousOn (Q ∘ horizontalGraph graph) (Icc c d) :=
    hQ.comp (continuousOn_horizontalGraph hgraph) (mapsTo_image _ _)
  have hdγ : ∀ t ∈ Ioo a b \ s, θ t ∉ S ∪ {c, d} →
      DifferentiableAt ℝ (horizontalGraph graph ∘ θ) t := by
    intro t ht havoid
    have hm := hmap (Ioo_subset_Icc_self ht.1)
    have htc : θ t ≠ c := fun h ↦ havoid (Or.inr (by simp [h]))
    have htd : θ t ≠ d := fun h ↦ havoid (Or.inr (by simp [h]))
    have htθ : θ t ∈ Ioo c d \ S :=
      ⟨⟨lt_of_le_of_ne hm.1 htc.symm, lt_of_le_of_ne hm.2 htd⟩,
        fun h ↦ havoid (Or.inl h)⟩
    exact ((hasDerivAt_horizontalGraph (hdgraph (θ t) htθ).hasDerivAt).scomp t
      (hdθ t ht)).differentiableAt
  have hcoord : Complex.imCLM ∘ (horizontalGraph graph ∘ θ) = θ := by
    ext t
    simp only [Function.comp_apply, Complex.imCLM_apply, horizontalGraph_im]
  have he := ae_deriv_projection Complex.imCLM hcoord hs
    (hS.union (Set.toFinite ({c, d} : Set ℝ)).countable) hdθ hdγ
  have h := BoxIntegral.hasIntegral_Henstock_substitution hab hs hθ hdθ hc hmap
  apply h.congr_ae ?_ rfl
  apply BoxIntegral.ae_eq_intervalBox hab
    (f := fun t ↦ θ' t * Q (horizontalGraph graph (θ t)))
    (g := fun t ↦ Q (horizontalGraph graph (θ t)) * (deriv (horizontalGraph graph ∘ θ) t).im)
  filter_upwards [he] with t ht
  simp only [Complex.imCLM_apply] at ht
  rw [ht, mul_comm]

end TauCeti.Green
