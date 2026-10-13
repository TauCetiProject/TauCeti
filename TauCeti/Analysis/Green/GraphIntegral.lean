/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoxIntegral.Substitution
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
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

noncomputable section

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

/-- The coordinate used by a directional Green identity. -/
inductive Coordinate
  | re
  | im

namespace Coordinate

/-- The sign of the ordered base and fiber coordinates relative to the positive plane. -/
def orientation : Coordinate → ℤ
  | .re => 1
  | .im => -1

@[simp]
theorem orientation_re : Coordinate.re.orientation = 1 := (rfl)

@[simp]
theorem orientation_im : Coordinate.im.orientation = -1 := (rfl)

/-- The real linear coordinate projection. -/
def proj : Coordinate → ℂ →L[ℝ] ℝ
  | re => Complex.reCLM
  | im => Complex.imCLM

/-- A graph parametrized by the chosen coordinate. -/
def graph (d : Coordinate) (g : ℝ → ℝ) : ℝ → ℂ :=
  match d with
  | re => verticalGraph g
  | im => horizontalGraph g

@[simp]
theorem proj_re : Coordinate.re.proj = Complex.reCLM := (rfl)

@[simp]
theorem proj_im : Coordinate.im.proj = Complex.imCLM := (rfl)

@[simp]
theorem graph_re_apply (g : ℝ → ℝ) (t : ℝ) : Coordinate.re.graph g t = ⟨t, g t⟩ := by
  simp only [graph]
  exact Complex.ext (verticalGraph_re g t) (verticalGraph_im g t)

@[simp]
theorem graph_im_apply (g : ℝ → ℝ) (t : ℝ) : Coordinate.im.graph g t = ⟨g t, t⟩ := by
  simp only [graph]
  exact Complex.ext (horizontalGraph_re g t) (horizontalGraph_im g t)

@[simp]
theorem proj_graph (d : Coordinate) (g : ℝ → ℝ) (t : ℝ) : d.proj (d.graph g t) = t := by
  cases d <;> simp [proj, graph]

/-- Continuity of a graph in either coordinate. -/
theorem continuousOn_graph (d : Coordinate) {g : ℝ → ℝ} {s : Set ℝ}
    (hg : ContinuousOn g s) : ContinuousOn (d.graph g) s := by
  cases d
  · exact continuousOn_verticalGraph hg
  · exact continuousOn_horizontalGraph hg

/-- A graph is differentiable at every differentiability point of its graph function. -/
theorem differentiableAt_graph (d : Coordinate) {g : ℝ → ℝ} {t : ℝ}
    (hg : DifferentiableAt ℝ g t) : DifferentiableAt ℝ (d.graph g) t := by
  cases d
  · exact (hasDerivAt_verticalGraph hg.hasDerivAt).differentiableAt
  · exact (hasDerivAt_horizontalGraph hg.hasDerivAt).differentiableAt

end Coordinate

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
    hS.ae_deriv_eq_zero_on_preimage θ (volume.restrict (Ioc a b))]
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
    have hzero : deriv θ t = 0 := hlevel hmem
    rw [(hdθ t ht').deriv] at hzero
    rw [deriv_zero_of_not_differentiableAt hγ, map_zero, hzero]

/-- Gauge integration on a graph depends only on the endpoint graph coordinates. The
parametrization may backtrack and have unbounded speed, and exceptional graph levels may have
uncountable preimages. Both coordinate directions use this same substitution theorem. -/
theorem hasIntegral_graph_reparam (d : Coordinate) {a b c e : ℝ} (hab : a < b)
    {graph θ θ' : ℝ → ℝ} {P : ℂ → ℝ} {s S : Set ℝ} (hs : s.Countable) (hS : S.Countable)
    (hgraph : ContinuousOn graph (Icc c e))
    (hdgraph : ∀ t ∈ Ioo c e \ S, DifferentiableAt ℝ graph t)
    (hP : ContinuousOn P (d.graph graph '' Icc c e))
    (hθ : ContinuousOn θ (Icc a b)) (hdθ : ∀ t ∈ Ioo a b \ s, HasDerivAt θ (θ' t) t)
    (hmap : MapsTo θ (Icc a b) (Icc c e)) :
    BoxIntegral.HasIntegral (BoxIntegral.intervalBox a b hab) BoxIntegral.IntegrationParams.Henstock
      (fun x ↦ P (d.graph graph (θ (x 0))) * d.proj (deriv (d.graph graph ∘ θ) (x 0)))
      BoxIntegral.BoxAdditiveMap.volume (∫ t in θ a..θ b, P (d.graph graph t)) := by
  have hc : ContinuousOn (P ∘ d.graph graph) (Icc c e) :=
    hP.comp (d.continuousOn_graph hgraph) (mapsTo_image _ _)
  have hdγ : ∀ t ∈ Ioo a b \ s, θ t ∉ S ∪ {c, e} →
      DifferentiableAt ℝ (d.graph graph ∘ θ) t := by
    intro t ht havoid
    have hm := hmap (Ioo_subset_Icc_self ht.1)
    have htc : θ t ≠ c := fun h ↦ havoid (Or.inr (by simp [h]))
    have hte : θ t ≠ e := fun h ↦ havoid (Or.inr (by simp [h]))
    have htθ : θ t ∈ Ioo c e \ S :=
      ⟨⟨lt_of_le_of_ne hm.1 htc.symm, lt_of_le_of_ne hm.2 hte⟩,
        fun h ↦ havoid (Or.inl h)⟩
    exact (d.differentiableAt_graph (hdgraph (θ t) htθ)).comp t (hdθ t ht).differentiableAt
  have hcoord : d.proj ∘ (d.graph graph ∘ θ) = θ := by
    ext t
    simp only [Function.comp_apply, Coordinate.proj_graph]
  have he := ae_deriv_projection d.proj hcoord hs
    (hS.union (Set.toFinite ({c, e} : Set ℝ)).countable) hdθ hdγ
  have h := BoxIntegral.hasIntegral_Henstock_substitution hab hs hθ hdθ hc hmap
  apply h.congr_ae ?_ rfl
  apply BoxIntegral.ae_eq_intervalBox hab
    (f := fun t ↦ θ' t * P (d.graph graph (θ t)))
    (g := fun t ↦ P (d.graph graph (θ t)) * d.proj (deriv (d.graph graph ∘ θ) t))
  filter_upwards [he] with t ht
  rw [ht, mul_comm]

/-- Gauge integration on a graph equals the ordinary integral over its base coordinate. -/
theorem hasIntegral_graph (d : Coordinate) {a b : ℝ} (hab : a < b)
    {graph : ℝ → ℝ} {P : ℂ → ℝ} {S : Set ℝ} (hS : S.Countable)
    (hgraph : ContinuousOn graph (Icc a b))
    (hdgraph : ∀ t ∈ Ioo a b \ S, DifferentiableAt ℝ graph t)
    (hP : ContinuousOn P (d.graph graph '' Icc a b)) :
    BoxIntegral.HasIntegral (BoxIntegral.intervalBox a b hab) BoxIntegral.IntegrationParams.Henstock
      (fun x ↦ P (d.graph graph (x 0)) * d.proj (deriv (d.graph graph) (x 0)))
      BoxIntegral.BoxAdditiveMap.volume (∫ t in a..b, P (d.graph graph t)) := by
  simpa only [Function.comp_id, id_eq] using
    hasIntegral_graph_reparam d hab countable_empty hS hgraph hdgraph hP
      (θ := id) (θ' := fun _ ↦ 1) continuousOn_id (fun t _ ↦ hasDerivAt_id t)
      (fun _ ht ↦ ht)

/-- A raw curve with constant projection contributes zero to that coordinate one-form.
No regularity of its other coordinate or of the field is needed. -/
theorem hasIntegral_of_projection_constant (L : ℂ →L[ℝ] ℝ) {a b c : ℝ} (hab : a < b)
    {γ : ℝ → ℂ} (hγ : ∀ t, L (γ t) = c) (P : ℂ → ℝ) :
    BoxIntegral.HasIntegral (BoxIntegral.intervalBox a b hab) BoxIntegral.IntegrationParams.Henstock
      (fun t ↦ P (γ (t 0)) * L (deriv γ (t 0))) BoxIntegral.BoxAdditiveMap.volume 0 := by
  have hc : L ∘ γ = fun _ ↦ c := funext hγ
  have hd (t : ℝ) : L (deriv γ t) = 0 := by
    by_cases h : DifferentiableAt ℝ γ t
    · have hp := L.hasFDerivAt.comp_hasDerivAt t h.hasDerivAt
      rw [hc] at hp
      exact hp.unique (hasDerivAt_const t c)
    · rw [deriv_zero_of_not_differentiableAt h, map_zero]
  simpa only [hd, mul_zero] using
    (BoxIntegral.hasIntegral_zero (I := BoxIntegral.intervalBox a b hab)
      (l := BoxIntegral.IntegrationParams.Henstock) (vol := BoxIntegral.BoxAdditiveMap.volume))

end TauCeti.Green
