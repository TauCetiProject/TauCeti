/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoxIntegral.Oriented.Calculus
public import TauCeti.Analysis.Green.Cell
public import TauCeti.Analysis.Calculus.Deriv.Projection

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

/-- A graph-coordinate reparametrization has a continuous scalar primitive. Its increments
are the coefficient integrals, and its composed derivative is the actual projected-curve
integrand outside a countable exceptional set. -/
theorem Coordinate.exists_graph_reparam_primitive (d : Coordinate) {a b c e : ℝ}
    {g θ θ' : ℝ → ℝ} {P : ℂ → ℝ} {s S : Set ℝ} (hs : s.Countable) (hS : S.Countable)
    (hg : ContinuousOn g (Icc c e))
    (hdg : ∀ x ∈ Ioo c e \ S, DifferentiableAt ℝ g x)
    (hP : ContinuousOn P (d.graph g '' Icc c e))
    (hdθ : ∀ t ∈ uIoo a b \ s, HasDerivAt θ (θ' t) t)
    (hmap : MapsTo θ (uIcc a b) (Icc c e)) :
    ∃ A : ℝ → ℝ, Continuous A ∧
      (∀ x ∈ Icc c e, ∀ y ∈ Icc c e, A y - A x = ∫ z in x..y, P (d.graph g z)) ∧
      ∃ T : Set ℝ, T.Countable ∧ ∀ t ∈ uIoo a b \ T,
        HasDerivAt (A ∘ θ) (P (d.graph g (θ t)) * d.proj (deriv (d.graph g ∘ θ) t)) t := by
  have hce : c ≤ e := (hmap (left_mem_uIcc)).1.trans (hmap left_mem_uIcc).2
  have hf : ContinuousOn (fun x ↦ P (d.graph g x)) (Icc c e) :=
    hP.comp (d.continuousOn_graph hg) (mapsTo_image _ _)
  obtain ⟨A, hA, hdA, hvalue⟩ :=
    TauCeti.intervalIntegral.exists_continuous_primitive_Icc hce hf
  let T := S ∪ {c, e}
  refine ⟨A, hA, hvalue, s ∪ {t | θ t ∈ T ∧ deriv θ t ≠ 0},
    hs.union (TauCeti.countable_setOf_mem_and_deriv_ne_zero θ
      (hS.union (toFinite _).countable)), ?_⟩
  intro t ht
  have hdt := hdθ t ⟨ht.1, fun h ↦ ht.2 (Or.inl h)⟩
  have hp : d.proj (deriv (d.graph g ∘ θ) t) = θ' t := by
    have hcoord : d.proj ∘ (d.graph g ∘ θ) = θ := by
      ext x
      simp only [Function.comp_apply, Coordinate.proj_graph]
    apply d.proj.apply_deriv_eq_of_comp hcoord hdt
    by_cases hm : θ t ∈ T
    · exact Or.inr (not_ne_iff.mp fun hz ↦ ht.2 (Or.inr ⟨hm, hz⟩))
    · exact Or.inl (d.differentiableAt_graph_comp hdg hdt.differentiableAt
        (hmap (uIoo_subset_uIcc_self ht.1)) hm)
  simpa only [hp, smul_eq_mul, mul_comm] using
    (hdA (θ t) (hmap (uIoo_subset_uIcc_self ht.1))).scomp t hdt

/-- Gauge integration on a graph depends only on the endpoint graph coordinates. The
parametrization may backtrack and have unbounded speed, and exceptional graph levels may have
uncountable preimages. Both coordinate directions use this same substitution theorem. -/
theorem hasHenstockIntervalIntegral_graph_reparam (d : Coordinate) {a b c e : ℝ}
    {graph θ θ' : ℝ → ℝ} {P : ℂ → ℝ} {s S : Set ℝ} (hs : s.Countable) (hS : S.Countable)
    (hgraph : ContinuousOn graph (Icc c e))
    (hdgraph : ∀ t ∈ Ioo c e \ S, DifferentiableAt ℝ graph t)
    (hP : ContinuousOn P (d.graph graph '' Icc c e))
    (hθ : ContinuousOn θ (uIcc a b)) (hdθ : ∀ t ∈ uIoo a b \ s, HasDerivAt θ (θ' t) t)
    (hmap : MapsTo θ (uIcc a b) (Icc c e)) :
    TauCeti.BoxIntegral.HasHenstockIntervalIntegral
      (fun t ↦ P (d.graph graph (θ t)) * d.proj (deriv (d.graph graph ∘ θ) t))
      a b (∫ t in θ a..θ b, P (d.graph graph t)) := by
  have hf : ContinuousOn (fun x ↦ P (d.graph graph x)) (Icc c e) :=
    hP.comp (d.continuousOn_graph hgraph) (mapsTo_image _ _)
  have hi := TauCeti.BoxIntegral.hasHenstockIntervalIntegral_deriv_smul_comp hs hθ hdθ
    (hf.mono (image_subset_iff.mpr hmap))
  apply hi.congr_ae
  have hcoord : d.proj ∘ (d.graph graph ∘ θ) = θ := by
    funext t
    simp only [Function.comp_apply, Coordinate.proj_graph]
  have hdθ' : ∀ t ∈ Ioo (min a b) (max a b) \ s, HasDerivAt θ (θ' t) t := by
    simpa only [uIoo] using hdθ
  have hproj := d.proj.apply_deriv_ae_eq hcoord hs (hS.union (toFinite {c, e}).countable)
    hdθ' (fun t ht havoid ↦ d.differentiableAt_graph_comp hdgraph
      (hdθ' t ht).differentiableAt
      (hmap (uIoo_subset_uIcc_self (by
        simpa only [uIoo] using ht.1))) havoid)
  have hproj' : (fun t ↦ d.proj (deriv (d.graph graph ∘ θ) t))
      =ᵐ[volume.restrict (uIoc a b)] θ' := by
    simpa only [uIoc] using hproj
  filter_upwards [hproj'] with t ht
  simp only [ht, smul_eq_mul, mul_comm]

end TauCeti.Green
