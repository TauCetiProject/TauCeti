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
  let f : ℝ → ℝ := fun x ↦ P (d.graph g (projIcc c e hce x))
  have hf : Continuous f :=
    (hP.comp (d.continuousOn_graph hg) (mapsTo_image _ _)).domRestrict.comp continuous_projIcc
  let A : ℝ → ℝ := fun x ↦ ∫ z in c..x, f z
  have hA : Continuous A := (intervalIntegral.differentiable_integral_of_continuous hf).continuous
  have hdA (x : ℝ) : HasDerivAt A (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable c x)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  let T := S ∪ {c, e}
  refine ⟨A, hA, ?_, s ∪ {t | θ t ∈ T ∧ deriv θ t ≠ 0},
    hs.union (TauCeti.countable_setOf_mem_and_deriv_ne_zero θ
      (hS.union (toFinite _).countable)), ?_⟩
  · intro x hx y hy
    calc
      A y - A x = ∫ z in x..y, f z := by
        apply sub_eq_iff_eq_add.mpr
        simpa [A, add_comm] using (intervalIntegral.integral_add_adjacent_intervals
          (hf.intervalIntegrable c x) (hf.intervalIntegrable x y)).symm
      _ = _ := intervalIntegral.integral_congr fun z hz ↦ by
        dsimp only [f]
        rw [projIcc_of_mem hce (uIcc_subset_Icc hx hy hz)]
  · intro t ht
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
    have he : f (θ t) = P (d.graph g (θ t)) := by
      dsimp only [f]
      rw [projIcc_of_mem hce (hmap (uIoo_subset_uIcc_self ht.1))]
    simpa only [hp, he, smul_eq_mul, mul_comm] using (hdA (θ t)).scomp t hdt

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
  obtain ⟨A, hA, hvalue, T, hT, hdA⟩ :=
    d.exists_graph_reparam_primitive hs hS hgraph hdgraph hP hdθ hmap
  have hi := TauCeti.BoxIntegral.hasHenstockIntervalIntegral_of_hasDerivAt_off_countable
    hT (hA.comp_continuousOn hθ) hdA
  simpa only [Function.comp_apply,
    hvalue (θ a) (hmap left_mem_uIcc) (θ b) (hmap right_mem_uIcc)] using hi

/-- Gauge integration on a graph equals the ordinary integral over its base coordinate. -/
theorem hasHenstockIntervalIntegral_graph (d : Coordinate) {a b : ℝ}
    {graph : ℝ → ℝ} {P : ℂ → ℝ} {S : Set ℝ} (hS : S.Countable)
    (hgraph : ContinuousOn graph (uIcc a b))
    (hdgraph : ∀ t ∈ uIoo a b \ S, DifferentiableAt ℝ graph t)
    (hP : ContinuousOn P (d.graph graph '' uIcc a b)) :
    TauCeti.BoxIntegral.HasHenstockIntervalIntegral
      (fun t ↦ P (d.graph graph t) * d.proj (deriv (d.graph graph) t))
      a b (∫ t in a..b, P (d.graph graph t)) := by
  simpa only [Function.comp_id, id_eq] using
    hasHenstockIntervalIntegral_graph_reparam d countable_empty hS hgraph hdgraph hP
      (θ := id) (θ' := fun _ ↦ 1) continuousOn_id (fun t _ ↦ hasDerivAt_id t)
      (fun _ ht ↦ ht)

/-- A raw curve with constant projection contributes zero to that coordinate one-form.
No regularity of its other coordinate or of the field is needed. -/
theorem hasHenstockIntervalIntegral_of_projection_constant (L : ℂ →L[ℝ] ℝ) {a b c : ℝ}
    {γ : ℝ → ℂ} (hγ : ∀ t, L (γ t) = c) (P : ℂ → ℝ) :
    TauCeti.BoxIntegral.HasHenstockIntervalIntegral (fun t ↦ P (γ t) * L (deriv γ t)) a b 0 := by
  have hd (t : ℝ) : L (deriv γ t) = 0 := L.apply_deriv_eq_zero_of_forall_eq hγ t
  simpa only [hd, mul_zero, Pi.zero_def] using
    TauCeti.BoxIntegral.hasHenstockIntervalIntegral_zero (E := ℝ) a b

end TauCeti.Green
