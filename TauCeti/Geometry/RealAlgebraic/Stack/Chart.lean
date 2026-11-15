/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Invariant
public import TauCeti.Analysis.Analytic.Submanifold.Basic

/-!
# Global delineations from analytic chart coordinates

A delineation constructed on an open set of the free coordinates of an analytic chart
transfers to an open neighborhood in the submanifold. Quantities constant along its root
sections transfer with it. Such chart-local stacks glue over a preconnected submanifold to
a global delineation carrying the same sectionwise constancy.

This connects local polynomial root constructions along analytic parametrizations to global
stacks on their base. For example, take the section quantity to be the ambient order of a
multivariate polynomial at `Fin.cons t x`: the gluing conclusion is then constancy of ambient
order along each global section, rather than constancy of the order of a restricted function.
The chart-coordinate open sets need not be connected, and no global root labelling or common
root count is assumed.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), 242–268, Sections 2–3 (analytic delineability and order-invariance).
-/

public section

open Polynomial Set

namespace TauCeti

variable {n d : ℕ} {S : Set (Fin n → ℝ)} {ι α : Type*}
  {P : ι → (Fin n → ℝ) → ℝ[X]} {q : (Fin n → ℝ) → ℝ → α}
  {e : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)}

/-- A stack in the free coordinates of an analytic chart transfers to an open neighborhood
in the base, preserving quantities constant along each section. -/
theorem IsAnalyticChart.exists_delineation_of_const_on_sections (he : IsAnalyticChart d S e)
    {x : Fin n → ℝ} (hx : x ∈ S) (hxe : x ∈ e.source)
    {V : Set (Fin d → ℝ)} (hV : IsOpen V) (hxV : firstCoords ℝ n d (e x) ∈ V)
    (D : Delineation (fun k (u : V) ↦ P k (e.symm (firstCoords ℝ d n u))))
    (hq : ∀ i, ∀ u v : V,
      q (e.symm (firstCoords ℝ d n u)) (D.root i u) =
        q (e.symm (firstCoords ℝ d n v)) (D.root i v)) :
    ∃ U : Set S, IsOpen U ∧ (⟨x, hx⟩ : S) ∈ U ∧
      ∃ D' : Delineation (fun k (y : U) ↦ P k y),
        ∀ i, ∀ y z : U, q y (D'.root i y) = q z (D'.root i z) := by
  let C : S → Fin d → ℝ := fun y ↦ firstCoords ℝ n d (e y)
  let U : Set S := (Subtype.val ⁻¹' e.source) ∩ C ⁻¹' V
  have hC : ContinuousOn C (Subtype.val ⁻¹' e.source) :=
    (firstCoords ℝ n d).continuous.comp_continuousOn
      (e.continuousOn.comp continuous_subtype_val.continuousOn (mapsTo_preimage _ _))
  have hU : IsOpen U :=
    hC.isOpen_inter_preimage (e.open_source.preimage continuous_subtype_val) hV
  let ψ : U → V := fun y ↦ ⟨C y, y.property.2⟩
  have hψ : Continuous ψ := (hC.mono inter_subset_left).domRestrict.subtype_mk _
  have hpoint (y : U) : e.symm (firstCoords ℝ d n (ψ y)) = (y : S) :=
    he.symm_firstCoords_firstCoords_apply y.property.1 y.val.property
  have htransport :
      ∃ D' : Delineation (fun k (y : U) ↦ P k (e.symm (firstCoords ℝ d n (ψ y)))),
        ∀ i, ∀ y z : U,
          q (e.symm (firstCoords ℝ d n (ψ y))) (D'.root i y) =
            q (e.symm (firstCoords ℝ d n (ψ z))) (D'.root i z) := by
    refine ⟨D.comp ψ hψ, fun i y z ↦ ?_⟩
    simpa only [Delineation.comp_root] using hq (Fin.cast (D.comp_count ψ hψ) i) (ψ y) (ψ z)
  simp only [hpoint] at htransport
  have hfamily : (fun k (y : U) ↦ P k (e.symm (firstCoords ℝ d n (ψ y)))) =
      (fun k (y : U) ↦ P k y) := by
    funext k y
    rw [hpoint y]
  rw [hfamily] at htransport
  exact ⟨U, hU, ⟨hxe, hxV⟩, htransport⟩

/-- Delineations in analytic chart coordinates glue over a preconnected base, preserving
quantities constant along their sections. The root counts and the constants may vary between
the chart-local constructions; the conclusion identifies and globalizes them.

For ambient polynomial order, instantiate `q` with `fun x t ↦ p.orderAt (Fin.cons t x)`.
No regularity of `q`, finiteness of the family, or coefficient continuity is required. -/
theorem exists_delineation_of_locally_chart (hS : IsPreconnected S)
    (hlocal : ∀ x ∈ S,
      ∃ e : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ),
        IsAnalyticChart d S e ∧ x ∈ e.source ∧
          ∃ V : Set (Fin d → ℝ), IsOpen V ∧ firstCoords ℝ n d (e x) ∈ V ∧
            ∃ D : Delineation (fun k (u : V) ↦ P k (e.symm (firstCoords ℝ d n u))),
              ∀ i, ∀ u v : V,
                q (e.symm (firstCoords ℝ d n u)) (D.root i u) =
                  q (e.symm (firstCoords ℝ d n v)) (D.root i v)) :
    ∃ D : Delineation (fun k (x : S) ↦ P k x),
      ∀ i, ∀ x y : S, q x (D.root i x) = q y (D.root i y) := by
  have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  apply exists_delineation_of_locally_const_on_sections
  intro x
  obtain ⟨e, he, hxe, V, hV, hxV, D, hq⟩ := hlocal x x.property
  exact he.exists_delineation_of_const_on_sections x.property hxe hV hxV D hq

end TauCeti
