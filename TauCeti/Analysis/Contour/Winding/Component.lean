/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Kim Morrison
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Connected.Basic
import TauCeti.Analysis.Contour.Curve.Distance
import TauCeti.Analysis.Contour.Winding.LocallyConstant
import TauCeti.Analysis.Contour.Winding.Vanishing

/-!
# The winding number is constant on off-curve components, and zero on the unbounded one

For a closed curve `γ` (so `γ a = γ b`) continuous on `Set.uIcc a b`, differentiable off a countable
set, with interval-integrable derivative, the generalized winding number
`fun w ↦ windingNumber γ a b w` is locally constant on the complement of the curve
(`isLocallyConstant_windingNumber_of_closed`). Locally constant functions are constant on
preconnected sets, so the winding number takes a single value on each connected component of the
complement (`windingNumber_eq_of_avoidance_of_isPreconnected`). On the **unbounded** component it is
that far-field value, which `windingNumber_eventually_zero_cocompact` pins to `0`
(`windingNumber_eq_zero_of_avoidance_of_isPreconnected_of_unbounded`). These are the two Layer-0
geometric facts the roadmap records for a point off the curve — the winding number is a locally
constant integer, homotopy-invariant within a component, and `0` on the unbounded component.

## Main results

* `TauCeti.Contour.windingNumber_eq_of_avoidance_of_isPreconnected` — the winding number agrees at
  any two points of a preconnected set that avoids the curve.
* `TauCeti.Contour.windingNumber_eq_zero_of_avoidance_of_isPreconnected_of_unbounded` — the
  winding number vanishes on a preconnected unbounded set that avoids the curve (the unbounded
  component).

## Provenance

Built on the AINTLIB-migrated `isLocallyConstant_windingNumber_of_closed`
(`Winding/LocallyConstant.lean`) and `windingNumber_eventually_zero_cocompact`
(`Winding/Vanishing.lean`), corresponding to the `WindingArgDiff.lean` and `NullHomologous.lean`
files of the AINTLIB `LeanModularForms` development. The constancy on a component transports the
locally-constant statement to a preconnected subset via the open inclusion of the off-curve subtype
(`IsPreconnected.preimage_of_isOpenMap`), and the unbounded-component vanishing extracts a far-field
point of the component from the cocompact eventual-zero statement.
-/

public section

open Complex MeasureTheory Set

open scoped Interval

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ}

/-- **The winding number is constant on a preconnected off-curve set.** For a closed curve `γ`
(differentiable off a countable set `P`, continuous on `Set.uIcc a b`, with interval-integrable
derivative), if `S` avoids the curve and is preconnected, then the generalized winding number takes
the same value at any two points of `S`. In particular it is constant on each connected component of
the complement of the curve — the homotopy-invariance-within-a-component form of the Layer-0 fact
that the winding number off the curve is locally constant. -/
theorem windingNumber_eq_of_avoidance_of_isPreconnected {S : Set ℂ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    (hSoff : S ⊆ {w : ℂ | ∀ t ∈ uIcc a b, γ t ≠ w})
    (hSconn : IsPreconnected S) {w₁ w₂ : ℂ} (hw₁ : w₁ ∈ S) (hw₂ : w₂ ∈ S) :
    windingNumber γ a b w₁ = windingNumber γ a b w₂ := by
  have hlc := isLocallyConstant_windingNumber_of_closed hclosed hP hγ_cont hγ_diff hderiv_int
  -- The off-curve set is open (the complement of the compact curve image), so `Subtype.val` from
  -- the subtype of off-curve points is an injective open map; transport preconnectedness of `S`
  -- along its preimage.
  have hrange : S ⊆ Set.range (Subtype.val : {w : ℂ // ∀ t ∈ uIcc a b, γ t ≠ w} → ℂ) := by
    rw [Subtype.range_val_subtype]; exact hSoff
  have hTconn : IsPreconnected
      (Subtype.val ⁻¹' S : Set {w : ℂ // ∀ t ∈ uIcc a b, γ t ≠ w}) :=
    hSconn.preimage_of_isOpenMap Subtype.val_injective
      (isOpen_setOf_avoidance hγ_cont).isOpenMap_subtype_val hrange
  exact hlc.apply_eq_of_isPreconnected hTconn
    (x := ⟨w₁, hSoff hw₁⟩) (y := ⟨w₂, hSoff hw₂⟩) hw₁ hw₂

/-- **The winding number vanishes on the unbounded component.** For a closed curve `γ`
(differentiable off a countable set `P`, continuous on `Set.uIcc a b`, with interval-integrable
derivative), if `S` avoids the curve, is preconnected, and is unbounded, then the generalized
winding number is `0` throughout `S`. Applied to the (necessarily unbounded) exterior connected
component of the complement, this is the Layer-0 fact that the winding number is `0` on the
unbounded component: constancy pins the value across the component, and it must equal the far-field
value, which the cocompact eventual-zero statement forces to be `0`. -/
theorem windingNumber_eq_zero_of_avoidance_of_isPreconnected_of_unbounded {S : Set ℂ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    (hSoff : S ⊆ {w : ℂ | ∀ t ∈ uIcc a b, γ t ≠ w})
    (hSconn : IsPreconnected S) (hSunb : ¬ Bornology.IsBounded S) {w : ℂ} (hw : w ∈ S) :
    windingNumber γ a b w = 0 := by
  -- The set where `γ` is avoided and the winding number is `0` is cocompact, so its complement is
  -- contained in a compact — hence bounded — set `K`.
  obtain ⟨K, hK, hKsub⟩ := Filter.mem_cocompact'.mp
    (windingNumber_eventually_zero_cocompact hclosed hP hγ_cont hγ_diff hderiv_int)
  -- An unbounded `S` cannot sit inside the bounded complement, so it meets the cocompact zero set.
  have hex : ∃ w' ∈ S, (∀ t ∈ uIcc a b, γ t ≠ w') ∧ windingNumber γ a b w' = 0 := by
    by_contra hcon
    exact hSunb <| hK.isBounded.subset fun x hxS ↦ hKsub fun hgood ↦ hcon ⟨x, hxS, hgood⟩
  obtain ⟨w', hw'S, _, hw'zero⟩ := hex
  rw [windingNumber_eq_of_avoidance_of_isPreconnected hclosed hP hγ_cont hγ_diff hderiv_int
    hSoff hSconn hw hw'S, hw'zero]

end TauCeti.Contour
