/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Homeomorph
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Cone
public import TauCeti.Topology.PL.Cone

/-!
# Piecewise-linear radial maps of vertex stars

A finite piecewise-affine coordinate formula for a map of geometric vertex links extends to
such a formula for its radial map of closed stars, including at the apex. For compact links, a
local PL formula suffices. Applying the construction to both
directions of a link homeomorphism supplies PL formulas for the closed-star homeomorphism
and its inverse. Restricting these formulas to open stars supplies local PL chart maps.

The formulas are on the ambient coordinate spaces and agree with the actual `closedStarMap`
on its whole domain. The ambient complexes and the target vertex type may be infinite.
Empty links are allowed: their stars consist only of the apex.

The construction factors through `TauCeti.coneMap`: remove the apex coordinate and record
the remaining mass as height, then reinsert the target apex coordinate after coning the
link formula. These two changes of coordinates are continuous affine maps.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
  Springer (1972), Chapters 1–2, especially “Pseudo-Radial Projection”, pp. 20–21.

The radial star map is from `Realization.Star.Homeomorph`; finite PL decompositions on
compact coordinate sets and their conical extensions are from `TauCeti.Topology.PL.Cone`.
-/

public section

noncomputable section

open Set TauCeti

namespace AbstractSimplicialComplex

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {K : AbstractSimplicialComplex ι} {L : AbstractSimplicialComplex κ} {v : ι} {w : κ}

/-- Reinsert the target apex, whose coordinate is one minus the cone height. -/
private def coneToStar (w : κ) : ((κ → ℝ) × ℝ) →ᴬ[ℝ] (κ → ℝ) :=
  let apex : κ → ℝ := Pi.single w 1
  let linear : ((κ → ℝ) × ℝ) →L[ℝ] (κ → ℝ) :=
    ContinuousLinearMap.fst ℝ (κ → ℝ) ℝ -
      (ContinuousLinearMap.snd ℝ (κ → ℝ) ℝ).smulRight apex
  linear.toContinuousAffineMap + ContinuousAffineMap.const ℝ ((κ → ℝ) × ℝ) apex

private theorem coneToStar_apply (w : κ) (p : (κ → ℝ) × ℝ) :
    coneToStar w p = p.1 - p.2 • Pi.single w 1 + Pi.single w 1 := (rfl)


private theorem coneToStar_coneMap_eq
    (f : geometricLink K v → geometricLink L w) (F : (ι → ℝ) → (κ → ℝ))
    (hF : ∀ y : geometricLink K v, F (y.1.1 : ι → ℝ) = (f y).1.1)
    (x : closedStarRealization K {v}) :
    coneToStar w (coneMap F (starToCone v (x.1.1 : ι → ℝ))) =
      ((closedStarMap f x).1.1 : κ → ℝ) := by
  by_cases hx : x.1.1 v < 1
  · rw [starToCone_of_lt x hx, coneMap_smul F _ (sub_pos.mpr hx).ne',
      coneToStar_apply, hF]
    ext j
    rw [closedStarMap_apply_of_lt f x hx j]
    by_cases hj : j = w <;> simp [hj]
  · rw [starToCone_of_not_lt x hx, coneMap_zero, coneToStar_apply]
    have he : x.1 = vertex K v := (Realization.eq_vertex_iff K x.1 v).mpr
      (le_antisymm (Realization.le_one K x.1 v) (not_lt.mp hx))
    have hex : x = starApex K v := Subtype.ext (by simpa only [starApex_val] using he)
    rw [hex, closedStarMap_starApex]
    ext j
    simp [vertex_val, Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- A finite piecewise-affine coordinate formula for a link map extends to a finite
piecewise-affine formula for its radial map on the entire closed star. No finiteness or
compactness of either complex or vertex type is needed. -/
theorem exists_isPiecewiseAffineOn_closedStarMap
    (f : geometricLink K v → geometricLink L w) (F : (ι → ℝ) → (κ → ℝ))
    (hF : ∀ y : geometricLink K v, F (y.1.1 : ι → ℝ) = (f y).1.1)
    (hf : IsPiecewiseAffineOn F (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ)))) :
    ∃ G : (ι → ℝ) → (κ → ℝ),
      IsPiecewiseAffineOn G
        (range (fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ))) ∧
      ∀ x : closedStarRealization K {v}, G (x.1.1 : ι → ℝ) = (closedStarMap f x).1.1 := by
  let S := range (fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ))
  have hin : MapsTo (starToCone v) S
      (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ))).cone := by
    rintro _ ⟨x, rfl⟩
    exact starToCone_mem x
  have hcone := hf.coneMap.comp
    (isPiecewiseAffineOn_continuousAffineMap (starToCone v) S) hin
  have hout := (isPiecewiseAffineOn_continuousAffineMap (coneToStar w) univ).comp
    hcone (mapsTo_univ _ _)
  exact ⟨(coneToStar w) ∘ coneMap F ∘ (starToCone v), hout,
    coneToStar_coneMap_eq f F hF⟩

/-- A PL coordinate formula on a geometric link extends to a PL coordinate formula on
its entire closed star, including the apex, whenever the link is compact. Neither ambient
vertex type needs to be finite. Finiteness of the link's face collection supplies compactness. -/
theorem exists_isPLOn_closedStarMap
    (hc : IsCompact (geometricLink K v))
    (f : geometricLink K v → geometricLink L w) (F : (ι → ℝ) → (κ → ℝ))
    (hF : ∀ y : geometricLink K v, F (y.1.1 : ι → ℝ) = (f y).1.1)
    (hf : IsPLOn F (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ)))) :
    ∃ G : (ι → ℝ) → (κ → ℝ),
      IsPLOn G (range (fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ))) ∧
      ∀ x : closedStarRealization K {v}, G (x.1.1 : ι → ℝ) = (closedStarMap f x).1.1 := by
  have : CompactSpace (geometricLink K v) := isCompact_iff_compactSpace.mp hc
  have hcoord : IsCompact (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ))) :=
    isCompact_range ((continuous_realization_coe K).comp continuous_subtype_val)
  obtain ⟨G, hG, heq⟩ := exists_isPiecewiseAffineOn_closedStarMap f F hF
    (hf.isPiecewiseAffineOn_of_isCompact hcoord)
  exact ⟨G, hG.isPLOn, heq⟩

end AbstractSimplicialComplex
