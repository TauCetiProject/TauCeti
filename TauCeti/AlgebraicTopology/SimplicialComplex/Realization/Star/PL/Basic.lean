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
directions of a link homeomorphism supplies PL formulas for the closed-star map and its inverse;
the corresponding homeomorphism packaging is in `Star.PL.Homeomorph`.

The formulas are on the ambient coordinate spaces and agree with the actual `closedStarMap`
on its whole domain. The ambient complexes and the target vertex type may be infinite.
Empty links are allowed: their stars consist only of the apex.

The constructions below do not assert that a link map is PL; callers provide ambient formulas and
their `IsPLOn` proofs.

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



private theorem coneToJoin_coneMap_eq
    (f : geometricLink K v → geometricLink L w) (F : (ι → ℝ) → (κ → ℝ))
    (hF : ∀ y : geometricLink K v, F (y.1.1 : ι → ℝ) = (f y).1.1)
    (x : closedStarRealization K {v}) :
    coneToJoin (Pi.single w 1) (coneMap F (starToCone v (x.1.1 : ι → ℝ))) =
      ((closedStarMap f x).1.1 : κ → ℝ) := by
  by_cases hx : x.1.1 v < 1
  · rw [starToCone_of_lt x hx, coneMap_smul F _ (sub_pos.mpr hx).ne',
      coneToJoin_apply, hF]
    ext j
    rw [closedStarMap_apply_of_lt f x hx j]
    by_cases hj : j = w <;> simp [hj]
  · rw [starToCone_of_not_lt x hx, coneMap_zero, coneToJoin_apply]
    rw [eq_starApex_of_not_lt K v hx, closedStarMap_starApex]
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
  have hout :=
    (isPiecewiseAffineOn_continuousAffineMap (coneToJoin (Pi.single w 1)) univ).comp
      hcone (mapsTo_univ _ _)
  exact ⟨(coneToJoin (Pi.single w 1)) ∘ coneMap F ∘ (starToCone v), hout,
    coneToJoin_coneMap_eq f F hF⟩

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

variable {ν : Type*} [DecidableEq ν]
  {N : AbstractSimplicialComplex ν} {u : ν}

/-- Two piecewise-linear radial closed-star maps compose piecewise linearly.

The returned ambient formula is piecewise linear on the source closed star and agrees there with
the radial extension of `g ∘ f`. Only compactness of the source link is required.
-/
theorem exists_isPLOn_closedStarMap_comp
    (hK : IsCompact (geometricLink K v))
    (f : geometricLink K v → geometricLink L w)
    (g : geometricLink L w → geometricLink N u)
    (F : (ι → ℝ) → (κ → ℝ))
    (hF : ∀ y : geometricLink K v, F (y.1.1 : ι → ℝ) = (f y).1.1)
    (hFpl : IsPLOn F (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ))))
    (G : (κ → ℝ) → (ν → ℝ))
    (hG : ∀ y : geometricLink L w, G (y.1.1 : κ → ℝ) = (g y).1.1)
    (hGpl : IsPLOn G (range (fun y : geometricLink L w => (y.1.1 : κ → ℝ)))) :
    ∃ H : (ι → ℝ) → (ν → ℝ),
      IsPLOn H (range (fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ))) ∧
        ∀ x : closedStarRealization K {v},
          H (x.1.1 : ι → ℝ) = (closedStarMap (g ∘ f) x).1.1 := by
  have hGF : IsPLOn (G ∘ F)
      (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ))) := by
    apply hGpl.comp hFpl
    rintro _ ⟨y, rfl⟩
    exact ⟨f y, (hF y).symm⟩
  exact exists_isPLOn_closedStarMap hK (g ∘ f) (G ∘ F)
    (fun y => by simp [hF, hG]) hGF

end AbstractSimplicialComplex
