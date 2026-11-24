/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.MaslovIndex

/-!
# Relabelling the regions and basepoints of a Heegaard region system

Local moves on a Heegaard diagram often change which complementary regions are separate: a tube
attached to the surface joins the two regions it connects, while the attaching curves and their
intersection points stay as they were. On the incidence data `TauCeti.HeegaardRegionSystem` such a
move is a relabelling of the regions along a surjective map `f : Region → Region'`
(`TauCeti.HeegaardRegionSystem.mapRegion`): the regions on the two sides of every arc are replaced
by their images under `f`, and the basepoints are placed in prescribed regions of the new system.
The intersection points, the curves through them and the order of the points along the curves
are unchanged, so the two systems have the same generators.

A domain `D'` of the relabelled system is read on the original one as `D' ∘ f`, which is
constant on the fibres of `f`. All local incidence quantities are compatible with this: the
boundaries of the `α`- and `β`-parts of `D'` are those of `D' ∘ f`, so `D'` connects `x` to `y`
exactly when `D' ∘ f` does (`TauCeti.HeegaardRegionSystem.isDomainBetween_mapRegion_iff`), and
the point measures agree. Only the Euler characteristics of the regions, which are external data,
need not be compatible: a tube joining two regions lowers the Euler characteristic of the union
by two. The Maslov index of `D'` for Euler characteristics `χ'` of the new regions is therefore
that of `D' ∘ f` for Euler characteristics `χ` of the old ones, corrected by the difference of
the two Euler sums (`TauCeti.HeegaardRegionSystem.maslovIndex_mapRegion`).

## Main definitions

* `TauCeti.HeegaardRegionSystem.mapRegion`: the system with its regions relabelled along a
  surjective map and its basepoints placed in given regions.

## Main results

* `TauCeti.HeegaardRegionSystem.isDomainBetween_mapRegion_iff`: domains of the relabelled system
  are those whose pullback is a domain.
* `TauCeti.HeegaardRegionSystem.mem_periodicDomains_mapRegion_iff`: periodic domains of the
  relabelled system are those avoiding its basepoints whose pullback has a boundary made of whole
  curves.
* `TauCeti.HeegaardRegionSystem.maslovIndex_mapRegion`: the Maslov index of a domain of the
  relabelled system.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v v' w w'

variable {n : ℕ} {Point : Type u} {Region : Type v} {Region' : Type v'} {Basepoint : Type w}
  {Basepoint' : Type w'} (H : HeegaardRegionSystem n Point Region Basepoint)

open Function

variable {f : Region → Region'} (hf : Surjective f) (b : Basepoint' → Region')

/-- The region system with its regions relabelled along a surjective map `f` and its basepoints in
the regions `b`: the regions on the two sides of each arc are replaced by their images under `f`,
and the intersection points and curves are kept. Identifying regions in this way models a move
that joins complementary regions, such as attaching a tube between them; taking `f = id` only
moves the basepoints.

This is an abbreviation so that the relabelled system visibly has the intersection data of `H`,
and hence the same type of generators, also to `simp` and `rw`. -/
abbrev mapRegion : HeegaardRegionSystem n Point Region' Basepoint' where
  toHeegaardIntersectionSystem := H.toHeegaardIntersectionSystem
  alphaNext := H.alphaNext
  alphaNext_isCycleOn := H.alphaNext_isCycleOn
  betaNext := H.betaNext
  betaNext_isCycleOn := H.betaNext_isCycleOn
  alphaLeft := f ∘ H.alphaLeft
  alphaRight := f ∘ H.alphaRight
  betaLeft := f ∘ H.betaLeft
  betaRight := f ∘ H.betaRight
  regionNonempty := H.regionNonempty.map f
  crossingCompatible p := by
    rcases isCrossingCompatible_iff.1 (H.crossingCompatible p) with
      ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
    · exact isCrossingCompatible_iff.2 <|
        Or.inl ⟨by simp [h₁], by simp [h₂], by simp [h₃], by simp [h₄]⟩
    · exact isCrossingCompatible_iff.2 <|
        Or.inr ⟨by simp [h₁], by simp [h₂], by simp [h₃], by simp [h₄]⟩
  regionCovered r' := by
    obtain ⟨r, rfl⟩ := hf r'
    rcases H.regionCovered r with ⟨p, hp⟩ | ⟨hP, hR⟩
    · exact Or.inl ⟨p, by rcases hp with hp | hp | hp | hp <;> simp [hp]⟩
    · exact Or.inr ⟨hP, hf.subsingleton⟩
  basepoint := b

/-- The `α`-part of the boundary of a domain of the relabelled system is that of its pullback. -/
@[simp]
theorem alphaBoundary_mapRegion (D : Region' → ℤ) :
    (H.mapRegion hf b).alphaBoundary D = H.alphaBoundary (D ∘ f) := by
  ext p
  simp

/-- The `β`-part of the boundary of a domain of the relabelled system is that of its pullback. -/
@[simp]
theorem betaBoundary_mapRegion (D : Region' → ℤ) :
    (H.mapRegion hf b).betaBoundary D = H.betaBoundary (D ∘ f) := by
  ext p
  simp

/-- The boundary of a `1`-chain on the `α`-arcs does not see the relabelling. -/
@[simp]
theorem alphaArcBoundary_mapRegion :
    (H.mapRegion hf b).alphaArcBoundary = H.alphaArcBoundary := by
  ext c q
  simp

/-- The boundary of a `1`-chain on the `β`-arcs does not see the relabelling. -/
@[simp]
theorem betaArcBoundary_mapRegion : (H.mapRegion hf b).betaArcBoundary = H.betaArcBoundary := by
  ext c q
  simp

/-- A domain of the relabelled system connects `x` to `y` exactly when its pullback along the
relabelling does. -/
theorem isDomainBetween_mapRegion_iff {x y : H.Generator} {D : Region' → ℤ} :
    (H.mapRegion hf b).IsDomainBetween x y D ↔ H.IsDomainBetween x y (D ∘ f) := by
  rw [(H.mapRegion hf b).isDomainBetween_iff, H.isDomainBetween_iff, alphaBoundary_mapRegion,
    betaBoundary_mapRegion, alphaArcBoundary_mapRegion, betaArcBoundary_mapRegion]

/-- A domain of the relabelled system is periodic exactly when it vanishes at the new basepoints
and the boundary of its pullback along the relabelling is a sum of whole curves. -/
theorem mem_periodicDomains_mapRegion_iff {P : Region' → ℤ} :
    P ∈ (H.mapRegion hf b).periodicDomains ↔ (∀ z, P (b z) = 0) ∧
      H.alphaArcBoundary (H.alphaBoundary (P ∘ f)) = 0 ∧
        H.betaArcBoundary (H.betaBoundary (P ∘ f)) = 0 := by
  simp only [mem_periodicDomains_iff, alphaBoundary_mapRegion, betaBoundary_mapRegion,
    alphaArcBoundary_mapRegion, betaArcBoundary_mapRegion]

/-- When the basepoints are moved along the relabelling, a domain of the relabelled system is
periodic exactly when its pullback is periodic. -/
theorem mem_periodicDomains_mapRegion_comp_iff {P : Region' → ℤ} :
    P ∈ (H.mapRegion hf (f ∘ H.basepoint)).periodicDomains ↔ P ∘ f ∈ H.periodicDomains := by
  rw [mem_periodicDomains_mapRegion_iff, mem_periodicDomains_iff]
  simp only [comp_apply]

/-- The point measures of a domain of the relabelled system are those of its pullback. -/
@[simp]
theorem pointMeasure_mapRegion (D : Region' → ℤ) :
    (H.mapRegion hf b).pointMeasure D = H.pointMeasure (D ∘ f) := by
  ext p
  simp

/-- The point measure of a domain of the relabelled system at a generator is that of its
pullback. -/
theorem generatorPointMeasure_mapRegion (x : H.Generator) (D : Region' → ℤ) :
    (H.mapRegion hf b).generatorPointMeasure x D = H.generatorPointMeasure x (D ∘ f) := by
  rw [(H.mapRegion hf b).generatorPointMeasure_apply x D, H.generatorPointMeasure_apply x,
    pointMeasure_mapRegion]

variable [Fintype Point] [DecidableEq Region] [Fintype Region] [DecidableEq Region']
  [Fintype Region']

/-- The Maslov index of a domain `D` of the relabelled system, for Euler characteristics `χ'` of
the new regions, is that of its pullback `D ∘ f` for Euler characteristics `χ` of the old regions,
corrected by the difference `∑ χ'(R') D(R') - ∑ χ(R) D(f R)` of the two Euler sums: the point
measures do not see the relabelling. -/
theorem maslovIndex_mapRegion (χ : Region → ℤ) (χ' : Region' → ℤ) (x y : H.Generator)
    (D : Region' → ℤ) :
    (H.mapRegion hf b).maslovIndex χ' x y D = H.maslovIndex χ x y (D ∘ f) +
      (∑ r', (χ' r' : ℚ) * D r' - ∑ r, (χ r : ℚ) * D (f r)) := by
  rw [(H.mapRegion hf b).maslovIndex_apply, H.maslovIndex_apply,
    (H.mapRegion hf b).eulerMeasure_eq_sub_sum_pointMeasure, H.eulerMeasure_eq_sub_sum_pointMeasure,
    pointMeasure_mapRegion, generatorPointMeasure_mapRegion, generatorPointMeasure_mapRegion]
  simp only [comp_apply]
  ring

end HeegaardRegionSystem

end TauCeti
