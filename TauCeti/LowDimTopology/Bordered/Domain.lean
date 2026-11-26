/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.AddSubgroup.NonnegativeCoset
public import TauCeti.GroupTheory.Perm.Basic
public import TauCeti.LowDimTopology.Bordered.Generator
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.RefinedGrading
public import TauCeti.LowDimTopology.Heegaard.Triple.Basic
import Mathlib.Tactic.Abel
import TauCeti.Algebra.BigOperators.Fin

/-!
# Domains and provincial admissibility of bordered Heegaard diagrams

A bordered Heegaard diagram of Lipshitz, Ozsváth and Thurston is a compact surface `Σ` of genus
`g` with one boundary circle, carrying `g` `β`-circles and an `α`-system of `α`-arcs, with their
ends on `∂Σ`, and `α`-circles. The `n` ends of the arcs cut the boundary circle, opened at the
basepoint `z ∈ ∂Σ`, into the pointed matched circle `Z`. The curves cut `Σ` into regions, and a
*domain* is an integral combination of regions. This file records the incidence data that domains
need, in the form of `TauCeti.HeegaardRegionSystem` for closed diagrams, and develops domains,
their boundary multiplicities, periodic domains and the two admissibility conditions of
Lipshitz, Ozsváth and Thurston on top of it.

The data extends `TauCeti.BorderedHeegaardIntersectionSystem`. Orient every curve. On an
`α`-circle the intersection points form a cycle, as for a closed diagram. On an `α`-arc they are
in order from its initial end to its terminal end, and we close the arc into a cycle through one
extra node `Sum.inr a` standing for the boundary: the nodes are `Point ⊕ Arc`, and
`alphaNext : Equiv.Perm (Point ⊕ Arc)` cycles through the points of each `α`-curve, and for an arc
`a` through the node `Sum.inr a` too. The segment of `α` *starting* at a node `v` runs to
`alphaNext v`; for the node `Sum.inr a` this is the initial segment of `a`, and the segment
starting at `alphaNext.symm (Sum.inr a)` is its terminal segment. The ends of the arcs are the
points `0, …, n - 1` of `Z`, in the order of the boundary orientation of `∂Σ`
(`TauCeti.BorderedHeegaardRegionSystem.arcEnd`). They cut `∂Σ - z` into the intervals
`0, …, n`, the interval `i` lying between the points `i - 1` and `i`; the two outer intervals `0`
and `n` lie on either side of `z`, in the region containing `z`. Each segment and each interval
has a region beside it, and the two segments of an arc at an end have the regions of the two
intervals at that end beside them.

The `α`-part of the boundary of a domain `D` is the `1`-chain on the `α`-segments whose
coefficient on the segment starting at `v` is the multiplicity of `D` to its left minus that to its
right; its `β`-part is defined in the same way. A domain *connects* `x` to `y` when, at each
intersection point, the boundary of its `α`-part is `y - x` and that of its `β`-part is `x - y`.
Nothing is asked at the boundary nodes, where the boundary of the `α`-part is balanced by the part
`∂^∂ D` of `∂D` along `∂Σ`. Lipshitz, Ozsváth and Thurston record `∂^∂ D` as a class in
`H₁(Z, a)`; as in `TauCeti.StrandGradingGroup`, we record such a class by its boundary in the
points of `Z`, the *border class* `TauCeti.BorderedHeegaardRegionSystem.borderClass`, given by the
differences of the multiplicities of `D` at the intervals on either side of each point.

The border class of a domain from `x` to `y` satisfies the counterpart for domains of the relation
`M_*(∂[φ]) = M(T) - M(S)` for a strand diagram `φ : S → T`: added up over the two ends of each
arc, it is the indicator of the arcs occupied by `y` minus that of the arcs occupied by `x`
(`TauCeti.BorderedHeegaardRegionSystem.IsDomainBetween.pushBoundary_borderClass`). In particular
the border class of a periodic domain cancels along every matched pair.

A domain is *periodic* when its multiplicity at the basepoint region is zero and its boundary is
made of whole `α`-arcs, `α`-circles, `β`-circles and a part along `∂Σ`; it is *provincial* when,
moreover, its border class vanishes, equivalently when it has multiplicity zero at every region
along the boundary. The boundary of a provincial periodic domain contains no `α`-arc. A diagram is
*admissible* when every nonzero periodic domain has both positive and negative coefficients, and
*provincially admissible* when every nonzero provincial periodic domain does. Domains from `x` to
`y` with prescribed basepoint multiplicity form a coset of the periodic domains, and those with
prescribed basepoint multiplicity and border class a coset of the provincial periodic domains. So
in an admissible diagram there are finitely many nonnegative domains from `x` to `y` with given
basepoint multiplicity, and in a provincially admissible diagram finitely many with given
basepoint multiplicity and border class: the finiteness behind the type `D` structure and the type
`A` module of the diagram, respectively.

As for closed diagrams, the data does not assert that the region labels are the connected
components of the complement of the curves of an actual bordered diagram; that identification is
separate.

## Main definitions

* `TauCeti.BorderedHeegaardRegionSystem`: the incidence data of a bordered Heegaard diagram.
* `TauCeti.BorderedHeegaardRegionSystem.matching`: the arc ending at each point of `Z`.
* `TauCeti.BorderedHeegaardRegionSystem.alphaBoundary`,
  `TauCeti.BorderedHeegaardRegionSystem.betaBoundary`: the `α`- and `β`-parts of the boundary of a
  domain.
* `TauCeti.BorderedHeegaardRegionSystem.borderClass`: the boundary of the class of `∂^∂ D`.
* `TauCeti.BorderedHeegaardRegionSystem.IsDomainBetween`: `D` is a domain connecting `x` to `y`.
* `TauCeti.BorderedHeegaardRegionSystem.periodicDomains`,
  `TauCeti.BorderedHeegaardRegionSystem.provincialPeriodicDomains`: the periodic and the provincial
  periodic domains.
* `TauCeti.BorderedHeegaardRegionSystem.Admissible`,
  `TauCeti.BorderedHeegaardRegionSystem.ProvinciallyAdmissible`: the two admissibility conditions.

## Main results

* `TauCeti.BorderedHeegaardRegionSystem.IsDomainBetween.pushBoundary_borderClass`: the border
  class of a domain from `x` to `y` adds up over each matched pair to `o(y) - o(x)`.
* `TauCeti.BorderedHeegaardRegionSystem.pushBoundary_borderClass_of_mem_periodicDomains`: the
  border class of a periodic domain cancels along each matched pair.
* `TauCeti.BorderedHeegaardRegionSystem.sum_borderClass`: every border class has total sum zero.
* `TauCeti.BorderedHeegaardRegionSystem.alphaBoundary_eq_zero_of_mem_provincialPeriodicDomains`:
  the boundary of a provincial periodic domain contains no `α`-arc.
* `TauCeti.BorderedHeegaardRegionSystem.IsDomainBetween.sub_mem_periodicDomains_iff`,
  `TauCeti.BorderedHeegaardRegionSystem.IsDomainBetween.sub_mem_provincialPeriodicDomains_iff`:
  the coset descriptions of the domains from `x` to `y`.
* In the namespace `TauCeti.BorderedHeegaardRegionSystem`,
  `Admissible.finite_setOf_isDomainBetween_basepoint_eq_nonneg` and
  `ProvinciallyAdmissible.finite_setOf_isDomainBetween_basepoint_eq_borderClass_eq_nonneg`:
  the finiteness of nonnegative domains, and
  `provinciallyAdmissible_iff_finite_setOf_mem_provincialPeriodicDomains_nonneg`: the converse.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), Chapter 4:
  bordered Heegaard diagrams, their domains and the boundary multiplicities `∂^∂ B`, periodic and
  provincial periodic domains, admissibility and provincial admissibility, and the finiteness of
  positive domains in (provincially) admissible diagrams.
-/

public section

open Finset

namespace TauCeti

universe u v w r

/-- Pushed forward along the `α`-curves, the `0`-chain of a generator is `1` on an `α`-arc it
occupies and `0` on any other `α`-arc: the points of a generator lie on distinct `α`-curves. -/
theorem BorderedHeegaardIntersectionSystem.pushBoundary_alpha_generatorChain_inl {g : ℕ}
    {Arc : Type u} {AlphaCircle : Type v} {Point : Type w}
    (H : BorderedHeegaardIntersectionSystem g Arc AlphaCircle Point) [Fintype Point]
    [DecidableEq Arc] [DecidableEq AlphaCircle] (x : H.Generator) (a : Arc) :
    StrandGradingGroup.pushBoundary H.alpha (H.generatorChain x) (.inl a) =
      if a ∈ H.occupied x then 1 else 0 := by
  classical
  have h : H.generatorChain x = fun q => if q ∈ univ.image x.point then 1 else 0 := by
    ext q
    simp only [generatorChain_apply, mem_image, mem_univ, true_and]
    exact if_congr ⟨fun h => ⟨_, h⟩, by rintro ⟨j, rfl⟩; simp⟩ rfl rfl
  have hinj : Set.InjOn H.alpha (univ.image x.point : Finset Point) := by
    simp only [coe_image, coe_univ, Set.image_univ]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    rw [x.alpha_comp_point_injective hij]
  rw [h, StrandGradingGroup.pushBoundary_indicator hinj]
  simp [image_image]

/-- The incidence data of a bordered Heegaard diagram of genus `g` whose boundary carries the `n`
ends of the `α`-arcs. On top of the intersection data it records the ends of each `α`-arc as
points `0, …, n - 1` of the boundary, in the order of the boundary orientation; the next node
along each oriented `α`-curve, where an `α`-arc `a` is closed up through the extra node
`Sum.inr a` at the boundary; the next point along each oriented `β`-circle; the regions to the
left and to the right of the segment starting at each node; and the region beside each of the
intervals `0, …, n` into which the ends cut the boundary circle opened at the basepoint. Region
labels agree around each crossing and at each end of an arc, the two outer intervals lie in the
same region, that of the basepoint, and each region meets a segment or the boundary. The data does
not assert that the labels are the connected complementary regions of a particular surface
realization; that requires a separate identification. -/
@[ext]
structure BorderedHeegaardRegionSystem (g n : ℕ) (Arc : Type u) (AlphaCircle : Type v)
    (Point : Type w) (Region : Type r)
    extends BorderedHeegaardIntersectionSystem g Arc AlphaCircle Point where
  /-- The ends of the `α`-arcs as the points of the boundary: `Sum.inl a` is the initial end of the
  arc `a` and `Sum.inr a` its terminal end. -/
  arcEnd : Arc ⊕ Arc ≃ Fin n
  /-- The next node along the oriented `α`-curve; an `α`-arc `a` runs from the node `Sum.inr a`
  through its intersection points back to `Sum.inr a`. -/
  alphaNext : Equiv.Perm (Point ⊕ Arc)
  /-- The nodes on each `α`-curve form one cycle of `alphaNext`. -/
  alphaNext_isCycleOn (c : Arc ⊕ AlphaCircle) :
    alphaNext.IsCycleOn {v | Sum.elim alpha Sum.inl v = c}
  /-- The next intersection point along the oriented `β`-circle. -/
  betaNext : Equiv.Perm Point
  /-- The intersection points on a nonempty `β`-circle form one cycle of `betaNext`; empty fibres
  satisfy this condition vacuously. -/
  betaNext_isCycleOn (j : Fin g) : betaNext.IsCycleOn {p | beta p = j}
  /-- The region to the left of the `α`-segment starting at a node. -/
  alphaLeft : Point ⊕ Arc → Region
  /-- The region to the right of the `α`-segment starting at a node. -/
  alphaRight : Point ⊕ Arc → Region
  /-- The region to the left of the `β`-segment starting at an intersection point. -/
  betaLeft : Point → Region
  /-- The region to the right of the `β`-segment starting at an intersection point. -/
  betaRight : Point → Region
  /-- The region beside the interval `i` of the boundary, between the points `i - 1` and `i`. -/
  borderRegion : Fin (n + 1) → Region
  /-- The four region labels around each crossing of an `α`- and a `β`-curve agree. -/
  crossingCompatible (p : Point) :
    HeegaardRegionSystem.IsCrossingCompatible alphaNext alphaLeft alphaRight betaNext
      betaLeft betaRight (.inl p) p
  /-- The initial segment of an arc leaves the boundary with the interval below its initial end on
  its left. -/
  alphaLeft_inr (a : Arc) : alphaLeft (.inr a) = borderRegion (arcEnd (.inl a)).castSucc
  /-- The initial segment of an arc leaves the boundary with the interval above its initial end on
  its right. -/
  alphaRight_inr (a : Arc) : alphaRight (.inr a) = borderRegion (arcEnd (.inl a)).succ
  /-- The terminal segment of an arc reaches the boundary with the interval above its terminal end
  on its left. -/
  alphaLeft_symm_inr (a : Arc) :
    alphaLeft (alphaNext.symm (.inr a)) = borderRegion (arcEnd (.inr a)).succ
  /-- The terminal segment of an arc reaches the boundary with the interval below its terminal end
  on its right. -/
  alphaRight_symm_inr (a : Arc) :
    alphaRight (alphaNext.symm (.inr a)) = borderRegion (arcEnd (.inr a)).castSucc
  /-- The two outer intervals lie on either side of the basepoint, in the same region. -/
  borderRegion_last : borderRegion (Fin.last n) = borderRegion 0
  /-- Every region meets an `α`-segment, a `β`-segment or the boundary. -/
  regionCovered (r : Region) :
    (∃ v, alphaLeft v = r ∨ alphaRight v = r) ∨ (∃ p, betaLeft p = r ∨ betaRight p = r) ∨
      ∃ i, borderRegion i = r

namespace BorderedHeegaardRegionSystem

variable {g n : ℕ} {Arc : Type u} {AlphaCircle : Type v} {Point : Type w} {Region : Type r}
  (H : BorderedHeegaardRegionSystem g n Arc AlphaCircle Point Region)

/-! ### Curves and ends -/

/-- The `α`-curve of a node: the curve of an intersection point, and the arc `a` for the boundary
node `Sum.inr a`. -/
def alphaCurve : Point ⊕ Arc → Arc ⊕ AlphaCircle :=
  Sum.elim H.alpha Sum.inl

@[simp]
theorem alphaCurve_inl (p : Point) : H.alphaCurve (.inl p) = H.alpha p :=
  (rfl)

@[simp]
theorem alphaCurve_inr (a : Arc) : H.alphaCurve (.inr a) = .inl a :=
  (rfl)

/-- The nodes on each `α`-curve form one cycle of `alphaNext`. -/
theorem alphaNext_isCycleOn_alphaCurve (c : Arc ⊕ AlphaCircle) :
    H.alphaNext.IsCycleOn {v | H.alphaCurve v = c} :=
  H.alphaNext_isCycleOn c

/-- The successor along an `α`-curve stays on that curve. -/
@[simp]
theorem alphaCurve_alphaNext (v : Point ⊕ Arc) : H.alphaCurve (H.alphaNext v) = H.alphaCurve v :=
  (H.alphaNext_isCycleOn_alphaCurve (H.alphaCurve v)).1.mapsTo rfl

/-- The predecessor along an `α`-curve stays on that curve. -/
@[simp]
theorem alphaCurve_alphaNext_symm (v : Point ⊕ Arc) :
    H.alphaCurve (H.alphaNext.symm v) = H.alphaCurve v := by
  simpa using (H.alphaCurve_alphaNext (H.alphaNext.symm v)).symm

/-- The successor along a `β`-circle stays on that circle. -/
@[simp]
theorem beta_betaNext (p : Point) : H.beta (H.betaNext p) = H.beta p :=
  (H.betaNext_isCycleOn (H.beta p)).1.mapsTo rfl

/-- The predecessor along a `β`-circle stays on that circle. -/
@[simp]
theorem beta_betaNext_symm (p : Point) : H.beta (H.betaNext.symm p) = H.beta p := by
  simpa using (H.beta_betaNext (H.betaNext.symm p)).symm

/-- The matching of the boundary points: the `α`-arc ending at each point. The two ends of each arc
form a matched pair, as for the matching `M` of the matched subalgebra
`TauCeti.StrandsAlgebra.matchedSubalgebra` and of the idempotents
`TauCeti.BorderedHeegaardIntersectionSystem.typeAIdem`. -/
def matching (i : Fin n) : Arc :=
  Sum.elim id id (H.arcEnd.symm i)

@[simp]
theorem matching_arcEnd_inl (a : Arc) : H.matching (H.arcEnd (.inl a)) = a := by
  simp [matching]

@[simp]
theorem matching_arcEnd_inr (a : Arc) : H.matching (H.arcEnd (.inr a)) = a := by
  simp [matching]

/-- The points matched to an arc are its two ends. -/
theorem matching_eq_iff {i : Fin n} {a : Arc} :
    H.matching i = a ↔ i = H.arcEnd (.inl a) ∨ i = H.arcEnd (.inr a) := by
  obtain ⟨e, rfl⟩ := H.arcEnd.surjective i
  rcases e with b | b <;> simp [eq_comm]

/-! ### Boundaries of domains -/

section Boundary

/-- The `α`-part `∂D ∩ α` of the boundary of a domain, as a `1`-chain on the `α`-segments: its
coefficient on the segment starting at the node `v` is the multiplicity of `D` to the left of the
segment minus the multiplicity to its right. -/
def alphaBoundary : (Region → ℤ) →+ (Point ⊕ Arc → ℤ) where
  toFun D v := D (H.alphaLeft v) - D (H.alphaRight v)
  map_zero' := by ext; simp
  map_add' D E := by ext; simp only [Pi.add_apply]; abel

/-- The `β`-part `∂D ∩ β` of the boundary of a domain, as a `1`-chain on the `β`-segments: its
coefficient on the segment starting at `p` is the multiplicity of `D` to the left of the segment
minus the multiplicity to its right. -/
def betaBoundary : (Region → ℤ) →+ (Point → ℤ) where
  toFun D p := D (H.betaLeft p) - D (H.betaRight p)
  map_zero' := by ext; simp
  map_add' D E := by ext; simp only [Pi.add_apply]; abel

/-- The boundary of the class of the part `∂^∂ D` of the boundary of a domain along `∂Σ`: its
coefficient at the point `i` is the multiplicity of `D` at the interval below `i` minus that at the
interval above `i`. When the basepoint multiplicity of `D` is zero, these differences determine the
multiplicities along the whole boundary. A chord running up from `s` to `t` has border class
`[t] - [s]`, the boundary of its class in the convention of `TauCeti.StrandGradingGroup`. -/
def borderClass : (Region → ℤ) →+ (Fin n → ℤ) where
  toFun D i := D (H.borderRegion i.castSucc) - D (H.borderRegion i.succ)
  map_zero' := by ext; simp
  map_add' D E := by ext; simp only [Pi.add_apply]; abel

@[simp]
theorem alphaBoundary_apply (D : Region → ℤ) (v : Point ⊕ Arc) :
    H.alphaBoundary D v = D (H.alphaLeft v) - D (H.alphaRight v) :=
  (rfl)

@[simp]
theorem betaBoundary_apply (D : Region → ℤ) (p : Point) :
    H.betaBoundary D p = D (H.betaLeft p) - D (H.betaRight p) :=
  (rfl)

@[simp]
theorem borderClass_apply (D : Region → ℤ) (i : Fin n) :
    H.borderClass D i = D (H.borderRegion i.castSucc) - D (H.borderRegion i.succ) :=
  (rfl)

/-- The whole surface has no `α`-boundary. -/
@[simp]
theorem alphaBoundary_one : H.alphaBoundary 1 = 0 := by
  ext
  simp

/-- The whole surface has no `β`-boundary. -/
@[simp]
theorem betaBoundary_one : H.betaBoundary 1 = 0 := by
  ext
  simp

/-- The whole surface has border class zero. -/
@[simp]
theorem borderClass_one : H.borderClass 1 = 0 := by
  ext
  simp

/-- The boundary of a `1`-chain on the `α`-segments, indexed by starting nodes. The segment
starting at `v` ends at `alphaNext v`, so the coefficient at `w` is that of the segment ending at
`w` minus that of the segment starting at `w`. -/
def alphaArcBoundary : (Point ⊕ Arc → ℤ) →+ (Point ⊕ Arc → ℤ) where
  toFun c w := c (H.alphaNext.symm w) - c w
  map_zero' := by ext; simp
  map_add' c d := by ext; simp only [Pi.add_apply]; abel

/-- The boundary of a `1`-chain on the `β`-segments, indexed by starting points. -/
def betaArcBoundary : (Point → ℤ) →+ (Point → ℤ) where
  toFun c q := c (H.betaNext.symm q) - c q
  map_zero' := by ext; simp
  map_add' c d := by ext; simp only [Pi.add_apply]; abel

@[simp]
theorem alphaArcBoundary_apply (c : Point ⊕ Arc → ℤ) (w : Point ⊕ Arc) :
    H.alphaArcBoundary c w = c (H.alphaNext.symm w) - c w :=
  (rfl)

@[simp]
theorem betaArcBoundary_apply (c : Point → ℤ) (q : Point) :
    H.betaArcBoundary c q = c (H.betaNext.symm q) - c q :=
  (rfl)

/-- At every intersection point, the boundaries of the `α`- and `β`-parts of the boundary of a
domain cancel. -/
theorem boundary_boundary_eq_zero (D : Region → ℤ) (p : Point) :
    H.alphaArcBoundary (H.alphaBoundary D) (.inl p) +
      H.betaArcBoundary (H.betaBoundary D) p = 0 :=
  (H.crossingCompatible p).sum_eq_zero D

/-- A `1`-chain on the `α`-segments is a cycle exactly when it is a combination of whole
`α`-curves, that is, constant along each `α`-arc and each `α`-circle. -/
theorem alphaArcBoundary_eq_zero_iff (c : Point ⊕ Arc → ℤ) :
    H.alphaArcBoundary c = 0 ↔ ∃ a : Arc ⊕ AlphaCircle → ℤ, ∀ v, c v = a (H.alphaCurve v) := by
  simpa [funext_iff] using
    H.alphaNext.forall_comp_symm_sub_eq_zero_iff H.alphaNext_isCycleOn_alphaCurve c

/-- A `1`-chain on the `β`-segments is a cycle exactly when it is a combination of whole
`β`-circles. -/
theorem betaArcBoundary_eq_zero_iff (c : Point → ℤ) :
    H.betaArcBoundary c = 0 ↔ ∃ b : Fin g → ℤ, ∀ p, c p = b (H.beta p) := by
  simpa [funext_iff] using H.betaNext.forall_comp_symm_sub_eq_zero_iff H.betaNext_isCycleOn c

/-- Around an `α`-arc the boundary of a `1`-chain sums to zero: its value at the boundary node of
the arc is minus its total over the intersection points of the arc. -/
theorem sum_alphaArcBoundary_inl_add_inr_eq_zero [Fintype Point] [DecidableEq Arc]
    [DecidableEq AlphaCircle] (c : Point ⊕ Arc → ℤ) (a : Arc) :
    ∑ q with H.alpha q = .inl a, H.alphaArcBoundary c (.inl q) +
      H.alphaArcBoundary c (.inr a) = 0 := by
  set S : Finset (Point ⊕ Arc) := ({q | H.alpha q = .inl a} : Finset Point).disjSum {a}
  have hS (v : Point ⊕ Arc) : v ∈ S ↔ H.alphaCurve v = .inl a := by
    rcases v with q | b <;> simp [S, eq_comm]
  have hsum : ∑ v ∈ S, c (H.alphaNext.symm v) = ∑ v ∈ S, c v :=
    Finset.sum_equiv H.alphaNext.symm (fun v => by simp [hS]) fun _ _ => rfl
  have h := congrArg (· - ∑ v ∈ S, c v) hsum
  simp only [sub_self, ← Finset.sum_sub_distrib] at h
  simpa only [S, Finset.sum_disjSum, Finset.sum_singleton, alphaArcBoundary_apply] using h

/-- The border class at the initial end of an arc is the coefficient of the `α`-part of the
boundary on the initial segment of the arc. -/
theorem borderClass_arcEnd_inl (D : Region → ℤ) (a : Arc) :
    H.borderClass D (H.arcEnd (.inl a)) = H.alphaBoundary D (.inr a) := by
  simp [H.alphaLeft_inr, H.alphaRight_inr]

/-- The border class at the terminal end of an arc is minus the coefficient of the `α`-part of the
boundary on the terminal segment of the arc. -/
theorem borderClass_arcEnd_inr (D : Region → ℤ) (a : Arc) :
    H.borderClass D (H.arcEnd (.inr a)) = -H.alphaBoundary D (H.alphaNext.symm (.inr a)) := by
  simp [H.alphaLeft_symm_inr, H.alphaRight_symm_inr]

/-- Adding the border class over the two ends of an arc gives minus the boundary of the `α`-part
at the boundary node of the arc. -/
theorem pushBoundary_borderClass_apply [DecidableEq Arc] (D : Region → ℤ) (a : Arc) :
    StrandGradingGroup.pushBoundary H.matching (H.borderClass D) a =
      -H.alphaArcBoundary (H.alphaBoundary D) (.inr a) := by
  have hends : ({i | H.matching i = a} : Finset (Fin n)) =
      {H.arcEnd (.inl a), H.arcEnd (.inr a)} := by
    ext i
    simp [matching_eq_iff]
  rw [StrandGradingGroup.pushBoundary_apply, hends,
    Finset.sum_pair (H.arcEnd.injective.ne Sum.inl_ne_inr), borderClass_arcEnd_inl,
    borderClass_arcEnd_inr, alphaArcBoundary_apply]
  abel

/-- The border class of every domain has total sum zero: the multiplicities of the domain at the
two outer intervals agree, since both lie in the region of the basepoint. So it is the boundary of
a class of `H₁(Z, a)`, as are the boundaries recorded in `TauCeti.StrandGradingGroup`. -/
theorem sum_borderClass (D : Region → ℤ) : ∑ i, H.borderClass D i = 0 := by
  simpa [H.borderRegion_last] using Fin.sum_univ_castSucc_sub_succ (D ∘ H.borderRegion)

end Boundary

/-! ### Domains connecting two generators -/

section Domain

variable {H}

/-- `D` is a domain connecting the generator `x` to the generator `y`: at every intersection
point, the boundary of its `α`-part is `y - x` and the boundary of its `β`-part is `x - y`. Nothing
is asked at the boundary nodes of the arcs, where `∂D` continues along `∂Σ`. -/
def IsDomainBetween (x y : H.Generator) (D : Region → ℤ) : Prop :=
  (∀ q, H.alphaArcBoundary (H.alphaBoundary D) (.inl q) =
      H.generatorChain y q - H.generatorChain x q) ∧
    H.betaArcBoundary (H.betaBoundary D) = H.generatorChain x - H.generatorChain y

@[simp]
theorem isDomainBetween_iff {x y : H.Generator} {D : Region → ℤ} :
    H.IsDomainBetween x y D ↔
      (∀ q, H.alphaArcBoundary (H.alphaBoundary D) (.inl q) =
          H.generatorChain y q - H.generatorChain x q) ∧
        H.betaArcBoundary (H.betaBoundary D) = H.generatorChain x - H.generatorChain y :=
  Iff.rfl

/-- The zero domain connects every generator to itself. -/
theorem isDomainBetween_zero (x : H.Generator) : H.IsDomainBetween x x 0 := by
  simp

/-- The whole surface connects every generator to itself. -/
theorem isDomainBetween_one (x : H.Generator) : H.IsDomainBetween x x 1 := by
  simp

namespace IsDomainBetween

variable {x y w : H.Generator} {D E : Region → ℤ}

/-- Juxtaposing a domain from `x` to `y` with one from `y` to `w` gives a domain from `x` to
`w`. -/
theorem add (hD : H.IsDomainBetween x y D) (hE : H.IsDomainBetween y w E) :
    H.IsDomainBetween x w (D + E) := by
  refine ⟨fun q => ?_, ?_⟩
  · rw [map_add, map_add, Pi.add_apply, hD.1, hE.1]
    abel
  · rw [map_add, map_add, hD.2, hE.2]
    abel

/-- Reversing a domain from `x` to `y` gives a domain from `y` to `x`. -/
theorem neg (hD : H.IsDomainBetween x y D) : H.IsDomainBetween y x (-D) := by
  refine ⟨fun q => ?_, ?_⟩
  · rw [map_neg, map_neg, Pi.neg_apply, hD.1, neg_sub]
  · rw [map_neg, map_neg, hD.2, neg_sub]

/-- At the boundary node of an arc, the boundary of the `α`-part of a domain from `x` to `y` is
`1` if `x` occupies the arc, minus `1` if `y` does, and the sum of both. -/
theorem alphaArcBoundary_inr [Finite Point] [DecidableEq Arc] (hD : H.IsDomainBetween x y D)
    (a : Arc) :
    H.alphaArcBoundary (H.alphaBoundary D) (.inr a) =
      (if a ∈ H.occupied x then 1 else 0) - (if a ∈ H.occupied y then 1 else 0) := by
  classical
  have := Fintype.ofFinite Point
  have h := H.sum_alphaArcBoundary_inl_add_inr_eq_zero (H.alphaBoundary D) a
  rw [Finset.sum_congr rfl fun q _ => hD.1 q, Finset.sum_sub_distrib,
    ← StrandGradingGroup.pushBoundary_apply, ← StrandGradingGroup.pushBoundary_apply,
    H.pushBoundary_alpha_generatorChain_inl, H.pushBoundary_alpha_generatorChain_inl] at h
  linarith

/-- **The border class of a domain and the occupancies.** Added up over the two ends of each arc,
the border class of a domain from `x` to `y` is the indicator of the arcs occupied by `y` minus
that of the arcs occupied by `x`. This is the counterpart of `M_*(∂[φ]) = M(T) - M(S)` for a strand
diagram `φ : S → T` (`TauCeti.StrandGradingGroup.pushBoundary`), with the occupancies of the
generators in place of the matched pairs occupied at the ends of a diagram. -/
theorem pushBoundary_borderClass [Finite Point] [DecidableEq Arc]
    (hD : H.IsDomainBetween x y D) :
    StrandGradingGroup.pushBoundary H.matching (H.borderClass D) =
      fun a => (if a ∈ H.occupied y then 1 else 0) - (if a ∈ H.occupied x then 1 else 0) := by
  ext a
  rw [pushBoundary_borderClass_apply, hD.alphaArcBoundary_inr, neg_sub]

end IsDomainBetween

end Domain

/-! ### Periodic and provincial periodic domains -/

section Periodic

/-- The periodic domains: the domains with multiplicity zero at the region of the basepoint whose
boundary is made of whole `α`-arcs, `α`-circles and `β`-circles and a part along the boundary,
that is, whose `α`- and `β`-parts are cycles at every node. -/
def periodicDomains : AddSubgroup (Region → ℤ) where
  carrier := {P | P (H.borderRegion 0) = 0 ∧ H.alphaArcBoundary (H.alphaBoundary P) = 0 ∧
    H.betaArcBoundary (H.betaBoundary P) = 0}
  add_mem' {P Q} hP hQ := ⟨by simp [hP.1, hQ.1], by simp [hP.2.1, hQ.2.1],
    by simp [hP.2.2, hQ.2.2]⟩
  zero_mem' := by simp
  neg_mem' {P} hP := ⟨by simp [hP.1], by simp [hP.2.1], by simp [hP.2.2]⟩

@[simp]
theorem mem_periodicDomains_iff {P : Region → ℤ} :
    P ∈ H.periodicDomains ↔ P (H.borderRegion 0) = 0 ∧
      H.alphaArcBoundary (H.alphaBoundary P) = 0 ∧ H.betaArcBoundary (H.betaBoundary P) = 0 :=
  Iff.rfl

/-- A domain is periodic exactly when it has multiplicity zero at the region of the basepoint and
the coefficients of the `α`- and `β`-parts of its boundary are constant along each curve. -/
theorem mem_periodicDomains_iff_exists_curves {P : Region → ℤ} :
    P ∈ H.periodicDomains ↔ P (H.borderRegion 0) = 0 ∧
      (∃ a : Arc ⊕ AlphaCircle → ℤ, ∀ v, H.alphaBoundary P v = a (H.alphaCurve v)) ∧
        ∃ b : Fin g → ℤ, ∀ p, H.betaBoundary P p = b (H.beta p) := by
  rw [mem_periodicDomains_iff, alphaArcBoundary_eq_zero_iff, betaArcBoundary_eq_zero_iff]

/-- The border class of a periodic domain cancels along each matched pair: its boundary along an
arc is a multiple of the whole arc, which leaves the boundary at its two ends with opposite
multiplicities. -/
theorem pushBoundary_borderClass_of_mem_periodicDomains [DecidableEq Arc] {P : Region → ℤ}
    (hP : P ∈ H.periodicDomains) :
    StrandGradingGroup.pushBoundary H.matching (H.borderClass P) = 0 := by
  ext a
  rw [pushBoundary_borderClass_apply, hP.2.1, Pi.zero_apply, neg_zero, Pi.zero_apply]

/-- A `1`-chain on the `α`-segments is a cycle as soon as its boundary vanishes at every
intersection point: around each arc, the boundary at the boundary node is minus the sum of its
values at the points of the arc. -/
theorem alphaArcBoundary_eq_zero_iff_forall_inl [Finite Point] (c : Point ⊕ Arc → ℤ) :
    H.alphaArcBoundary c = 0 ↔ ∀ q, H.alphaArcBoundary c (.inl q) = 0 := by
  classical
  have := Fintype.ofFinite Point
  refine ⟨fun h q => by rw [h, Pi.zero_apply], fun h => funext fun v => ?_⟩
  rcases v with q | a
  · exact h q
  · simpa [h] using H.sum_alphaArcBoundary_inl_add_inr_eq_zero c a

/-- The provincial periodic domains: the periodic domains whose border class vanishes. -/
def provincialPeriodicDomains : AddSubgroup (Region → ℤ) :=
  H.periodicDomains ⊓ H.borderClass.ker

@[simp]
theorem mem_provincialPeriodicDomains_iff {P : Region → ℤ} :
    P ∈ H.provincialPeriodicDomains ↔ P ∈ H.periodicDomains ∧ H.borderClass P = 0 := by
  rw [provincialPeriodicDomains, AddSubgroup.mem_inf, AddMonoidHom.mem_ker]

theorem provincialPeriodicDomains_le_periodicDomains :
    H.provincialPeriodicDomains ≤ H.periodicDomains :=
  inf_le_left

/-- Two domains with the same basepoint multiplicity and the same border class have the same
multiplicity at every region along the boundary. -/
theorem apply_borderRegion_eq_of_borderClass_eq {D D' : Region → ℤ}
    (h₀ : D' (H.borderRegion 0) = D (H.borderRegion 0)) (h : H.borderClass D' = H.borderClass D)
    (i : Fin (n + 1)) : D' (H.borderRegion i) = D (H.borderRegion i) := by
  induction i using Fin.induction with
  | zero => exact h₀
  | succ i ih =>
    have hi := congrFun h i
    simp only [borderClass_apply] at hi
    linarith

/-- The multiplicity of a domain at the interval below the boundary point `i` is its basepoint
multiplicity minus the border class summed over the points below `i`. -/
theorem apply_borderRegion_castSucc (D : Region → ℤ) (i : Fin n) :
    D (H.borderRegion i.castSucc) =
      D (H.borderRegion 0) - ∑ y ∈ ({y | y < i} : Finset (Fin n)), H.borderClass D y := by
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero =>
    have : ({y | y < (⟨0, hk⟩ : Fin n)} : Finset (Fin n)) = ∅ := by
      ext y
      simp [Fin.lt_def]
    simp [this, Fin.castSucc, Fin.castAdd, Fin.castLE]
  | succ k ih =>
    have hset : ({y | y < (⟨k + 1, hk⟩ : Fin n)} : Finset (Fin n)) =
        insert ⟨k, by omega⟩ ({y | y < (⟨k, by omega⟩ : Fin n)} : Finset (Fin n)) := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.lt_def, Fin.ext_iff]
      omega
    have hcs : (⟨k + 1, hk⟩ : Fin n).castSucc = (⟨k, by omega⟩ : Fin n).succ := by
      ext
      simp
    have hδ := H.borderClass_apply D ⟨k, by omega⟩
    rw [hset, sum_insert (by simp), hcs]
    linarith [ih (by omega)]

/-- A domain is a provincial periodic domain exactly when it has multiplicity zero at every region
along the boundary and its `α`- and `β`-parts are cycles. -/
theorem mem_provincialPeriodicDomains_iff_forall_borderRegion {P : Region → ℤ} :
    P ∈ H.provincialPeriodicDomains ↔ (∀ i, P (H.borderRegion i) = 0) ∧
      H.alphaArcBoundary (H.alphaBoundary P) = 0 ∧ H.betaArcBoundary (H.betaBoundary P) = 0 := by
  rw [mem_provincialPeriodicDomains_iff, mem_periodicDomains_iff]
  constructor
  · rintro ⟨⟨h₀, hα, hβ⟩, hc⟩
    refine ⟨fun i => ?_, hα, hβ⟩
    simpa using H.apply_borderRegion_eq_of_borderClass_eq (D := 0) (D' := P) (by simpa using h₀)
      (by simpa using hc) i
  · rintro ⟨h, hα, hβ⟩
    exact ⟨⟨h 0, hα, hβ⟩, by ext i; simp [h]⟩

/-- **The boundary of a provincial periodic domain contains no `α`-arc.** The coefficient of its
boundary is constant along each arc and vanishes on the initial segment, whose two sides lie along
the boundary. -/
theorem alphaBoundary_eq_zero_of_mem_provincialPeriodicDomains {P : Region → ℤ}
    (hP : P ∈ H.provincialPeriodicDomains) {v : Point ⊕ Arc} {a : Arc}
    (hv : H.alphaCurve v = .inl a) : H.alphaBoundary P v = 0 := by
  obtain ⟨hb, hα, -⟩ := (H.mem_provincialPeriodicDomains_iff_forall_borderRegion).mp hP
  obtain ⟨c, hc⟩ := (H.alphaArcBoundary_eq_zero_iff _).mp hα
  have h : H.alphaBoundary P v = H.alphaBoundary P (.inr a) := by
    rw [hc, hc, hv, alphaCurve_inr]
  simp [h, H.alphaLeft_inr, H.alphaRight_inr, hb]

variable {H}

/-- A domain connects a generator to itself and has multiplicity zero at the region of the
basepoint exactly when it is periodic. -/
theorem isDomainBetween_self_iff [Finite Point] {x : H.Generator} {P : Region → ℤ} :
    H.IsDomainBetween x x P ∧ P (H.borderRegion 0) = 0 ↔ P ∈ H.periodicDomains := by
  simp [alphaArcBoundary_eq_zero_iff_forall_inl, and_comm]

/-- Given a domain `D` connecting `x` to `y`, another domain `D'` connects `x` to `y` with the same
basepoint multiplicity as `D` exactly when `D' - D` is periodic. So the domains connecting `x` to
`y` with prescribed basepoint multiplicity form a coset of the periodic domains. -/
theorem IsDomainBetween.sub_mem_periodicDomains_iff [Finite Point] {x y : H.Generator}
    {D D' : Region → ℤ} (hD : H.IsDomainBetween x y D) :
    D' - D ∈ H.periodicDomains ↔
      H.IsDomainBetween x y D' ∧ D' (H.borderRegion 0) = D (H.borderRegion 0) := by
  rw [mem_periodicDomains_iff, H.alphaArcBoundary_eq_zero_iff_forall_inl, isDomainBetween_iff]
  simp only [map_sub, Pi.sub_apply, hD.1, hD.2, sub_eq_zero]
  tauto

/-- Given a domain `D` connecting `x` to `y`, another domain `D'` connects `x` to `y` with the same
basepoint multiplicity and the same border class as `D` exactly when `D' - D` is a provincial
periodic domain. So the domains connecting `x` to `y` with prescribed basepoint multiplicity and
border class form a coset of the provincial periodic domains. -/
theorem IsDomainBetween.sub_mem_provincialPeriodicDomains_iff [Finite Point]
    {x y : H.Generator} {D D' : Region → ℤ} (hD : H.IsDomainBetween x y D) :
    D' - D ∈ H.provincialPeriodicDomains ↔
      H.IsDomainBetween x y D' ∧ D' (H.borderRegion 0) = D (H.borderRegion 0) ∧
        H.borderClass D' = H.borderClass D := by
  rw [mem_provincialPeriodicDomains_iff, hD.sub_mem_periodicDomains_iff, map_sub, sub_eq_zero,
    and_assoc]

end Periodic

/-! ### Admissibility -/

section Admissible

/-- The bordered diagram is admissible when every nonzero periodic domain has both positive and
negative coefficients. -/
def Admissible : Prop :=
  ∀ P ∈ H.periodicDomains, P ≠ 0 → (∃ r, 0 < P r) ∧ ∃ r, P r < 0

/-- The bordered diagram is provincially admissible when every nonzero provincial periodic domain
has both positive and negative coefficients. -/
def ProvinciallyAdmissible : Prop :=
  ∀ P ∈ H.provincialPeriodicDomains, P ≠ 0 → (∃ r, 0 < P r) ∧ ∃ r, P r < 0

/-- A diagram is admissible exactly when its only nonnegative periodic domain is zero. -/
theorem admissible_iff : H.Admissible ↔ ∀ P ∈ H.periodicDomains, 0 ≤ P → P = 0 :=
  H.periodicDomains.forall_exists_pos_and_neg_iff_forall_nonneg_eq_zero

/-- A diagram is provincially admissible exactly when its only nonnegative provincial periodic
domain is zero. -/
theorem provinciallyAdmissible_iff :
    H.ProvinciallyAdmissible ↔ ∀ P ∈ H.provincialPeriodicDomains, 0 ≤ P → P = 0 :=
  H.provincialPeriodicDomains.forall_exists_pos_and_neg_iff_forall_nonneg_eq_zero

/-- An admissible diagram is provincially admissible. -/
theorem Admissible.provinciallyAdmissible (h : H.Admissible) : H.ProvinciallyAdmissible :=
  fun P hP => h P (H.provincialPeriodicDomains_le_periodicDomains hP)

/-- A diagram is admissible exactly when it has finitely many nonnegative periodic domains. -/
theorem admissible_iff_finite_setOf_mem_periodicDomains_nonneg :
    H.Admissible ↔ {P | P ∈ H.periodicDomains ∧ 0 ≤ P}.Finite :=
  H.admissible_iff.trans H.periodicDomains.finite_setOf_mem_nonneg_iff.symm

/-- A diagram is provincially admissible exactly when it has finitely many nonnegative provincial
periodic domains. -/
theorem provinciallyAdmissible_iff_finite_setOf_mem_provincialPeriodicDomains_nonneg :
    H.ProvinciallyAdmissible ↔ {P | P ∈ H.provincialPeriodicDomains ∧ 0 ≤ P}.Finite :=
  H.provinciallyAdmissible_iff.trans H.provincialPeriodicDomains.finite_setOf_mem_nonneg_iff.symm

variable [Finite Point] [Finite Region] {H}

/-- **Finiteness in an admissible diagram.** In an admissible diagram, there are only finitely
many nonnegative domains connecting `x` to `y` with a given basepoint multiplicity. -/
theorem Admissible.finite_setOf_isDomainBetween_basepoint_eq_nonneg (h : H.Admissible)
    (x y : H.Generator) (m : ℤ) :
    {D | 0 ≤ D ∧ H.IsDomainBetween x y D ∧ D (H.borderRegion 0) = m}.Finite :=
  AddSubgroup.finite_of_forall_sub_mem (H.admissible_iff.mp h) (fun _ hD => hD.1)
    fun _ hD _ hD' => hD.2.1.sub_mem_periodicDomains_iff.mpr ⟨hD'.2.1, hD'.2.2.trans hD.2.2.symm⟩

/-- **Finiteness in a provincially admissible diagram.** In a provincially admissible diagram,
there are only finitely many nonnegative domains connecting `x` to `y` with a given basepoint
multiplicity and a given border class. -/
theorem ProvinciallyAdmissible.finite_setOf_isDomainBetween_basepoint_eq_borderClass_eq_nonneg
    (h : H.ProvinciallyAdmissible) (x y : H.Generator) (m : ℤ) (δ : Fin n → ℤ) :
    {D | 0 ≤ D ∧ H.IsDomainBetween x y D ∧ D (H.borderRegion 0) = m ∧ H.borderClass D = δ}.Finite :=
  AddSubgroup.finite_of_forall_sub_mem (H.provinciallyAdmissible_iff.mp h) (fun _ hD => hD.1)
    fun _ hD _ hD' => hD.2.1.sub_mem_provincialPeriodicDomains_iff.mpr
      ⟨hD'.2.1, hD'.2.2.1.trans hD.2.2.1.symm, hD'.2.2.2.trans hD.2.2.2.symm⟩

end Admissible

end BorderedHeegaardRegionSystem

end TauCeti
