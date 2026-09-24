/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Order.Pi
public import TauCeti.GroupTheory.Perm.Basic
public import TauCeti.LowDimTopology.Heegaard.Generator
import Mathlib.Tactic.Abel

/-!
# Domains and periodic domains of a pointed Heegaard diagram

The attaching curves of a pointed Heegaard diagram `(Σ, α, β, z)` cut the surface into
*regions*, the closures of the components of `Σ - α - β`. A *domain* is an integral
combination of regions. This file records the incidence data that domains need, with no
surface in sight, and develops domains, periodic domains and weak admissibility on top of it.

The data extends `TauCeti.HeegaardIntersectionSystem`, which labels each intersection point by
its `α`- and `β`-curve. Orient every attaching curve. The intersection points on the `α`-curve
`α_i` cut it into arcs, one starting at each point `p` on `α_i` and ending at the next point
along `α_i`, `alphaNext p`; the points on `α_i` form a single cycle of `alphaNext`. Each such
arc has a region on its left and one on its right. The `β`-curves are recorded in the same way,
with compatible region labels at each crossing and every region incident to an arc unless there
are no intersection arcs. Each basepoint lies in a region. Every attaching curve is assumed to
meet the other family, so that it is subdivided into arcs; this holds as soon as the diagram has
a generator.

In these terms the `α`-part of the boundary of a domain `D` is the `1`-chain on `α`-arcs whose
coefficient on the arc starting at `p` is `D (alphaLeft p) - D (alphaRight p)`, and the boundary
of the arc starting at `p` is `alphaNext p - p`. A domain `D` *connects* a generator `x` to a
generator `y` when `∂(∂D ∩ α) = y - x` and `∂(∂D ∩ β) = x - y`; the domain of every Whitney
disk from `x` to `y` connects `x` to `y` in this sense. A domain is *periodic* when it has
multiplicity zero at every basepoint and its boundary is a sum of whole `α`- and `β`-curves. The
periodic domains form a subgroup, and the domains connecting `x` to `y` with prescribed basepoint
multiplicities form a coset of it. A diagram is *weakly admissible* when every nonzero periodic
domain has both positive and negative coefficients: the finiteness hypothesis under which the
differential of `HF̂` is a finite count.

## Main definitions

* `TauCeti.HeegaardRegionSystem`: intersection data together with the cyclic order of the
  intersection points along each curve, the regions on the two sides of each arc, and the
  regions containing the basepoints.
* `TauCeti.HeegaardRegionSystem.alphaBoundary`, `TauCeti.HeegaardRegionSystem.betaBoundary`: the
  `α`- and `β`-parts of the boundary of a domain.
* `TauCeti.HeegaardRegionSystem.alphaArcBoundary`, `TauCeti.HeegaardRegionSystem.betaArcBoundary`:
  the boundary of a `1`-chain on the `α`- or `β`-arcs.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween`: `D` is a domain connecting `x` to `y`.
* `TauCeti.HeegaardRegionSystem.periodicDomains`: the subgroup of periodic domains.
* `TauCeti.HeegaardRegionSystem.WeaklyAdmissible`: every nonzero periodic domain has both
  positive and negative coefficients.

## Main results

* `TauCeti.HeegaardRegionSystem.boundary_boundary_eq_zero`: the full boundary of every region
  chain is a cycle.
* `TauCeti.HeegaardRegionSystem.alphaArcBoundary_eq_zero_iff`: a `1`-chain on the `α`-arcs is a
  cycle exactly when it is a combination of whole `α`-curves.
* `TauCeti.HeegaardRegionSystem.mem_periodicDomains_iff_exists_curves`: a domain is periodic
  exactly when it avoids the basepoints and its boundary is a combination of whole curves.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.add`: domains connecting `x` to `y` and `y` to
  `w` add to a domain connecting `x` to `w`.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.sub_mem_periodicDomains_iff`: the domains
  connecting `x` to `y` with the basepoint multiplicities of a given one form a coset of the
  periodic domains.
* `TauCeti.HeegaardRegionSystem.weaklyAdmissible_iff`: weak admissibility says that the only
  nonnegative periodic domain is zero.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.4 (domains and periodic domains)
  and §4.2 (admissibility). Their weak admissibility for a spin^c structure `𝔰` quantifies only
  over the periodic domains `P` with `⟨c₁(𝔰), H(P)⟩ = 0`; the condition here quantifies over all
  periodic domains, so it implies weak admissibility for every spin^c structure.
* R. Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geom. Topol. **10**
  (2006), [arXiv:math/0502404](https://arxiv.org/abs/math/0502404), for the corner
  conditions `∂(∂D ∩ α) = y - x` and `∂(∂D ∩ β) = x - y`.
-/

public section

namespace TauCeti

universe u v w

/-- The incidence data of a pointed Heegaard diagram needed for domains. On top of the
intersection data it records, for each intersection point `p`, the next intersection point along
the oriented `α`- and `β`-curve through `p`, the regions to the left and to the right of the arcs
starting at `p`, and the region containing each basepoint. The points on each curve form a single
cycle of the corresponding successor permutation. Region labels agree around each crossing, and
each region is incident to an arc (apart from the one-region case with no arcs). -/
@[ext]
structure HeegaardRegionSystem (n : ℕ) (Point : Type u) (Region : Type v) (Basepoint : Type w)
    extends HeegaardIntersectionSystem n Point where
  /-- The next intersection point along the oriented `α`-curve. -/
  alphaNext : Equiv.Perm Point
  /-- The intersection points on each `α`-curve form one cycle of `alphaNext`. -/
  alphaNext_isCycleOn (i : Fin n) : alphaNext.IsCycleOn {p | alpha p = i}
  /-- The next intersection point along the oriented `β`-curve. -/
  betaNext : Equiv.Perm Point
  /-- The intersection points on each `β`-curve form one cycle of `betaNext`. -/
  betaNext_isCycleOn (j : Fin n) : betaNext.IsCycleOn {p | beta p = j}
  /-- The region to the left of the `α`-arc starting at an intersection point. -/
  alphaLeft : Point → Region
  /-- The region to the right of the `α`-arc starting at an intersection point. -/
  alphaRight : Point → Region
  /-- The region to the left of the `β`-arc starting at an intersection point. -/
  betaLeft : Point → Region
  /-- The region to the right of the `β`-arc starting at an intersection point. -/
  betaRight : Point → Region
  /-- The diagram has a complementary region. -/
  regionNonempty : Nonempty Region
  /-- The four region labels around each transverse crossing agree on the `α`- and `β`-arc
  sides. The two alternatives are the two possible local crossing orientations. -/
  crossingCompatible (p : Point) :
    (alphaLeft (alphaNext.symm p) = betaLeft p ∧
      alphaRight (alphaNext.symm p) = betaLeft (betaNext.symm p) ∧
      alphaLeft p = betaRight p ∧
      alphaRight p = betaRight (betaNext.symm p)) ∨
    (alphaLeft (alphaNext.symm p) = betaRight (betaNext.symm p) ∧
      alphaRight (alphaNext.symm p) = betaRight p ∧
      alphaLeft p = betaLeft (betaNext.symm p) ∧
      alphaRight p = betaLeft p)
  /-- Every region meets an arc, except for the unique region of a diagram with no
  intersection arcs. -/
  regionCovered (r : Region) :
    (∃ p : Point, alphaLeft p = r ∨ alphaRight p = r ∨
      betaLeft p = r ∨ betaRight p = r) ∨ (IsEmpty Point ∧ Subsingleton Region)
  /-- The region containing a basepoint. -/
  basepoint : Basepoint → Region

namespace HeegaardRegionSystem

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint)

/-- The successor along an `α`-curve stays on that curve. -/
@[simp]
theorem alpha_alphaNext (p : Point) : H.alpha (H.alphaNext p) = H.alpha p :=
  (H.alphaNext_isCycleOn (H.alpha p)).1.mapsTo rfl

/-- The predecessor along an `α`-curve stays on that curve. -/
@[simp]
theorem alpha_alphaNext_symm (p : Point) : H.alpha (H.alphaNext.symm p) = H.alpha p := by
  simpa using (H.alpha_alphaNext (H.alphaNext.symm p)).symm

/-- The successor along a `β`-curve stays on that curve. -/
@[simp]
theorem beta_betaNext (p : Point) : H.beta (H.betaNext p) = H.beta p :=
  (H.betaNext_isCycleOn (H.beta p)).1.mapsTo rfl

/-- The predecessor along a `β`-curve stays on that curve. -/
@[simp]
theorem beta_betaNext_symm (p : Point) : H.beta (H.betaNext.symm p) = H.beta p := by
  simpa using (H.beta_betaNext (H.betaNext.symm p)).symm

section Boundary

/-- The `α`-part `∂D ∩ α` of the boundary of a domain, as a `1`-chain on the `α`-arcs: its
coefficient on the arc starting at `p` is the multiplicity of `D` to the left of the arc minus
the multiplicity to its right. -/
def alphaBoundary : (Region → ℤ) →+ (Point → ℤ) where
  toFun D p := D (H.alphaLeft p) - D (H.alphaRight p)
  map_zero' := by ext; simp
  map_add' D E := by ext; simp only [Pi.add_apply]; abel

/-- The `β`-part `∂D ∩ β` of the boundary of a domain, as a `1`-chain on the `β`-arcs: its
coefficient on the arc starting at `p` is the multiplicity of `D` to the left of the arc minus
the multiplicity to its right. -/
def betaBoundary : (Region → ℤ) →+ (Point → ℤ) where
  toFun D p := D (H.betaLeft p) - D (H.betaRight p)
  map_zero' := by ext; simp
  map_add' D E := by ext; simp only [Pi.add_apply]; abel

@[simp]
theorem alphaBoundary_apply (D : Region → ℤ) (p : Point) :
    H.alphaBoundary D p = D (H.alphaLeft p) - D (H.alphaRight p) :=
  (rfl)

@[simp]
theorem betaBoundary_apply (D : Region → ℤ) (p : Point) :
    H.betaBoundary D p = D (H.betaLeft p) - D (H.betaRight p) :=
  (rfl)

/-- The boundary of a `1`-chain on the `α`-arcs, indexed by starting points. The arc starting at
`p` ends at `alphaNext p`, so the coefficient at `q` is that of the arc ending at `q` minus that
of the arc starting at `q`. -/
def alphaArcBoundary : (Point → ℤ) →+ (Point → ℤ) where
  toFun c q := c (H.alphaNext.symm q) - c q
  map_zero' := by ext; simp
  map_add' c d := by ext; simp only [Pi.add_apply]; abel

/-- The boundary of a `1`-chain on the `β`-arcs, indexed by starting points. The arc starting at
`p` ends at `betaNext p`, so the coefficient at `q` is that of the arc ending at `q` minus that
of the arc starting at `q`. -/
def betaArcBoundary : (Point → ℤ) →+ (Point → ℤ) where
  toFun c q := c (H.betaNext.symm q) - c q
  map_zero' := by ext; simp
  map_add' c d := by ext; simp only [Pi.add_apply]; abel

@[simp]
theorem alphaArcBoundary_apply (c : Point → ℤ) (q : Point) :
    H.alphaArcBoundary c q = c (H.alphaNext.symm q) - c q :=
  (rfl)

@[simp]
theorem betaArcBoundary_apply (c : Point → ℤ) (q : Point) :
    H.betaArcBoundary c q = c (H.betaNext.symm q) - c q :=
  (rfl)

/-- The full boundary of a region chain is a cycle. -/
theorem boundary_boundary_eq_zero (D : Region → ℤ) :
    H.alphaArcBoundary (H.alphaBoundary D) +
      H.betaArcBoundary (H.betaBoundary D) = 0 := by
  funext p
  simp only [Pi.add_apply, Pi.zero_apply, alphaArcBoundary_apply, betaArcBoundary_apply,
    alphaBoundary_apply, betaBoundary_apply]
  rcases H.crossingCompatible p with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  · rw [h₁, h₂, h₃, h₄]
    abel
  · rw [h₁, h₂, h₃, h₄]
    abel

/-- A `1`-chain on the `α`-arcs is a cycle exactly when it is a combination of whole `α`-curves,
that is, constant along each `α`-curve. -/
theorem alphaArcBoundary_eq_zero_iff (c : Point → ℤ) :
    H.alphaArcBoundary c = 0 ↔ ∃ a : Fin n → ℤ, ∀ p, c p = a (H.alpha p) := by
  simp only [funext_iff, alphaArcBoundary_apply, Pi.zero_apply, sub_eq_zero]
  constructor
  · intro hc
    obtain ⟨a, ha⟩ := (Function.factorsThrough_iff _).mp
      (H.alphaNext.factorsThrough_of_forall_isCycleOn H.alphaNext_isCycleOn fun p => by
        simpa using (hc (H.alphaNext p)).symm)
    exact ⟨a, congrFun ha⟩
  · rintro ⟨a, ha⟩ q
    rw [ha, ha, alpha_alphaNext_symm]

/-- A `1`-chain on the `β`-arcs is a cycle exactly when it is a combination of whole `β`-curves,
that is, constant along each `β`-curve. -/
theorem betaArcBoundary_eq_zero_iff (c : Point → ℤ) :
    H.betaArcBoundary c = 0 ↔ ∃ b : Fin n → ℤ, ∀ p, c p = b (H.beta p) := by
  simp only [funext_iff, betaArcBoundary_apply, Pi.zero_apply, sub_eq_zero]
  constructor
  · intro hc
    obtain ⟨b, hb⟩ := (Function.factorsThrough_iff _).mp
      (H.betaNext.factorsThrough_of_forall_isCycleOn H.betaNext_isCycleOn fun p => by
        simpa using (hc (H.betaNext p)).symm)
    exact ⟨b, congrFun hb⟩
  · rintro ⟨b, hb⟩ q
    rw [hb, hb, beta_betaNext_symm]

end Boundary

section Domain

variable {H}

/-- `D` is a domain connecting the generator `x` to the generator `y`: the boundary of its
`α`-part is `y - x` and the boundary of its `β`-part is `x - y`. The domain of every Whitney disk
from `x` to `y` satisfies these corner conditions. -/
def IsDomainBetween (x y : H.Generator) (D : Region → ℤ) : Prop :=
  H.alphaArcBoundary (H.alphaBoundary D) = H.generatorChain y - H.generatorChain x ∧
    H.betaArcBoundary (H.betaBoundary D) = H.generatorChain x - H.generatorChain y

theorem isDomainBetween_iff {x y : H.Generator} {D : Region → ℤ} :
    H.IsDomainBetween x y D ↔
      H.alphaArcBoundary (H.alphaBoundary D) = H.generatorChain y - H.generatorChain x ∧
        H.betaArcBoundary (H.betaBoundary D) = H.generatorChain x - H.generatorChain y :=
  Iff.rfl

/-- The zero domain connects every generator to itself. -/
theorem isDomainBetween_zero (x : H.Generator) : H.IsDomainBetween x x 0 := by
  simp [isDomainBetween_iff]

namespace IsDomainBetween

variable {x y w : H.Generator} {D E : Region → ℤ}

/-- Juxtaposing a domain from `x` to `y` with one from `y` to `w` gives a domain from `x` to
`w`. -/
theorem add (hD : H.IsDomainBetween x y D) (hE : H.IsDomainBetween y w E) :
    H.IsDomainBetween x w (D + E) := by
  refine ⟨?_, ?_⟩ <;> simp only [map_add, hD.1, hD.2, hE.1, hE.2] <;> abel

/-- Reversing a domain from `x` to `y` gives a domain from `y` to `x`. -/
theorem neg (hD : H.IsDomainBetween x y D) : H.IsDomainBetween y x (-D) := by
  refine ⟨?_, ?_⟩ <;> simp only [map_neg, hD.1, hD.2, neg_sub]

end IsDomainBetween

variable (H) in
/-- The periodic domains: the domains with multiplicity zero at every basepoint whose boundary
is a sum of whole `α`- and `β`-curves, that is, whose `α`- and `β`-parts are cycles. -/
def periodicDomains : AddSubgroup (Region → ℤ) where
  carrier := {P | (∀ z, P (H.basepoint z) = 0) ∧ H.alphaArcBoundary (H.alphaBoundary P) = 0 ∧
    H.betaArcBoundary (H.betaBoundary P) = 0}
  add_mem' {P Q} hP hQ := ⟨fun z => by simp [hP.1 z, hQ.1 z], by simp [hP.2.1, hQ.2.1],
    by simp [hP.2.2, hQ.2.2]⟩
  zero_mem' := by simp
  neg_mem' {P} hP := ⟨fun z => by simp [hP.1 z], by simp [hP.2.1], by simp [hP.2.2]⟩

theorem mem_periodicDomains_iff {P : Region → ℤ} :
    P ∈ H.periodicDomains ↔ (∀ z, P (H.basepoint z) = 0) ∧
      H.alphaArcBoundary (H.alphaBoundary P) = 0 ∧ H.betaArcBoundary (H.betaBoundary P) = 0 :=
  Iff.rfl

/-- A domain is periodic exactly when it has multiplicity zero at every basepoint and its
boundary is `∑ aᵢ αᵢ + ∑ bⱼ βⱼ` for some integers `aᵢ`, `bⱼ`. -/
theorem mem_periodicDomains_iff_exists_curves {P : Region → ℤ} :
    P ∈ H.periodicDomains ↔ (∀ z, P (H.basepoint z) = 0) ∧
      (∃ a : Fin n → ℤ, ∀ p, P (H.alphaLeft p) - P (H.alphaRight p) = a (H.alpha p)) ∧
        ∃ b : Fin n → ℤ, ∀ p, P (H.betaLeft p) - P (H.betaRight p) = b (H.beta p) := by
  simp [mem_periodicDomains_iff, alphaArcBoundary_eq_zero_iff, betaArcBoundary_eq_zero_iff]

/-- A domain connects every generator to itself and avoids the basepoints exactly when it is
periodic. -/
theorem isDomainBetween_self_iff {x : H.Generator} {P : Region → ℤ} :
    H.IsDomainBetween x x P ∧ (∀ z, P (H.basepoint z) = 0) ↔ P ∈ H.periodicDomains := by
  simp [isDomainBetween_iff, mem_periodicDomains_iff, and_comm, and_assoc]

/-- Given a domain `D` connecting `x` to `y`, another domain `D'` connects `x` to `y` with the
same basepoint multiplicities as `D` exactly when `D' - D` is periodic. So the domains connecting
`x` to `y` with prescribed basepoint multiplicities form a coset of the periodic domains. -/
theorem IsDomainBetween.sub_mem_periodicDomains_iff {x y : H.Generator} {D D' : Region → ℤ}
    (hD : H.IsDomainBetween x y D) :
    D' - D ∈ H.periodicDomains ↔
      H.IsDomainBetween x y D' ∧ ∀ z, D' (H.basepoint z) = D (H.basepoint z) := by
  simp only [mem_periodicDomains_iff, isDomainBetween_iff, map_sub, hD.1, hD.2, Pi.sub_apply,
    sub_eq_zero]
  tauto

variable (H) in
/-- A pointed Heegaard diagram is weakly admissible when every nonzero periodic domain has both
positive and negative coefficients. -/
def WeaklyAdmissible : Prop :=
  ∀ P ∈ H.periodicDomains, P ≠ 0 → (∃ r, 0 < P r) ∧ ∃ r, P r < 0

/-- A diagram is weakly admissible exactly when its only nonnegative periodic domain is zero. -/
theorem weaklyAdmissible_iff :
    H.WeaklyAdmissible ↔ ∀ P ∈ H.periodicDomains, 0 ≤ P → P = 0 := by
  constructor
  · intro h P hP hnonneg
    by_contra hne
    obtain ⟨r, hr⟩ := (h P hP hne).2
    exact (hnonneg r).not_gt hr
  · intro h P hP hne
    refine ⟨?_, ?_⟩
    · by_contra hpos
      push Not at hpos
      refine hne (neg_eq_zero.mp (h (-P) (neg_mem hP) fun r => ?_))
      simpa using hpos r
    · by_contra hneg
      push Not at hneg
      exact hne (h P hP hneg)

end Domain

end HeegaardRegionSystem

end TauCeti
