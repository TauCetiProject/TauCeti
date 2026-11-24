/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Order.Pi
public import TauCeti.Algebra.Group.AddSubgroup.NonnegativeCoset
public import TauCeti.GroupTheory.Perm.Basic
public import TauCeti.LowDimTopology.Heegaard.Generator
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Domains and periodic domains of a pointed Heegaard diagram

The attaching curves of a pointed Heegaard diagram `(Σ, α, β, z)` cut the surface into
*regions*, the closures of the components of `Σ - α - β`. A *domain* is an integral
combination of regions. This file records the incidence data that domains need, with no
surface in sight, and develops domains, periodic domains and weak admissibility on top of it.

`HeegaardRegionSystem` is abstract incidence data: `Region` is supplied by the caller.
Its local incidence conditions do not identify the connected components of the complement
of a specified surface diagram. To use these definitions for such a diagram, one must
separately show that its supplied labels are exactly those components; identifying two
components changes the incidence system and can change its periodic domains and
admissibility. All results below concern the supplied incidence system.

The data extends `TauCeti.HeegaardIntersectionSystem`, which labels each intersection point by
its `α`- and `β`-curve. Orient every attaching curve. The intersection points on the `α`-curve
`α_i` cut it into arcs, one starting at each point `p` on `α_i` and ending at the next point
along `α_i`, `alphaNext p`; when that curve has intersection points, they form a single cycle of
`alphaNext`. Empty curve fibres satisfy the cycle condition vacuously. Each such
arc has a region on its left and one on its right. The `β`-curves are recorded in the same way,
with compatible region labels at each crossing and every region incident to an arc unless there
are no intersection arcs. Each basepoint lies in a region. A generator supplies an intersection
point on every curve, so curves in a diagram with a generator are subdivided into arcs.

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
* `TauCeti.HeegaardRegionSystem.IsCrossingCompatible`: the four region labels at a transverse
  crossing of two oriented curves agree.
* `TauCeti.HeegaardRegionSystem.alphaBoundary`, `TauCeti.HeegaardRegionSystem.betaBoundary`: the
  `α`- and `β`-parts of the boundary of a domain.
* `TauCeti.HeegaardRegionSystem.alphaArcBoundary`, `TauCeti.HeegaardRegionSystem.betaArcBoundary`:
  the boundary of a `1`-chain on the `α`- or `β`-arcs.
* `TauCeti.HeegaardRegionSystem.withBasepoints`: the same curves and regions with other
  basepoints; its generators and domains are those of the original diagram
  (`TauCeti.HeegaardRegionSystem.isDomainBetween_withBasepoints`).
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

namespace HeegaardRegionSystem

section Crossing

variable {A B R : Type*}

/-- Two oriented curves `a` and `b` cross transversally at a point, which is the start of the arc
of `a` labelled `a₀` and of the arc of `b` labelled `b₀`; the arcs ending there are the
predecessors `aNext.symm a₀` and `bNext.symm b₀`. The crossing is *compatible* with the region
labels on the two sides of these four arcs when the four corner regions agree, for one of the two
local orientations of the crossing. -/
def IsCrossingCompatible (aNext : Equiv.Perm A) (aLeft aRight : A → R) (bNext : Equiv.Perm B)
    (bLeft bRight : B → R) (a₀ : A) (b₀ : B) : Prop :=
  (aLeft (aNext.symm a₀) = bLeft b₀ ∧ aRight (aNext.symm a₀) = bLeft (bNext.symm b₀) ∧
      aLeft a₀ = bRight b₀ ∧ aRight a₀ = bRight (bNext.symm b₀)) ∨
    (aLeft (aNext.symm a₀) = bRight (bNext.symm b₀) ∧ aRight (aNext.symm a₀) = bRight b₀ ∧
      aLeft a₀ = bLeft (bNext.symm b₀) ∧ aRight a₀ = bLeft b₀)

variable {aNext : Equiv.Perm A} {aLeft aRight : A → R} {bNext : Equiv.Perm B}
  {bLeft bRight : B → R} {a₀ : A} {b₀ : B}

/-- A crossing is compatible exactly when the four corner regions agree for one of the two local
orientations of the crossing. -/
theorem isCrossingCompatible_iff :
    IsCrossingCompatible aNext aLeft aRight bNext bLeft bRight a₀ b₀ ↔
      (aLeft (aNext.symm a₀) = bLeft b₀ ∧ aRight (aNext.symm a₀) = bLeft (bNext.symm b₀) ∧
          aLeft a₀ = bRight b₀ ∧ aRight a₀ = bRight (bNext.symm b₀)) ∨
        (aLeft (aNext.symm a₀) = bRight (bNext.symm b₀) ∧ aRight (aNext.symm a₀) = bRight b₀ ∧
          aLeft a₀ = bLeft (bNext.symm b₀) ∧ aRight a₀ = bLeft b₀) :=
  Iff.rfl

/-- At a compatible crossing, the boundaries along the two curves of every region chain cancel:
the `a`-boundary of the `a`-part of `∂D` and the `b`-boundary of its `b`-part sum to zero there. -/
theorem IsCrossingCompatible.sum_eq_zero
    (h : IsCrossingCompatible aNext aLeft aRight bNext bLeft bRight a₀ b₀) (D : R → ℤ) :
    (D (aLeft (aNext.symm a₀)) - D (aRight (aNext.symm a₀)) - (D (aLeft a₀) - D (aRight a₀))) +
      (D (bLeft (bNext.symm b₀)) - D (bRight (bNext.symm b₀)) - (D (bLeft b₀) - D (bRight b₀))) =
      0 := by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ <;> rw [h₁, h₂, h₃, h₄] <;> abel

/-- At a compatible crossing, the multiplicities of a region chain at the four corners, read along
the arcs of either curve, have the same sum. -/
theorem IsCrossingCompatible.corner_sum_eq
    (h : IsCrossingCompatible aNext aLeft aRight bNext bLeft bRight a₀ b₀) (D : R → ℤ) :
    D (aLeft (aNext.symm a₀)) + D (aRight (aNext.symm a₀)) + (D (aLeft a₀) + D (aRight a₀)) =
      D (bLeft (bNext.symm b₀)) + D (bRight (bNext.symm b₀)) + (D (bLeft b₀) + D (bRight b₀)) := by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ <;> rw [h₁, h₂, h₃, h₄] <;> abel

/-- At a compatible crossing, the local intersection number of the `a`-part of `∂D` with the
`b`-part of `∂E` cancels that of the `b`-part of `∂E` with the `a`-part of `∂D`. Each is the sum of
the coefficients of one boundary on the two arcs at the crossing, times the change across the other
curve of the sum of the multiplicities on the two sides of the first. -/
theorem IsCrossingCompatible.cross_add_cross_eq_zero
    (h : IsCrossingCompatible aNext aLeft aRight bNext bLeft bRight a₀ b₀) (D E : R → ℤ) :
    (D (aLeft (aNext.symm a₀)) - D (aRight (aNext.symm a₀)) + (D (aLeft a₀) - D (aRight a₀))) *
        (E (aLeft a₀) + E (aRight a₀) - (E (aLeft (aNext.symm a₀)) + E (aRight (aNext.symm a₀)))) +
      (E (bLeft (bNext.symm b₀)) - E (bRight (bNext.symm b₀)) + (E (bLeft b₀) - E (bRight b₀))) *
        (D (bLeft b₀) + D (bRight b₀) - (D (bLeft (bNext.symm b₀)) + D (bRight (bNext.symm b₀)))) =
      0 := by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ <;> rw [h₁, h₂, h₃, h₄] <;> ring

/-- Summation by parts along an oriented curve: pairing the boundary of the `1`-chain `∂X` with
the corner sums of `Y` equals pairing the sums of the coefficients of `∂X` on the two arcs at each
point with the change there of the side sums of `Y`. -/
theorem sum_arcBoundary_mul_cornerSum {P : Type*} [Fintype P] (next : Equiv.Perm P)
    (left right : P → R) (X Y : R → ℤ) :
    ∑ q, (X (left (next.symm q)) - X (right (next.symm q)) - (X (left q) - X (right q))) *
        (Y (left (next.symm q)) + Y (right (next.symm q)) + (Y (left q) + Y (right q))) =
      ∑ q, (X (left (next.symm q)) - X (right (next.symm q)) + (X (left q) - X (right q))) *
        (Y (left q) + Y (right q) - (Y (left (next.symm q)) + Y (right (next.symm q)))) := by
  have h := Equiv.sum_comp next.symm fun q =>
    (X (left q) - X (right q)) * (Y (left q) + Y (right q))
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  calc _ = ∑ q, 2 * ((X (left (next.symm q)) - X (right (next.symm q))) *
          (Y (left (next.symm q)) + Y (right (next.symm q))) -
            (X (left q) - X (right q)) * (Y (left q) + Y (right q))) :=
        Finset.sum_congr rfl fun q _ => by ring
    _ = 0 := by rw [← Finset.mul_sum, Finset.sum_sub_distrib, h, sub_self, mul_zero]

/-- Summation by parts along an oriented curve, for point measures `m` given by the corner sums of
`Y` divided by four: pairing the boundary `c` of the `1`-chain `∂X` with `m` equals pairing the
sums of the coefficients of `∂X` on the two arcs at each point with the change there of the side
sums of `Y`, divided by four. -/
theorem sum_mul_cornerSum_div_four {P : Type*} [Fintype P] (next : Equiv.Perm P)
    (left right : P → R) (X Y : R → ℤ) (c : P → ℤ) (m : P → ℚ)
    (hc : ∀ q, c q = X (left (next.symm q)) - X (right (next.symm q)) - (X (left q) - X (right q)))
    (hm : ∀ q, m q = ((Y (left (next.symm q)) + Y (right (next.symm q)) +
      (Y (left q) + Y (right q)) : ℤ) : ℚ) / 4) :
    ∑ q, (c q : ℚ) * m q =
      ((∑ q, (X (left (next.symm q)) - X (right (next.symm q)) + (X (left q) - X (right q))) *
        (Y (left q) + Y (right q) - (Y (left (next.symm q)) + Y (right (next.symm q)))) : ℤ) :
          ℚ) / 4 := by
  rw [← sum_arcBoundary_mul_cornerSum, Int.cast_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun q _ => by rw [hc, hm]; push_cast; ring

end Crossing

end HeegaardRegionSystem

/-- The incidence data of a pointed Heegaard diagram needed for domains. On top of the
intersection data it records, for each intersection point `p`, the next intersection point along
the oriented `α`- and `β`-curve through `p`, the regions to the left and to the right of the arcs
starting at `p`, and the region containing each basepoint. The points on each curve form a single
cycle of the corresponding successor permutation when nonempty. Region labels agree around each
crossing. Each region is incident to an arc, apart from the one-region case with no arcs. The data
does not assert that the labels are the connected complementary regions of a particular surface
realization; that requires a separate identification. -/
@[ext]
structure HeegaardRegionSystem (n : ℕ) (Point : Type u) (Region : Type v) (Basepoint : Type w)
    extends HeegaardIntersectionSystem n Point where
  /-- The next intersection point along the oriented `α`-curve. -/
  alphaNext : Equiv.Perm Point
  /-- The intersection points on a nonempty `α`-curve fibre form one cycle of `alphaNext`;
  empty fibres satisfy this condition vacuously. -/
  alphaNext_isCycleOn (i : Fin n) : alphaNext.IsCycleOn {p | alpha p = i}
  /-- The next intersection point along the oriented `β`-curve. -/
  betaNext : Equiv.Perm Point
  /-- The intersection points on a nonempty `β`-curve fibre form one cycle of `betaNext`;
  empty fibres satisfy this condition vacuously. -/
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
    HeegaardRegionSystem.IsCrossingCompatible alphaNext alphaLeft alphaRight betaNext betaLeft
      betaRight p p
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

section WithBasepoints

/-- The same curves and regions with the basepoints replaced by basepoints indexed by `B` in the
regions `b`. Generators and domains do not involve the basepoints, so the generators of
`H.withBasepoints b` are those of `H`. Forgetting some of the basepoints is the case
`b = H.basepoint ∘ ι`; for a doubly pointed knot diagram this passes from the knot diagram to the
diagram of the ambient three-manifold pointed at `w` only. -/
abbrev withBasepoints {B : Type*} (b : B → Region) : HeegaardRegionSystem n Point Region B :=
  { H with basepoint := b }

variable {B : Type*} (b : B → Region)

@[simp]
theorem withBasepoints_basepoint : (H.withBasepoints b).basepoint = b :=
  (rfl)

@[simp]
theorem withBasepoints_toHeegaardIntersectionSystem :
    (H.withBasepoints b).toHeegaardIntersectionSystem = H.toHeegaardIntersectionSystem :=
  (rfl)

@[simp]
theorem withBasepoints_alphaLeft : (H.withBasepoints b).alphaLeft = H.alphaLeft :=
  (rfl)

@[simp]
theorem withBasepoints_alphaRight : (H.withBasepoints b).alphaRight = H.alphaRight :=
  (rfl)

@[simp]
theorem withBasepoints_betaLeft : (H.withBasepoints b).betaLeft = H.betaLeft :=
  (rfl)

@[simp]
theorem withBasepoints_betaRight : (H.withBasepoints b).betaRight = H.betaRight :=
  (rfl)

@[simp]
theorem withBasepoints_alphaNext : (H.withBasepoints b).alphaNext = H.alphaNext :=
  (rfl)

@[simp]
theorem withBasepoints_betaNext : (H.withBasepoints b).betaNext = H.betaNext :=
  (rfl)

@[simp]
theorem withBasepoints_basepoint_self : H.withBasepoints H.basepoint = H :=
  (rfl)

@[simp]
theorem withBasepoints_withBasepoints {B' : Type*} (b' : B' → Region) :
    (H.withBasepoints b).withBasepoints b' = H.withBasepoints b' :=
  (rfl)

end WithBasepoints

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

/-- The whole surface, the domain with multiplicity one in every region, has no `α`-boundary. -/
@[simp]
theorem alphaBoundary_one : H.alphaBoundary 1 = 0 := by
  ext
  simp

/-- The whole surface, the domain with multiplicity one in every region, has no `β`-boundary. -/
@[simp]
theorem betaBoundary_one : H.betaBoundary 1 = 0 := by
  ext
  simp

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
  exact (H.crossingCompatible p).sum_eq_zero D

/-- A `1`-chain on the `α`-arcs is a cycle exactly when it is a combination of whole `α`-curves,
that is, constant along each `α`-curve. -/
theorem alphaArcBoundary_eq_zero_iff (c : Point → ℤ) :
    H.alphaArcBoundary c = 0 ↔ ∃ a : Fin n → ℤ, ∀ p, c p = a (H.alpha p) := by
  simpa [funext_iff] using H.alphaNext.forall_comp_symm_sub_eq_zero_iff H.alphaNext_isCycleOn c

/-- A `1`-chain on the `β`-arcs is a cycle exactly when it is a combination of whole `β`-curves,
that is, constant along each `β`-curve. -/
theorem betaArcBoundary_eq_zero_iff (c : Point → ℤ) :
    H.betaArcBoundary c = 0 ↔ ∃ b : Fin n → ℤ, ∀ p, c p = b (H.beta p) := by
  simpa [funext_iff] using H.betaNext.forall_comp_symm_sub_eq_zero_iff H.betaNext_isCycleOn c

end Boundary

section Domain

variable {H}

/-- `D` is a domain connecting the generator `x` to the generator `y`: the boundary of its
`α`-part is `y - x` and the boundary of its `β`-part is `x - y`. The domain of every Whitney disk
from `x` to `y` satisfies these corner conditions. -/
def IsDomainBetween (x y : H.Generator) (D : Region → ℤ) : Prop :=
  H.alphaArcBoundary (H.alphaBoundary D) = H.generatorChain y - H.generatorChain x ∧
    H.betaArcBoundary (H.betaBoundary D) = H.generatorChain x - H.generatorChain y

@[simp]
theorem isDomainBetween_iff {x y : H.Generator} {D : Region → ℤ} :
    H.IsDomainBetween x y D ↔
      H.alphaArcBoundary (H.alphaBoundary D) = H.generatorChain y - H.generatorChain x ∧
        H.betaArcBoundary (H.betaBoundary D) = H.generatorChain x - H.generatorChain y :=
  Iff.rfl

/-- Being a domain between two generators does not involve the basepoints. -/
theorem isDomainBetween_withBasepoints {B : Type*} (b : B → Region) {x y : H.Generator}
    {D : Region → ℤ} : (H.withBasepoints b).IsDomainBetween x y D ↔ H.IsDomainBetween x y D :=
  Iff.rfl

/-- The zero domain connects every generator to itself. -/
theorem isDomainBetween_zero (x : H.Generator) : H.IsDomainBetween x x 0 := by
  simp

/-- The whole surface connects every generator to itself. -/
theorem isDomainBetween_one (x : H.Generator) : H.IsDomainBetween x x 1 := by
  simp

/-- A domain connects a generator to itself exactly when its `α`- and `β`-parts are cycles, that
is, when its boundary is a combination of whole curves. This does not depend on the generator. -/
theorem isDomainBetween_self_iff_arcBoundary_eq_zero {x : H.Generator} {E : Region → ℤ} :
    H.IsDomainBetween x x E ↔
      H.alphaArcBoundary (H.alphaBoundary E) = 0 ∧ H.betaArcBoundary (H.betaBoundary E) = 0 := by
  simp

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

/-- On an `α`-curve where `x` and `y` differ, the point of `x` is a corner of every domain from
`x` to `y`, at which the boundary of its `α`-part has coefficient `-1`. -/
theorem alphaArcBoundary_alphaBoundary_point_left
    (hD : H.IsDomainBetween x y D) {i : Fin n} (hi : H.point x i ≠ H.point y i) :
    H.alphaArcBoundary (H.alphaBoundary D) (H.point x i) = -1 := by
  classical
  simp only [HeegaardIntersectionSystem.point_apply] at hi
  rw [(isDomainBetween_iff.mp hD).1]
  simp [Ne.symm hi]

/-- On an `α`-curve where `x` and `y` differ, the point of `y` is a corner of every domain from
`x` to `y`, at which the boundary of its `α`-part has coefficient `1`. -/
theorem alphaArcBoundary_alphaBoundary_point_right
    (hD : H.IsDomainBetween x y D) {i : Fin n} (hi : H.point x i ≠ H.point y i) :
    H.alphaArcBoundary (H.alphaBoundary D) (H.point y i) = 1 := by
  classical
  simp only [HeegaardIntersectionSystem.point_apply] at hi
  rw [(isDomainBetween_iff.mp hD).1]
  simp [hi]

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

@[simp]
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
  simp [alphaArcBoundary_eq_zero_iff, betaArcBoundary_eq_zero_iff]

/-- A domain connects every generator to itself and avoids the basepoints exactly when it is
periodic. -/
theorem isDomainBetween_self_iff {x : H.Generator} {P : Region → ℤ} :
    H.IsDomainBetween x x P ∧ (∀ z, P (H.basepoint z) = 0) ↔ P ∈ H.periodicDomains := by
  simp [and_comm, and_assoc]

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

/-- In a diagram with a single basepoint `z`, a domain `E` connects a generator to itself exactly
when `E - n_z(E) Σ` is periodic, where `Σ = 1` is the whole surface. -/
theorem isDomainBetween_self_iff_sub_smul_one_mem_periodicDomains [Subsingleton Basepoint]
    (z : Basepoint) {x : H.Generator} {E : Region → ℤ} :
    H.IsDomainBetween x x E ↔ E - E (H.basepoint z) • 1 ∈ H.periodicDomains := by
  simp only [mem_periodicDomains_iff, isDomainBetween_iff, sub_self, map_sub, map_zsmul,
    alphaBoundary_one, betaBoundary_one, smul_zero, sub_zero, Pi.sub_apply, Pi.smul_apply,
    Pi.one_apply, smul_eq_mul, mul_one, Subsingleton.elim _ z, implies_true, true_and]

/-- In a diagram with at most one basepoint, a nonnegative domain `E` from `x` to itself is a
periodic domain plus a nonnegative number of copies of the whole surface: with a basepoint `z`,
that number is `n_z(E)`, and without one `E` is itself periodic. -/
theorem IsDomainBetween.exists_nonneg_sub_smul_one_mem_periodicDomains [Subsingleton Basepoint]
    {x : H.Generator} {E : Region → ℤ} (hE : H.IsDomainBetween x x E) (hE₀ : 0 ≤ E) :
    ∃ m : ℤ, 0 ≤ m ∧ E - m • 1 ∈ H.periodicDomains := by
  rcases isEmpty_or_nonempty Basepoint with hB | ⟨⟨z⟩⟩
  · exact ⟨0, le_rfl, by simpa using isDomainBetween_self_iff.mp ⟨hE, isEmptyElim⟩⟩
  · exact ⟨E (H.basepoint z), hE₀ _,
      (isDomainBetween_self_iff_sub_smul_one_mem_periodicDomains z).mp hE⟩

variable (H) in
/-- The supplied region incidence system is weakly admissible when every nonzero periodic domain
has both positive and negative coefficients. Interpreting this for a geometric diagram requires
identifying its actual complementary regions with `Region`. -/
def WeaklyAdmissible : Prop :=
  ∀ P ∈ H.periodicDomains, P ≠ 0 → (∃ r, 0 < P r) ∧ ∃ r, P r < 0

/-- A diagram is weakly admissible exactly when its only nonnegative periodic domain is zero. -/
theorem weaklyAdmissible_iff :
    H.WeaklyAdmissible ↔ ∀ P ∈ H.periodicDomains, 0 ≤ P → P = 0 :=
  H.periodicDomains.forall_exists_pos_and_neg_iff_forall_nonneg_eq_zero

end Domain

end HeegaardRegionSystem

end TauCeti
