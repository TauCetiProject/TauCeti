/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.Algebra.Group.AddSubgroup.NonnegativeCoset
public import TauCeti.Algebra.Group.AddSubgroup.PositiveWeights
public import TauCeti.LowDimTopology.Heegaard.Domain
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Heegaard triple diagrams: triangle domains and weak admissibility

A pointed Heegaard triple diagram `(Σ, α, β, γ, z)` carries three families of `n` attaching
curves. The holomorphic triangle maps of Heegaard Floer homology, which give the handleslide
invariance of `HF̂` and the maps of cobordisms, count Whitney triangles: maps of a triangle whose
three edges go to the tori `T_α`, `T_β` and `T_γ`, with corners at generators
`x ∈ T_α ∩ T_β`, `y ∈ T_β ∩ T_γ` and `w ∈ T_α ∩ T_γ`. As for Whitney disks, the class of such a
triangle is recorded by its *domain*, the integral combination of the regions of
`Σ - α - β - γ` given by its local multiplicities.

This file records the incidence data that triangle domains need, in the same form as
`TauCeti.HeegaardRegionSystem` does for a pair of curve families, and develops triangle domains,
periodic domains and weak admissibility on top of it. The intersection points come in three
kinds, `α ∩ β`, `β ∩ γ` and `α ∩ γ`, recorded by three intersection systems
(`TauCeti.HeegaardIntersectionSystem`); their generators are the possible corners. The points on
an `α`-curve are its `α ∩ β` and `α ∩ γ` points, and similarly for `β` and `γ`. As for a pair of
families, the data does not assert that the region labels are the connected components of the
complement of an actual triple of curve families on a surface; that identification is separate.

The boundary of the domain of a triangle with corners `x`, `y`, `w` runs along `α` from `x` to
`w`, along `γ` from `w` to `y` and along `β` from `y` to `x`
(`TauCeti.HeegaardTripleRegionSystem.IsTriangleDomain`). With this orientation, juxtaposing a
domain from `x` to `x'` in the `(α, β)` diagram with a triangle domain at `x'` gives a triangle
domain at `x`, and likewise at the other two corners; these are the actions of the disk classes
`π₂(x, x')`, `π₂(y, y')` and `π₂(w', w)` on the triangle classes `π₂(x, y, w)` used to show that
triangle maps are chain maps.

Two triangle domains with the same corners and basepoint multiplicities differ by a *triply
periodic domain*, one whose boundary is a sum of whole `α`-, `β`- and `γ`-curves. Among these are
the sums of *doubly periodic domains*, the periodic domains of the three diagrams `(α, β)`,
`(β, γ)` and `(α, γ)`; in the triple, a periodic domain of `(α, β)` is one with no `γ`-boundary.
On a geometric triple, the classes of triangles in a fixed spin^c structure of the associated
four-manifold `X_{αβγ}` differ by sums of doubly periodic domains (Ozsváth–Szabó, §8.1).
Accordingly, Ozsváth and Szabó call a triple *weakly admissible* when every nonzero sum of doubly
periodic domains has both positive and negative coefficients
(`TauCeti.HeegaardTripleRegionSystem.WeaklyAdmissible`), and prove that then only finitely many
nonnegative triangle domains lie in each such class. Here this is
`TauCeti.HeegaardTripleRegionSystem.WeaklyAdmissible.finite_setOf_nonneg_sub_mem`, together with
the area-form characterization of weak admissibility, under which the area of a triangle domain
depends only on its class. Once the energy of a holomorphic triangle is identified with the area
of its domain (an analytic input not formalized here), this is the energy bound behind the
finiteness of the triangle maps.

As for pairs, the condition here quantifies over all doubly periodic domains, without
restricting to those with zero pairing against the first Chern class of a spin^c structure, so it
implies the spin^c-wise conditions of Ozsváth and Szabó.

## Main definitions

* `TauCeti.HeegaardTripleRegionSystem.IsCrossingCompatible`: the four region labels at a
  transverse crossing of two oriented curves agree.
* `TauCeti.HeegaardTripleRegionSystem`: the incidence data of a pointed Heegaard triple diagram.
* `TauCeti.HeegaardTripleRegionSystem.IsTriangleDomain`: `D` is a domain of a triangle with
  corners `x`, `y`, `w`.
* `TauCeti.HeegaardTripleRegionSystem.IsAlphaBetaDomainBetween` and its `(β, γ)` and `(α, γ)`
  counterparts: domains of the three Heegaard diagrams of the triple, read in the regions of the
  triple.
* `TauCeti.HeegaardTripleRegionSystem.triplyPeriodicDomains`,
  `TauCeti.HeegaardTripleRegionSystem.alphaBetaPeriodicDomains` (and its two counterparts) and
  `TauCeti.HeegaardTripleRegionSystem.doublyPeriodicDomains`: the triply periodic domains, the
  periodic domains of the three diagrams, and their sums.
* `TauCeti.HeegaardTripleRegionSystem.WeaklyAdmissible`: every nonzero sum of doubly periodic
  domains has both positive and negative coefficients.

## Main results

* `TauCeti.HeegaardTripleRegionSystem.boundary_boundary_alphaBeta_eq_zero` and its two
  counterparts: the full boundary of every domain is a cycle.
* `TauCeti.HeegaardTripleRegionSystem.mem_triplyPeriodicDomains_iff_exists_curves`: a domain is
  triply periodic exactly when it avoids the basepoints and its boundary is a combination of whole
  curves.
* `TauCeti.HeegaardTripleRegionSystem.IsTriangleDomain.sub_mem_triplyPeriodicDomains_iff`: the
  triangle domains with given corners and basepoint multiplicities form a coset of the triply
  periodic domains.
* `TauCeti.HeegaardTripleRegionSystem.IsAlphaBetaDomainBetween.add_isTriangleDomain`,
  `TauCeti.HeegaardTripleRegionSystem.IsBetaGammaDomainBetween.add_isTriangleDomain` and
  `TauCeti.HeegaardTripleRegionSystem.IsTriangleDomain.add_isAlphaGammaDomainBetween`:
  juxtaposition of disk domains with triangle domains.
* `TauCeti.HeegaardTripleRegionSystem.weaklyAdmissible_iff_exists_pos_forall_sum_mul_eq_zero`:
  weak admissibility is the existence of a strictly positive area form vanishing on doubly
  periodic domains, and `TauCeti.HeegaardTripleRegionSystem.sum_mul_eq_of_sub_mem` says that
  domains in one class have the same area.
* `TauCeti.HeegaardTripleRegionSystem.WeaklyAdmissible.finite_setOf_nonneg_sub_mem` and
  `TauCeti.HeegaardTripleRegionSystem.weaklyAdmissible_iff_forall_finite_setOf_nonneg_sub_mem`:
  weak admissibility is the finiteness of the nonnegative domains in each class.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §8.1 (Heegaard triples, triangles,
  triply and doubly periodic domains, Definition 8.8 of weak admissibility for triples and the
  finiteness of nonnegative triangle classes in Lemmas 8.9–8.11).
* S. Sarkar, *Maslov index formulas for Whitney n-gons*, J. Symplectic Geom. **9** (2011), for
  domains of Whitney polygons and their corner conditions.
-/

public section

open Finset

namespace TauCeti

universe u₁ u₂ u₃ v w

/-- Two oriented curves `a` and `b` cross transversally at a point, which is the start of the arc
of `a` labelled `a₀` and of the arc of `b` labelled `b₀`; the arcs ending there are the
predecessors `aNext.symm a₀` and `bNext.symm b₀`. The crossing is *compatible* with the region
labels on the two sides of these four arcs when the four corner regions agree, for one of the two
local orientations of the crossing. -/
def HeegaardTripleRegionSystem.IsCrossingCompatible {A B R : Type*} (aNext : Equiv.Perm A)
    (aLeft aRight : A → R) (bNext : Equiv.Perm B) (bLeft bRight : B → R) (a₀ : A) (b₀ : B) : Prop :=
  (aLeft (aNext.symm a₀) = bLeft b₀ ∧ aRight (aNext.symm a₀) = bLeft (bNext.symm b₀) ∧
      aLeft a₀ = bRight b₀ ∧ aRight a₀ = bRight (bNext.symm b₀)) ∨
    (aLeft (aNext.symm a₀) = bRight (bNext.symm b₀) ∧ aRight (aNext.symm a₀) = bRight b₀ ∧
      aLeft a₀ = bLeft (bNext.symm b₀) ∧ aRight a₀ = bLeft b₀)

/-- A crossing is compatible exactly when the four corner regions agree for one of the two local
orientations of the crossing. -/
theorem HeegaardTripleRegionSystem.isCrossingCompatible_iff {A B R : Type*}
    {aNext : Equiv.Perm A} {aLeft aRight : A → R} {bNext : Equiv.Perm B} {bLeft bRight : B → R}
    {a₀ : A} {b₀ : B} :
    HeegaardTripleRegionSystem.IsCrossingCompatible aNext aLeft aRight bNext bLeft bRight a₀ b₀ ↔
      (aLeft (aNext.symm a₀) = bLeft b₀ ∧ aRight (aNext.symm a₀) = bLeft (bNext.symm b₀) ∧
          aLeft a₀ = bRight b₀ ∧ aRight a₀ = bRight (bNext.symm b₀)) ∨
        (aLeft (aNext.symm a₀) = bRight (bNext.symm b₀) ∧ aRight (aNext.symm a₀) = bRight b₀ ∧
          aLeft a₀ = bLeft (bNext.symm b₀) ∧ aRight a₀ = bLeft b₀) :=
  Iff.rfl

/-- At a compatible crossing, the boundaries along the two curves of every region chain cancel:
the `a`-boundary of the `a`-part of `∂D` and the `b`-boundary of its `b`-part sum to zero there. -/
theorem HeegaardTripleRegionSystem.IsCrossingCompatible.sum_eq_zero {A B R : Type*}
    {aNext : Equiv.Perm A} {aLeft aRight : A → R} {bNext : Equiv.Perm B} {bLeft bRight : B → R}
    {a₀ : A} {b₀ : B}
    (h : HeegaardTripleRegionSystem.IsCrossingCompatible aNext aLeft aRight bNext bLeft bRight
      a₀ b₀)
    (D : R → ℤ) :
    (D (aLeft (aNext.symm a₀)) - D (aRight (aNext.symm a₀)) - (D (aLeft a₀) - D (aRight a₀))) +
      (D (bLeft (bNext.symm b₀)) - D (bRight (bNext.symm b₀)) - (D (bLeft b₀) - D (bRight b₀))) =
      0 := by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ <;> rw [h₁, h₂, h₃, h₄] <;> abel

/-- The incidence data of a pointed Heegaard triple diagram `(Σ, α, β, γ, z)` needed for triangle
domains. The intersection points of the three kinds are recorded by three intersection systems:
`alphaBeta` labels each point of `α ∩ β` by its `α`- and `β`-curve, `betaGamma` labels each point of
`β ∩ γ` by its `β`-curve (its `alpha` label) and its `γ`-curve (its `beta` label), and `alphaGamma`
labels each point of `α ∩ γ` by its `α`-curve and its `γ`-curve (its `beta` label). The points on
the `α`-curves are those of `α ∩ β` and of `α ∩ γ`, and so on. For each family the data records
the next point along the oriented curve, the regions to the left and right of the arc starting
at each point, compatibility of the region labels at every crossing, and the region containing
each basepoint. The data does not assert that the labels are the connected complementary regions
of a particular triple of curve families on a surface. -/
@[ext]
structure HeegaardTripleRegionSystem (n : ℕ) (PointAB : Type u₁) (PointBC : Type u₂)
    (PointAC : Type u₃) (Region : Type v) (Basepoint : Type w) where
  /-- The labels of the points of `α ∩ β` by their `α`- and `β`-curves. -/
  alphaBeta : HeegaardIntersectionSystem n PointAB
  /-- The labels of the points of `β ∩ γ` by their `β`-curve (`alpha`) and `γ`-curve (`beta`). -/
  betaGamma : HeegaardIntersectionSystem n PointBC
  /-- The labels of the points of `α ∩ γ` by their `α`-curve (`alpha`) and `γ`-curve (`beta`). -/
  alphaGamma : HeegaardIntersectionSystem n PointAC
  /-- The next point along the oriented `α`-curve. -/
  alphaNext : Equiv.Perm (PointAB ⊕ PointAC)
  /-- The points on a nonempty `α`-curve form one cycle of `alphaNext`. -/
  alphaNext_isCycleOn (i : Fin n) :
    alphaNext.IsCycleOn {p | Sum.elim alphaBeta.alpha alphaGamma.alpha p = i}
  /-- The next point along the oriented `β`-curve. -/
  betaNext : Equiv.Perm (PointAB ⊕ PointBC)
  /-- The points on a nonempty `β`-curve form one cycle of `betaNext`. -/
  betaNext_isCycleOn (j : Fin n) :
    betaNext.IsCycleOn {p | Sum.elim alphaBeta.beta betaGamma.alpha p = j}
  /-- The next point along the oriented `γ`-curve. -/
  gammaNext : Equiv.Perm (PointBC ⊕ PointAC)
  /-- The points on a nonempty `γ`-curve form one cycle of `gammaNext`. -/
  gammaNext_isCycleOn (k : Fin n) :
    gammaNext.IsCycleOn {p | Sum.elim betaGamma.beta alphaGamma.beta p = k}
  /-- The region to the left of the `α`-arc starting at a point. -/
  alphaLeft : PointAB ⊕ PointAC → Region
  /-- The region to the right of the `α`-arc starting at a point. -/
  alphaRight : PointAB ⊕ PointAC → Region
  /-- The region to the left of the `β`-arc starting at a point. -/
  betaLeft : PointAB ⊕ PointBC → Region
  /-- The region to the right of the `β`-arc starting at a point. -/
  betaRight : PointAB ⊕ PointBC → Region
  /-- The region to the left of the `γ`-arc starting at a point. -/
  gammaLeft : PointBC ⊕ PointAC → Region
  /-- The region to the right of the `γ`-arc starting at a point. -/
  gammaRight : PointBC ⊕ PointAC → Region
  /-- The region labels agree around each crossing of an `α`- and a `β`-curve. -/
  crossing_alphaBeta (p : PointAB) :
    HeegaardTripleRegionSystem.IsCrossingCompatible alphaNext alphaLeft alphaRight betaNext
      betaLeft betaRight (.inl p) (.inl p)
  /-- The region labels agree around each crossing of a `β`- and a `γ`-curve. -/
  crossing_betaGamma (p : PointBC) :
    HeegaardTripleRegionSystem.IsCrossingCompatible betaNext betaLeft betaRight gammaNext
      gammaLeft gammaRight (.inr p) (.inl p)
  /-- The region labels agree around each crossing of an `α`- and a `γ`-curve. -/
  crossing_alphaGamma (p : PointAC) :
    HeegaardTripleRegionSystem.IsCrossingCompatible alphaNext alphaLeft alphaRight gammaNext
      gammaLeft gammaRight (.inr p) (.inr p)
  /-- The region containing a basepoint. -/
  basepoint : Basepoint → Region

namespace HeegaardTripleRegionSystem

variable {n : ℕ} {PointAB : Type u₁} {PointBC : Type u₂} {PointAC : Type u₃} {Region : Type v}
  {Basepoint : Type w}
  (T : HeegaardTripleRegionSystem n PointAB PointBC PointAC Region Basepoint)

/-- The successor along an `α`-curve stays on that curve. -/
@[simp]
theorem alpha_alphaNext (p : PointAB ⊕ PointAC) :
    Sum.elim T.alphaBeta.alpha T.alphaGamma.alpha (T.alphaNext p) =
      Sum.elim T.alphaBeta.alpha T.alphaGamma.alpha p :=
  (T.alphaNext_isCycleOn _).1.mapsTo rfl

/-- The predecessor along an `α`-curve stays on that curve. -/
@[simp]
theorem alpha_alphaNext_symm (p : PointAB ⊕ PointAC) :
    Sum.elim T.alphaBeta.alpha T.alphaGamma.alpha (T.alphaNext.symm p) =
      Sum.elim T.alphaBeta.alpha T.alphaGamma.alpha p := by
  simpa using (T.alpha_alphaNext (T.alphaNext.symm p)).symm

/-- The successor along a `β`-curve stays on that curve. -/
@[simp]
theorem beta_betaNext (p : PointAB ⊕ PointBC) :
    Sum.elim T.alphaBeta.beta T.betaGamma.alpha (T.betaNext p) =
      Sum.elim T.alphaBeta.beta T.betaGamma.alpha p :=
  (T.betaNext_isCycleOn _).1.mapsTo rfl

/-- The predecessor along a `β`-curve stays on that curve. -/
@[simp]
theorem beta_betaNext_symm (p : PointAB ⊕ PointBC) :
    Sum.elim T.alphaBeta.beta T.betaGamma.alpha (T.betaNext.symm p) =
      Sum.elim T.alphaBeta.beta T.betaGamma.alpha p := by
  simpa using (T.beta_betaNext (T.betaNext.symm p)).symm

/-- The successor along a `γ`-curve stays on that curve. -/
@[simp]
theorem gamma_gammaNext (p : PointBC ⊕ PointAC) :
    Sum.elim T.betaGamma.beta T.alphaGamma.beta (T.gammaNext p) =
      Sum.elim T.betaGamma.beta T.alphaGamma.beta p :=
  (T.gammaNext_isCycleOn _).1.mapsTo rfl

/-- The predecessor along a `γ`-curve stays on that curve. -/
@[simp]
theorem gamma_gammaNext_symm (p : PointBC ⊕ PointAC) :
    Sum.elim T.betaGamma.beta T.alphaGamma.beta (T.gammaNext.symm p) =
      Sum.elim T.betaGamma.beta T.alphaGamma.beta p := by
  simpa using (T.gamma_gammaNext (T.gammaNext.symm p)).symm

section Boundary

/-- The `α`-part `∂D ∩ α` of the boundary of a domain, as a `1`-chain on the `α`-arcs: its
coefficient on the arc starting at `p` is the multiplicity of `D` to the left of the arc minus
the multiplicity to its right. -/
def alphaBoundary : (Region → ℤ) →+ (PointAB ⊕ PointAC → ℤ) where
  toFun D p := D (T.alphaLeft p) - D (T.alphaRight p)
  map_zero' := by ext; simp
  map_add' D E := by ext; simp only [Pi.add_apply]; abel

/-- The `β`-part `∂D ∩ β` of the boundary of a domain, as a `1`-chain on the `β`-arcs. -/
def betaBoundary : (Region → ℤ) →+ (PointAB ⊕ PointBC → ℤ) where
  toFun D p := D (T.betaLeft p) - D (T.betaRight p)
  map_zero' := by ext; simp
  map_add' D E := by ext; simp only [Pi.add_apply]; abel

/-- The `γ`-part `∂D ∩ γ` of the boundary of a domain, as a `1`-chain on the `γ`-arcs. -/
def gammaBoundary : (Region → ℤ) →+ (PointBC ⊕ PointAC → ℤ) where
  toFun D p := D (T.gammaLeft p) - D (T.gammaRight p)
  map_zero' := by ext; simp
  map_add' D E := by ext; simp only [Pi.add_apply]; abel

@[simp]
theorem alphaBoundary_apply (D : Region → ℤ) (p : PointAB ⊕ PointAC) :
    T.alphaBoundary D p = D (T.alphaLeft p) - D (T.alphaRight p) :=
  (rfl)

@[simp]
theorem betaBoundary_apply (D : Region → ℤ) (p : PointAB ⊕ PointBC) :
    T.betaBoundary D p = D (T.betaLeft p) - D (T.betaRight p) :=
  (rfl)

@[simp]
theorem gammaBoundary_apply (D : Region → ℤ) (p : PointBC ⊕ PointAC) :
    T.gammaBoundary D p = D (T.gammaLeft p) - D (T.gammaRight p) :=
  (rfl)

/-- The whole surface, the domain with multiplicity one in every region, has no `α`-boundary. -/
@[simp]
theorem alphaBoundary_one : T.alphaBoundary 1 = 0 := by
  ext
  simp

/-- The whole surface, the domain with multiplicity one in every region, has no `β`-boundary. -/
@[simp]
theorem betaBoundary_one : T.betaBoundary 1 = 0 := by
  ext
  simp

/-- The whole surface, the domain with multiplicity one in every region, has no `γ`-boundary. -/
@[simp]
theorem gammaBoundary_one : T.gammaBoundary 1 = 0 := by
  ext
  simp

/-- The boundary of a `1`-chain on the `α`-arcs, indexed by starting points: the coefficient at
`q` is that of the arc ending at `q` minus that of the arc starting at `q`. -/
def alphaArcBoundary : (PointAB ⊕ PointAC → ℤ) →+ (PointAB ⊕ PointAC → ℤ) where
  toFun c q := c (T.alphaNext.symm q) - c q
  map_zero' := by ext; simp
  map_add' c d := by ext; simp only [Pi.add_apply]; abel

/-- The boundary of a `1`-chain on the `β`-arcs, indexed by starting points. -/
def betaArcBoundary : (PointAB ⊕ PointBC → ℤ) →+ (PointAB ⊕ PointBC → ℤ) where
  toFun c q := c (T.betaNext.symm q) - c q
  map_zero' := by ext; simp
  map_add' c d := by ext; simp only [Pi.add_apply]; abel

/-- The boundary of a `1`-chain on the `γ`-arcs, indexed by starting points. -/
def gammaArcBoundary : (PointBC ⊕ PointAC → ℤ) →+ (PointBC ⊕ PointAC → ℤ) where
  toFun c q := c (T.gammaNext.symm q) - c q
  map_zero' := by ext; simp
  map_add' c d := by ext; simp only [Pi.add_apply]; abel

@[simp]
theorem alphaArcBoundary_apply (c : PointAB ⊕ PointAC → ℤ) (q : PointAB ⊕ PointAC) :
    T.alphaArcBoundary c q = c (T.alphaNext.symm q) - c q :=
  (rfl)

@[simp]
theorem betaArcBoundary_apply (c : PointAB ⊕ PointBC → ℤ) (q : PointAB ⊕ PointBC) :
    T.betaArcBoundary c q = c (T.betaNext.symm q) - c q :=
  (rfl)

@[simp]
theorem gammaArcBoundary_apply (c : PointBC ⊕ PointAC → ℤ) (q : PointBC ⊕ PointAC) :
    T.gammaArcBoundary c q = c (T.gammaNext.symm q) - c q :=
  (rfl)

/-- At a point of `α ∩ β`, the boundaries of the `α`- and `β`-parts of the boundary of a domain
cancel. -/
theorem boundary_boundary_alphaBeta_eq_zero (D : Region → ℤ) (p : PointAB) :
    T.alphaArcBoundary (T.alphaBoundary D) (.inl p) +
      T.betaArcBoundary (T.betaBoundary D) (.inl p) = 0 := by
  simpa using (T.crossing_alphaBeta p).sum_eq_zero D

/-- At a point of `β ∩ γ`, the boundaries of the `β`- and `γ`-parts of the boundary of a domain
cancel. -/
theorem boundary_boundary_betaGamma_eq_zero (D : Region → ℤ) (p : PointBC) :
    T.betaArcBoundary (T.betaBoundary D) (.inr p) +
      T.gammaArcBoundary (T.gammaBoundary D) (.inl p) = 0 := by
  simpa using (T.crossing_betaGamma p).sum_eq_zero D

/-- At a point of `α ∩ γ`, the boundaries of the `α`- and `γ`-parts of the boundary of a domain
cancel. -/
theorem boundary_boundary_alphaGamma_eq_zero (D : Region → ℤ) (p : PointAC) :
    T.alphaArcBoundary (T.alphaBoundary D) (.inr p) +
      T.gammaArcBoundary (T.gammaBoundary D) (.inr p) = 0 := by
  simpa using (T.crossing_alphaGamma p).sum_eq_zero D

/-- A `1`-chain on the `α`-arcs is a cycle exactly when it is a combination of whole `α`-curves. -/
theorem alphaArcBoundary_eq_zero_iff (c : PointAB ⊕ PointAC → ℤ) :
    T.alphaArcBoundary c = 0 ↔
      ∃ a : Fin n → ℤ, ∀ p, c p = a (Sum.elim T.alphaBeta.alpha T.alphaGamma.alpha p) := by
  simpa [funext_iff] using T.alphaNext.forall_comp_symm_sub_eq_zero_iff T.alphaNext_isCycleOn c

/-- A `1`-chain on the `β`-arcs is a cycle exactly when it is a combination of whole `β`-curves. -/
theorem betaArcBoundary_eq_zero_iff (c : PointAB ⊕ PointBC → ℤ) :
    T.betaArcBoundary c = 0 ↔
      ∃ b : Fin n → ℤ, ∀ p, c p = b (Sum.elim T.alphaBeta.beta T.betaGamma.alpha p) := by
  simpa [funext_iff] using T.betaNext.forall_comp_symm_sub_eq_zero_iff T.betaNext_isCycleOn c

/-- A `1`-chain on the `γ`-arcs is a cycle exactly when it is a combination of whole `γ`-curves. -/
theorem gammaArcBoundary_eq_zero_iff (c : PointBC ⊕ PointAC → ℤ) :
    T.gammaArcBoundary c = 0 ↔
      ∃ k : Fin n → ℤ, ∀ p, c p = k (Sum.elim T.betaGamma.beta T.alphaGamma.beta p) := by
  simpa [funext_iff] using T.gammaNext.forall_comp_symm_sub_eq_zero_iff T.gammaNext_isCycleOn c

end Boundary

section Domain

variable {T}
variable {x x' : T.alphaBeta.Generator} {y y' : T.betaGamma.Generator}
  {w w' : T.alphaGamma.Generator} {D E : Region → ℤ}

/-- `D` is the domain of a triangle with corners `x ∈ T_α ∩ T_β`, `y ∈ T_β ∩ T_γ` and
`w ∈ T_α ∩ T_γ`: the boundary of its `α`-part is `w - x`, that of its `β`-part is `x - y` and that
of its `γ`-part is `y - w`. So `∂D` runs along `α` from `x` to `w`, along `γ` from `w` to `y` and
along `β` from `y` to `x`. -/
def IsTriangleDomain (x : T.alphaBeta.Generator) (y : T.betaGamma.Generator)
    (w : T.alphaGamma.Generator) (D : Region → ℤ) : Prop :=
  T.alphaArcBoundary (T.alphaBoundary D) =
      Sum.elim (-T.alphaBeta.generatorChain x) (T.alphaGamma.generatorChain w) ∧
    T.betaArcBoundary (T.betaBoundary D) =
      Sum.elim (T.alphaBeta.generatorChain x) (-T.betaGamma.generatorChain y) ∧
    T.gammaArcBoundary (T.gammaBoundary D) =
      Sum.elim (T.betaGamma.generatorChain y) (-T.alphaGamma.generatorChain w)

@[simp]
theorem isTriangleDomain_iff :
    T.IsTriangleDomain x y w D ↔
      T.alphaArcBoundary (T.alphaBoundary D) =
          Sum.elim (-T.alphaBeta.generatorChain x) (T.alphaGamma.generatorChain w) ∧
        T.betaArcBoundary (T.betaBoundary D) =
          Sum.elim (T.alphaBeta.generatorChain x) (-T.betaGamma.generatorChain y) ∧
        T.gammaArcBoundary (T.gammaBoundary D) =
          Sum.elim (T.betaGamma.generatorChain y) (-T.alphaGamma.generatorChain w) :=
  Iff.rfl

/-- `D` is the domain of a disk from `x` to `x'` in the Heegaard diagram `(Σ, α, β)` of the triple,
read in the regions of the triple: it has no `γ`-boundary, the boundary of its `α`-part is
`x' - x` and that of its `β`-part is `x - x'`. -/
def IsAlphaBetaDomainBetween (x x' : T.alphaBeta.Generator) (D : Region → ℤ) : Prop :=
  T.alphaArcBoundary (T.alphaBoundary D) =
      Sum.elim (T.alphaBeta.generatorChain x' - T.alphaBeta.generatorChain x) 0 ∧
    T.betaArcBoundary (T.betaBoundary D) =
      Sum.elim (T.alphaBeta.generatorChain x - T.alphaBeta.generatorChain x') 0 ∧
    T.gammaBoundary D = 0

/-- `D` is the domain of a disk from `y` to `y'` in the Heegaard diagram `(Σ, β, γ)` of the triple:
it has no `α`-boundary, the boundary of its `β`-part is `y' - y` and that of its `γ`-part is
`y - y'`. -/
def IsBetaGammaDomainBetween (y y' : T.betaGamma.Generator) (D : Region → ℤ) : Prop :=
  T.alphaBoundary D = 0 ∧
    T.betaArcBoundary (T.betaBoundary D) =
      Sum.elim (0 : PointAB → ℤ) (T.betaGamma.generatorChain y' - T.betaGamma.generatorChain y) ∧
    T.gammaArcBoundary (T.gammaBoundary D) =
      Sum.elim (T.betaGamma.generatorChain y - T.betaGamma.generatorChain y') 0

/-- `D` is the domain of a disk from `w` to `w'` in the Heegaard diagram `(Σ, α, γ)` of the triple:
it has no `β`-boundary, the boundary of its `α`-part is `w' - w` and that of its `γ`-part is
`w - w'`. -/
def IsAlphaGammaDomainBetween (w w' : T.alphaGamma.Generator) (D : Region → ℤ) : Prop :=
  T.alphaArcBoundary (T.alphaBoundary D) =
      Sum.elim (0 : PointAB → ℤ) (T.alphaGamma.generatorChain w' - T.alphaGamma.generatorChain w) ∧
    T.betaBoundary D = 0 ∧
    T.gammaArcBoundary (T.gammaBoundary D) =
      Sum.elim (0 : PointBC → ℤ) (T.alphaGamma.generatorChain w - T.alphaGamma.generatorChain w')

@[simp]
theorem isAlphaBetaDomainBetween_iff :
    T.IsAlphaBetaDomainBetween x x' D ↔
      T.alphaArcBoundary (T.alphaBoundary D) =
          Sum.elim (T.alphaBeta.generatorChain x' - T.alphaBeta.generatorChain x) 0 ∧
        T.betaArcBoundary (T.betaBoundary D) =
          Sum.elim (T.alphaBeta.generatorChain x - T.alphaBeta.generatorChain x') 0 ∧
        T.gammaBoundary D = 0 :=
  Iff.rfl

@[simp]
theorem isBetaGammaDomainBetween_iff :
    T.IsBetaGammaDomainBetween y y' D ↔
      T.alphaBoundary D = 0 ∧
        T.betaArcBoundary (T.betaBoundary D) =
          Sum.elim (0 : PointAB → ℤ)
            (T.betaGamma.generatorChain y' - T.betaGamma.generatorChain y) ∧
        T.gammaArcBoundary (T.gammaBoundary D) =
          Sum.elim (T.betaGamma.generatorChain y - T.betaGamma.generatorChain y') 0 :=
  Iff.rfl

@[simp]
theorem isAlphaGammaDomainBetween_iff :
    T.IsAlphaGammaDomainBetween w w' D ↔
      T.alphaArcBoundary (T.alphaBoundary D) =
          Sum.elim (0 : PointAB → ℤ)
            (T.alphaGamma.generatorChain w' - T.alphaGamma.generatorChain w) ∧
        T.betaBoundary D = 0 ∧
        T.gammaArcBoundary (T.gammaBoundary D) =
          Sum.elim (0 : PointBC → ℤ)
            (T.alphaGamma.generatorChain w - T.alphaGamma.generatorChain w') :=
  Iff.rfl

/-- The zero domain connects every generator of `(Σ, α, β)` to itself. -/
theorem isAlphaBetaDomainBetween_zero (x : T.alphaBeta.Generator) :
    T.IsAlphaBetaDomainBetween x x 0 := by
  simp

/-- The whole surface connects every generator of `(Σ, α, β)` to itself. -/
theorem isAlphaBetaDomainBetween_one (x : T.alphaBeta.Generator) :
    T.IsAlphaBetaDomainBetween x x 1 := by
  simp

/-- The zero domain connects every generator of `(Σ, β, γ)` to itself. -/
theorem isBetaGammaDomainBetween_zero (y : T.betaGamma.Generator) :
    T.IsBetaGammaDomainBetween y y 0 := by
  simp

/-- The whole surface connects every generator of `(Σ, β, γ)` to itself. -/
theorem isBetaGammaDomainBetween_one (y : T.betaGamma.Generator) :
    T.IsBetaGammaDomainBetween y y 1 := by
  simp

/-- The zero domain connects every generator of `(Σ, α, γ)` to itself. -/
theorem isAlphaGammaDomainBetween_zero (w : T.alphaGamma.Generator) :
    T.IsAlphaGammaDomainBetween w w 0 := by
  simp

/-- The whole surface connects every generator of `(Σ, α, γ)` to itself. -/
theorem isAlphaGammaDomainBetween_one (w : T.alphaGamma.Generator) :
    T.IsAlphaGammaDomainBetween w w 1 := by
  simp

/-- Juxtaposing a domain from `x` to `x'` with one from `x'` to `x''` in `(Σ, α, β)` gives a
domain from `x` to `x''`. -/
theorem IsAlphaBetaDomainBetween.add {x'' : T.alphaBeta.Generator}
    (hD : T.IsAlphaBetaDomainBetween x x' D) (hE : T.IsAlphaBetaDomainBetween x' x'' E) :
    T.IsAlphaBetaDomainBetween x x'' (D + E) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_add, map_add, hD.1, hE.1]
    ext (p | p) <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply,
      Pi.zero_apply] <;> ring
  · rw [map_add, map_add, hD.2.1, hE.2.1]
    ext (p | p) <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply,
      Pi.zero_apply] <;> ring
  · rw [map_add, hD.2.2, hE.2.2, add_zero]

/-- Reversing a domain from `x` to `x'` in `(Σ, α, β)` gives a domain from `x'` to `x`. -/
theorem IsAlphaBetaDomainBetween.neg (hD : T.IsAlphaBetaDomainBetween x x' D) :
    T.IsAlphaBetaDomainBetween x' x (-D) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_neg, map_neg, hD.1]
    ext (p | p) <;> simp
  · rw [map_neg, map_neg, hD.2.1]
    ext (p | p) <;> simp
  · rw [map_neg, hD.2.2, neg_zero]

/-- Juxtaposing a domain from `y` to `y'` with one from `y'` to `y''` in `(Σ, β, γ)` gives a
domain from `y` to `y''`. -/
theorem IsBetaGammaDomainBetween.add {y'' : T.betaGamma.Generator}
    (hD : T.IsBetaGammaDomainBetween y y' D) (hE : T.IsBetaGammaDomainBetween y' y'' E) :
    T.IsBetaGammaDomainBetween y y'' (D + E) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_add, hD.1, hE.1, add_zero]
  · rw [map_add, map_add, hD.2.1, hE.2.1]
    ext (p | p) <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply,
      Pi.zero_apply] <;> ring
  · rw [map_add, map_add, hD.2.2, hE.2.2]
    ext (p | p) <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply,
      Pi.zero_apply] <;> ring

/-- Reversing a domain from `y` to `y'` in `(Σ, β, γ)` gives a domain from `y'` to `y`. -/
theorem IsBetaGammaDomainBetween.neg (hD : T.IsBetaGammaDomainBetween y y' D) :
    T.IsBetaGammaDomainBetween y' y (-D) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_neg, hD.1, neg_zero]
  · rw [map_neg, map_neg, hD.2.1]
    ext (p | p) <;> simp
  · rw [map_neg, map_neg, hD.2.2]
    ext (p | p) <;> simp

/-- Juxtaposing a domain from `w` to `w'` with one from `w'` to `w''` in `(Σ, α, γ)` gives a
domain from `w` to `w''`. -/
theorem IsAlphaGammaDomainBetween.add {w'' : T.alphaGamma.Generator}
    (hD : T.IsAlphaGammaDomainBetween w w' D) (hE : T.IsAlphaGammaDomainBetween w' w'' E) :
    T.IsAlphaGammaDomainBetween w w'' (D + E) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_add, map_add, hD.1, hE.1]
    ext (p | p) <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply,
      Pi.zero_apply] <;> ring
  · rw [map_add, hD.2.1, hE.2.1, add_zero]
  · rw [map_add, map_add, hD.2.2, hE.2.2]
    ext (p | p) <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply,
      Pi.zero_apply] <;> ring

/-- Reversing a domain from `w` to `w'` in `(Σ, α, γ)` gives a domain from `w'` to `w`. -/
theorem IsAlphaGammaDomainBetween.neg (hD : T.IsAlphaGammaDomainBetween w w' D) :
    T.IsAlphaGammaDomainBetween w' w (-D) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_neg, map_neg, hD.1]
    ext (p | p) <;> simp
  · rw [map_neg, hD.2.1, neg_zero]
  · rw [map_neg, map_neg, hD.2.2]
    ext (p | p) <;> simp

/-- Juxtaposing a disk domain from `x` to `x'` in `(Σ, α, β)` with a triangle domain at the corner
`x'` gives a triangle domain at the corner `x`. -/
theorem IsAlphaBetaDomainBetween.add_isTriangleDomain (hD : T.IsAlphaBetaDomainBetween x x' D)
    (hE : T.IsTriangleDomain x' y w E) : T.IsTriangleDomain x y w (D + E) := by
  obtain ⟨hDα, hDβ, hDγ⟩ := hD
  obtain ⟨hEα, hEβ, hEγ⟩ := hE
  refine ⟨?_, ?_, ?_⟩
  · rw [map_add, map_add, hDα, hEα]
    ext (p | p) <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply,
      Pi.neg_apply, Pi.zero_apply] <;> ring
  · rw [map_add, map_add, hDβ, hEβ]
    ext (p | p) <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply,
      Pi.neg_apply, Pi.zero_apply] <;> ring
  · rw [map_add, hDγ, zero_add, hEγ]

/-- Juxtaposing a disk domain from `y` to `y'` in `(Σ, β, γ)` with a triangle domain at the corner
`y'` gives a triangle domain at the corner `y`. -/
theorem IsBetaGammaDomainBetween.add_isTriangleDomain (hD : T.IsBetaGammaDomainBetween y y' D)
    (hE : T.IsTriangleDomain x y' w E) : T.IsTriangleDomain x y w (D + E) := by
  obtain ⟨hDα, hDβ, hDγ⟩ := hD
  obtain ⟨hEα, hEβ, hEγ⟩ := hE
  refine ⟨?_, ?_, ?_⟩
  · rw [map_add, hDα, zero_add, hEα]
  · rw [map_add, map_add, hDβ, hEβ]
    ext (p | p) <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply,
      Pi.neg_apply, Pi.zero_apply] <;> ring
  · rw [map_add, map_add, hDγ, hEγ]
    ext (p | p) <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply,
      Pi.neg_apply, Pi.zero_apply] <;> ring

/-- Juxtaposing a triangle domain at the corner `w` with a disk domain from `w` to `w'` in
`(Σ, α, γ)` gives a triangle domain at the corner `w'`. -/
theorem IsTriangleDomain.add_isAlphaGammaDomainBetween (hE : T.IsTriangleDomain x y w E)
    (hD : T.IsAlphaGammaDomainBetween w w' D) : T.IsTriangleDomain x y w' (E + D) := by
  obtain ⟨hDα, hDβ, hDγ⟩ := hD
  obtain ⟨hEα, hEβ, hEγ⟩ := hE
  refine ⟨?_, ?_, ?_⟩
  · rw [map_add, map_add, hDα, hEα]
    ext (p | p) <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply,
      Pi.neg_apply, Pi.zero_apply] <;> ring
  · rw [map_add, hDβ, add_zero, hEβ]
  · rw [map_add, map_add, hDγ, hEγ]
    ext (p | p) <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply,
      Pi.neg_apply, Pi.zero_apply] <;> ring

end Domain

section Periodic

variable {T}
variable {x : T.alphaBeta.Generator} {y : T.betaGamma.Generator} {w : T.alphaGamma.Generator}
  {D D' P : Region → ℤ}

variable (T) in
/-- The triply periodic domains: the domains with multiplicity zero at every basepoint whose
boundary is a sum of whole `α`-, `β`- and `γ`-curves. -/
def triplyPeriodicDomains : AddSubgroup (Region → ℤ) where
  carrier := {P | (∀ z, P (T.basepoint z) = 0) ∧ T.alphaArcBoundary (T.alphaBoundary P) = 0 ∧
    T.betaArcBoundary (T.betaBoundary P) = 0 ∧ T.gammaArcBoundary (T.gammaBoundary P) = 0}
  add_mem' {P Q} hP hQ := ⟨fun z => by simp [hP.1 z, hQ.1 z], by simp [hP.2.1, hQ.2.1],
    by simp [hP.2.2.1, hQ.2.2.1], by simp [hP.2.2.2, hQ.2.2.2]⟩
  zero_mem' := by simp
  neg_mem' {P} hP := ⟨fun z => by simp [hP.1 z], by simp [hP.2.1], by simp [hP.2.2.1],
    by simp [hP.2.2.2]⟩

@[simp]
theorem mem_triplyPeriodicDomains_iff :
    P ∈ T.triplyPeriodicDomains ↔ (∀ z, P (T.basepoint z) = 0) ∧
      T.alphaArcBoundary (T.alphaBoundary P) = 0 ∧ T.betaArcBoundary (T.betaBoundary P) = 0 ∧
        T.gammaArcBoundary (T.gammaBoundary P) = 0 :=
  Iff.rfl

/-- A domain is triply periodic exactly when it has multiplicity zero at every basepoint and its
boundary is `∑ aᵢ αᵢ + ∑ bⱼ βⱼ + ∑ cₖ γₖ` for some integers `aᵢ`, `bⱼ`, `cₖ`. -/
theorem mem_triplyPeriodicDomains_iff_exists_curves :
    P ∈ T.triplyPeriodicDomains ↔ (∀ z, P (T.basepoint z) = 0) ∧
      (∃ a : Fin n → ℤ, ∀ p, P (T.alphaLeft p) - P (T.alphaRight p) =
        a (Sum.elim T.alphaBeta.alpha T.alphaGamma.alpha p)) ∧
      (∃ b : Fin n → ℤ, ∀ p, P (T.betaLeft p) - P (T.betaRight p) =
        b (Sum.elim T.alphaBeta.beta T.betaGamma.alpha p)) ∧
      ∃ c : Fin n → ℤ, ∀ p, P (T.gammaLeft p) - P (T.gammaRight p) =
        c (Sum.elim T.betaGamma.beta T.alphaGamma.beta p) := by
  simp [alphaArcBoundary_eq_zero_iff, betaArcBoundary_eq_zero_iff, gammaArcBoundary_eq_zero_iff]

/-- Given a triangle domain `D` with corners `x`, `y`, `w`, another domain `D'` is a triangle
domain with the same corners and basepoint multiplicities exactly when `D' - D` is triply
periodic. So these triangle domains form a coset of the triply periodic domains. -/
theorem IsTriangleDomain.sub_mem_triplyPeriodicDomains_iff (hD : T.IsTriangleDomain x y w D) :
    D' - D ∈ T.triplyPeriodicDomains ↔
      T.IsTriangleDomain x y w D' ∧ ∀ z, D' (T.basepoint z) = D (T.basepoint z) := by
  simp only [mem_triplyPeriodicDomains_iff, isTriangleDomain_iff, map_sub, hD.1, hD.2.1, hD.2.2,
    Pi.sub_apply, sub_eq_zero]
  tauto

variable (T) in
/-- The periodic domains of the Heegaard diagram `(Σ, α, β)`, read in the regions of the triple:
the domains with multiplicity zero at every basepoint and no `γ`-boundary whose `α`- and
`β`-boundaries are sums of whole curves. -/
def alphaBetaPeriodicDomains : AddSubgroup (Region → ℤ) where
  carrier := {P | (∀ z, P (T.basepoint z) = 0) ∧ T.alphaArcBoundary (T.alphaBoundary P) = 0 ∧
    T.betaArcBoundary (T.betaBoundary P) = 0 ∧ T.gammaBoundary P = 0}
  add_mem' {P Q} hP hQ := ⟨fun z => by simp [hP.1 z, hQ.1 z], by simp [hP.2.1, hQ.2.1],
    by simp [hP.2.2.1, hQ.2.2.1], by simp [hP.2.2.2, hQ.2.2.2]⟩
  zero_mem' := by simp
  neg_mem' {P} hP := ⟨fun z => by simp [hP.1 z], by simp [hP.2.1], by simp [hP.2.2.1],
    by simp [hP.2.2.2]⟩

variable (T) in
/-- The periodic domains of the Heegaard diagram `(Σ, β, γ)`, read in the regions of the triple:
the domains with multiplicity zero at every basepoint and no `α`-boundary whose `β`- and
`γ`-boundaries are sums of whole curves. -/
def betaGammaPeriodicDomains : AddSubgroup (Region → ℤ) where
  carrier := {P | (∀ z, P (T.basepoint z) = 0) ∧ T.alphaBoundary P = 0 ∧
    T.betaArcBoundary (T.betaBoundary P) = 0 ∧ T.gammaArcBoundary (T.gammaBoundary P) = 0}
  add_mem' {P Q} hP hQ := ⟨fun z => by simp [hP.1 z, hQ.1 z], by simp [hP.2.1, hQ.2.1],
    by simp [hP.2.2.1, hQ.2.2.1], by simp [hP.2.2.2, hQ.2.2.2]⟩
  zero_mem' := by simp
  neg_mem' {P} hP := ⟨fun z => by simp [hP.1 z], by simp [hP.2.1], by simp [hP.2.2.1],
    by simp [hP.2.2.2]⟩

variable (T) in
/-- The periodic domains of the Heegaard diagram `(Σ, α, γ)`, read in the regions of the triple:
the domains with multiplicity zero at every basepoint and no `β`-boundary whose `α`- and
`γ`-boundaries are sums of whole curves. -/
def alphaGammaPeriodicDomains : AddSubgroup (Region → ℤ) where
  carrier := {P | (∀ z, P (T.basepoint z) = 0) ∧ T.alphaArcBoundary (T.alphaBoundary P) = 0 ∧
    T.betaBoundary P = 0 ∧ T.gammaArcBoundary (T.gammaBoundary P) = 0}
  add_mem' {P Q} hP hQ := ⟨fun z => by simp [hP.1 z, hQ.1 z], by simp [hP.2.1, hQ.2.1],
    by simp [hP.2.2.1, hQ.2.2.1], by simp [hP.2.2.2, hQ.2.2.2]⟩
  zero_mem' := by simp
  neg_mem' {P} hP := ⟨fun z => by simp [hP.1 z], by simp [hP.2.1], by simp [hP.2.2.1],
    by simp [hP.2.2.2]⟩

@[simp]
theorem mem_alphaBetaPeriodicDomains_iff :
    P ∈ T.alphaBetaPeriodicDomains ↔ (∀ z, P (T.basepoint z) = 0) ∧
      T.alphaArcBoundary (T.alphaBoundary P) = 0 ∧ T.betaArcBoundary (T.betaBoundary P) = 0 ∧
        T.gammaBoundary P = 0 :=
  Iff.rfl

@[simp]
theorem mem_betaGammaPeriodicDomains_iff :
    P ∈ T.betaGammaPeriodicDomains ↔ (∀ z, P (T.basepoint z) = 0) ∧ T.alphaBoundary P = 0 ∧
      T.betaArcBoundary (T.betaBoundary P) = 0 ∧ T.gammaArcBoundary (T.gammaBoundary P) = 0 :=
  Iff.rfl

@[simp]
theorem mem_alphaGammaPeriodicDomains_iff :
    P ∈ T.alphaGammaPeriodicDomains ↔ (∀ z, P (T.basepoint z) = 0) ∧
      T.alphaArcBoundary (T.alphaBoundary P) = 0 ∧ T.betaBoundary P = 0 ∧
        T.gammaArcBoundary (T.gammaBoundary P) = 0 :=
  Iff.rfl

/-- A domain from a generator `x` of `(Σ, α, β)` to itself avoiding the basepoints is exactly a
periodic domain of `(Σ, α, β)`. -/
theorem isAlphaBetaDomainBetween_self_iff :
    T.IsAlphaBetaDomainBetween x x P ∧ (∀ z, P (T.basepoint z) = 0) ↔
      P ∈ T.alphaBetaPeriodicDomains := by
  simp only [isAlphaBetaDomainBetween_iff, sub_self, Sum.elim_zero_zero,
    mem_alphaBetaPeriodicDomains_iff]
  tauto

/-- A domain from a generator `y` of `(Σ, β, γ)` to itself avoiding the basepoints is exactly a
periodic domain of `(Σ, β, γ)`. -/
theorem isBetaGammaDomainBetween_self_iff :
    T.IsBetaGammaDomainBetween y y P ∧ (∀ z, P (T.basepoint z) = 0) ↔
      P ∈ T.betaGammaPeriodicDomains := by
  simp only [isBetaGammaDomainBetween_iff, sub_self, Sum.elim_zero_zero,
    mem_betaGammaPeriodicDomains_iff]
  tauto

/-- A domain from a generator `w` of `(Σ, α, γ)` to itself avoiding the basepoints is exactly a
periodic domain of `(Σ, α, γ)`. -/
theorem isAlphaGammaDomainBetween_self_iff :
    T.IsAlphaGammaDomainBetween w w P ∧ (∀ z, P (T.basepoint z) = 0) ↔
      P ∈ T.alphaGammaPeriodicDomains := by
  simp only [isAlphaGammaDomainBetween_iff, sub_self, Sum.elim_zero_zero,
    mem_alphaGammaPeriodicDomains_iff]
  tauto

/-- Given a domain `D` from `x` to `x'` in `(Σ, α, β)`, another domain `D'` is a domain from `x`
to `x'` with the same basepoint multiplicities exactly when `D' - D` is a periodic domain of
`(Σ, α, β)`. -/
theorem IsAlphaBetaDomainBetween.sub_mem_alphaBetaPeriodicDomains_iff
    {x x' : T.alphaBeta.Generator} (hD : T.IsAlphaBetaDomainBetween x x' D) :
    D' - D ∈ T.alphaBetaPeriodicDomains ↔
      T.IsAlphaBetaDomainBetween x x' D' ∧ ∀ z, D' (T.basepoint z) = D (T.basepoint z) := by
  simp only [mem_alphaBetaPeriodicDomains_iff, isAlphaBetaDomainBetween_iff, map_sub, hD.1,
    hD.2.1, hD.2.2, Pi.sub_apply, sub_eq_zero, sub_zero]
  tauto

/-- Given a domain `D` from `y` to `y'` in `(Σ, β, γ)`, another domain `D'` is a domain from `y`
to `y'` with the same basepoint multiplicities exactly when `D' - D` is a periodic domain of
`(Σ, β, γ)`. -/
theorem IsBetaGammaDomainBetween.sub_mem_betaGammaPeriodicDomains_iff
    {y y' : T.betaGamma.Generator} (hD : T.IsBetaGammaDomainBetween y y' D) :
    D' - D ∈ T.betaGammaPeriodicDomains ↔
      T.IsBetaGammaDomainBetween y y' D' ∧ ∀ z, D' (T.basepoint z) = D (T.basepoint z) := by
  simp only [mem_betaGammaPeriodicDomains_iff, isBetaGammaDomainBetween_iff, map_sub, hD.1,
    hD.2.1, hD.2.2, Pi.sub_apply, sub_eq_zero, sub_zero]
  tauto

/-- Given a domain `D` from `w` to `w'` in `(Σ, α, γ)`, another domain `D'` is a domain from `w`
to `w'` with the same basepoint multiplicities exactly when `D' - D` is a periodic domain of
`(Σ, α, γ)`. -/
theorem IsAlphaGammaDomainBetween.sub_mem_alphaGammaPeriodicDomains_iff
    {w w' : T.alphaGamma.Generator} (hD : T.IsAlphaGammaDomainBetween w w' D) :
    D' - D ∈ T.alphaGammaPeriodicDomains ↔
      T.IsAlphaGammaDomainBetween w w' D' ∧ ∀ z, D' (T.basepoint z) = D (T.basepoint z) := by
  simp only [mem_alphaGammaPeriodicDomains_iff, isAlphaGammaDomainBetween_iff, map_sub, hD.1,
    hD.2.1, hD.2.2, Pi.sub_apply, sub_eq_zero, sub_zero]
  tauto

theorem alphaBetaPeriodicDomains_le_triplyPeriodicDomains :
    T.alphaBetaPeriodicDomains ≤ T.triplyPeriodicDomains := fun P hP =>
  ⟨hP.1, hP.2.1, hP.2.2.1, by rw [hP.2.2.2, map_zero]⟩

theorem betaGammaPeriodicDomains_le_triplyPeriodicDomains :
    T.betaGammaPeriodicDomains ≤ T.triplyPeriodicDomains := fun P hP =>
  ⟨hP.1, by rw [hP.2.1, map_zero], hP.2.2.1, hP.2.2.2⟩

theorem alphaGammaPeriodicDomains_le_triplyPeriodicDomains :
    T.alphaGammaPeriodicDomains ≤ T.triplyPeriodicDomains := fun P hP =>
  ⟨hP.1, hP.2.1, by rw [hP.2.2.1, map_zero], hP.2.2.2⟩

variable (T) in
/-- The sums of doubly periodic domains: the subgroup generated by the periodic domains of the
three Heegaard diagrams `(Σ, α, β)`, `(Σ, β, γ)` and `(Σ, α, γ)` of the triple. -/
def doublyPeriodicDomains : AddSubgroup (Region → ℤ) :=
  T.alphaBetaPeriodicDomains ⊔ T.betaGammaPeriodicDomains ⊔ T.alphaGammaPeriodicDomains

/-- A domain is a sum of doubly periodic domains exactly when it is the sum of a periodic domain
of each of the three Heegaard diagrams of the triple. -/
theorem mem_doublyPeriodicDomains_iff :
    P ∈ T.doublyPeriodicDomains ↔ ∃ P₁ ∈ T.alphaBetaPeriodicDomains,
      ∃ P₂ ∈ T.betaGammaPeriodicDomains, ∃ P₃ ∈ T.alphaGammaPeriodicDomains,
        P₁ + P₂ + P₃ = P := by
  simp only [doublyPeriodicDomains, AddSubgroup.mem_sup]
  constructor
  · rintro ⟨Q, ⟨P₁, hP₁, P₂, hP₂, rfl⟩, P₃, hP₃, rfl⟩
    exact ⟨P₁, hP₁, P₂, hP₂, P₃, hP₃, rfl⟩
  · rintro ⟨P₁, hP₁, P₂, hP₂, P₃, hP₃, rfl⟩
    exact ⟨P₁ + P₂, ⟨P₁, hP₁, P₂, hP₂, rfl⟩, P₃, hP₃, rfl⟩

/-- Every sum of doubly periodic domains is triply periodic. -/
theorem doublyPeriodicDomains_le_triplyPeriodicDomains :
    T.doublyPeriodicDomains ≤ T.triplyPeriodicDomains :=
  sup_le (sup_le alphaBetaPeriodicDomains_le_triplyPeriodicDomains
    betaGammaPeriodicDomains_le_triplyPeriodicDomains)
    alphaGammaPeriodicDomains_le_triplyPeriodicDomains

/-- Adding a sum of doubly periodic domains to a triangle domain gives a triangle domain with the
same corners and basepoint multiplicities. -/
theorem IsTriangleDomain.of_sub_mem_doublyPeriodicDomains (hD : T.IsTriangleDomain x y w D)
    (h : D' - D ∈ T.doublyPeriodicDomains) :
    T.IsTriangleDomain x y w D' ∧ ∀ z, D' (T.basepoint z) = D (T.basepoint z) :=
  hD.sub_mem_triplyPeriodicDomains_iff.mp (doublyPeriodicDomains_le_triplyPeriodicDomains h)

end Periodic

section Admissible

variable {T}

variable (T) in
/-- A Heegaard triple region system is weakly admissible when every nonzero sum of doubly periodic
domains has both positive and negative coefficients. -/
def WeaklyAdmissible : Prop :=
  ∀ P ∈ T.doublyPeriodicDomains, P ≠ 0 → (∃ r, 0 < P r) ∧ ∃ r, P r < 0

/-- A triple is weakly admissible exactly when its only nonnegative sum of doubly periodic domains
is zero. -/
theorem weaklyAdmissible_iff :
    T.WeaklyAdmissible ↔ ∀ P ∈ T.doublyPeriodicDomains, 0 ≤ P → P = 0 := by
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

theorem alphaBetaPeriodicDomains_le_doublyPeriodicDomains :
    T.alphaBetaPeriodicDomains ≤ T.doublyPeriodicDomains :=
  le_sup_left.trans le_sup_left

theorem betaGammaPeriodicDomains_le_doublyPeriodicDomains :
    T.betaGammaPeriodicDomains ≤ T.doublyPeriodicDomains :=
  le_sup_right.trans le_sup_left

theorem alphaGammaPeriodicDomains_le_doublyPeriodicDomains :
    T.alphaGammaPeriodicDomains ≤ T.doublyPeriodicDomains :=
  le_sup_right

variable (T) in
/-- A triple is weakly admissible exactly when its regions carry strictly positive areas `A` for
which every sum of doubly periodic domains has signed area `∑ r, A r * P r` equal to zero. -/
theorem weaklyAdmissible_iff_exists_pos_forall_sum_mul_eq_zero [Fintype Region] :
    T.WeaklyAdmissible ↔
      ∃ A : Region → ℝ, (∀ r, 0 < A r) ∧
        ∀ P ∈ T.doublyPeriodicDomains, ∑ r, A r * P r = 0 := by
  rw [weaklyAdmissible_iff]
  refine ⟨fun h => ?_, fun ⟨A, hA, hAP⟩ P hP hP₀ => ?_⟩
  · -- Integer weights from the lattice form of Stiemke's theorem are real weights.
    obtain ⟨c, hc, hcP⟩ := T.doublyPeriodicDomains.exists_pos_dotProduct_eq_zero_iff.2 h
    refine ⟨fun r => c r, fun r => Int.cast_pos.2 (hc r), fun P hP => ?_⟩
    simpa [dotProduct] using congrArg (Int.cast : ℤ → ℝ) (hcP P hP)
  · have hP₀' : (0 : Region → ℝ) ≤ fun r => (P r : ℝ) := fun r => Int.cast_nonneg (hP₀ r)
    have := (dotProduct_eq_zero_iff_of_pos hA hP₀').1 (hAP P hP)
    exact funext fun r => by simpa using congrFun this r

/-- If an area form `A` vanishes on the sums of doubly periodic domains, then two domains whose
difference is such a sum, for instance two triangle domains in the same class, have the same
area. -/
theorem sum_mul_eq_of_sub_mem [Fintype Region] {A : Region → ℝ}
    (hA : ∀ P ∈ T.doublyPeriodicDomains, ∑ r, A r * P r = 0) {D D' : Region → ℤ}
    (h : D' - D ∈ T.doublyPeriodicDomains) :
    ∑ r, A r * D' r = ∑ r, A r * D r := by
  have := hA (D' - D) h
  simpa [mul_sub, sum_sub_distrib, sub_eq_zero] using this

/-- In a weakly admissible triple with finitely many regions, each class `D₀ + P`, with `P` ranging
over the sums of doubly periodic domains, contains only finitely many nonnegative domains. When
`D₀` is a triangle domain, these are triangle domains with the corners and basepoint
multiplicities of `D₀` (`IsTriangleDomain.of_sub_mem_doublyPeriodicDomains`). -/
theorem WeaklyAdmissible.finite_setOf_nonneg_sub_mem [Finite Region] (hT : T.WeaklyAdmissible)
    (D₀ : Region → ℤ) :
    {D : Region → ℤ | 0 ≤ D ∧ D - D₀ ∈ T.doublyPeriodicDomains}.Finite :=
  (AddSubgroup.finite_setOf_nonneg_sub_mem_iff _).mpr (weaklyAdmissible_iff.mp hT) D₀

variable (T) in
/-- A triple with finitely many regions is weakly admissible exactly when each class `D₀ + P`, with
`P` ranging over the sums of doubly periodic domains, contains only finitely many nonnegative
domains. -/
theorem weaklyAdmissible_iff_forall_finite_setOf_nonneg_sub_mem [Finite Region] :
    T.WeaklyAdmissible ↔
      ∀ D₀ : Region → ℤ, {D : Region → ℤ | 0 ≤ D ∧ D - D₀ ∈ T.doublyPeriodicDomains}.Finite := by
  rw [weaklyAdmissible_iff, AddSubgroup.finite_setOf_nonneg_sub_mem_iff]

end Admissible

end HeegaardTripleRegionSystem

end TauCeti
