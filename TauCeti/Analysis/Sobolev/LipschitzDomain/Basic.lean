/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Epigraph.Basic

/-!
# Domains with Lipschitz boundary

This file defines a Lipschitz boundary chart on a real normed space.  Its affine-isometric
coordinates identify the ambient space with the Euclidean product `WithLp 2 (ℝ × E)`, where
membership in the open set agrees inside an open product cylinder with membership in the strict
epigraph of a Lipschitz function.  An open set is a Lipschitz domain when every point of its
frontier admits one of these charts.

The definition allows an arbitrary affine isometry before taking the graph.  Consequently it is
independent of rigid coordinates, while retaining the distinguished normal coordinate needed by
the graph trace and extension operators.  Charts may be restricted to smaller cylinders, and
affine isometries transport both individual charts and Lipschitz domains.

Every strict epigraph of a Lipschitz function, and in particular every open half-space, is a
Lipschitz domain.  These examples connect the abstract predicate to the graph-flattening Sobolev
operators in `TauCeti.Analysis.Sobolev.Trace.Epigraph.Basic`.

## Main declarations

* `TauCeti.IsLipschitzBoundaryChart`: an open set agrees locally with a Lipschitz epigraph after
  an affine isometry.
* `TauCeti.IsLipschitzBoundaryAt`: existence of such a chart at one point.
* `TauCeti.IsLipschitzDomain`: every frontier point has a Lipschitz boundary chart.
* `TauCeti.IsLipschitzDomain.affineIsometryImage`: rigid-coordinate invariance.
* `TauCeti.isLipschitzDomain_normalEpigraph`: Lipschitz epigraphs satisfy the definition.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5.
* J. Nečas, *Direct Methods in the Theory of Elliptic Equations*, Chapter 2.
-/

public section

noncomputable section

namespace TauCeti

open Set TopologicalSpace
open scoped NNReal

universe u

variable {X X' E : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup X'] [NormedSpace ℝ X']
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A Lipschitz boundary chart for `Ω` at `x`.

The affine isometry `e` supplies rigid coordinates.  Inside the product cylinder of normal
radius `r` and tangential radius `s` centred at `e x`, the set `Ω` is exactly the region above
the graph of `φ`.  The first condition puts the centre point itself on that graph. -/
def IsLipschitzBoundaryChart (Ω : Opens X) (x : X)
    (e : X ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : C(E, ℝ)) (K : ℝ≥0) (r s : ℝ) : Prop :=
  φ (e x).snd = (e x).fst ∧
    0 < r ∧ 0 < s ∧ LipschitzWith K φ ∧
      ∀ y, dist (e y).fst (e x).fst < r → dist (e y).snd (e x).snd < s →
        (y ∈ Ω ↔ φ (e y).snd < (e y).fst)

/-- The defining conditions of a Lipschitz boundary chart. -/
theorem isLipschitzBoundaryChart_iff (Ω : Opens X) (x : X)
    (e : X ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : C(E, ℝ)) (K : ℝ≥0) (r s : ℝ) :
    IsLipschitzBoundaryChart Ω x e φ K r s ↔
      φ (e x).snd = (e x).fst ∧
        0 < r ∧ 0 < s ∧ LipschitzWith K φ ∧
          ∀ y, dist (e y).fst (e x).fst < r → dist (e y).snd (e x).snd < s →
            (y ∈ Ω ↔ φ (e y).snd < (e y).fst) :=
  Iff.rfl

namespace IsLipschitzBoundaryChart

variable {Ω : Opens X} {x : X}
  {e : X ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : C(E, ℝ)} {K : ℝ≥0} {r s : ℝ}

/-- The centre of a Lipschitz boundary chart lies on its graph. -/
theorem center (h : IsLipschitzBoundaryChart Ω x e φ K r s) :
    φ (e x).snd = (e x).fst :=
  h.1

/-- The normal radius of a Lipschitz boundary chart is positive. -/
theorem normalRadius_pos (h : IsLipschitzBoundaryChart Ω x e φ K r s) : 0 < r :=
  h.2.1

/-- The tangential radius of a Lipschitz boundary chart is positive. -/
theorem tangentRadius_pos (h : IsLipschitzBoundaryChart Ω x e φ K r s) : 0 < s :=
  h.2.2.1

/-- The graph function of a Lipschitz boundary chart has its stated Lipschitz constant. -/
theorem lipschitzWith (h : IsLipschitzBoundaryChart Ω x e φ K r s) : LipschitzWith K φ :=
  h.2.2.2.1

/-- Inside its cylinder, a Lipschitz boundary chart characterizes membership in the domain. -/
theorem mem_iff (h : IsLipschitzBoundaryChart Ω x e φ K r s) (y : X)
    (hr : dist (e y).fst (e x).fst < r) (hs : dist (e y).snd (e x).snd < s) :
    y ∈ Ω ↔ φ (e y).snd < (e y).fst :=
  h.2.2.2.2 y hr hs

/-- A Lipschitz boundary chart remains one after restricting both cylinder radii. -/
theorem mono (h : IsLipschitzBoundaryChart Ω x e φ K r s) {r' s' : ℝ}
    (hr' : 0 < r') (hs' : 0 < s') (hrr : r' ≤ r) (hss : s' ≤ s) :
    IsLipschitzBoundaryChart Ω x e φ K r' s' := by
  refine ⟨h.center, hr', hs', h.lipschitzWith, fun y hyr hys ↦ ?_⟩
  exact h.mem_iff y (hyr.trans_le hrr) (hys.trans_le hss)

/-- Transport a Lipschitz boundary chart by a rigid change of ambient coordinates. -/
theorem affineIsometryImage (h : IsLipschitzBoundaryChart Ω x e φ K r s)
    (g : X ≃ᵃⁱ[ℝ] X') :
    IsLipschitzBoundaryChart
      (⟨g '' Ω, g.toHomeomorph.isOpenMap _ Ω.isOpen⟩ : Opens X')
      (g x) (g.symm.trans e) φ K r s := by
  refine ⟨?_, h.normalRadius_pos, h.tangentRadius_pos, h.lipschitzWith, ?_⟩
  · simpa using h.center
  · intro y hyr hys
    have hy := h.mem_iff (g.symm y) (by simpa using hyr) (by simpa using hys)
    change (y ∈ g '' (Ω : Set X) ↔ φ (e (g.symm y)).snd < (e (g.symm y)).fst)
    rw [show y ∈ g '' (Ω : Set X) ↔ g.symm y ∈ Ω by
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa using hz
      · intro hz
        exact ⟨g.symm y, hz, g.apply_symm_apply y⟩]
    exact hy

end IsLipschitzBoundaryChart

/-- An open set has Lipschitz boundary at `x` if some rigid coordinate system identifies it,
inside a positive product cylinder, with the strict epigraph of a Lipschitz function. -/
def IsLipschitzBoundaryAt (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Opens X) (x : X) : Prop :=
  ∃ (e : X ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : C(E, ℝ)) (K : ℝ≥0) (r s : ℝ),
    IsLipschitzBoundaryChart Ω x e φ K r s

/-- Characterization of having Lipschitz boundary at a point by chart data. -/
theorem isLipschitzBoundaryAt_iff (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Opens X) (x : X) :
    IsLipschitzBoundaryAt E Ω x ↔
      ∃ (e : X ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : C(E, ℝ)) (K : ℝ≥0) (r s : ℝ),
        IsLipschitzBoundaryChart Ω x e φ K r s :=
  Iff.rfl

namespace IsLipschitzBoundaryAt

variable {Ω : Opens X} {x : X}

/-- Lipschitz boundary at a point is invariant under affine isometries. -/
theorem affineIsometryImage (h : IsLipschitzBoundaryAt E Ω x)
    (g : X ≃ᵃⁱ[ℝ] X') :
    IsLipschitzBoundaryAt E
      (⟨g '' Ω, g.toHomeomorph.isOpenMap _ Ω.isOpen⟩ : Opens X') (g x) := by
  obtain ⟨e, φ, K, r, s, h⟩ := h
  exact ⟨g.symm.trans e, φ, K, r, s, h.affineIsometryImage g⟩

end IsLipschitzBoundaryAt

/-- An open subset of a normed space is a Lipschitz domain with tangential model `E` if it has
Lipschitz boundary at every point of its frontier. -/
def IsLipschitzDomain (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Opens X) : Prop :=
  ∀ x ∈ frontier (Ω : Set X), IsLipschitzBoundaryAt E Ω x

/-- A Lipschitz domain has Lipschitz boundary at every frontier point. -/
theorem IsLipschitzDomain.boundaryAt {Ω : Opens X} (h : IsLipschitzDomain E Ω)
    {x : X} (hx : x ∈ frontier (Ω : Set X)) :
    IsLipschitzBoundaryAt E Ω x :=
  h x hx

/-- The Lipschitz-domain predicate is invariant under affine isometries. -/
theorem IsLipschitzDomain.affineIsometryImage {Ω : Opens X}
    (h : IsLipschitzDomain E Ω) (g : X ≃ᵃⁱ[ℝ] X') :
    IsLipschitzDomain E
      (⟨g '' Ω, g.toHomeomorph.isOpenMap _ Ω.isOpen⟩ : Opens X') := by
  intro y hy
  have hy' : y ∈ g '' frontier (Ω : Set X) := by
    rw [show g '' frontier (Ω : Set X) = frontier (g '' (Ω : Set X)) by
      simpa only [AffineIsometryEquiv.coe_toHomeomorph] using
        g.toHomeomorph.image_frontier (Ω : Set X)]
    exact hy
  obtain ⟨x, hx, rfl⟩ := hy'
  exact (h.boundaryAt hx).affineIsometryImage g

/-- A point on the graph of a Lipschitz function has the tautological Lipschitz boundary chart
for its strict epigraph. -/
theorem isLipschitzBoundaryChart_normalEpigraph {φ : C(E, ℝ)} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) {x : WithLp 2 (ℝ × E)} (hx : φ x.snd = x.fst) :
    IsLipschitzBoundaryChart (normalEpigraph φ) x (AffineIsometryEquiv.refl ℝ (WithLp 2 (ℝ × E)))
      φ K 1 1 := by
  refine ⟨by simpa using hx, zero_lt_one, zero_lt_one, hφ, ?_⟩
  intro y _ _
  exact mem_normalEpigraph φ y

/-- The strict epigraph of a Lipschitz function is a Lipschitz domain. -/
theorem isLipschitzDomain_normalEpigraph {φ : C(E, ℝ)} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) : IsLipschitzDomain E (normalEpigraph φ) := by
  intro x hx
  rw [coe_normalEpigraph] at hx
  have hxgraph : φ x.snd = x.fst :=
    frontier_lt_subset_eq (f := fun z : WithLp 2 (ℝ × E) => φ z.snd)
      (g := fun z : WithLp 2 (ℝ × E) => z.fst) (by fun_prop) (by fun_prop) hx
  exact ⟨AffineIsometryEquiv.refl ℝ (WithLp 2 (ℝ × E)), φ, K, 1, 1,
    isLipschitzBoundaryChart_normalEpigraph hφ hxgraph⟩

/-- Every open normal half-space is a Lipschitz domain. -/
theorem isLipschitzDomain_normalHalfSpace (a : ℝ) :
    IsLipschitzDomain E (normalHalfSpace (E := E) a) := by
  let φ : C(E, ℝ) := ContinuousMap.const E a
  have hφ : LipschitzWith 0 φ := LipschitzWith.const a
  have heq : normalEpigraph φ = normalHalfSpace (E := E) a := by
    ext x
    simp [φ]
  rw [← heq]
  exact isLipschitzDomain_normalEpigraph hφ

end TauCeti
