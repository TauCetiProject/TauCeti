/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.Product

/-!
# Consistency of wall transport

Polygonal transport is determined by its endpoints precisely when every admissible closed
path has identity transport. For a finite family of polyhedral walls, it suffices to check
loops at a single allowed basepoint: the admissible two-segment paths join that point to every
other allowed endpoint.
-/

public section

namespace TauCeti.WallComplement

variable {V ι G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  [Group G] {W : ι → Set V}
  (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
  (hcomm : ∀ i j, affineSpan ℝ (W i) =
    affineSpan ℝ (W j) → Commute (label i) (label j))

/-- Wall transport is consistent when all admissible paths with the same endpoints
have the same product. -/
def IsConsistent : Prop :=
  ∀ ⦃x y : WallComplement W⦄ (p q : AdmissiblePLPath x y),
    p.wallPathProduct ν label hcomm = q.wallPathProduct ν label hcomm

variable {ν label hcomm}

/-- A consistent wall transport sends every admissible loop to the identity. -/
theorem IsConsistent.wallPathProduct_eq_one (h : IsConsistent ν label hcomm)
    {x : WallComplement W} (p : AdmissiblePLPath x x) :
    p.wallPathProduct ν label hcomm = 1 :=
  (h p .nil).trans (Quiver.Path.wallPathProduct_nil ν label hcomm)

/-- Endpoint independence is equivalent to trivial transport on all closed paths. -/
theorem isConsistent_iff_wallPathProduct_eq_one
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction) :
    IsConsistent ν label hcomm ↔
      ∀ (x : WallComplement W) (p : AdmissiblePLPath x x),
        p.wallPathProduct ν label hcomm = 1 := by
  refine ⟨fun h _ p => h.wallPathProduct_eq_one p, fun h x _ p q => ?_⟩
  have hloop := h x (p.comp q.reverse)
  rw [Quiver.Path.wallPathProduct_comp, Quiver.Path.wallPathProduct_reverse _ _ _ hν,
    inv_mul_eq_one] at hloop
  exact hloop.symm

/-- For polyhedral walls of codimension one, consistency can be tested using loops at any
single off-wall basepoint. Transport along a path to the basepoint conjugates the loop product. -/
theorem isConsistent_iff_wallPathProduct_eq_one_at
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)
    (hpoly : ∀ i, IsConvexPolyhedron (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)
    (b : WallComplement W) :
    IsConsistent ν label hcomm ↔
      ∀ p : AdmissiblePLPath b b, p.wallPathProduct ν label hcomm = 1 := by
  rw [isConsistent_iff_wallPathProduct_eq_one hν]
  refine ⟨fun h => h b, fun h x p => ?_⟩
  obtain ⟨q, -⟩ := AdmissiblePLPath.exists_length_eq_two hpoly hdim b x
  have hloop := h ((q.comp p).comp q.reverse)
  rwa [Quiver.Path.wallPathProduct_comp, Quiver.Path.wallPathProduct_comp,
    Quiver.Path.wallPathProduct_reverse _ _ _ hν, inv_mul_eq_iff_eq_mul, mul_one,
    mul_eq_right] at hloop

end TauCeti.WallComplement
