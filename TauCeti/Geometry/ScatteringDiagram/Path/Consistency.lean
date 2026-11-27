/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.Product

/-!
# Consistency of wall transport

Polygonal transport is determined by its endpoints precisely when every admissible
closed path has identity transport. It suffices to check loops at one basepoint
from which every endpoint is reachable. Codimension-one convex polyhedral walls
provide this reachability.
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

/-- Consistency is equality of the transport products of paths with common endpoints. -/
theorem isConsistent_iff :
    IsConsistent ν label hcomm ↔
      ∀ ⦃x y : WallComplement W⦄ (p q : AdmissiblePLPath x y),
        p.wallPathProduct ν label hcomm = q.wallPathProduct ν label hcomm :=
  Iff.rfl

variable {ν label hcomm}

/-- Consistent transport gives equal products for paths with common endpoints. -/
theorem IsConsistent.wallPathProduct_eq (h : IsConsistent ν label hcomm)
    {x y : WallComplement W} (p q : AdmissiblePLPath x y) :
    p.wallPathProduct ν label hcomm = q.wallPathProduct ν label hcomm :=
  h p q

/-- A consistent wall transport sends every admissible loop to the identity. -/
theorem IsConsistent.wallPathProduct_eq_one (h : IsConsistent ν label hcomm)
    {x : WallComplement W} (p : AdmissiblePLPath x x) :
    p.wallPathProduct ν label hcomm = 1 :=
  (h.wallPathProduct_eq p .nil).trans (Quiver.Path.wallPathProduct_nil ν label hcomm)

/-- Endpoint independence is equivalent to trivial transport on all closed paths. -/
theorem isConsistent_iff_wallPathProduct_eq_one :
    IsConsistent ν label hcomm ↔
      ∀ (x : WallComplement W) (p : AdmissiblePLPath x x),
        p.wallPathProduct ν label hcomm = 1 := by
  refine ⟨fun h _ p => h.wallPathProduct_eq_one p, fun h x _ p q => ?_⟩
  have hp := h x (p.comp q.reverse)
  have hq := h x (q.comp q.reverse)
  simp only [Quiver.Path.wallPathProduct_comp] at hp hq
  exact mul_left_cancel (hp.trans hq.symm)

/-- An off-wall basepoint that reaches every endpoint detects consistency by its loops. -/
theorem isConsistent_iff_wallPathProduct_eq_one_at_of_reachable
    {b : WallComplement W} (hconn : ∀ x, Nonempty (AdmissiblePLPath b x)) :
    IsConsistent ν label hcomm ↔
      ∀ p : AdmissiblePLPath b b, p.wallPathProduct ν label hcomm = 1 := by
  rw [isConsistent_iff_wallPathProduct_eq_one]
  refine ⟨fun h => h b, fun h x p => ?_⟩
  obtain ⟨q⟩ := hconn x
  have hp := h ((q.comp p).comp q.reverse)
  have hq := h (q.comp q.reverse)
  simp only [Quiver.Path.wallPathProduct_comp] at hp hq
  have heq := mul_left_cancel (hp.trans hq.symm)
  exact mul_right_cancel (heq.trans (one_mul _).symm)

/-- For convex polyhedral walls of codimension one, consistency can be tested using loops
at any single off-wall basepoint. -/
theorem isConsistent_iff_wallPathProduct_eq_one_at
    (hpoly : ∀ i, IsConvexPolyhedron (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)
    (b : WallComplement W) :
    IsConsistent ν label hcomm ↔
      ∀ p : AdmissiblePLPath b b, p.wallPathProduct ν label hcomm = 1 :=
  isConsistent_iff_wallPathProduct_eq_one_at_of_reachable fun x => by
    obtain ⟨q, -⟩ := AdmissiblePLPath.exists_length_eq_two hpoly hdim b x
    exact ⟨q⟩

end TauCeti.WallComplement
