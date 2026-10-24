/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Cone.Basic
public import Mathlib.CategoryTheory.Triangulated.Rotate

/-!
# Cone triangles of curved differential graded right modules

The closed maps `M ⟶ N ⟶ cone(f) ⟶ M[1]` give a triangle in the existing curved homotopy
category, using its coherent integer shift. Its third arrow is the negative cone projection,
as required by the canonical stable-suspension comparison. All three adjacent composites vanish.
A square of closed maps commuting up to homotopy gives a morphism of these cone triangles.
Every commutative square on their first arrows in the homotopy category therefore extends to
a morphism of cone triangles.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 7.6.
* The Tau Ceti contributors, `TauCeti.Algebra.Homology.Curved.Cone.Triangle`: the existing
  curved-duplex cone-triangle interface is the formal precedent for this module.
-/

public section

open CategoryTheory CategoryTheory.Pretriangulated

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- These quotient and shift builders retain the original module objects.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  EnrichedFunctor.ofDGMap EnrichedFunctor.mapDGHomotopyCategory
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w} {M N : CurvedDGRightModuleCat.{u, u, u} h}
  (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N)

/-- The mapping-cone triangle with the negative projection as third arrow, compatible with the
canonical stable-suspension comparison on the curved homotopy category. -/
@[expose, implicit_reducible]
noncomputable def coneTriangle :
    Triangle (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :=
  Triangle.mk ((dgClosedToHomotopy R).map f)
    ((dgClosedToHomotopy R).map (coneInclusion f))
    (-((dgClosedToHomotopy R).map (coneProjection f)))

/-- The first arrow of the cone triangle is the homotopy class of the original map. -/
@[simp]
theorem coneTriangle_mor₁ : (coneTriangle f).mor₁ = (dgClosedToHomotopy R).map f :=
  rfl

/-- The second arrow of the cone triangle is the homotopy class of the cone inclusion. -/
@[simp]
theorem coneTriangle_mor₂ :
    (coneTriangle f).mor₂ = (dgClosedToHomotopy R).map (coneInclusion f) :=
  rfl

/-- The third arrow of the cone triangle is the negative class of the cone projection. -/
@[simp]
theorem coneTriangle_mor₃ :
    (coneTriangle f).mor₃ = -((dgClosedToHomotopy R).map (coneProjection f)) :=
  rfl

/-- Rotation gives the cone inclusion, negative projection, and negative shifted map. -/
theorem coneTriangle_rotate :
    (coneTriangle f).rotate =
      Triangle.mk ((dgClosedToHomotopy R).map (coneInclusion f))
        (-((dgClosedToHomotopy R).map (coneProjection f)))
        (-((dgClosedToHomotopy R).map ((closedShiftFunctor 1).map f))) := by
  -- Rotation has this constructor normal form; the shift on the quotient is the actual
  -- homotopy shift. This reduction lets the quotient-map computation match its third arrow.
  change Triangle.mk ((dgClosedToHomotopy R).map (coneInclusion f))
    (-((dgClosedToHomotopy R).map (coneProjection f)))
    (-((homotopyShiftFunctor 1).map ((dgClosedToHomotopy R).map f))) = _
  rw [homotopyShiftFunctor_map_quotient]

/-- The first and second arrows of the cone triangle compose to zero. -/
@[reassoc]
theorem coneTriangle_mor₁_comp_mor₂ : (coneTriangle f).mor₁ ≫ (coneTriangle f).mor₂ = 0 :=
  quotient_map_comp_coneInclusion f

/-- The second and third arrows of the cone triangle compose to zero. -/
@[reassoc]
theorem coneTriangle_mor₂_comp_mor₃ : (coneTriangle f).mor₂ ≫ (coneTriangle f).mor₃ = 0 := by
  -- The third arrow has the sign fixed by the stable-suspension comparison.
  change (dgClosedToHomotopy R).map (coneInclusion f) ≫
    (-((dgClosedToHomotopy R).map (coneProjection f))) = 0
  rw [Preadditive.comp_neg, ← Functor.map_comp, coneInclusion_comp_coneProjection,
    Functor.map_zero, neg_zero]

/-- The third arrow followed by the shift of the first arrow composes to zero. -/
@[reassoc]
theorem coneTriangle_mor₃_comp_shift_mor₁ :
    (coneTriangle f).mor₃ ≫ (coneTriangle f).mor₁⟦(1 : ℤ)⟧' = 0 := by
  -- Its shifted first arrow uses the existing homotopy shift, whose quotient formula applies.
  change (-((dgClosedToHomotopy R).map (coneProjection f))) ≫
    (homotopyShiftFunctor 1).map ((dgClosedToHomotopy R).map f) = 0
  rw [Preadditive.neg_comp, homotopyShiftFunctor_map_quotient,
    quotient_map_coneProjection_comp_shift, neg_zero]

variable {M' N' : CurvedDGRightModuleCat.{u, u, u} h}
  (g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M' ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N')
  (a : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M')
  (b : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N')
  (k : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N'.grading) (-1))
  (hsq : ∀ x : M, closedHom b (closedHom f x) - closedHom g (closedHom a x) =
    N'.differential (k.1 x) + k.1 (M.differential x))

/-- A homotopy-commutative square gives a morphism of the canonical cone triangles. -/
-- The generated public projections are reflexive equations; their export requires
-- this constructor body to be exposed in the pinned Lean module system.
@[expose, simps hom₁ hom₂ hom₃]
noncomputable def coneTriangleMap : coneTriangle f ⟶ coneTriangle g where
  hom₁ := (dgClosedToHomotopy R).map a
  hom₂ := (dgClosedToHomotopy R).map b
  hom₃ := (dgClosedToHomotopy R).map (coneMap f g a b k hsq)
  comm₁ := by
    -- Reduce the triangle constructors to the quotient classes of their prescribed arrows.
    change (dgClosedToHomotopy R).map f ≫ (dgClosedToHomotopy R).map b =
      (dgClosedToHomotopy R).map a ≫ (dgClosedToHomotopy R).map g
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply (quotient_map_eq_iff_exists_homotopy _ _).mpr
    refine ⟨k, fun x ↦ ?_⟩
    simpa only [closedHom_comp, LinearMap.comp_apply] using hsq x
  comm₂ := by
    -- The second square consists of the quotient classes of the two closed inclusions.
    change (dgClosedToHomotopy R).map (coneInclusion f) ≫
        (dgClosedToHomotopy R).map (coneMap f g a b k hsq) =
      (dgClosedToHomotopy R).map b ≫ (dgClosedToHomotopy R).map (coneInclusion g)
    rw [← Functor.map_comp, ← Functor.map_comp, coneInclusion_comp_coneMap]
  comm₃ := by
    -- The third square uses the concrete projection and the actual shifted quotient map.
    change (-((dgClosedToHomotopy R).map (coneProjection f))) ≫
        (homotopyShiftFunctor 1).map ((dgClosedToHomotopy R).map a) =
      (dgClosedToHomotopy R).map (coneMap f g a b k hsq) ≫
        (-((dgClosedToHomotopy R).map (coneProjection g)))
    rw [Preadditive.neg_comp, Preadditive.comp_neg]
    congr 1
    rw [homotopyShiftFunctor_map_quotient, ← Functor.map_comp, ← Functor.map_comp,
      coneMap_comp_coneProjection]

/-- A commutative square on the first arrows of two cone triangles extends to a morphism of
triangles, by lifting its maps and its commutativity to closed maps and an odd homotopy. -/
theorem exists_coneTriangleMap
    (a : (coneTriangle f).obj₁ ⟶ (coneTriangle g).obj₁)
    (b : (coneTriangle f).obj₂ ⟶ (coneTriangle g).obj₂)
    (hsq : (coneTriangle f).mor₁ ≫ b = a ≫ (coneTriangle g).mor₁) :
    ∃ t : coneTriangle f ⟶ coneTriangle g, t.hom₁ = a ∧ t.hom₂ = b := by
  obtain ⟨a, rfl⟩ := (dgClosedToHomotopy R).map_surjective a
  obtain ⟨b, rfl⟩ := (dgClosedToHomotopy R).map_surjective b
  -- Reduce the triangle's first arrows before extracting an odd homotopy of the closed square.
  change (dgClosedToHomotopy R).map f ≫ (dgClosedToHomotopy R).map b =
    (dgClosedToHomotopy R).map a ≫ (dgClosedToHomotopy R).map g at hsq
  rw [← Functor.map_comp, ← Functor.map_comp] at hsq
  obtain ⟨k, hk⟩ := (quotient_map_eq_iff_exists_homotopy _ _).mp hsq
  have hk' : ∀ x : M, closedHom b (closedHom f x) - closedHom g (closedHom a x) =
      N'.differential (k.1 x) + k.1 (M.differential x) := by
    simpa only [closedHom_comp, LinearMap.comp_apply] using hk
  exact ⟨coneTriangleMap f g a b k hk', rfl, rfl⟩

end TauCeti.CurvedDGRightModuleCat
