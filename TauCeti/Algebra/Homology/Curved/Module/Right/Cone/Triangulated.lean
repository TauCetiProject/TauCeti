/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Cone.Triangle
public import TauCeti.Algebra.Homology.Curved.Module.Right.Triangulated
public import TauCeti.CategoryTheory.Triangulated.Signs

/-!
# Distinguished mapping-cone triangles of curved DG right modules

The existing triangulation is transported from the graded-split Frobenius stable category using
its canonical suspension comparison. An extension of a conflation to the identity-cone
presentation computes its connecting arrow with positive sign. Applying this to the cone
sequence gives the triangle with arrows inclusion, projection, and shifted original map.
Negating its third object identifies it with the rotation of the mapping-cone triangle, whose
third arrow is therefore the negative cone projection.

Every distinguished triangle is isomorphic to one of these concrete cone triangles. All
structures, objects, shifts, and suspension comparisons used here are the existing ones, and
the curvature is unrestricted.

## References

* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2, Theorem 2.6.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 7.6.
* The Tau Ceti contributors, `TauCeti.Algebra.Homology.Periodic.Triangulated`: the concrete
  triangle comparison follows the periodic cone construction, with the same negative projection.
* The Tau Ceti contributors, `TauCeti.Algebra.Homology.Curved.Module.Right.Suspension`: the
  canonical stable-suspension comparison supplies the connecting-map sign.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- The homotopy quotient retains the underlying curved modules as objects.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying coneIdentityInjectivePresentation
  EnrichedFunctor.ofDGMap EnrichedFunctor.mapDGHomotopyCategory

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

private noncomputable def coneIdentityExtension {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone f) ⟶
      (coneIdentityInjectivePresentation N).I :=
  coneMap f (𝟙 (ForgetEnrichment.of _ N)) f (𝟙 _) 0 (by intro x; simp) ≫
    eqToHom (coneIdentityInjectivePresentation_I N).symm

private noncomputable def coneShiftConnecting {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    (closedShiftFunctor 1).obj (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) ⟶
      (coneIdentityInjectivePresentation N).K :=
  (closedShiftFunctor 1).map f ≫ eqToHom (coneIdentityInjectivePresentation_K N).symm

private theorem coneIdentityExtension_inclusion {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    coneInclusion f ≫ coneIdentityExtension f = (coneIdentityInjectivePresentation N).i := by
  apply (cancel_mono (eqToHom (coneIdentityInjectivePresentation_I N))).mp
  simpa only [coneIdentityExtension, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id, coneInclusion_comp_coneMap, Category.id_comp] using
    (coneIdentityInjectivePresentation_i N).symm

private theorem coneIdentityExtension_projection {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    coneProjection f ≫ coneShiftConnecting f =
      coneIdentityExtension f ≫ (coneIdentityInjectivePresentation N).p := by
  apply (cancel_mono (eqToHom (coneIdentityInjectivePresentation_K N))).mp
  dsimp only [coneIdentityExtension, coneShiftConnecting]
  simp only [Category.assoc]
  rw [coneIdentityInjectivePresentation_p]
  simpa only [eqToHom_trans, eqToHom_refl, Category.comp_id] using
    (coneMap_comp_coneProjection f (𝟙 (ForgetEnrichment.of _ N)) f (𝟙 _) 0
      (by intro x; simp)).symm

private theorem coneInclusion_coneProjection_shift_distinguished
    {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    Triangle.mk ((dgClosedToHomotopy R).map (coneInclusion f))
        ((dgClosedToHomotopy R).map (coneProjection f))
        ((dgClosedToHomotopy R).map ((closedShiftFunctor 1).map f)) ∈
      distTriang (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) := by
  have hT := mk_distinguished_of_conflation
    (S := ShortComplex.mk (coneInclusion f) (coneProjection f)
      (coneInclusion_comp_coneProjection f))
    (by simpa only [coneShortComplex_eq_mk] using (coneShortComplex_conflation f))
    (coneIdentityExtension f) (coneShiftConnecting f)
    (coneIdentityExtension_inclusion f) (coneIdentityExtension_projection f)
  -- The target of the connecting map is the identity-cone cokernel N[1], identified by its
  -- public K equation with the closed shift of N. Expose the composite before mapping it,
  -- then cancel the resulting object transports.
  dsimp only [coneShiftConnecting] at hT
  rw [Functor.map_comp, eqToHom_map] at hT
  simpa only [Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id] using hT

/-- Every mapping-cone triangle with its negative projection is distinguished, for arbitrary
curvature, in the canonical triangulation of the curved homotopy category. -/
theorem coneTriangle_distinguished {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    coneTriangle f ∈ distTriang (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) := by
  apply (rotate_distinguished_triangle (coneTriangle f)).mpr
  refine isomorphic_distinguished _ (coneInclusion_coneProjection_shift_distinguished f) _ ?_
  rw [coneTriangle_rotate]
  exact Triangle.isoNegThird _ _ _

/-- Distinguished triangles are precisely those isomorphic to the concrete mapping-cone
triangles of closed maps, with the negative cone projection as third arrow. -/
theorem mem_distTriang_iff_nonempty_iso_coneTriangle
    (T : Triangle (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h))) :
    T ∈ distTriang (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) ↔
      ∃ (M N : CurvedDGRightModuleCat.{u, u, u} h)
        (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
          ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N),
        Nonempty (T ≅ coneTriangle f) := by
  refine ⟨fun hT ↦ ?_, fun ⟨M, N, f, ⟨e⟩⟩ ↦
    isomorphic_distinguished _ (coneTriangle_distinguished f) _ e⟩
  let Q := dgClosedToHomotopy (C := CurvedDGRightModuleCat.{u, u, u} h) R
  let M := DGHomotopyCategory.underlying R T.obj₁
  let N := DGHomotopyCategory.underlying R T.obj₂
  let X := ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M
  let Y := ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N
  let e₁ : Q.obj X ≅ T.obj₁ := eqToIso (DGHomotopyCategory.of_underlying R T.obj₁)
  let e₂ : Q.obj Y ≅ T.obj₂ := eqToIso (DGHomotopyCategory.of_underlying R T.obj₂)
  let f := Q.preimage (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
  refine ⟨M, N, f,
    ⟨(isoTriangleOfIso₁₂ _ _ (coneTriangle_distinguished f) hT e₁ e₂ ?_).symm⟩⟩
  -- The triangle's first arrow is a quotient map, so fullness identifies this representative.
  rw [coneTriangle_mor₁]
  exact (congrArg (· ≫ e₂.hom) (Q.map_preimage _)).trans (by simp [Category.assoc])

end TauCeti.CurvedDGRightModuleCat
