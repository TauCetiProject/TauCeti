/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Inflation
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# The finite-quotient colimit of continuous nonabelian first cohomology

The open normal subgroups of a group `G` with a topology, ordered by reverse inclusion,
index a diagram whose stage at `N` is `H¹(G ⧸ N, Aᴺ)`. Its arrows refine the quotient
and include the fixed coefficient subgroups. The legs of its inflation cocone land in
`H¹(G, A)`.

For a compact topological group `G` and discrete coefficients `A`, inflation makes the
ambient class set the colimit. Every class is represented at a finite stage. Two such
representatives of the same class agree after refining to the intersection, by injectivity of
inflation from that stage.

The finite-stage input is the nonabelian inflation theorem in Serre, *Galois Cohomology*,
I.2.2. The colimit construction uses Mathlib's `Types.FilteredColimit.isColimitOf'`.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.NonabelianH1

variable (G A : Type*) [Group G] [TopologicalSpace G] [Group A] [TopologicalSpace A]
  [MulDistribMulAction G A]

/-- The diagram of nonabelian first cohomology of the open normal quotients, with coefficients
fixed by the corresponding subgroups and arrows directed towards finer quotients. -/
-- The object types must reduce at instance transparency for callers to apply the diagram arrows
-- to native quotient classes.
@[expose, implicit_reducible] def finiteQuotientDiagram : (OpenNormalSubgroup G)ᵒᵖ ⥤ Type _ where
  obj U := NonabelianH1 (G ⧸ U.unop.toSubgroup) (FixedPoints.subgroup U.unop.toSubgroup A)
  map f := TypeCat.ofHom (transition (leOfHom f.unop))
  map_id _ := by
    ext a
    exact transition_refl a
  map_comp f g := by
    ext a
    exact (transition_transition (leOfHom g.unop) (leOfHom f.unop) a).symm

/-- A finite-quotient diagram object uses the coefficients fixed by its indexing subgroup. -/
theorem finiteQuotientDiagram_obj (U : (OpenNormalSubgroup G)ᵒᵖ) :
    (finiteQuotientDiagram G A).obj U =
      NonabelianH1 (G ⧸ U.unop.toSubgroup) (FixedPoints.subgroup U.unop.toSubgroup A) :=
  rfl

/-- The diagram arrow from `U` to `V` applies refinement along `V ≤ U`. -/
@[simp]
theorem finiteQuotientDiagram_map_apply {U V : (OpenNormalSubgroup G)ᵒᵖ} (f : U ⟶ V)
    (a : (finiteQuotientDiagram G A).obj U) :
    (finiteQuotientDiagram G A).map f a = transition (leOfHom f.unop) a :=
  (rfl)

/-- The cocone from the finite quotients whose legs are the inflation maps. -/
-- The apex must reduce at instance transparency so that cocone lifts apply to ambient classes.
@[expose, implicit_reducible] def finiteQuotientCocone : Cocone (finiteQuotientDiagram G A) where
  pt := NonabelianH1 G A
  ι :=
    { app := fun U ↦ TypeCat.ofHom (infl U.unop.toSubgroup)
      naturality := fun U V f ↦ by
        ext a
        exact infl_transition (leOfHom f.unop) a }

/-- The apex of the inflation cocone is the ambient nonabelian class set. -/
theorem finiteQuotientCocone_pt : (finiteQuotientCocone G A).pt = NonabelianH1 G A :=
  rfl

/-- At each open normal subgroup, the leg of the cocone is inflation. -/
@[simp↓]
theorem finiteQuotientCocone_ι_app_apply (U : (OpenNormalSubgroup G)ᵒᵖ)
    (a : (finiteQuotientDiagram G A).obj U) :
    (finiteQuotientCocone G A).ι.app U a = infl U.unop.toSubgroup a :=
  (rfl)

variable [IsTopologicalGroup G] [CompactSpace G] [DiscreteTopology A]

/-- For compact source and discrete coefficients, inflation exhibits the ambient nonabelian
first cohomology as the filtered colimit of the finite-quotient diagram in types. -/
noncomputable def finiteQuotientIsColimit : IsColimit (finiteQuotientCocone G A) := by
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun U a b h ↦ ?_)
  · obtain ⟨N, c, hc⟩ := exists_mem_range_infl x
    exact ⟨Opposite.op N, c, hc.symm⟩
  · exact ⟨U, 𝟙 U, congrArg ((finiteQuotientDiagram G A).map (𝟙 U))
      (infl_injective U.unop.toSubgroup h)⟩

/-- The canonical comparison from the colimit of the finite-quotient diagram to the ambient
nonabelian class set. -/
noncomputable def finiteQuotientColimitEquiv :
    colimit (finiteQuotientDiagram G A) ≃ NonabelianH1 G A :=
  ((colimit.isColimit _).coconePointUniqueUpToIso (finiteQuotientIsColimit G A)).toEquiv

/-- The canonical comparison acts on each colimit inclusion by inflation. -/
@[simp]
theorem finiteQuotientColimitEquiv_ι (U : (OpenNormalSubgroup G)ᵒᵖ)
    (a : (finiteQuotientDiagram G A).obj U) :
    finiteQuotientColimitEquiv G A (colimit.ι (finiteQuotientDiagram G A) U a) =
      infl U.unop.toSubgroup a :=
  ConcreteCategory.congr_hom ((colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
    (finiteQuotientIsColimit G A) U) a

/-- The inverse comparison takes a class inflated from a given stage to its colimit inclusion. -/
@[simp]
theorem finiteQuotientColimitEquiv_symm_infl (U : OpenNormalSubgroup G)
    (a : (finiteQuotientDiagram G A).obj (Opposite.op U)) :
    (finiteQuotientColimitEquiv G A).symm (infl U.toSubgroup a) =
      colimit.ι (finiteQuotientDiagram G A) (Opposite.op U) a :=
  (finiteQuotientColimitEquiv G A).symm_apply_eq.mpr
    (finiteQuotientColimitEquiv_ι G A (Opposite.op U) a).symm

end TauCeti.NonabelianH1
