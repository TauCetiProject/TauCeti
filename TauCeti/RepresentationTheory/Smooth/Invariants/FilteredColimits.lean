/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import TauCeti.RepresentationTheory.Smooth.Colimits
public import TauCeti.RepresentationTheory.Smooth.Invariants
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Invariants of smooth representations commute with filtered colimits

Let `G` be a topological group, `A` a commutative ring and `U` a compact subgroup of `G` (in
practice a compact open subgroup of a locally profinite group). The functor
`TauCeti.SmoothRep.invariantsFunctor A U` of `U`-invariants on smooth representations preserves
filtered colimits. No hypothesis on the pro-order of `U` is needed. The representations and the
index categories are taken in the universe of `A`, where Mathlib's forgetful functor on modules
preserves filtered colimits.

Filtered colimits of smooth representations are computed on the underlying modules, so the
point is surjectivity: a `U`-invariant vector `x` of the colimit comes from a vector `y` at some
stage `j`. The stabilizer of `y` in `U` is open, hence of finite index since `U` is compact. For
each of the finitely many coset representatives `u`, the vectors `u y` and `y` have the same image
`x` in the colimit, so they agree at some later stage; one stage `k` serves all of them, and there
the image of `y` is fixed by the representatives and by the stabilizer, hence by `U`.

## Main results

* `TauCeti.SmoothRep.exists_mem_invariants_of_isColimit`: a `U`-invariant vector of a filtered
  colimit is the image of a `U`-invariant vector at some stage.
* `TauCeti.SmoothRep.preservesFilteredColimits_invariantsFunctor`: `invariantsFunctor A U`
  preserves filtered colimits.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §3.3, Proposition 10(2) and its proof, p. 17.
-/

public section

open CategoryTheory Limits

universe u v

namespace TauCeti

namespace SmoothRep

variable {A : Type u} [CommRing A] {G : Type v} [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G]

section Elements

variable {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ SmoothRep.{u} A G}
  {c : Cocone F} (hc : IsColimit c) (U : Subgroup G) [CompactSpace U]

include hc

/-- **A `U`-invariant vector of a filtered colimit comes from a `U`-invariant vector** at some
stage, for `U` compact. -/
theorem exists_mem_invariants_of_isColimit {x : c.pt.obj.V}
    (hx : x ∈ Representation.invariants (c.pt.obj.ρ.comp U.subtype)) :
    ∃ (k : J) (y : (F.obj k).obj.V),
      y ∈ Representation.invariants ((F.obj k).obj.ρ.comp U.subtype) ∧
        (c.ι.app k).hom.hom y = x := by
  classical
  -- Filtered colimits of smooth representations are computed on underlying sets, where they are
  -- described elementwise.
  let hT := isColimitOfPreserves (ι A G ⋙ forget₂ (Rep A G) (ModuleCat A) ⋙ forget _) hc
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hT x
  -- The underlying function of a morphism of smooth representations, after the forgetful
  -- functors, is its `hom.hom` by definition.
  replace hy : (c.ι.app j).hom.hom y = x := hy
  subst hy
  let ρ := (F.obj j).obj.ρ
  have : Representation.IsSmooth ρ := (F.obj j).property
  have : SeparatelyContinuousMul U :=
    ⟨(continuous_const_mul _ |>.comp continuous_subtypeVal).subtype_mk _,
      (continuous_mul_const _ |>.comp continuous_subtypeVal).subtype_mk _⟩
  -- the stabilizer of `y` in `U` is open, hence of finite index
  let S : Subgroup U := (ρ.stabilizer y).subgroupOf U
  have hS : IsOpen (S : Set U) :=
    (Representation.IsSmooth.isOpen_stabilizer (ρ := ρ) y).preimage continuous_subtypeVal
  have := S.quotient_finite_of_isOpen hS
  have := Fintype.ofFinite (U ⧸ S)
  -- For each coset representative `q.out` the vectors `q.out • y` and `y` have the same image, so
  -- they agree at a later stage, recorded as an object of the filtered category `Under j`.
  have hq (q : U ⧸ S) : ∃ X : Under j,
      (F.map X.hom).hom.hom (ρ (q.out : G) y) = (F.map X.hom).hom.hom y := by
    have h : (c.ι.app j).hom.hom (ρ (q.out : G) y) = (c.ι.app j).hom.hom y := by
      rw [Rep.hom_comm_apply]
      exact hx q.out
    obtain ⟨k, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hT _ _).1 h
    exact ⟨Under.mk f, hf⟩
  choose X hX using hq
  obtain ⟨T, hXT⟩ := IsFiltered.sup_objs_exists (Finset.univ.image X)
  refine ⟨T.right, (F.map T.hom).hom.hom y, fun u ↦ ?_, ?_⟩
  · obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S u
    have hu : (u : G) = ((QuotientGroup.mk u : U ⧸ S).out : G) * ((s : U)⁻¹ : U) := by
      rw [hs, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_right]
    have hsy : ρ (((s : U)⁻¹ : U) : G) y = y :=
      Representation.mem_stabilizer.mp (Subgroup.mem_subgroupOf.mp (S.inv_mem s.property))
    obtain ⟨m⟩ := hXT (Finset.mem_image_of_mem X (Finset.mem_univ (QuotientGroup.mk u)))
    rw [MonoidHom.comp_apply, Subgroup.subtype_apply, ← Rep.hom_comm_apply, hu, map_mul,
      mul_apply_eq_comp, hsy, ← Under.w m, Functor.map_comp]
    simp only [ObjectProperty.FullSubcategory.comp_hom, Rep.hom_comp,
      Representation.IntertwiningMap.comp_apply]
    exact congrArg (F.map m.right).hom.hom (hX _)
  · -- The image of `F.map T.hom y` in the colimit is that of `y`, by naturality of `c`.
    rw [← c.w T.hom]
    simp only [ObjectProperty.FullSubcategory.comp_hom, Rep.hom_comp,
      Representation.IntertwiningMap.comp_apply]

/-- **Invariants commute with filtered colimits**: for `U` compact, the functor of `U`-invariants
on smooth representations preserves filtered colimits. -/
theorem isColimit_mapCocone_invariantsFunctor :
    Nonempty (IsColimit ((invariantsFunctor.{u} A U).mapCocone c)) := by
  have := reflectsColimit_of_reflectsIsomorphisms (F ⋙ invariantsFunctor.{u} A U)
    (forget (ModuleCat.{u} A))
  refine ⟨isColimitOfReflects (forget (ModuleCat.{u} A)) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ (fun x ↦ ?_) fun i j xi xj h ↦ ?_
  · obtain ⟨k, y, hy, hyx⟩ := exists_mem_invariants_of_isColimit hc U x.property
    exact ⟨k, ⟨y, hy⟩, Subtype.ext hyx.symm⟩
  · obtain ⟨k, f, g, hfg⟩ := (Types.FilteredColimit.isColimit_eq_iff _
      (isColimitOfPreserves (ι A G ⋙ forget₂ (Rep A G) (ModuleCat A) ⋙ forget _) hc)).1
      (congrArg Subtype.val h)
    exact ⟨k, f, g, Subtype.ext hfg⟩

end Elements

/-- **Invariants preserve filtered colimits** of smooth representations, for `U` compact. -/
instance preservesFilteredColimits_invariantsFunctor (U : Subgroup G) [CompactSpace U] :
    PreservesFilteredColimits (invariantsFunctor.{u} A U) where
  preserves_filtered_colimits _ _ _ :=
    ⟨fun {_} ↦ ⟨fun hc ↦ isColimit_mapCocone_invariantsFunctor hc U⟩⟩

end SmoothRep

end TauCeti
