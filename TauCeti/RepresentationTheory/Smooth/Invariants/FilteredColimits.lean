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
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
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
  {c : Cocone F} (hc : IsColimit c)

include hc

/-- Every vector of a filtered colimit of smooth representations comes from some stage. -/
theorem exists_apply_eq_of_isColimit (x : c.pt.obj.V) :
    ∃ (j : J) (y : (F.obj j).obj.V), (c.ι.app j).hom.hom y = x := by
  obtain ⟨j, y, h⟩ := Concrete.isColimit_exists_rep (F ⋙ ι A G ⋙ forget₂ (Rep A G) (ModuleCat A))
    (isColimitOfPreserves (ι A G ⋙ forget₂ (Rep A G) (ModuleCat A)) hc) x
  exact ⟨j, y, h⟩

/-- Two vectors at stages `i` and `j` of a filtered colimit of smooth representations have the
same image exactly when they agree at some later stage. -/
theorem apply_eq_apply_iff_of_isColimit {i j : J} (x : (F.obj i).obj.V) (y : (F.obj j).obj.V) :
    (c.ι.app i).hom.hom x = (c.ι.app j).hom.hom y ↔
      ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), (F.map f).hom.hom x = (F.map g).hom.hom y :=
  Concrete.isColimit_rep_eq_iff_exists (F ⋙ ι A G ⋙ forget₂ (Rep A G) (ModuleCat A))
    (isColimitOfPreserves (ι A G ⋙ forget₂ (Rep A G) (ModuleCat A)) hc) (i := i) (j := j) x y

/-- Two vectors at the same stage with the same image agree after a single map to a later stage. -/
theorem exists_map_eq_of_isColimit {j : J} {x y : (F.obj j).obj.V}
    (h : (c.ι.app j).hom.hom x = (c.ι.app j).hom.hom y) :
    ∃ (k : J) (f : j ⟶ k), (F.map f).hom.hom x = (F.map f).hom.hom y := by
  obtain ⟨k, f, g, hfg⟩ := (apply_eq_apply_iff_of_isColimit hc x y).mp h
  refine ⟨IsFiltered.coeq f g, f ≫ IsFiltered.coeqHom f g, ?_⟩
  have h₁ : (F.map (f ≫ IsFiltered.coeqHom f g)).hom.hom x =
      (F.map (IsFiltered.coeqHom f g)).hom.hom ((F.map f).hom.hom x) := by
    rw [F.map_comp]
    rfl
  have h₂ : (F.map (g ≫ IsFiltered.coeqHom f g)).hom.hom y =
      (F.map (IsFiltered.coeqHom f g)).hom.hom ((F.map g).hom.hom y) := by
    rw [F.map_comp]
    rfl
  rw [h₁, hfg, ← h₂, IsFiltered.coeq_condition]

omit hc [SeparatelyContinuousMul G] in
/-- Finitely many pairs of vectors at a stage `j`, each pair agreeing after some map out of `j`,
all agree after a single map out of `j`. -/
theorem exists_map_eq_of_finset {ι : Type*} (s : Finset ι) {j : J} (x y : ι → (F.obj j).obj.V)
    (h : ∀ i ∈ s, ∃ (k : J) (f : j ⟶ k), (F.map f).hom.hom (x i) = (F.map f).hom.hom (y i)) :
    ∃ (k : J) (f : j ⟶ k), ∀ i ∈ s, (F.map f).hom.hom (x i) = (F.map f).hom.hom (y i) := by
  classical
  -- agreement after `f` persists after any `f ≫ g`
  have hcomp : ∀ {k k' : J} (f : j ⟶ k) (g : k ⟶ k') {a b : (F.obj j).obj.V},
      (F.map f).hom.hom a = (F.map f).hom.hom b →
        (F.map (f ≫ g)).hom.hom a = (F.map (f ≫ g)).hom.hom b := by
    intro k k' f g a b hab
    rw [F.map_comp]
    change (F.map g).hom.hom ((F.map f).hom.hom a) = (F.map g).hom.hom ((F.map f).hom.hom b)
    rw [hab]
  induction s using Finset.induction_on with
  | empty => exact ⟨j, 𝟙 j, by simp⟩
  | insert i s hi ih =>
    obtain ⟨k, f, hf⟩ := ih fun i' hi' ↦ h i' (Finset.mem_insert_of_mem hi')
    obtain ⟨k', f', hf'⟩ := h i (Finset.mem_insert_self i s)
    let a := f ≫ IsFiltered.leftToMax k k'
    let b := f' ≫ IsFiltered.rightToMax k k'
    refine ⟨IsFiltered.coeq a b, a ≫ IsFiltered.coeqHom a b, fun i' hi' ↦ ?_⟩
    rcases Finset.mem_insert.mp hi' with rfl | hi'
    · rw [IsFiltered.coeq_condition]
      exact hcomp _ _ (hcomp _ _ hf')
    · exact hcomp _ _ (hcomp _ _ (hf i' hi'))

variable (U : Subgroup G) [CompactSpace U]

/-- **A `U`-invariant vector of a filtered colimit comes from a `U`-invariant vector** at some
stage, for `U` compact. -/
theorem exists_mem_invariants_of_isColimit {x : c.pt.obj.V}
    (hx : x ∈ Representation.invariants (c.pt.obj.ρ.comp U.subtype)) :
    ∃ (k : J) (y : (F.obj k).obj.V),
      y ∈ Representation.invariants ((F.obj k).obj.ρ.comp U.subtype) ∧
        (c.ι.app k).hom.hom y = x := by
  classical
  obtain ⟨j, y, rfl⟩ := exists_apply_eq_of_isColimit hc x
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
  -- each coset representative fixes the image of `y` after some map out of `j`
  obtain ⟨k, f, hf⟩ := exists_map_eq_of_finset (F := F) Finset.univ
    (fun q : U ⧸ S ↦ ρ (q.out : G) y) (fun _ ↦ y) fun q _ ↦ exists_map_eq_of_isColimit hc <| by
      rw [Rep.hom_comm_apply]
      exact hx q.out
  refine ⟨k, (F.map f).hom.hom y, fun u ↦ ?_, ?_⟩
  · obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S u
    have hu : (u : G) = ((QuotientGroup.mk u : U ⧸ S).out : G) * ((s : U)⁻¹ : U) := by
      rw [hs, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_right]
    have hsy : ρ (((s : U)⁻¹ : U) : G) y = y :=
      Representation.mem_stabilizer.mp (Subgroup.mem_subgroupOf.mp (S.inv_mem s.property))
    change (F.obj k).obj.ρ (u : G) ((F.map f).hom.hom y) = _
    rw [← Rep.hom_comm_apply]
    change (F.map f).hom.hom (ρ (u : G) y) = _
    rw [hu, map_mul, mul_apply_eq_comp, hsy]
    exact hf _ (Finset.mem_univ _)
  · change ((F.map f ≫ c.ι.app k).hom.hom y) = _
    rw [c.w f]

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
  · obtain ⟨k, f, g, hfg⟩ := (apply_eq_apply_iff_of_isColimit hc xi.val xj.val).mp
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
