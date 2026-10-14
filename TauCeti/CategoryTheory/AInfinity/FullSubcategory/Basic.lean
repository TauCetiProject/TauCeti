/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Strict
public import TauCeti.CategoryTheory.AInfinity.Induced
public import TauCeti.CategoryTheory.Graded.FullSubquiver

/-!
# Full subcategories of A-infinity categories

Restricting the objects of an `A∞` category `𝒞` on a graded linear quiver `C` to those satisfying
a predicate `P` leaves its hom modules and its operations on composable strings intact.  This is
the **full subcategory** `𝒞.fullSubcategory P`, the `A∞` category induced along the inclusion
`Subtype.val` of the objects satisfying `P` (`TauCeti.AInfinityCategory.induced`), on the full
subquiver `TauCeti.GradedLinearQuiver.FullSubquiver P`.  It is reducible, so the API of induced
categories (operations on composable strings, differential, composition) applies to it directly.

Since `Subtype.val` is injective, the map of total modules of morphisms of the full subquiver into
that of `C` is injective, and it intertwines the operations on all strings, not only on composable
ones: a string of morphisms which is not composable in the full subquiver is not composable in
`C`.  It is therefore a strict `A∞` morphism of total algebras.
The homotopy-level consequences are in
`TauCeti.CategoryTheory.AInfinity.FullSubcategory.HomotopyCategory`.

## Main definitions

* `TauCeti.AInfinityCategory.fullSubcategory`: the full `A∞` subcategory on the objects
  satisfying a predicate.
* `TauCeti.AInfinityCategory.fullSubcategoryInclusion`: the inclusion of its total algebra of
  morphisms into that of `𝒞`, a strict `A∞` morphism.

## Main results

* `TauCeti.AInfinityCategory.totalHomMap_fullSubcategory_m`: the inclusion of total modules
  intertwines the operations of the full subcategory with those of `𝒞`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7, for `A∞` categories.
  A full subcategory keeps the morphisms between the chosen objects and the operations on them.
-/

public section

namespace TauCeti

universe u v w

open GradedLinearQuiver GradedLinearQuiver.InducedQuiver GradedLinearQuiver.FullSubquiver

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  (𝒞 : AInfinityCategory R C) (P : C → Prop)

/-- The **full subcategory** of an `A∞` category on the objects satisfying `P`: the `A∞` category
induced along the inclusion of these objects, whose operations on composable strings are those of
`𝒞`. -/
noncomputable abbrev fullSubcategory : AInfinityCategory R (FullSubquiver P) :=
  𝒞.induced Subtype.val

/-- **The inclusion intertwines the operations.** Including the value of an operation of the full
subcategory into the total module of `𝒞` gives the operation of `𝒞` on the included
morphisms. -/
@[simp]
theorem totalHomMap_fullSubcategory_m (n : ℕ) (x : Fin n → TotalHom R (FullSubquiver P)) :
    totalHomMap R Subtype.val ((𝒞.fullSubcategory P).m n x) =
      𝒞.m n fun i ↦ totalHomMap R Subtype.val (x i) := by
  rcases n with _ | n
  · simp [AInfinityAlgebra.m_zero]
  refine sub_eq_zero.1 <| (Submodule.mem_bot R).1 <| multilinearMap_apply_mem
    (f := (totalHomMap R Subtype.val).compMultilinearMap ((𝒞.fullSubcategory P).m (n + 1)) -
      (𝒞.m (n + 1)).compLinearMap fun _ ↦ totalHomMap R Subtype.val)
    (fun X x ↦ ?_) (fun s t x i j hij hne ↦ ?_) x
  · rw [Submodule.mem_bot, sub_apply, LinearMap.compMultilinearMap_apply,
      MultilinearMap.compLinearMap_apply, sub_eq_zero]
    refine 𝒞.totalHomMap_induced_m_of_chain _ (fun i ↦ X i.rev.castSucc) (fun i ↦ X i.rev.succ)
      (fun i ↦ LinearMap.mem_range_self _ _) fun i j hij ↦ congrArg X (Fin.ext ?_)
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_rev]
    omega
  · have hne' : ((t j).obj : C) ≠ (s i).obj := fun e ↦ hne (InducedQuiver.ext (Subtype.ext e))
    simp only [sub_apply, LinearMap.compMultilinearMap_apply,
      MultilinearMap.compLinearMap_apply, totalHomMap_homInclusion,
      ((𝒞.fullSubcategory P).isPathCompatible_m (n + 1)).eq_zero_of_ne s t x i j hij hne,
      (𝒞.isPathCompatible_m (n + 1)).eq_zero_of_ne (fun k ↦ (s k).obj) (fun k ↦ (t k).obj) x i j
        hij hne', map_zero, sub_zero]

/-- The **inclusion of the total algebra of morphisms** of a full subcategory into that of `𝒞`,
a strict `A∞` morphism. -/
noncomputable def fullSubcategoryInclusion :
    AInfinityStrictHom (𝒞.fullSubcategory P).toAInfinityAlgebra 𝒞.toAInfinityAlgebra where
  toLinearMap := totalHomMap R Subtype.val
  map_mem' ha := by
    rw [(𝒞.fullSubcategory P).grading_eq] at ha
    rw [𝒞.grading_eq]
    exact totalHomMap_mem_totalGrading_piece ha
  map_m' n := MultilinearMap.ext fun x ↦ 𝒞.totalHomMap_fullSubcategory_m P n x

/-- The underlying linear map of the full-subcategory inclusion is the inclusion of total
modules. -/
@[simp]
theorem fullSubcategoryInclusion_toLinearMap :
    (𝒞.fullSubcategoryInclusion P).toLinearMap = totalHomMap R Subtype.val := by
  unfold fullSubcategoryInclusion
  rfl

/-- The inclusion of total algebras of a full subcategory is the inclusion of total modules. -/
@[simp]
theorem coe_fullSubcategoryInclusion :
    ⇑(𝒞.fullSubcategoryInclusion P) = totalHomMap R Subtype.val :=
  congrArg (fun g : TotalHom R (FullSubquiver P) →ₗ[R] TotalHom R C ↦ ⇑g)
    (𝒞.fullSubcategoryInclusion_toLinearMap P)

end AInfinityCategory

end TauCeti
