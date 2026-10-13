/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Comap
public import TauCeti.CategoryTheory.AInfinity.Basic
public import TauCeti.CategoryTheory.Graded.FullSubquiver

/-!
# Full subcategories of A-infinity categories

Restricting the objects of an `A∞` category `𝒞` on a graded linear quiver `C` to those satisfying
a predicate `P` leaves its hom modules and its operations on composable strings intact.  This is
the **full subcategory** `𝒞.fullSubcategory P`, an `A∞` category on the full subquiver
`TauCeti.GradedLinearQuiver.FullSubquiver P`: its operation on a composable string of objects
satisfying `P` is the operation of `𝒞` on the same string.

The total module of morphisms of the full subquiver includes into that of `C`, and its image is
closed under the operations of `𝒞`: a composable string of morphisms between objects satisfying
`P` is sent to a morphism between two such objects, and every other string to zero.  The
`A∞` structure of the full subcategory is therefore the pullback of the total algebra of `𝒞` along
this injective inclusion (`TauCeti.AInfinityAlgebra.comap`), which is a strict `A∞` morphism of
total algebras.  Differentials and composition are those of `𝒞`.
The homotopy-level consequences are in
`TauCeti.CategoryTheory.AInfinity.FullSubcategory.HomotopyCategory`.

## Main definitions

* `TauCeti.AInfinityCategory.fullSubcategory`: the full `A∞` subcategory on the objects
  satisfying a predicate.
* `TauCeti.AInfinityCategory.fullSubcategoryInclusion`: the inclusion of its total algebra of
  morphisms into that of `𝒞`, a strict `A∞` morphism.

## Main results

* `TauCeti.AInfinityCategory.totalHomInclusion_fullSubcategory_m`: the inclusion of total
  modules intertwines the operations of the full subcategory with those of `𝒞`.
* `TauCeti.AInfinityCategory.coe_pathOperation_fullSubcategory_apply`: the operation of the full
  subcategory on a composable string is the operation of `𝒞` on the same string.
* `TauCeti.AInfinityCategory.homDifferential_fullSubcategory` and
  `TauCeti.AInfinityCategory.comp_fullSubcategory`: its differential and composition are those
  of `𝒞`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7, for `A∞` categories.
  A full subcategory keeps the morphisms between the chosen objects and the operations on them.
-/

public section

namespace TauCeti

universe u v w

open GradedLinearQuiver GradedLinearQuiver.FullSubquiver

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  (𝒞 : AInfinityCategory R C) (P : C → Prop)

/-- The image of the total module of morphisms of the full subquiver is closed under the
operations of `𝒞`. -/
private theorem m_totalHomInclusion_mem_range (n : ℕ)
    (x : Fin (n + 1) → TotalHom R (FullSubquiver P)) :
    𝒞.m (n + 1) (fun i ↦ totalHomInclusion R P (x i)) ∈
      LinearMap.range (totalHomInclusion R P) := by
  refine multilinearMap_apply_mem (f := (𝒞.m (n + 1)).compLinearMap fun _ ↦ totalHomInclusion R P)
    (fun X x ↦ ?_) (fun s t x i j hij hne ↦ ?_) x
  · simp only [MultilinearMap.compLinearMap_apply, totalHomInclusion_homInclusion]
    obtain ⟨b, hb⟩ := (𝒞.isPathCompatible_m (n + 1)).mem_range_homInclusion (fun k ↦ (X k).obj) x
    exact ⟨homInclusion (X 0) (X (Fin.last _)) b, by rw [totalHomInclusion_homInclusion, hb]⟩
  · simp only [MultilinearMap.compLinearMap_apply, totalHomInclusion_homInclusion]
    exact (𝒞.isPathCompatible_m (n + 1)).eq_zero_of_ne (fun k ↦ (s k).obj) (fun k ↦ (t k).obj) x
      i j hij fun e ↦ hne (FullSubquiver.ext e)

/-- The total algebra of morphisms of the full subcategory: the pullback of the total algebra of
`𝒞` along the inclusion of total modules. -/
private noncomputable def fullSubcategoryAlgebra :
    AInfinityAlgebra R (TotalHom R (FullSubquiver P)) :=
  𝒞.toAInfinityAlgebra.comap (totalGrading R (FullSubquiver P)) (totalHomInclusion R P)
    totalHomInclusion_injective
    (fun _ _ ↦ by rw [𝒞.grading_eq, totalHomInclusion_mem_totalGrading_piece_iff])
    (fun _ hn ↦ by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
      exact 𝒞.m_totalHomInclusion_mem_range P n)

private theorem totalHomInclusion_fullSubcategoryAlgebra_m (n : ℕ)
    (x : Fin n → TotalHom R (FullSubquiver P)) :
    totalHomInclusion R P ((𝒞.fullSubcategoryAlgebra P).m n x) =
      𝒞.m n fun i ↦ totalHomInclusion R P (x i) :=
  AInfinityAlgebra.map_m_comap _ _ _ _ _ _ n x

/-- The **full subcategory** of an `A∞` category on the objects satisfying `P`: the `A∞` category
on the full subquiver whose operations on composable strings are those of `𝒞`
(`TauCeti.AInfinityCategory.coe_pathOperation_fullSubcategory_apply`). -/
noncomputable def fullSubcategory : AInfinityCategory R (FullSubquiver P) where
  toAInfinityAlgebra := 𝒞.fullSubcategoryAlgebra P
  grading_eq := AInfinityAlgebra.comap_grading _ _ _ _ _ _
  isPathCompatible_m_of_pos n _ :=
    { mem_range_homInclusion X x := by
        obtain ⟨b, hb⟩ :=
          (𝒞.isPathCompatible_m n).mem_range_homInclusion (fun k ↦ (X k).obj) x
        refine ⟨b, totalHomInclusion_injective ?_⟩
        simpa [totalHomInclusion_fullSubcategoryAlgebra_m] using hb
      eq_zero_of_ne s t x i j hij hne := totalHomInclusion_injective <| by
        simpa [totalHomInclusion_fullSubcategoryAlgebra_m] using
          (𝒞.isPathCompatible_m n).eq_zero_of_ne (fun k ↦ (s k).obj) (fun k ↦ (t k).obj) x
            i j hij fun e ↦ hne (FullSubquiver.ext e) }

/-- **The inclusion intertwines the operations.** Including the value of an operation of the full
subcategory into the total module of `𝒞` gives the operation of `𝒞` on the included
morphisms. -/
@[simp]
theorem totalHomInclusion_fullSubcategory_m (n : ℕ) (x : Fin n → TotalHom R (FullSubquiver P)) :
    totalHomInclusion R P ((𝒞.fullSubcategory P).m n x) =
      𝒞.m n fun i ↦ totalHomInclusion R P (x i) :=
  𝒞.totalHomInclusion_fullSubcategoryAlgebra_m P n x

/-- The full subcategory is the unique `A∞` category on the full subquiver whose operations the
inclusion of total modules intertwines with those of `𝒞`. -/
theorem eq_fullSubcategory {𝒟 : AInfinityCategory R (FullSubquiver P)}
    (h : ∀ n, 0 < n → ∀ x : Fin n → TotalHom R (FullSubquiver P),
      totalHomInclusion R P (𝒟.m n x) = 𝒞.m n fun i ↦ totalHomInclusion R P (x i)) :
    𝒟 = 𝒞.fullSubcategory P := by
  refine ext <| funext fun n ↦ ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [𝒟.m_zero, AInfinityAlgebra.m_zero]
  · exact MultilinearMap.ext fun x ↦ totalHomInclusion_injective <| by
      rw [h n hn, totalHomInclusion_fullSubcategory_m]

/-- The operation of the full subcategory on a composable string is the operation of `𝒞` on the
same string. -/
@[simp]
theorem coe_pathOperation_fullSubcategory_apply {n : ℕ} (X : Fin (n + 1) → FullSubquiver P)
    (d : Fin n → ℤ) (x : ∀ i, grHom R (X i.rev.castSucc) (X i.rev.succ) (d i)) :
    ((𝒞.fullSubcategory P).pathOperation X d x : homModule (R := R) (X 0).obj (X (Fin.last n)).obj)
      = 𝒞.pathOperation (fun k ↦ (X k).obj) d x := by
  apply homInclusion_injective (X 0).obj (X (Fin.last n)).obj
  have h := 𝒞.homInclusion_pathOperation (fun k ↦ (X k).obj) d x
  rw [← totalHomInclusion_homInclusion, homInclusion_pathOperation,
    totalHomInclusion_fullSubcategory_m]
  simpa only [totalHomInclusion_homInclusion] using h.symm

/-- The differential of the full subcategory is the differential of `𝒞`. -/
@[simp]
theorem homDifferential_fullSubcategory (X Y : FullSubquiver P)
    (f : homModule (R := R) X.obj Y.obj) :
    (𝒞.fullSubcategory P).homDifferential X Y f = 𝒞.homDifferential X.obj Y.obj f := by
  apply homInclusion_injective X.obj Y.obj
  rw [← totalHomInclusion_homInclusion, homInclusion_homDifferential,
    AInfinityAlgebra.differential_apply, totalHomInclusion_fullSubcategory_m,
    homInclusion_homDifferential, AInfinityAlgebra.differential_apply]
  congr 1
  funext i
  fin_cases i
  simp

/-- The composition of the full subcategory is the composition of `𝒞`. -/
@[simp]
theorem comp_fullSubcategory (X Y Z : FullSubquiver P) (g : homModule (R := R) Y.obj Z.obj)
    (f : homModule (R := R) X.obj Y.obj) :
    (𝒞.fullSubcategory P).comp X Y Z g f = 𝒞.comp X.obj Y.obj Z.obj g f := by
  apply homInclusion_injective X.obj Z.obj
  rw [← totalHomInclusion_homInclusion, homInclusion_comp, homInclusion_comp,
    totalHomInclusion_fullSubcategory_m]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The **inclusion of the total algebra of morphisms** of a full subcategory into that of `𝒞`,
a strict `A∞` morphism. -/
noncomputable def fullSubcategoryInclusion :
    AInfinityStrictHom (𝒞.fullSubcategory P).toAInfinityAlgebra 𝒞.toAInfinityAlgebra :=
  AInfinityAlgebra.comapStrictHom _ _ _ _ _ _

/-- The underlying linear map of the full-subcategory inclusion is the inclusion of total
modules. -/
@[simp]
theorem fullSubcategoryInclusion_toLinearMap :
    (𝒞.fullSubcategoryInclusion P).toLinearMap = totalHomInclusion R P :=
  AInfinityAlgebra.comapStrictHom_toLinearMap _ _ _ _ _ _

/-- The inclusion of total algebras of a full subcategory is the inclusion of total modules. -/
@[simp]
theorem coe_fullSubcategoryInclusion :
    ⇑(𝒞.fullSubcategoryInclusion P) = totalHomInclusion R P :=
  congrArg (fun g : TotalHom R (FullSubquiver P) →ₗ[R] TotalHom R C ↦ ⇑g)
    (𝒞.fullSubcategoryInclusion_toLinearMap P)

end AInfinityCategory

end TauCeti
