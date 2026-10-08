/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DirectSum.FiniteSupport
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Map
public import TauCeti.CategoryTheory.AInfinity.Basic

/-!
# The one-object A-infinity category of an A-infinity algebra

An `A∞` algebra `𝒜` on a graded module `A` is an `A∞` category with a single object, whose
endomorphisms are `A`.  The graded linear quiver `TauCeti.AInfinitySingleObj 𝒜` has one object
`TauCeti.AInfinitySingleObj.star 𝒜` with endomorphism module `A`, graded as `𝒜` is, and
`TauCeti.AInfinitySingleObj.aInfinityCategory 𝒜` is its `A∞` structure: the operations of `𝒜`,
transported to the total module of morphisms along the inclusion of the single hom module, which
is a linear equivalence.

The operation of the category on a string of endomorphisms is the operation of the algebra,
`TauCeti.AInfinitySingleObj.coe_pathOperation_aInfinityCategory_apply`; in particular its
differential and composition are `m₁` and `m₂` of `𝒜`.

## Main definitions

* `TauCeti.AInfinitySingleObj`: the one-object graded linear quiver of an `A∞` algebra.
* `TauCeti.AInfinitySingleObj.aInfinityCategory`: its `A∞` category structure.

## Main results

* `TauCeti.AInfinitySingleObj.coe_pathOperation_aInfinityCategory_apply`: the operations of the
  one-object `A∞` category are the operations of the algebra.
* `TauCeti.AInfinitySingleObj.homDifferential_aInfinityCategory` and
  `TauCeti.AInfinitySingleObj.comp_aInfinityCategory`: its differential and composition are `m₁`
  and `m₂`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7.1.
-/

public section

namespace TauCeti

universe uR uA

open GradedLinearQuiver

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- The objects of the **one-object `A∞` category** of an `A∞` algebra `𝒜`: a single object
`TauCeti.AInfinitySingleObj.star 𝒜`, whose endomorphisms are the underlying module of `𝒜`.

The type is a structure indexed by `𝒜`, so that the quivers of different `A∞` algebras are not
interchangeable. -/
structure AInfinitySingleObj (𝒜 : AInfinityAlgebra R A) : Type

namespace AInfinitySingleObj

variable (𝒜 : AInfinityAlgebra R A)

/-- The unique object of the one-object `A∞` category. -/
def star : AInfinitySingleObj 𝒜 := ⟨⟩

instance : Unique (AInfinitySingleObj 𝒜) where
  default := star 𝒜
  uniq _ := rfl

/-- The one-object graded linear quiver of an `A∞` algebra: the endomorphisms of the single object
are the underlying graded module of the algebra. -/
instance : GradedLinearQuiver.{0, uA, uR} R (AInfinitySingleObj 𝒜) where
  homModule _ _ := ModuleCat.of R A
  grading _ _ := 𝒜.grading

/-- The inclusion of the endomorphisms of the single object into the total module of morphisms is
a linear equivalence, with inverse the projection. -/
noncomputable def totalHomEquiv : A ≃ₗ[R] TotalHom R (AInfinitySingleObj 𝒜) :=
  letI := Classical.decEq (AInfinitySingleObj 𝒜)
  (DirectSum.componentLinearEquiv (R := R) (fun p ↦ homModule (R := R) p.1 p.2) (star 𝒜, star 𝒜)
    fun _ h ↦ absurd (Subsingleton.elim _ _) h).symm

/-- The equivalence `totalHomEquiv` is the inclusion of the endomorphisms of the single object. -/
@[simp]
theorem totalHomEquiv_apply (a : A) :
    totalHomEquiv 𝒜 a = homInclusion (R := R) (star 𝒜) (star 𝒜) a := by
  let := Classical.decEq (AInfinitySingleObj 𝒜)
  rw [homInclusion_eq_lof]
  exact DirectSum.componentLinearEquiv_symm_apply
    (fun p : AInfinitySingleObj 𝒜 × AInfinitySingleObj 𝒜 ↦ homModule (R := R) p.1 p.2) _ _ a

/-- The inverse of `totalHomEquiv` is the projection onto the endomorphisms of the single
object. -/
@[simp]
theorem totalHomEquiv_symm_apply (x : TotalHom R (AInfinitySingleObj 𝒜)) :
    (totalHomEquiv 𝒜).symm x = homProjection (R := R) (star 𝒜) (star 𝒜) x := by
  rw [LinearEquiv.symm_apply_eq, totalHomEquiv_apply]
  refine totalHom_ext fun X Y ↦ ?_
  obtain rfl := Subsingleton.elim X (star 𝒜)
  obtain rfl := Subsingleton.elim Y (star 𝒜)
  rw [homProjection_homInclusion]

/-- The **one-object `A∞` category** of an `A∞` algebra: the operations of the algebra,
transported to the total module of morphisms of its one-object graded linear quiver. -/
noncomputable def aInfinityCategory : AInfinityCategory R (AInfinitySingleObj 𝒜) where
  __ := 𝒜.map (totalHomEquiv 𝒜)
  grading_eq := InternalGrading.ext fun p ↦ Submodule.ext fun x ↦ by
    rw [AInfinityAlgebra.map_grading, InternalGrading.mem_map_piece_iff,
      mem_totalGrading_piece_iff, totalHomEquiv_symm_apply]
    exact ⟨fun h X Y ↦ by rwa [Subsingleton.elim X (star 𝒜), Subsingleton.elim Y (star 𝒜)],
      fun h ↦ h _ _⟩
  isPathCompatible_m_of_pos _ _ :=
    { mem_range_homInclusion X _ := by
        obtain rfl : X = fun _ ↦ star 𝒜 := funext fun _ ↦ Subsingleton.elim _ _
        exact ⟨_, (totalHomEquiv_apply 𝒜 _).symm.trans ((totalHomEquiv 𝒜).apply_symm_apply _)⟩
      eq_zero_of_ne _ _ _ _ _ _ hne := absurd (Subsingleton.elim _ _) hne }

/-- The total `A∞` algebra of the one-object `A∞` category is the algebra, transported to the
total module of morphisms. -/
theorem toAInfinityAlgebra_aInfinityCategory :
    (aInfinityCategory 𝒜).toAInfinityAlgebra = 𝒜.map (totalHomEquiv 𝒜) := (rfl)

/-- The operations of the one-object `A∞` category are the operations of the algebra. -/
@[simp]
theorem coe_pathOperation_aInfinityCategory_apply {n : ℕ} (X : Fin (n + 1) → AInfinitySingleObj 𝒜)
    (d : Fin n → ℤ) (x : ∀ i, grHom R (X i.rev.castSucc) (X i.rev.succ) (d i)) :
    ((aInfinityCategory 𝒜).pathOperation X d x : A) = 𝒜.m n fun i ↦ (x i : A) := by
  obtain rfl : X = fun _ ↦ star 𝒜 := funext fun _ ↦ Subsingleton.elim _ _
  simp [AInfinityCategory.coe_pathOperation_apply, toAInfinityAlgebra_aInfinityCategory]

/-- The differential of the one-object `A∞` category is the unary operation of the algebra. -/
@[simp]
theorem homDifferential_aInfinityCategory (X Y : AInfinitySingleObj 𝒜) (a : A) :
    (aInfinityCategory 𝒜).homDifferential X Y a = 𝒜.m 1 ![a] := by
  obtain rfl := Subsingleton.elim X (star 𝒜)
  obtain rfl := Subsingleton.elim Y (star 𝒜)
  simp only [AInfinityCategory.homDifferential_apply, toAInfinityAlgebra_aInfinityCategory,
    AInfinityAlgebra.map_m_apply, totalHomEquiv_apply, totalHomEquiv_symm_apply,
    homProjection_homInclusion]
  congr 1
  funext i
  fin_cases i
  simp

/-- The composition of the one-object `A∞` category is the binary operation of the algebra. -/
@[simp]
theorem comp_aInfinityCategory (X Y Z : AInfinitySingleObj 𝒜) (a b : A) :
    (aInfinityCategory 𝒜).comp X Y Z a b = 𝒜.m 2 ![a, b] := by
  obtain rfl := Subsingleton.elim X (star 𝒜)
  obtain rfl := Subsingleton.elim Y (star 𝒜)
  obtain rfl := Subsingleton.elim Z (star 𝒜)
  simp only [AInfinityCategory.comp_apply, toAInfinityAlgebra_aInfinityCategory,
    AInfinityAlgebra.map_m_apply, totalHomEquiv_apply, totalHomEquiv_symm_apply,
    homProjection_homInclusion]
  congr 1
  funext i
  fin_cases i <;> simp

end AInfinitySingleObj

end TauCeti
