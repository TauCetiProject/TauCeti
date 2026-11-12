/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Map
public import TauCeti.Algebra.Homology.SquareZero
public import TauCeti.CategoryTheory.AInfinity.HomotopyCategory

/-!
# The cohomology of the Hom complexes of an A-infinity category

Let `𝒞` be an `A∞` category on a graded linear quiver `C`.  Every operation of the total algebra of
morphisms sends a string of morphisms `X ⟶ Y` back to a morphism `X ⟶ Y`: a string of length at
least two is composable only when `X = Y`, and is sent to zero otherwise
(`TauCeti.AInfinityCategory.m_homInclusion_mem_range`).  So each hom module is a sub-`A∞` algebra
of the total algebra, `TauCeti.AInfinityCategory.homAlgebra`, whose unary operation is the Hom
differential `m₁`.  For `X = Y` it is the endomorphism `A∞` algebra of `X`; for `X ≠ Y` its
operations of arity at least two vanish.  Its cohomology is the cohomology `H(Hom(X, Y), m₁)` of
the Hom complex, in all degrees at once, and the `A∞` algebra API (cycles, boundaries, cohomology
classes, the grading of cohomology, and over a field the cohomology contraction) applies to it.

The composite of two closed morphisms is closed, and its class depends only on the classes of the
factors (`TauCeti.AInfinityCategory.cohomologyClass_comp_congr`).  The Hom cohomologies are the hom
modules of the **cohomology quiver** `TauCeti.AInfinityCategory.CohomologyQuiver`, which has one
object for each object of `C`.  This quiver carries the minimal model of `𝒞`
(`TauCeti/CategoryTheory/AInfinity/Transfer/Cohomology.lean`).

## Main definitions

* `TauCeti.AInfinityCategory.homAlgebra`: the hom module `X ⟶ Y` as a sub-`A∞` algebra of the
  total algebra of morphisms.
* `TauCeti.AInfinityCategory.CohomologyQuiver`: the graded linear quiver of Hom cohomologies.
* `TauCeti.AInfinityCategory.cohomologyQuiverEquiv`: its objects are the objects of `C`.

## Main results

* `TauCeti.AInfinityCategory.m_homInclusion_mem_range`: the operations preserve every hom module.
* `TauCeti.AInfinityCategory.homAlgebra_differential`: the unary operation of a hom module is the
  Hom differential.
* `TauCeti.AInfinityCategory.mem_homAlgebra_cycles` and
  `TauCeti.AInfinityCategory.homAlgebra_boundaries`: its cycles are the closed morphisms and its
  boundaries the exact ones.
* `TauCeti.AInfinityCategory.homAlgebraCohomologyEquiv`: its cohomology is the cohomology
  `ker m₁ ⧸ im m₁` of the Hom complex.
* `TauCeti.AInfinityCategory.cohomologyClass_comp_congr`: composition is well defined on Hom
  cohomology.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7.
-/

public section

namespace TauCeti

open GradedLinearQuiver

universe u v w

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  (𝒞 : AInfinityCategory R C)

/-! ### Hom modules as sub-`A∞` algebras -/

/-- **Every operation of positive arity sends morphisms `X ⟶ Y` to a morphism `X ⟶ Y`.**  A
string of morphisms `X ⟶ Y` of length at least two is composable only when `X = Y`, and is sent to
zero otherwise. -/
theorem m_homInclusion_mem_range (X Y : C) {n : ℕ} (hn : 0 < n)
    (x : Fin n → homModule (R := R) X Y) :
    𝒞.m n (fun i ↦ homInclusion X Y (x i)) ∈ LinearMap.range (homInclusion (R := R) X Y) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
  by_cases h : k = 0 ∨ X = Y
  · refine (𝒞.isPathCompatible_m (0 + k + 1)).mem_range_homInclusion_of_chain (fun _ ↦ X)
      (fun _ ↦ Y) x (fun j ↦ ?_) rfl rfl
    rcases h with rfl | h
    · exact j.elim0
    · exact h.symm
  · rw [not_or] at h
    rw [(𝒞.isPathCompatible_m (0 + k + 1)).eq_zero_of_ne (fun _ ↦ X) (fun _ ↦ Y) x ⟨0, by omega⟩
      ⟨1, by omega⟩ rfl fun e ↦ h.2 e.symm]
    exact zero_mem _

/-- The hom module `X ⟶ Y` of an `A∞` category, as a **sub-`A∞` algebra** of the total algebra of
morphisms (`m_homInclusion_mem_range`).  Its unary operation is the Hom differential
(`homAlgebra_differential`), so its cohomology is the cohomology of the Hom complex.  For `X ≠ Y`
its operations of arity at least two vanish; for `X = Y` it is the endomorphism `A∞` algebra
of `X`. -/
noncomputable def homAlgebra (X Y : C) : AInfinityAlgebra R (homModule (R := R) X Y) :=
  𝒞.toAInfinityAlgebra.comap (grading (R := R) X Y) (homInclusion X Y) (homInclusion_injective X Y)
    (fun p f ↦ by rw [𝒞.grading_eq, homInclusion_mem_totalGrading_piece_iff])
    (fun _ hn x ↦ 𝒞.m_homInclusion_mem_range X Y hn x)

/-- The grading of the sub-`A∞` algebra of morphisms `X ⟶ Y` is the grading of the hom module. -/
@[simp]
theorem homAlgebra_grading (X Y : C) : (𝒞.homAlgebra X Y).grading = grading (R := R) X Y :=
  AInfinityAlgebra.comap_grading ..

/-- The operations of the sub-`A∞` algebra of morphisms `X ⟶ Y` are those of the total algebra. -/
@[simp]
theorem homInclusion_m_homAlgebra (X Y : C) (n : ℕ) (x : Fin n → homModule (R := R) X Y) :
    homInclusion X Y ((𝒞.homAlgebra X Y).m n x) = 𝒞.m n fun i ↦ homInclusion X Y (x i) :=
  AInfinityAlgebra.map_m_comap ..

/-- The unary operation of the sub-`A∞` algebra of morphisms `X ⟶ Y` is the Hom differential. -/
@[simp]
theorem homAlgebra_differential (X Y : C) :
    (𝒞.homAlgebra X Y).differential = 𝒞.homDifferential X Y := by
  ext f
  apply homInclusion_injective X Y
  rw [homInclusion_homDifferential, AInfinityAlgebra.differential_apply,
    AInfinityAlgebra.differential_apply, homInclusion_m_homAlgebra]
  congr 1
  funext i
  fin_cases i
  rfl

/-- The unary operation of the sub-`A∞` algebra of morphisms `X ⟶ Y` is the Hom differential,
evaluated at a morphism. -/
theorem homAlgebra_differential_apply (X Y : C) (f : homModule (R := R) X Y) :
    (𝒞.homAlgebra X Y).differential f = 𝒞.homDifferential X Y f := by
  rw [homAlgebra_differential]

/-- A morphism is a cycle of the sub-`A∞` algebra of morphisms exactly when it is closed. -/
theorem mem_homAlgebra_cycles {X Y : C} {f : homModule (R := R) X Y} :
    f ∈ (𝒞.homAlgebra X Y).cycles ↔ 𝒞.homDifferential X Y f = 0 := by
  rw [AInfinityAlgebra.cycles_def, homAlgebra_differential, LinearMap.mem_ker]

/-- The boundaries of the sub-`A∞` algebra of morphisms are the exact morphisms. -/
theorem homAlgebra_boundaries (X Y : C) :
    (𝒞.homAlgebra X Y).boundaries = LinearMap.range (𝒞.homDifferential X Y) := by
  rw [AInfinityAlgebra.boundaries_def, homAlgebra_differential]

/-- The cycles of the sub-`A∞` algebra of morphisms are the kernel of the Hom differential. -/
theorem homAlgebra_cycles (X Y : C) :
    (𝒞.homAlgebra X Y).cycles = LinearMap.ker (𝒞.homDifferential X Y) := by
  rw [AInfinityAlgebra.cycles_def, homAlgebra_differential]

/-- The cohomology of the sub-`A∞` algebra of morphisms `X ⟶ Y` is the cohomology
`ker m₁ ⧸ im m₁` of the Hom complex, the source of the maps induced by `A∞` functors on Hom
cohomology (`TauCeti.AInfinityFunctor.homCohomologyMap`). -/
noncomputable def homAlgebraCohomologyEquiv (X Y : C) :
    (𝒞.homAlgebra X Y).Cohomology ≃ₗ[R]
      (𝒞.homDifferential X Y).homology (𝒞.homDifferential_comp_homDifferential X Y) :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (𝒞.homAlgebra_cycles X Y)) <| by
    ext ⟨f, hf⟩
    rw [LinearMap.mem_boundariesInKer, Submodule.mem_map]
    constructor
    · rintro ⟨g, hg, hgf⟩
      rw [AInfinityAlgebra.mem_boundariesInCycles, homAlgebra_boundaries] at hg
      rwa [← congrArg Subtype.val hgf]
    · intro h
      refine ⟨⟨f, (𝒞.homAlgebra_cycles X Y).symm ▸ hf⟩, ?_, rfl⟩
      rwa [AInfinityAlgebra.mem_boundariesInCycles, homAlgebra_boundaries]

/-- The comparison of Hom cohomologies sends the class of a closed morphism to its class. -/
@[simp]
theorem homAlgebraCohomologyEquiv_cohomologyClass {X Y : C} {f : homModule (R := R) X Y}
    (hf : f ∈ (𝒞.homAlgebra X Y).cycles) :
    𝒞.homAlgebraCohomologyEquiv X Y ((𝒞.homAlgebra X Y).cohomologyClass hf) =
      Submodule.Quotient.mk ⟨f, 𝒞.homAlgebra_cycles X Y ▸ hf⟩ := by
  rw [AInfinityAlgebra.cohomologyClass_eq_mk, homAlgebraCohomologyEquiv,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  -- `LinearEquiv.ofEq` keeps the underlying morphism and only changes the membership proof.
  rfl

/-- The composite of two cycles of the sub-`A∞` algebras of morphisms is a cycle. -/
theorem comp_mem_homAlgebra_cycles {X Y Z : C} {g : homModule (R := R) Y Z}
    {f : homModule (R := R) X Y} (hg : g ∈ (𝒞.homAlgebra Y Z).cycles)
    (hf : f ∈ (𝒞.homAlgebra X Y).cycles) : 𝒞.comp X Y Z g f ∈ (𝒞.homAlgebra X Z).cycles := by
  rw [mem_homAlgebra_cycles] at hg hf ⊢
  exact 𝒞.homDifferential_comp_eq_zero hg hf

/-- The class of the composite of two cycles depends only on the classes of the factors. -/
theorem cohomologyClass_comp_congr {X Y Z : C} {g g' : homModule (R := R) Y Z}
    {f f' : homModule (R := R) X Y} (hg : g ∈ (𝒞.homAlgebra Y Z).cycles)
    (hf : f ∈ (𝒞.homAlgebra X Y).cycles) (hg' : g' ∈ (𝒞.homAlgebra Y Z).cycles)
    (hf' : f' ∈ (𝒞.homAlgebra X Y).cycles)
    (hgg : (𝒞.homAlgebra Y Z).cohomologyClass hg = (𝒞.homAlgebra Y Z).cohomologyClass hg')
    (hff : (𝒞.homAlgebra X Y).cohomologyClass hf = (𝒞.homAlgebra X Y).cohomologyClass hf') :
    (𝒞.homAlgebra X Z).cohomologyClass (𝒞.comp_mem_homAlgebra_cycles hg hf) =
      (𝒞.homAlgebra X Z).cohomologyClass (𝒞.comp_mem_homAlgebra_cycles hg' hf') := by
  rw [AInfinityAlgebra.cohomologyClass_eq_iff, homAlgebra_boundaries] at hgg hff ⊢
  rw [mem_homAlgebra_cycles] at hg hf hg' hf'
  have e : 𝒞.comp X Y Z g f - 𝒞.comp X Y Z g' f' =
      𝒞.comp X Y Z (g - g') f + 𝒞.comp X Y Z g' (f - f') := by
    simp only [map_sub, LinearMap.sub_apply]
    abel
  rw [e]
  exact add_mem (𝒞.comp_mem_range_homDifferential_of_left hgg hf)
    (𝒞.comp_mem_range_homDifferential_of_right hg' hff)

/-! ### The cohomology quiver -/

/-- The objects of the **cohomology quiver** of an `A∞` category `𝒞` on `C`: one object for each
object of `C`.  Its hom module from `X` to `Y` is the cohomology of the Hom complex of `𝒞` from
`X.obj` to `Y.obj`, with its grading by degree. -/
@[ext]
structure CohomologyQuiver (𝒞 : AInfinityCategory R C) where
  /-- The underlying object of `C`. -/
  obj : C

/-- The cohomology quiver of an `A∞` category is a graded linear quiver, with the cohomology of the
Hom complexes as its hom modules. -/
noncomputable instance : GradedLinearQuiver.{u, v, w} R 𝒞.CohomologyQuiver where
  homModule X Y := ModuleCat.of R (𝒞.homAlgebra X.obj Y.obj).Cohomology
  grading X Y := (𝒞.homAlgebra X.obj Y.obj).cohomologyGrading

/-- The hom module between two objects of the cohomology quiver is the cohomology of the Hom
complex between the underlying objects. -/
theorem homModule_cohomologyQuiver (X Y : 𝒞.CohomologyQuiver) :
    homModule (R := R) X Y = ModuleCat.of R (𝒞.homAlgebra X.obj Y.obj).Cohomology := (rfl)

/-- The grading of the hom module between two objects of the cohomology quiver is the grading of
the cohomology by degree. -/
theorem grading_cohomologyQuiver (X Y : 𝒞.CohomologyQuiver) :
    grading (R := R) X Y = (𝒞.homAlgebra X.obj Y.obj).cohomologyGrading := (rfl)

/-- The objects of the cohomology quiver are the objects of `C`. -/
def cohomologyQuiverEquiv : 𝒞.CohomologyQuiver ≃ C where
  toFun X := X.obj
  invFun X := ⟨X⟩

/-- The identification of objects sends an object of the cohomology quiver to its underlying
object. -/
@[simp]
theorem cohomologyQuiverEquiv_apply (X : 𝒞.CohomologyQuiver) : 𝒞.cohomologyQuiverEquiv X = X.obj :=
  (rfl)

/-- The inverse identification of objects sends an object of `C` to the corresponding object of
the cohomology quiver. -/
@[simp]
theorem cohomologyQuiverEquiv_symm_apply (X : C) : 𝒞.cohomologyQuiverEquiv.symm X = ⟨X⟩ :=
  (rfl)

end AInfinityCategory

end TauCeti
