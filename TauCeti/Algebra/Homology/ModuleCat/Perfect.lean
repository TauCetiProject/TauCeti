/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.KProjective
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Perfect complexes of modules

An object of the unbounded derived category of left modules is perfect if it has a bounded
representative consisting of finitely generated projective modules. The ring need not be
commutative. In particular, finite projective modules in any degree are perfect; one does not
require a finite free representative.

Perfectness is invariant under isomorphisms and shifts and satisfies two out of three in
distinguished triangles. To construct the third finite model, a derived morphism between two
bounded projective models is represented by a chain map, whose mapping cone again has finite
projective terms. This is the elementary finite-model input to lifting and inverse-system
arguments for perfect complexes.

## References

* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657), for the definition.
* [Stacks Project, Tag 066R](https://stacks.math.columbia.edu/tag/066R), for triangle closure.

The cone construction and the passage from derived morphisms to chain maps use Mathlib's
mapping cone and Joël Riou's K-projective comparison.
-/

public section

noncomputable section

open CategoryTheory Limits Pretriangulated DerivedCategory

universe w v u

namespace TauCeti.DerivedDeRham

variable (A : Type u) [Ring A] [HasDerivedCategory.{w} (ModuleCat.{v} A)]

/-- A perfect object of the derived category of left `A`-modules has a bounded representative
whose terms are finitely generated projective modules. -/
def IsPerfect (K : DerivedCategory (ModuleCat.{v} A)) : Prop :=
  ∃ P : CochainComplex (ModuleCat.{v} A) ℤ, CochainComplex.bounded _ P ∧
    (∀ i, Module.Finite A (P.X i)) ∧ (∀ i, Module.Projective A (P.X i)) ∧
    Nonempty (Q.obj P ≅ K)

end TauCeti.DerivedDeRham

namespace DerivedCategory

open TauCeti.DerivedDeRham

variable {A : Type u} [Ring A] [HasDerivedCategory.{w} (ModuleCat.{v} A)]

/-- The finite-model characterization of perfectness. -/
theorem isPerfect_iff (K : DerivedCategory (ModuleCat.{v} A)) :
    IsPerfect A K ↔
      ∃ (P : CochainComplex (ModuleCat.{v} A) ℤ) (a b : ℤ),
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
        (∀ i, Module.Finite A (P.X i)) ∧ (∀ i, Module.Projective A (P.X i)) ∧
        Nonempty (Q.obj P ≅ K) := by
  simp only [IsPerfect, CochainComplex.bounded_iff]
  aesop

end DerivedCategory

namespace TauCeti.DerivedDeRham

variable {A : Type u} [Ring A] [HasDerivedCategory.{w} (ModuleCat.{v} A)]

namespace IsPerfect

variable {K L : DerivedCategory (ModuleCat.{v} A)}

/-- Perfectness is invariant under isomorphism in the derived category. -/
theorem of_iso (hK : IsPerfect A K) (e : K ≅ L) : IsPerfect A L := by
  obtain ⟨P, hP, hf, hp, ⟨eP⟩⟩ := hK
  exact ⟨P, hP, hf, hp, ⟨eP ≪≫ e⟩⟩

end IsPerfect

instance : ObjectProperty.IsClosedUnderIsomorphisms (IsPerfect A) where
  of_iso e h := h.of_iso e

end TauCeti.DerivedDeRham

namespace CochainComplex

open TauCeti.DerivedDeRham

variable {A : Type u} [Ring A] [HasDerivedCategory.{w} (ModuleCat.{v} A)]

/-- The derived object of a bounded complex of finite projective modules is perfect. -/
theorem isPerfect_Q_obj (P : CochainComplex (ModuleCat.{v} A) ℤ)
    (hP : CochainComplex.bounded _ P) [∀ i, Module.Finite A (P.X i)]
    [∀ i, Module.Projective A (P.X i)] : IsPerfect A (Q.obj P) :=
  ⟨P, hP, fun _ ↦ inferInstance, fun _ ↦ inferInstance, ⟨Iso.refl _⟩⟩

end CochainComplex

namespace ModuleCat

open TauCeti.DerivedDeRham

variable {A : Type u} [Ring A] [HasDerivedCategory.{w} (ModuleCat.{v} A)]

/-- A finite projective module placed in any integer degree is perfect. -/
theorem isPerfect_single (M : ModuleCat.{v} A) [Module.Finite A M] [Module.Projective A M]
    (n : ℤ) : IsPerfect A ((singleFunctor (ModuleCat A) n).obj M) := by
  let P := (HomologicalComplex.single (ModuleCat A) (.up ℤ) n).obj M
  have hterm (i : ℤ) : Module.Finite A (P.X i) ∧ Module.Projective A (P.X i) := by
    by_cases hi : i = n
    · subst i
      let e := (HomologicalComplex.singleObjXSelf (.up ℤ) n M).toLinearEquiv
      exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩
    · have := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) n M i hi)
      exact ⟨inferInstance, inferInstance⟩
  exact ⟨P, (CochainComplex.bounded_iff _ _).2 ⟨n, n, inferInstance, inferInstance⟩,
    fun i ↦ (hterm i).1,
    fun i ↦ (hterm i).2, ⟨(singleFunctorIsoCompQ (ModuleCat A) n).symm.app M⟩⟩

end ModuleCat

namespace TauCeti.DerivedDeRham.IsPerfect

variable {A : Type u} [Ring A] [HasDerivedCategory.{w} (ModuleCat.{v} A)]

/-- Every shift of a perfect complex is perfect. -/
theorem shift {K : DerivedCategory (ModuleCat.{v} A)} (hK : IsPerfect A K) (n : ℤ) :
    IsPerfect A (K⟦n⟧) := by
  obtain ⟨P, hP, hf, hp, ⟨e⟩⟩ := hK
  refine ⟨P⟦n⟧, (CochainComplex.bounded _).le_shift n P hP, ?_, ?_,
    ⟨(Q.commShiftIso n).app P ≪≫ (shiftFunctor _ n).mapIso e⟩⟩
  · intro i
    have := hf (i + n)
    exact Module.Finite.equiv (P.shiftFunctorObjXIso n i (i + n) rfl).toLinearEquiv.symm
  · intro i
    have := hp (i + n)
    exact Module.Projective.of_equiv
      (P.shiftFunctorObjXIso n i (i + n) rfl).toLinearEquiv.symm

end TauCeti.DerivedDeRham.IsPerfect

namespace DerivedCategory

open TauCeti.DerivedDeRham

variable {A : Type u} [Ring A] [HasDerivedCategory.{w} (ModuleCat.{v} A)]

/-- Shifting neither creates nor destroys perfectness. -/
@[simp]
theorem isPerfect_shift_iff (K : DerivedCategory (ModuleCat.{v} A)) (n : ℤ) :
    IsPerfect A (K⟦n⟧) ↔ IsPerfect A K :=
  ⟨fun h ↦ (h.shift (-n)).of_iso ((shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).app K),
    fun h ↦ h.shift n⟩

end DerivedCategory

namespace TauCeti.DerivedDeRham

variable {A : Type u} [Ring A] [HasDerivedCategory.{w} (ModuleCat.{v} A)]

instance : ObjectProperty.IsStableUnderShift (IsPerfect A) ℤ where
  isStableUnderShiftBy n := ⟨fun _ h ↦ h.shift n⟩

/-- Perfect complexes are closed under the third vertex of a distinguished triangle. -/
instance : ObjectProperty.IsTriangulatedClosed₃ (IsPerfect A) :=
  ObjectProperty.IsTriangulatedClosed₃.mk' <| by
    intro T hT h₁ h₂
    obtain ⟨P, hP, hfP, hpP, ⟨eP⟩⟩ := h₁
    obtain ⟨S, hS, hfS, hpS, ⟨eS⟩⟩ := h₂
    have := hfP
    have := hfS
    have := hpP
    have := hpS
    obtain ⟨_, b, _, hb⟩ := (CochainComplex.bounded_iff _ _).1 hP
    have (i : ℤ) : Projective (P.X i) := inferInstance
    have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
    obtain ⟨f, hf⟩ := CochainComplex.IsKProjective.Q_map_surjective P S
      (eP.hom ≫ T.mor₁ ≫ eS.inv)
    obtain ⟨e, -, -⟩ := exists_iso_of_arrow_iso _ _
      (mappingCone_triangle_distinguished f) hT
      (Arrow.isoMk eP eS (by simp [hf]))
    have hterm (i : ℤ) :
        Module.Finite A ((CochainComplex.mappingCone f).X i) ∧
          Module.Projective A ((CochainComplex.mappingCone f).X i) := by
      let e := (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl) ≪≫
        ModuleCat.biprodIsoProd (P.X (i + 1)) (S.X i)
      exact ⟨Module.Finite.equiv e.toLinearEquiv.symm,
        Module.Projective.of_equiv e.toLinearEquiv.symm⟩
    exact ⟨CochainComplex.mappingCone f, CochainComplex.bounded_mappingCone f hP hS,
      fun i ↦ (hterm i).1, fun i ↦ (hterm i).2, ⟨Triangle.π₃.mapIso e⟩⟩

/-- The zero derived object is perfect. -/
instance : ObjectProperty.ContainsZero (IsPerfect A) := by
  let M : ModuleCat.{v} A := ModuleCat.of A PUnit
  have hM : IsZero M := ModuleCat.isZero_of_subsingleton _
  exact ⟨⟨_, (singleFunctor (ModuleCat A) 0).map_isZero hM, ModuleCat.isPerfect_single M 0⟩⟩

/-- Perfect complexes form a triangulated subcategory, giving two out of three for every
vertex of a distinguished triangle. This does not assert closure under arbitrary retracts. -/
instance : ObjectProperty.IsTriangulated (IsPerfect A) where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

end TauCeti.DerivedDeRham
