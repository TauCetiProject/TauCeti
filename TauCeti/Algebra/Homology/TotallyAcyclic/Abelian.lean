/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import TauCeti.Algebra.Homology.Disk
public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Totally acyclic complexes and Gorenstein-projective objects in an abelian category

Let `C` be an abelian category. A cochain complex `P` in `C` is a **totally acyclic complex of
projectives** when its terms are projective, it is acyclic, and every chain map from `P` to a
projective object placed in some degree is null-homotopic. The last condition says that the
complex `Hom_C(P, Q)` is acyclic for every projective `Q`; equivalently, `P` is left orthogonal in
the homotopy category `K(C)` to the projective objects placed in any degree. An object is
**Gorenstein-projective** when it is isomorphic to the degree-zero cycles of such a complex.

As for Mathlib's `CochainComplex.IsKProjective`, the definition asks for null-homotopies of chain
maps, and the equivalent formulations are lemmas:

* `CochainComplex.isTotallyAcyclicProjective_iff_leftOrthogonal`: orthogonality in `K(C)` to
  `HomotopyCategory.singleProjectives C`;
* `CochainComplex.isTotallyAcyclicProjective_iff_factor`: the elementary form, every morphism
  `f : Pⁱ ⟶ Q` to a projective object which vanishes on the image of the differential into `Pⁱ`
  factors through the differential `Pⁱ ⟶ Pⁱ⁺¹`. It rests on
  `CochainComplex.nonempty_homotopy_mkHomToSingle_zero_iff`.

Taking `C` to be the category of all modules over a ring gives the Gorenstein-projective modules
of Enochs and Jenda. Taking `C = FGModuleCat A` for a left noetherian ring `A` gives the finitely
generated Gorenstein-projective modules: `FGModuleCat.isGorensteinProjective_iff`, in
`TauCeti/Algebra/Homology/TotallyAcyclic/FGModuleCat.lean`, identifies them with Tau Ceti's module
notion `TauCeti.IsGorensteinProjective`. That module notion also covers finitely generated modules
over rings which are not noetherian, where they need not form an abelian category.

## Main definitions

* `CochainComplex.IsTotallyAcyclicProjective`: totally acyclic complexes of projectives.
* `HomotopyCategory.singleProjectives C`: the projective objects placed in any degree, in `K(C)`.
* `CategoryTheory.isGorensteinProjective C`: the Gorenstein-projective objects of `C`.

## Main results

* `CochainComplex.IsTotallyAcyclicProjective.shift`: total acyclicity is stable under shifts.
* `CochainComplex.IsTotallyAcyclicProjective.isGorensteinProjective_cycles`: the cycles of a
  totally acyclic complex of projectives in any degree are Gorenstein-projective.
* `CategoryTheory.isGorensteinProjective_of_projective`: projective objects are
  Gorenstein-projective, through the disk `Q --𝟙--> Q` (`CochainComplex.disk`).

## References

* Edgar E. Enochs and Overtoun M. G. Jenda, *Relative Homological Algebra*, de Gruyter
  Expositions in Mathematics **30** (2000), Chapter 10.
* Xiao-Wu Chen, *Relative singularity categories and Gorenstein-projective modules*, Math. Nachr.
  **284** (2011), 199–212.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomotopyCategory

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- The projective objects of `C` placed in any single degree, as objects of the homotopy
category, up to isomorphism. -/
def singleProjectives : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  fun X ↦ ∃ (n : ℤ) (Q : C), Projective Q ∧ Nonempty (X ≅ (singleFunctor C n).obj Q)

variable {C} in
/-- The objects of `singleProjectives C` are the projective objects placed in a single degree, up
to isomorphism. -/
lemma singleProjectives_iff (X : HomotopyCategory C (.up ℤ)) :
    singleProjectives C X ↔
      ∃ (n : ℤ) (Q : C), Projective Q ∧ Nonempty (X ≅ (singleFunctor C n).obj Q) :=
  (Iff.rfl)

instance : (singleProjectives C).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨n, Q, hQ, ⟨e'⟩⟩ ↦ ⟨n, Q, hQ, ⟨e.symm ≪≫ e'⟩⟩

instance : (singleProjectives C).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun _ ⟨n, Q, hQ, ⟨e⟩⟩ ↦ ⟨n - a, Q, hQ,
    ⟨(shiftFunctor _ a).mapIso e ≪≫ ((singleFunctors C).shiftIso a (n - a) n (by lia)).app Q⟩⟩⟩

end HomotopyCategory

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A cochain complex `P` is a **totally acyclic complex of projectives** when its terms are
projective, it is acyclic, and every chain map from `P` to a projective object placed in a single
degree is null-homotopic; the last condition says that `Hom_C(P, Q)` is acyclic for every
projective `Q`. -/
structure IsTotallyAcyclicProjective (P : CochainComplex C ℤ) : Prop where
  /-- Every term is projective. -/
  projective (n : ℤ) : Projective (P.X n)
  /-- The complex is acyclic. -/
  acyclic : P.Acyclic
  /-- Every chain map to a projective object placed in a single degree is null-homotopic. -/
  nonempty_homotopy_zero (n : ℤ) (Q : C) [Projective Q]
    (f : P ⟶ (HomologicalComplex.single C (.up ℤ) n).obj Q) : Nonempty (Homotopy f 0)

variable {P : CochainComplex C ℤ}

/-- **Elementary form of total acyclicity**: a complex of projectives is totally acyclic if and
only if it is acyclic and every morphism `Pⁱ ⟶ Q` to a projective object which vanishes on the
image of `Pⁱ⁻¹ ⟶ Pⁱ` factors through `Pⁱ ⟶ Pⁱ⁺¹`. -/
lemma isTotallyAcyclicProjective_iff_factor :
    P.IsTotallyAcyclicProjective ↔ (∀ n, Projective (P.X n)) ∧ P.Acyclic ∧
      ∀ (i j : ℤ) (_ : i + 1 = j) (Q : C) [Projective Q] (φ : P.X i ⟶ Q),
        P.d (i - 1) i ≫ φ = 0 → ∃ g : P.X j ⟶ Q, P.d i j ≫ g = φ := by
  have hrel (i k : ℤ) (hk : (ComplexShape.up ℤ).Rel k i) : k = i - 1 := by
    simp only [ComplexShape.up_Rel] at hk
    lia
  constructor
  · intro hP
    refine ⟨hP.projective, hP.acyclic, fun i j hij Q _ φ hφ ↦ ?_⟩
    have hφ' : ∀ k, (ComplexShape.up ℤ).Rel k i → P.d k i ≫ φ = 0 := fun k hk ↦ by
      rw [hrel i k hk, hφ]
    exact (P.nonempty_homotopy_mkHomToSingle_zero_iff hij φ hφ').1
      (hP.nonempty_homotopy_zero i Q _)
  · rintro ⟨hproj, hac, h⟩
    refine ⟨hproj, hac, fun n Q _ f ↦ ?_⟩
    have hφ : ∀ k, (ComplexShape.up ℤ).Rel k n →
        P.d k n ≫ f.f n ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) n Q).hom = 0 := fun k hk ↦ by
      rw [← Category.assoc, ← f.comm, HomologicalComplex.single_obj_d, comp_zero, zero_comp]
    have hf : f = HomologicalComplex.mkHomToSingle _ hφ :=
      HomologicalComplex.to_single_hom_ext (by simp [HomologicalComplex.mkHomToSingle_f])
    rw [hf]
    exact (P.nonempty_homotopy_mkHomToSingle_zero_iff rfl _ hφ).2
      (h n (n + 1) rfl Q _ (by rw [hφ (n - 1) (by simp)]))

/-- **Total acyclicity as orthogonality**: a complex of projectives is totally acyclic if and only
if it is acyclic and left orthogonal, in the homotopy category, to the projective objects placed
in any degree. -/
lemma isTotallyAcyclicProjective_iff_leftOrthogonal :
    P.IsTotallyAcyclicProjective ↔ (∀ n, Projective (P.X n)) ∧ P.Acyclic ∧
      (HomotopyCategory.singleProjectives C).leftOrthogonal
        ((HomotopyCategory.quotient C (.up ℤ)).obj P) := by
  constructor
  · intro hP
    refine ⟨hP.projective, hP.acyclic, fun Y f ⟨n, Q, _, ⟨e⟩⟩ ↦ ?_⟩
    rw [← cancel_mono e.hom, zero_comp]
    obtain ⟨g, hg⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective (f ≫ e.hom)
    obtain ⟨h⟩ := hP.nonempty_homotopy_zero n Q g
    exact hg.symm.trans ((HomotopyCategory.eq_of_homotopy _ _ h).trans (Functor.map_zero _ _ _))
  · rintro ⟨hproj, hac, h⟩
    refine ⟨hproj, hac, fun n Q _ f ↦ ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
    rw [Functor.map_zero]
    exact h ((HomotopyCategory.quotient C (.up ℤ)).map f) ⟨n, Q, inferInstance, ⟨Iso.refl _⟩⟩

namespace IsTotallyAcyclicProjective

variable (hP : P.IsTotallyAcyclicProjective)
include hP

/-- Total acyclicity is invariant under isomorphisms of complexes. -/
lemma of_iso {P' : CochainComplex C ℤ} (e : P ≅ P') : P'.IsTotallyAcyclicProjective := by
  obtain ⟨hproj, hac, h⟩ := isTotallyAcyclicProjective_iff_leftOrthogonal.1 hP
  refine isTotallyAcyclicProjective_iff_leftOrthogonal.2 ⟨fun n ↦ ?_, ?_, ?_⟩
  · exact Projective.of_iso ((HomologicalComplex.eval C _ n).mapIso e) (hproj n)
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hac ⊢
    exact (HomotopyCategory.subcategoryAcyclic C).prop_of_iso
      ((HomotopyCategory.quotient C _).mapIso e) hac
  · exact ObjectProperty.prop_of_iso _ ((HomotopyCategory.quotient C _).mapIso e) h

/-- Total acyclicity is stable under shifts. -/
lemma shift (n : ℤ) : (P⟦n⟧).IsTotallyAcyclicProjective := by
  obtain ⟨hproj, hac, h⟩ := isTotallyAcyclicProjective_iff_leftOrthogonal.1 hP
  let e := ((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).symm.app P
  refine isTotallyAcyclicProjective_iff_leftOrthogonal.2 ⟨fun k ↦ hproj (k + n), ?_, ?_⟩
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hac ⊢
    exact (HomotopyCategory.subcategoryAcyclic C).prop_of_iso e
      ((HomotopyCategory.subcategoryAcyclic C).le_shift n _ hac)
  · exact ObjectProperty.prop_of_iso _ e
      ((HomotopyCategory.singleProjectives C).leftOrthogonal.le_shift n _ h)

end IsTotallyAcyclicProjective

end CochainComplex

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- An object of `C` is **Gorenstein-projective** when it is isomorphic to the degree-zero cycles
of a totally acyclic complex of projectives, a *complete resolution* of the object. -/
def isGorensteinProjective : ObjectProperty C :=
  fun M ↦ ∃ P : CochainComplex C ℤ, P.IsTotallyAcyclicProjective ∧ Nonempty (P.cycles 0 ≅ M)

variable {C}

/-- The defining property of a Gorenstein-projective object: it has a complete resolution. -/
lemma isGorensteinProjective_iff (M : C) :
    isGorensteinProjective C M ↔
      ∃ P : CochainComplex C ℤ, P.IsTotallyAcyclicProjective ∧ Nonempty (P.cycles 0 ≅ M) :=
  Iff.rfl

instance : (isGorensteinProjective C).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨P, hP, ⟨e'⟩⟩ ↦ ⟨P, hP, ⟨e' ≪≫ e⟩⟩

section Disk

open CochainComplex

variable (Q : C)

/-- The disk `Q --𝟙--> Q` of a projective object is a totally acyclic complex of projectives. -/
lemma isTotallyAcyclicProjective_disk [Projective Q] : (disk Q).IsTotallyAcyclicProjective := by
  refine isTotallyAcyclicProjective_iff_factor.2 ⟨projective_disk_X Q, acyclic_disk Q,
    fun i j hij Q' _ φ hφ ↦ ?_⟩
  by_cases h₀ : i = -1
  · subst h₀
    obtain rfl : j = 0 := by lia
    exact ⟨inv ((disk Q).d (-1) 0) ≫ φ, by simp⟩
  -- Otherwise `φ` vanishes: in degree `0` it is killed by the isomorphism `d : Q⁻¹ ⟶ Q⁰`.
  refine ⟨0, ?_⟩
  rw [comp_zero]
  by_cases h₁ : i = 0
  · subst h₁
    rw [zero_sub] at hφ
    rw [← cancel_epi ((disk Q).d (-1) 0), hφ, comp_zero]
  exact (isZero_disk_X Q i h₀ h₁).eq_of_src _ _

/-- **Projective objects are Gorenstein-projective**: the complex `Q --𝟙--> Q`, concentrated in
degrees `-1` and `0`, is a complete resolution of a projective object `Q`. -/
theorem isGorensteinProjective_of_projective [Projective Q] : isGorensteinProjective C Q :=
  ⟨disk Q, isTotallyAcyclicProjective_disk Q, ⟨diskCyclesIso Q⟩⟩

end Disk

end CategoryTheory

namespace CochainComplex.IsTotallyAcyclicProjective

variable {C : Type u} [Category.{v} C] [Abelian C] {P : CochainComplex C ℤ}

/-- **The cycles of a totally acyclic complex of projectives are Gorenstein-projective**, in every
degree. -/
theorem isGorensteinProjective_cycles (hP : P.IsTotallyAcyclicProjective) (n : ℤ) :
    isGorensteinProjective C (P.cycles n) :=
  ⟨P⟦n⟧, hP.shift n, ⟨P.shiftCyclesIso n 0 n (add_zero n)⟩⟩

end CochainComplex.IsTotallyAcyclicProjective
