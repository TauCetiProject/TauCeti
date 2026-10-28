/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
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
  factors through the differential `Pⁱ ⟶ Pⁱ⁺¹`.

Taking `C` to be the category of all modules over a ring gives the Gorenstein-projective modules
of Enochs and Jenda. For finitely generated modules over a ring which is not necessarily
noetherian, Tau Ceti has the separate notion `CochainComplex.IsTotallyAcyclic`.

## Main definitions

* `CochainComplex.IsTotallyAcyclicProjective`: totally acyclic complexes of projectives.
* `CategoryTheory.isGorensteinProjective C`: the Gorenstein-projective objects of `C`.

## Main results

* `CochainComplex.nonempty_homotopy_mkHomToSingle_zero_iff`: a chain map from a complex to an
  object placed in degree `i`, given by `φ : Kⁱ ⟶ A`, is null-homotopic if and only if `φ`
  factors through the differential `Kⁱ ⟶ Kⁱ⁺¹`.
* `CochainComplex.IsTotallyAcyclicProjective.shift`: total acyclicity is stable under shifts.
* `CochainComplex.IsTotallyAcyclicProjective.isGorensteinProjective_cycles`: the cycles of a
  totally acyclic complex of projectives in any degree are Gorenstein-projective.
* `CategoryTheory.isGorensteinProjective_of_projective`: projective objects are
  Gorenstein-projective.

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

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The projective objects of `C` placed in any single degree, as objects of the homotopy
category, up to isomorphism. -/
def singleProjectives : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  fun X ↦ ∃ (n : ℤ) (Q : C), Projective Q ∧ Nonempty (X ≅ (singleFunctor C n).obj Q)

instance : (singleProjectives C).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨n, Q, hQ, ⟨e'⟩⟩ ↦ ⟨n, Q, hQ, ⟨e.symm ≪≫ e'⟩⟩

instance : (singleProjectives C).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun _ ⟨n, Q, hQ, ⟨e⟩⟩ ↦ ⟨n - a, Q, hQ,
    ⟨(shiftFunctor _ a).mapIso e ≪≫ ((singleFunctors C).shiftIso a (n - a) n (by lia)).app Q⟩⟩⟩

end HomotopyCategory

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Null-homotopic chain maps to an object in one degree**: the chain map from `K` to `A`
placed in degree `i` given by `φ : Kⁱ ⟶ A` is null-homotopic if and only if `φ` factors through
the differential `Kⁱ ⟶ Kʲ`, where `j = i + 1`. -/
lemma nonempty_homotopy_mkHomToSingle_zero_iff (K : CochainComplex C ℤ) {i j : ℤ}
    (hij : i + 1 = j) {A : C} (φ : K.X i ⟶ A)
    (hφ : ∀ k, (ComplexShape.up ℤ).Rel k i → K.d k i ≫ φ = 0) :
    Nonempty (Homotopy (HomologicalComplex.mkHomToSingle φ hφ) 0) ↔
      ∃ g : K.X j ⟶ A, K.d i j ≫ g = φ := by
  subst hij
  constructor
  · rintro ⟨h⟩
    refine ⟨h.hom (i + 1) i ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) i A).hom, ?_⟩
    have := h.comm i
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp),
      HomologicalComplex.single_obj_d, comp_zero, add_zero, HomologicalComplex.zero_f, add_zero,
      HomologicalComplex.mkHomToSingle_f] at this
    rw [← Category.assoc, ← this, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rintro ⟨g, hg⟩
    refine ⟨{
      hom := fun p q ↦ if h : p = i + 1 ∧ q = i then
        (K.XIsoOfEq h.1).hom ≫ g ≫ (HomologicalComplex.singleObjXIsoOfEq _ i A q h.2).inv
        else 0
      zero := fun p q hpq ↦ dite_eq_right (by rintro ⟨rfl, rfl⟩; exact hpq rfl)
      comm := fun p ↦ ?_ }⟩
    by_cases hp : p = i
    · subst hp
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (p - 1) p by simp),
        HomologicalComplex.single_obj_d, comp_zero, add_zero, HomologicalComplex.zero_f, add_zero,
        HomologicalComplex.mkHomToSingle_f, dite_eq_left ⟨rfl, rfl⟩, ← hg]
      simp [HomologicalComplex.singleObjXSelf]
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_tgt _ _

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

variable (Q : C)

/-- The relation `-1 → 0` in the shape of cochain complexes. -/
private lemma rel_neg_one_zero : (ComplexShape.up ℤ).Rel (-1) 0 := by simp

/-- The complex `Q --𝟙--> Q` concentrated in degrees `-1` and `0`. -/
private noncomputable abbrev disk : CochainComplex C ℤ :=
  HomologicalComplex.double (𝟙 Q) rel_neg_one_zero

private lemma isIso_disk_d : IsIso ((disk Q).d (-1) 0) := by
  rw [HomologicalComplex.double_d _ _ (by decide)]
  infer_instance

private lemma disk_d_eq_zero (j k : ℤ) (hj : j ≠ -1) : (disk Q).d j k = 0 :=
  HomologicalComplex.double_d_eq_zero₀ _ _ _ _ hj

private lemma isZero_disk_X (n : ℤ) (h₀ : n ≠ -1) (h₁ : n ≠ 0) : IsZero ((disk Q).X n) :=
  HomologicalComplex.isZero_double_X _ _ _ h₀ h₁

private lemma isTotallyAcyclicProjective_disk [Projective Q] :
    (disk Q).IsTotallyAcyclicProjective := by
  have := isIso_disk_d Q
  refine CochainComplex.isTotallyAcyclicProjective_iff_factor.2 ⟨fun n ↦ ?_, fun n ↦ ?_,
    fun i j hij Q' _ φ hφ ↦ ?_⟩
  · by_cases h₀ : n = -1
    · subst h₀
      exact Projective.of_iso (HomologicalComplex.doubleXIso₀ (𝟙 Q) rel_neg_one_zero).symm
        inferInstance
    by_cases h₁ : n = 0
    · subst h₁
      exact Projective.of_iso
        (HomologicalComplex.doubleXIso₁ (𝟙 Q) rel_neg_one_zero (by decide)).symm inferInstance
    exact (isZero_disk_X Q n h₀ h₁).projective
  · by_cases h₀ : n = -1
    · subst h₀
      rw [HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp),
        ShortComplex.exact_iff_mono _ (disk_d_eq_zero Q _ _ (by decide))]
      exact inferInstanceAs (Mono ((disk Q).d (-1) 0))
    by_cases h₁ : n = 0
    · subst h₁
      rw [HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp),
        ShortComplex.exact_iff_epi _ (disk_d_eq_zero Q _ _ (by decide))]
      exact inferInstanceAs (Epi ((disk Q).d (-1) 0))
    exact HomologicalComplex.ExactAt.of_isZero (isZero_disk_X Q n h₀ h₁)
  · by_cases h₀ : i = -1
    · subst h₀
      obtain rfl : j = 0 := by lia
      exact ⟨inv ((disk Q).d (-1) 0) ≫ φ, by simp⟩
    refine ⟨0, ?_⟩
    rw [comp_zero]
    by_cases h₁ : i = 0
    · subst h₁
      rw [← cancel_epi ((disk Q).d (-1) 0), comp_zero, show (0 : ℤ) - 1 = -1 by simp] at *
      exact hφ.symm
    exact (isZero_disk_X Q i h₀ h₁).eq_of_src _ _

/-- **Projective objects are Gorenstein-projective**: the complex `Q --𝟙--> Q`, concentrated in
degrees `-1` and `0`, is a complete resolution of a projective object `Q`. -/
theorem isGorensteinProjective_of_projective [Projective Q] : isGorensteinProjective C Q :=
  ⟨disk Q, isTotallyAcyclicProjective_disk Q, ⟨(disk Q).iCyclesIso 0 1 (by simp)
    (disk_d_eq_zero Q _ _ (by decide)) ≪≫
      HomologicalComplex.doubleXIso₁ (𝟙 Q) rel_neg_one_zero (by decide)⟩⟩

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
