/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Abelian
public import TauCeti.CategoryTheory.GrothendieckGroup.Triangulated
public import TauCeti.Algebra.Homology.DerivedCategory.Bounded
public import TauCeti.CategoryTheory.GrothendieckGroup.BoundedHomotopy
public import TauCeti.CategoryTheory.GrothendieckGroup.EulerCharacteristic
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Abelian K₀ and the bounded derived category

For an essentially small abelian category `A` whose bounded derived category is essentially small,
this file proves that the canonical additive homomorphism

```text
K₀(A) ⟶ K₀(Dᵇ(A)),
```

sending `[X]` to the class of the complex with `X` in degree zero, is an isomorphism. A short exact
sequence in `A` gives a distinguished triangle between the corresponding degree-zero complexes, so
the map is well defined.

The inverse sends the class of a bounded complex `X` to the alternating sum `∑ n, (-1)ⁿ [Hⁿ X]` of
its cohomology classes. This is additive on distinguished triangles because the long exact
cohomology sequence of a triangle is cut into short exact pieces by the kernels of its maps, and
the resulting sum telescopes. It is a left inverse of the degree-zero map, and the degree-zero map
is surjective: every object of `Dᵇ(A)` is represented by a bounded complex, whose class is already
in the bounded homotopy category the alternating sum of the classes of its terms
(`TauCeti.TriangulatedK0.of_bounded_quotient_obj`).

## Main definitions

* `TauCeti.AbelianK0.toBoundedDerivedK0` is induced by the degree-zero embedding into the bounded
  derived category.
* `TauCeti.AbelianK0.boundedDerivedK0Equiv`: the isomorphism between abelian `K₀` and triangulated
  `K₀` of the bounded derived category.

## Main results

* `TauCeti.TriangulatedK0.of_singleFunctor_shortExact` is the triangulated `K₀` relation between
  the degree-zero objects of a short exact sequence.
* `TauCeti.AbelianK0.sum_negOnePow_of_homology_of_distTriang`: the alternating class of the
  cohomology is additive on distinguished triangles of the derived category.
* `TauCeti.AbelianK0.boundedDerivedK0Equiv_symm_of`: the inverse comparison is the alternating
  class of the cohomology.
* `TauCeti.TriangulatedK0.of_eq_sum_homology`: in triangulated `K₀` of the bounded derived
  category, the class of a bounded complex is the alternating sum of the classes of its cohomology
  objects placed in degree zero.

## Mathlib infrastructure

The degree-zero embedding `DerivedCategory.singleFunctor`, the distinguished triangle
`ShortComplex.ShortExact.singleTriangle`, the long exact cohomology sequence
`DerivedCategory.HomologySequence` and the representation of bounded objects by bounded complexes
`DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE` are from Mathlib's derived-category API.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Exercise 9.15, for the comparison between the Grothendieck group of an abelian category and that
  of its bounded derived category.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w w' w'' v u

variable {A : Type u} [Category.{v} A] [Abelian A] [EssentiallySmall.{w} A]
  [HasDerivedCategory.{w'} A] [EssentiallySmall.{w''} (DerivedCategory.Bounded A)]

namespace TriangulatedK0

omit [EssentiallySmall.{w} A] in
/-- A short exact sequence gives a distinguished triangle in the bounded derived category, so
its degree-zero objects satisfy the triangulated `K₀` relation. -/
theorem of_singleFunctor_shortExact {S : ShortComplex A} (hS : S.ShortExact) :
    of ((DerivedCategory.Bounded.singleFunctor A 0).obj S.X₂) =
      of ((DerivedCategory.Bounded.singleFunctor A 0).obj S.X₁) +
        of ((DerivedCategory.Bounded.singleFunctor A 0).obj S.X₃) := by
  simpa using of_distTriang hS.boundedSingleTriangle_distinguished

end TriangulatedK0

namespace AbelianK0

/-- The canonical homomorphism from abelian `K₀` to the triangulated `K₀` of the bounded derived
category. It sends the class of an object to the class of the complex concentrated in degree
zero. -/
noncomputable def toBoundedDerivedK0 : AbelianK0 A →+ TriangulatedK0 (DerivedCategory.Bounded A) :=
  lift
    { obj := fun X ↦ TriangulatedK0.of ((DerivedCategory.Bounded.singleFunctor A 0).obj X)
      map_iso := fun _ _ e ↦ TriangulatedK0.of_congr
        ((DerivedCategory.Bounded.singleFunctor A 0).mapIso e)
      map_shortExact := fun _ hS ↦ TriangulatedK0.of_singleFunctor_shortExact hS }

/-- The canonical map to derived `K₀` sends an object class to the class of its degree-zero
complex. -/
@[simp] theorem toBoundedDerivedK0_of (X : A) :
    toBoundedDerivedK0 (of X) =
      TriangulatedK0.of ((DerivedCategory.Bounded.singleFunctor A 0).obj X) :=
  lift_of _ X

/-! ### The alternating class of the cohomology -/

open _root_.DerivedCategory (homologyFunctor)

omit [EssentiallySmall.{w''} (DerivedCategory.Bounded A)] in
/-- Enlarging a finite range of degrees beyond the cohomological support of an object of the
derived category does not change the alternating class of its cohomology. -/
private lemma sum_negOnePow_of_homology_eq_of_isZero (X : DerivedCategory A) {s t : Finset ℤ}
    (hs : ∀ n ∉ s, IsZero ((homologyFunctor A n).obj X))
    (ht : ∀ n ∉ t, IsZero ((homologyFunctor A n).obj X)) :
    ∑ n ∈ s, (n.negOnePow : ℤ) • of ((homologyFunctor A n).obj X) =
      ∑ n ∈ t, (n.negOnePow : ℤ) • of ((homologyFunctor A n).obj X) := by
  have key : ∀ u : Finset ℤ, u ⊆ s ∪ t → (∀ n ∉ u, IsZero ((homologyFunctor A n).obj X)) →
      ∑ n ∈ u, (n.negOnePow : ℤ) • of ((homologyFunctor A n).obj X) =
        ∑ n ∈ s ∪ t, (n.negOnePow : ℤ) • of ((homologyFunctor A n).obj X) := fun u hu hu' ↦
    Finset.sum_subset hu fun n _ hn ↦ by rw [of_eq_zero_of_isZero (hu' n hn), smul_zero]
  rw [key s Finset.subset_union_left hs, key t Finset.subset_union_right ht]

/-- An alternating sum of consecutive pairs telescopes to its two end terms. -/
private lemma sum_Icc_negOnePow_smul_add {G : Type*} [AddCommGroup G] (f : ℤ → G) (a b : ℤ)
    (hab : a ≤ b) :
    ∑ n ∈ Finset.Icc a b, (n.negOnePow : ℤ) • (f n + f (n + 1)) =
      (a.negOnePow : ℤ) • f a + (b.negOnePow : ℤ) • f (b + 1) := by
  induction b, hab using Int.leInduction with
  | base => simp [smul_add]
  | succ b hb ih =>
    have hins : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by simp), ih, Int.negOnePow_succ]
    simp only [Units.val_neg, neg_smul, smul_add]
    abel

omit [HasDerivedCategory.{w'} A] [EssentiallySmall.{w''} (DerivedCategory.Bounded A)] in
/-- In an exact sequence `X₁ ⟶ X₂ ⟶ X₃`, the class of `X₁` is the sum of the classes of the two
kernels. -/
private lemma of_kernel_add_of_kernel_of_exact {S : ShortComplex A} (hS : S.Exact) :
    (of (kernel S.g) : AbelianK0 A) + of (kernel S.f) = of S.X₁ := by
  rw [of_kernel_add_of_kernel, of_eq_zero_of_isZero (S.exact_iff_isZero_homology.1 hS), zero_add]

omit [EssentiallySmall.{w''} (DerivedCategory.Bounded A)] in
/-- The degree-`n` relation behind additivity on a distinguished triangle: cutting the long exact
cohomology sequence at the kernels of `Hⁿ(T.mor₁)` and `Hⁿ⁺¹(T.mor₁)`. -/
private lemma of_homology_obj₁_add_of_homology_obj₃ {T : Triangle (DerivedCategory A)}
    (hT : T ∈ distTriang _) (n : ℤ) :
    of ((homologyFunctor A n).obj T.obj₁) + of ((homologyFunctor A n).obj T.obj₃) =
      of ((homologyFunctor A n).obj T.obj₂) +
        (of (kernel ((homologyFunctor A n).map T.mor₁)) +
          of (kernel ((homologyFunctor A (n + 1)).map T.mor₁))) := by
  have h₁ := of_kernel_add_of_kernel_of_exact (DerivedCategory.HomologySequence.exact₂ T hT n)
  have h₂ := of_kernel_add_of_kernel_of_exact
    (DerivedCategory.HomologySequence.exact₃ T hT n (n + 1))
  have h₃ := of_kernel_add_of_kernel_of_exact
    (DerivedCategory.HomologySequence.exact₁ T hT n (n + 1))
  dsimp only at h₁ h₂ h₃
  rw [← h₁, ← h₂, ← h₃]
  abel

omit [EssentiallySmall.{w''} (DerivedCategory.Bounded A)] in
/-- **The alternating class of the cohomology is additive on distinguished triangles.** For a
distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` in the derived category and a finite set `s` of
degrees outside which the cohomology of `X` and `Z` vanishes,
`∑ n ∈ s, (-1)ⁿ [Hⁿ Y] = ∑ n ∈ s, (-1)ⁿ [Hⁿ X] + ∑ n ∈ s, (-1)ⁿ [Hⁿ Z]` in abelian `K₀`. -/
theorem sum_negOnePow_of_homology_of_distTriang {T : Triangle (DerivedCategory A)}
    (hT : T ∈ distTriang _) {s : Finset ℤ}
    (h₁ : ∀ n ∉ s, IsZero ((homologyFunctor A n).obj T.obj₁))
    (h₃ : ∀ n ∉ s, IsZero ((homologyFunctor A n).obj T.obj₃)) :
    ∑ n ∈ s, (n.negOnePow : ℤ) • of ((homologyFunctor A n).obj T.obj₂) =
      ∑ n ∈ s, (n.negOnePow : ℤ) • of ((homologyFunctor A n).obj T.obj₁) +
        ∑ n ∈ s, (n.negOnePow : ℤ) • of ((homologyFunctor A n).obj T.obj₃) := by
  have h₂ : ∀ n ∉ s, IsZero ((homologyFunctor A n).obj T.obj₂) := fun n hn ↦
    (DerivedCategory.HomologySequence.exact₂ T hT n).isZero_of_both_isZero (h₁ n hn) (h₃ n hn)
  -- Enclose `s` in an interval `[a, b]` whose end degrees `a` and `b + 1` lie outside `s`, so that
  -- the two end terms of the telescoping sum vanish.
  obtain ⟨M, hM⟩ := s.bddBelow
  obtain ⟨N, hN⟩ := s.bddAbove
  have hI : ∀ n ∉ Finset.Icc (M - 1) (max N (M - 1)), n ∉ s := fun n hn h ↦ hn <|
    Finset.mem_Icc.2 ⟨by linarith [hM h], le_max_of_le_left (hN h)⟩
  have hk : ∀ n ∉ s, IsZero (kernel ((homologyFunctor A n).map T.mor₁)) := fun n hn ↦
    IsZero.of_mono (kernel.ι _) (h₁ n hn)
  have ha : M - 1 ∉ s := fun h ↦ by linarith [hM h]
  have hb : max N (M - 1) + 1 ∉ s := fun h ↦ by linarith [hN h, le_max_left N (M - 1)]
  rw [sum_negOnePow_of_homology_eq_of_isZero _ h₁ fun n hn ↦ h₁ n (hI n hn),
    sum_negOnePow_of_homology_eq_of_isZero _ h₂ fun n hn ↦ h₂ n (hI n hn),
    sum_negOnePow_of_homology_eq_of_isZero _ h₃ fun n hn ↦ h₃ n (hI n hn),
    ← Finset.sum_add_distrib]
  have key : ∀ n : ℤ, (n.negOnePow : ℤ) • of ((homologyFunctor A n).obj T.obj₁) +
      (n.negOnePow : ℤ) • of ((homologyFunctor A n).obj T.obj₃) =
      (n.negOnePow : ℤ) • of ((homologyFunctor A n).obj T.obj₂) +
        (n.negOnePow : ℤ) • (of (kernel ((homologyFunctor A n).map T.mor₁)) +
          of (kernel ((homologyFunctor A (n + 1)).map T.mor₁))) := fun n ↦ by
    rw [← smul_add, ← smul_add, of_homology_obj₁_add_of_homology_obj₃ hT]
  rw [Finset.sum_congr rfl fun n _ ↦ key n, Finset.sum_add_distrib,
    sum_Icc_negOnePow_smul_add (fun n ↦ of (kernel ((homologyFunctor A n).map T.mor₁))) _ _
      (by omega),
    of_eq_zero_of_isZero (hk _ ha), of_eq_zero_of_isZero (hk _ hb)]
  simp

/-! ### The inverse comparison -/

omit [EssentiallySmall.{w} A] [EssentiallySmall.{w''} (DerivedCategory.Bounded A)] in
/-- An object of the bounded derived category has cohomology in only finitely many degrees. -/
private lemma exists_finset_isZero_homology (X : DerivedCategory.Bounded A) :
    ∃ s : Finset ℤ, ∀ n ∉ s, IsZero ((homologyFunctor A n).obj X.obj) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := X.property
  refine ⟨Finset.Icc a b, fun n hn ↦ ?_⟩
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  rcases hn with hn | hn
  · exact (X.obj.isGE_iff a).1 ha n hn
  · exact (X.obj.isLE_iff b).1 hb n hn

omit [EssentiallySmall.{w''} (DerivedCategory.Bounded A)] in
/-- The alternating class of the cohomology, as a triangle-additive invariant on the bounded
derived category. -/
private noncomputable def boundedDerivedHomologyEulerChar :
    TriangulatedK0.AdditiveInvariant (DerivedCategory.Bounded A) (AbelianK0 A) where
  obj X := ∑ n ∈ (exists_finset_isZero_homology X).choose,
    (n.negOnePow : ℤ) • of ((homologyFunctor A n).obj X.obj)
  map_iso X Y e := by
    let e' : X.obj ≅ Y.obj := DerivedCategory.Bounded.ι.mapIso e
    rw [sum_negOnePow_of_homology_eq_of_isZero X.obj (exists_finset_isZero_homology X).choose_spec
      (t := (exists_finset_isZero_homology Y).choose) fun n hn ↦
        ((exists_finset_isZero_homology Y).choose_spec n hn).of_iso
          ((homologyFunctor A n).mapIso e')]
    exact Finset.sum_congr rfl fun n _ ↦ by rw [of_congr ((homologyFunctor A n).mapIso e')]
  map_distTriang T hT := by
    obtain ⟨s₁, hs₁⟩ := exists_finset_isZero_homology T.obj₁
    obtain ⟨s₂, hs₂⟩ := exists_finset_isZero_homology T.obj₂
    obtain ⟨s₃, hs₃⟩ := exists_finset_isZero_homology T.obj₃
    have h : ∀ (X : DerivedCategory.Bounded A) (t : Finset ℤ), t ⊆ s₁ ∪ s₂ ∪ s₃ →
        (∀ n ∉ t, IsZero ((homologyFunctor A n).obj X.obj)) →
        ∀ n ∉ s₁ ∪ s₂ ∪ s₃, IsZero ((homologyFunctor A n).obj X.obj) :=
      fun _ _ ht hX n hn ↦ hX n fun h ↦ hn (ht h)
    have h₁ := h _ _ (by grind) hs₁
    have h₂ := h _ _ (by grind) hs₂
    have h₃ := h _ _ (by grind) hs₃
    rw [sum_negOnePow_of_homology_eq_of_isZero T.obj₁.obj
        (exists_finset_isZero_homology _).choose_spec h₁,
      sum_negOnePow_of_homology_eq_of_isZero T.obj₂.obj
        (exists_finset_isZero_homology _).choose_spec h₂,
      sum_negOnePow_of_homology_eq_of_isZero T.obj₃.obj
        (exists_finset_isZero_homology _).choose_spec h₃]
    exact sum_negOnePow_of_homology_of_distTriang
      (DerivedCategory.Bounded.ι.map_distinguished T hT) h₁ h₃

omit [EssentiallySmall.{w''} (DerivedCategory.Bounded A)] in
/-- The invariant may be computed over any finite set of degrees containing the support of the
cohomology. -/
private lemma boundedDerivedHomologyEulerChar_obj (X : DerivedCategory.Bounded A) {s : Finset ℤ}
    (hs : ∀ n ∉ s, IsZero ((homologyFunctor A n).obj X.obj)) :
    boundedDerivedHomologyEulerChar.obj X =
      ∑ n ∈ s, (n.negOnePow : ℤ) • of ((homologyFunctor A n).obj X.obj) :=
  sum_negOnePow_of_homology_eq_of_isZero X.obj (exists_finset_isZero_homology X).choose_spec hs

/-- The alternating class of the cohomology is a left inverse of `toBoundedDerivedK0`: an object
placed in degree zero has its only cohomology in degree zero. -/
private lemma lift_boundedDerivedHomologyEulerChar_comp_toBoundedDerivedK0 :
    (TriangulatedK0.lift boundedDerivedHomologyEulerChar).comp toBoundedDerivedK0 =
      AddMonoidHom.id (AbelianK0 A) :=
  hom_ext fun X ↦ by
    have hs : ∀ n ∉ ({0} : Finset ℤ), IsZero ((homologyFunctor A n).obj
        ((DerivedCategory.Bounded.singleFunctor A 0).obj X).obj) := fun n hn ↦ by
      rw [Finset.mem_singleton] at hn
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact DerivedCategory.isZero_of_isGE ((DerivedCategory.singleFunctor A 0).obj X) 0 n hn
      · exact DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor A 0).obj X) 0 n hn
    rw [AddMonoidHom.comp_apply, toBoundedDerivedK0_of, TriangulatedK0.lift_of,
      boundedDerivedHomologyEulerChar_obj _ hs, Finset.sum_singleton, Int.negOnePow_zero,
      Units.val_one, one_smul, AddMonoidHom.id_apply]
    exact of_congr ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app X)

omit [EssentiallySmall.{w} A] [EssentiallySmall.{w''} (DerivedCategory.Bounded A)] in
/-- A bounded complex up to homotopy defines a bounded object of the derived category. -/
private lemma bounded_Qh_obj (K : HomotopyCategory.Bounded A) :
    (DerivedCategory.TStructure.t (C := A)).bounded (DerivedCategory.Qh.obj K.obj) := by
  obtain ⟨a, b, _, _⟩ := (CochainComplex.bounded_iff _ _).1
    ((HomotopyCategory.bounded_quotient_obj_iff _).1 K.property)
  exact (DerivedCategory.TStructure.t (C := A)).bounded.prop_of_iso
    ((DerivedCategory.quotientCompQhIso A).app K.obj.as).symm
    ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩

variable (A) in
/-- The localization functor from the bounded homotopy category to the bounded derived
category. -/
private noncomputable abbrev boundedQh : HomotopyCategory.Bounded A ⥤ DerivedCategory.Bounded A :=
  (DerivedCategory.TStructure.t (C := A)).bounded.lift
    (HomotopyCategory.Bounded.ι A ⋙ DerivedCategory.Qh) bounded_Qh_obj

omit [EssentiallySmall.{w} A] [EssentiallySmall.{w''} (DerivedCategory.Bounded A)] in
/-- Every object of the bounded derived category is represented by a bounded complex. -/
private lemma exists_iso_boundedQh_obj (Y : DerivedCategory.Bounded A) :
    ∃ K : HomotopyCategory.Bounded A, Nonempty ((boundedQh A).obj K ≅ Y) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := Y.property
  obtain ⟨K, _, _, ⟨e⟩⟩ := Y.obj.exists_iso_Q_obj_of_isGE_of_isLE a b
  have hK : CochainComplex.bounded A K := (CochainComplex.bounded_iff _ _).2 ⟨a, b, ‹_›, ‹_›⟩
  exact ⟨(HomotopyCategory.Bounded.quotient A).obj ⟨K, hK⟩,
    ⟨(DerivedCategory.TStructure.t (C := A)).bounded.fullyFaithfulι.preimageIso
      (((DerivedCategory.TStructure.t (C := A)).bounded.liftCompιIso
        (HomotopyCategory.Bounded.ι A ⋙ DerivedCategory.Qh) bounded_Qh_obj).app _ ≪≫
        DerivedCategory.Qh.mapIso ((HomotopyCategory.Bounded.quotientCompιIso A).app ⟨K, hK⟩) ≪≫
        (DerivedCategory.quotientCompQhIso A).app K ≪≫ e.symm)⟩⟩

omit [EssentiallySmall.{w} A] [EssentiallySmall.{w''} (DerivedCategory.Bounded A)] in
/-- The localization functor sends an object placed in degree zero to that object placed in degree
zero. -/
private noncomputable def boundedQhSingleIso (X : A) :
    (boundedQh A).obj ((HomotopyCategory.Bounded.singleFunctor A 0).obj X) ≅
      (DerivedCategory.Bounded.singleFunctor A 0).obj X :=
  (DerivedCategory.TStructure.t (C := A)).bounded.fullyFaithfulι.preimageIso
    (((DerivedCategory.TStructure.t (C := A)).bounded.liftCompιIso
        (HomotopyCategory.Bounded.ι A ⋙ DerivedCategory.Qh) bounded_Qh_obj).app _ ≪≫
      DerivedCategory.Qh.mapIso ((HomotopyCategory.Bounded.singleFunctorCompιIso A 0).app X) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQh A 0).app X).symm ≪≫
      (((DerivedCategory.TStructure.t (C := A)).bounded.liftCompιIso
        (DerivedCategory.singleFunctor A 0)
        (fun _ ↦ ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩)).app X).symm)

/-- Every class in triangulated `K₀` of the bounded derived category comes from abelian `K₀`: it
is a class in the bounded homotopy category, where the class of a complex is the alternating sum of
the classes of its terms. -/
private lemma toBoundedDerivedK0_surjective :
    Function.Surjective (toBoundedDerivedK0 (A := A)) := by
  have hcomp : (TriangulatedK0.map (boundedQh A)).comp
      (SplitK0.boundedHomotopyEquiv A).toAddMonoidHom = toBoundedDerivedK0.comp (fromSplit A) :=
    SplitK0.hom_ext fun X ↦ by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        SplitK0.boundedHomotopyEquiv_of, TriangulatedK0.map_of, fromSplit_of,
        toBoundedDerivedK0_of]
      exact TriangulatedK0.of_congr (boundedQhSingleIso X)
  rw [← AddMonoidHom.range_eq_top, eq_top_iff, ← TriangulatedK0.closure_range_of,
    AddSubgroup.closure_le]
  rintro _ ⟨Y, rfl⟩
  obtain ⟨K, ⟨e⟩⟩ := exists_iso_boundedQh_obj Y
  refine ⟨fromSplit A ((SplitK0.boundedHomotopyEquiv A).symm (TriangulatedK0.of K)), ?_⟩
  rw [← AddMonoidHom.comp_apply, ← hcomp, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply, TriangulatedK0.map_of]
  exact TriangulatedK0.of_congr e

variable (A) in
/-- **Abelian `K₀` is triangulated `K₀` of the bounded derived category.** The class of an object
goes to the class of that object placed in degree zero, and in the inverse direction the class of a
bounded complex goes to the alternating sum of the classes of its cohomology objects. -/
noncomputable def boundedDerivedK0Equiv :
    AbelianK0 A ≃+ TriangulatedK0 (DerivedCategory.Bounded A) :=
  AddMonoidHom.toAddEquiv toBoundedDerivedK0 (TriangulatedK0.lift boundedDerivedHomologyEulerChar)
    lift_boundedDerivedHomologyEulerChar_comp_toBoundedDerivedK0
    (AddMonoidHom.ext fun y ↦ by
      obtain ⟨x, rfl⟩ := toBoundedDerivedK0_surjective y
      rw [AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply (TriangulatedK0.lift _),
        lift_boundedDerivedHomologyEulerChar_comp_toBoundedDerivedK0, AddMonoidHom.id_apply,
        AddMonoidHom.id_apply])

/-- The forward map of `TauCeti.AbelianK0.boundedDerivedK0Equiv` is
`TauCeti.AbelianK0.toBoundedDerivedK0`. -/
@[simp]
lemma boundedDerivedK0Equiv_toAddMonoidHom :
    ((boundedDerivedK0Equiv A : AbelianK0 A ≃+ TriangulatedK0 (DerivedCategory.Bounded A)) :
      AbelianK0 A →+ TriangulatedK0 (DerivedCategory.Bounded A)) = toBoundedDerivedK0 :=
  (rfl)

/-- `TauCeti.AbelianK0.boundedDerivedK0Equiv` sends the class of an object to the class of that
object placed in degree zero. -/
@[simp]
lemma boundedDerivedK0Equiv_of (X : A) :
    boundedDerivedK0Equiv A (of X) =
      TriangulatedK0.of ((DerivedCategory.Bounded.singleFunctor A 0).obj X) :=
  toBoundedDerivedK0_of X

/-- The inverse of `TauCeti.AbelianK0.boundedDerivedK0Equiv` sends the class of a bounded complex
to the alternating sum of the classes of its cohomology objects, summed over any finite set of
degrees outside which the cohomology vanishes. -/
theorem boundedDerivedK0Equiv_symm_of (X : DerivedCategory.Bounded A) {s : Finset ℤ}
    (hs : ∀ n ∉ s, IsZero ((homologyFunctor A n).obj X.obj)) :
    (boundedDerivedK0Equiv A).symm (TriangulatedK0.of X) =
      ∑ n ∈ s, (n.negOnePow : ℤ) • of ((homologyFunctor A n).obj X.obj) := by
  rw [boundedDerivedK0Equiv, AddMonoidHom.toAddEquiv_symm_apply, TriangulatedK0.lift_of,
    boundedDerivedHomologyEulerChar_obj _ hs]

end AbelianK0

namespace TriangulatedK0

open _root_.DerivedCategory (homologyFunctor)

/-- **The class of a bounded complex** in triangulated `K₀` of the bounded derived category is the
alternating sum of the classes of its cohomology objects, each placed in degree zero. The sum runs
over any finite set of degrees outside which the cohomology vanishes. -/
theorem of_eq_sum_homology (X : DerivedCategory.Bounded A) {s : Finset ℤ}
    (hs : ∀ n ∉ s, IsZero ((homologyFunctor A n).obj X.obj)) :
    of X = ∑ n ∈ s, (n.negOnePow : ℤ) •
      of ((DerivedCategory.Bounded.singleFunctor A 0).obj ((homologyFunctor A n).obj X.obj)) := by
  rw [← (AbelianK0.boundedDerivedK0Equiv A).apply_symm_apply (of X),
    AbelianK0.boundedDerivedK0Equiv_symm_of X hs, map_sum]
  simp

end TriangulatedK0

end TauCeti
