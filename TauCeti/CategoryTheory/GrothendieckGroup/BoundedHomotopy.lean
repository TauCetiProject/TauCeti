/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.StupidTrunc
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded
public import TauCeti.CategoryTheory.GrothendieckGroup.BoundedComplex
public import TauCeti.CategoryTheory.GrothendieckGroup.Triangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Split `K₀` and the bounded homotopy category

This file proves the standard comparison between split `K₀` of an additive category and the
triangulated `K₀` of its bounded homotopy category. The Euler characteristic of a representing
complex (`TauCeti.SplitK0.eulerChar`) is well defined on the objects of the homotopy category by
homotopy invariance, and additive on distinguished triangles by the mapping-cone formula, so it
induces a homomorphism out of triangulated `K₀`. It is inverse to the map placing an object in
degree zero: splitting off the top term of a bounded complex is a degreewise split short exact
sequence, hence a distinguished triangle, and induction on the length of the complex shows that
the class of a bounded complex is the alternating sum of the classes of its terms.

## Main definitions

* `TauCeti.SplitK0.boundedHomotopyEquiv`: the isomorphism between split `K₀` of an additive
  category and triangulated `K₀` of its bounded homotopy category.

## Main results

* `TauCeti.TriangulatedK0.of_bounded_quotient_obj`: in triangulated `K₀` of the bounded homotopy
  category, the class of a bounded complex is the alternating sum of the classes of its terms
  placed in degree zero; `TauCeti.TriangulatedK0.of_boundedSingleFunctor_obj` computes the class
  of an object placed in degree `n` as `(-1)ⁿ` times its class in degree zero.
* `TauCeti.SplitK0.boundedHomotopyEquiv_symm_of_quotient_obj`: the inverse comparison is the Euler
  characteristic.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Exercise 9.15, for the comparison of `K₀` of an additive category with `K₀` of its bounded
  homotopy category through the alternating sum of the terms.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
  HomologicalComplex

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable [HasZeroObject C] [EssentiallySmall.{w} C]

namespace SplitK0

omit [HasBinaryBiproducts C] [HasZeroObject C] [EssentiallySmall.{w} C] in
private lemma exists_finset_isZero_X (K : HomotopyCategory.Bounded C) :
    ∃ s : Finset ℤ, ∀ n ∉ s, IsZero (K.obj.as.X n) :=
  (CochainComplex.bounded_iff_exists_finset_isZero_X _ K.obj.as).1
    ((HomotopyCategory.bounded_quotient_obj_iff _).1 K.property)

variable (C) in
/-- The Euler characteristic of the representing bounded complex, as a triangle-additive invariant
on the bounded homotopy category. Homotopy invariance makes it constant on isomorphism classes,
and the mapping-cone formula makes it additive on distinguished triangles. -/
private noncomputable def boundedHomotopyEulerChar :
    TriangulatedK0.AdditiveInvariant (HomotopyCategory.Bounded C) (SplitK0 C) where
  obj K := eulerChar K.obj.as (exists_finset_isZero_X K).choose
  map_iso K L e := eulerChar_eq_of_homotopyEquiv_of_isZero
    (_root_.HomotopyCategory.homotopyEquivOfIso ((HomotopyCategory.Bounded.ι C).mapIso e))
    (exists_finset_isZero_X K).choose_spec (exists_finset_isZero_X L).choose_spec
  map_distTriang T hT := by
    obtain ⟨s₁, hs₁⟩ := exists_finset_isZero_X T.obj₁
    obtain ⟨s₂, hs₂⟩ := exists_finset_isZero_X T.obj₂
    obtain ⟨f, hf⟩ := (_root_.HomotopyCategory.quotient C (.up ℤ)).map_surjective
      (X := T.obj₁.obj.as) (Y := T.obj₂.obj.as) T.mor₁.hom
    -- The third vertex is isomorphic in the homotopy category to the standard mapping cone of a
    -- representative of the first morphism.
    let e := Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ _
      ((HomotopyCategory.Bounded.ι C).map_distinguished _ hT)
      (_root_.HomotopyCategory.mappingCone_triangleh_distinguished f) (Iso.refl _) (Iso.refl _)
      ((Category.comp_id _).trans (hf.symm.trans (Category.id_comp _).symm)))
    have hcone : ∀ n ∉ s₂ ∪ s₁.map (Equiv.addRight (-1 : ℤ)).toEmbedding,
        IsZero ((CochainComplex.mappingCone f).X n) := by
      intro n hn
      rw [CochainComplex.mappingCone.isZero_X_iff]
      exact ⟨hs₁ _ fun h ↦ hn (by simp [h]), hs₂ _ fun h ↦ hn (by simp [h])⟩
    rw [eulerChar_eq_of_homotopyEquiv_of_isZero
      (_root_.HomotopyCategory.homotopyEquivOfIso (C := T.obj₃.obj.as)
        (D := CochainComplex.mappingCone f) e)
      (exists_finset_isZero_X T.obj₃).choose_spec hcone,
      eulerChar_mappingCone_of_isZero f hs₁ hs₂ hcone,
      eulerChar_eq_eulerChar_of_isZero _ (exists_finset_isZero_X T.obj₁).choose_spec hs₁,
      eulerChar_eq_eulerChar_of_isZero _ (exists_finset_isZero_X T.obj₂).choose_spec hs₂]
    abel

private lemma boundedHomotopyEulerChar_obj (K : HomotopyCategory.Bounded C) {s : Finset ℤ}
    (hs : ∀ n ∉ s, IsZero (K.obj.as.X n)) :
    (boundedHomotopyEulerChar C).obj K = eulerChar K.obj.as s :=
  eulerChar_eq_eulerChar_of_isZero _ (exists_finset_isZero_X K).choose_spec hs

private lemma boundedHomotopyEulerChar_obj_quotient (K : CochainComplex.Bounded C)
    {s : Finset ℤ} (hs : ∀ n ∉ s, IsZero (K.obj.X n)) :
    (boundedHomotopyEulerChar C).obj ((HomotopyCategory.Bounded.quotient C).obj K) =
      eulerChar K.obj s := by
  have h := boundedHomotopyEulerChar_obj ((HomotopyCategory.Bounded.quotient C).obj K) (s := s)
    (by rw [HomotopyCategory.Bounded.quotient_obj_obj]; exact hs)
  rwa [HomotopyCategory.Bounded.quotient_obj_obj] at h

variable (C) in
/-- The comparison map sending the class of an object to the class of that object placed in
degree zero. -/
private noncomputable def toBoundedHomotopy :
    SplitK0 C →+ TriangulatedK0 (HomotopyCategory.Bounded C) :=
  (TriangulatedK0.fromSplit _).comp (map (HomotopyCategory.Bounded.singleFunctor C 0))

private lemma toBoundedHomotopy_of (X : C) :
    toBoundedHomotopy C (of X) =
      TriangulatedK0.of ((HomotopyCategory.Bounded.singleFunctor C 0).obj X) := by
  simp [toBoundedHomotopy]

end SplitK0

namespace TriangulatedK0

private lemma of_bounded_eq_of_obj_eq {K L : HomotopyCategory.Bounded C} (h : K.obj = L.obj) :
    (of K : TriangulatedK0 (HomotopyCategory.Bounded C)) = of L :=
  of_congr ((HomotopyCategory.Bounded.fullyFaithfulι C).preimageIso (eqToIso h))

/-- The object `X` placed in degree `n` in the bounded homotopy category is the class of the
single complex on `X`. -/
private lemma of_boundedSingleFunctor_obj_eq_of_quotient_obj (n : ℤ) (X : C)
    (h : CochainComplex.bounded C ((single C (.up ℤ) n).obj X)) :
    (of ((HomotopyCategory.Bounded.singleFunctor C n).obj X) :
      TriangulatedK0 (HomotopyCategory.Bounded C)) =
      of ((HomotopyCategory.Bounded.quotient C).obj ⟨_, h⟩) :=
  of_congr ((HomotopyCategory.Bounded.fullyFaithfulι C).preimageIso
    ((HomotopyCategory.Bounded.singleFunctorCompιIso C n).app X ≪≫ eqToIso (by
      rw [ObjectProperty.ι_obj, HomotopyCategory.Bounded.quotient_obj_obj]
      exact (_root_.HomotopyCategory.quotient_obj_singleFunctors_obj C n X).symm)))

/-- In triangulated `K₀` of the bounded homotopy category, an object placed in degree `n` has the
class of the same object placed in degree zero, multiplied by the sign `(-1)ⁿ`. -/
theorem of_boundedSingleFunctor_obj (n : ℤ) (X : C) :
    (of ((HomotopyCategory.Bounded.singleFunctor C n).obj X) :
      TriangulatedK0 (HomotopyCategory.Bounded C)) =
      (n.negOnePow : ℤ) • of ((HomotopyCategory.Bounded.singleFunctor C 0).obj X) := by
  have h := of_congr (((HomotopyCategory.Bounded.singleFunctors C).shiftIso n 0 n
    (add_zero n)).app X)
  rw [Functor.comp_obj, of_shift] at h
  rw [← h, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

/-- The induction behind `TauCeti.TriangulatedK0.of_bounded_quotient_obj`, on the upper bound of
a complex: splitting off the top term expresses a complex as an extension of a shorter complex by
a complex concentrated in a single degree. -/
private lemma of_bounded_quotient_obj_aux (a : ℤ) : ∀ b, a - 1 ≤ b →
    ∀ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE a) (_ : K.IsStrictlyLE b)
      (hK : CochainComplex.bounded C K),
      (of ((HomotopyCategory.Bounded.quotient C).obj ⟨K, hK⟩) :
        TriangulatedK0 (HomotopyCategory.Bounded C)) =
        SplitK0.toBoundedHomotopy C (SplitK0.eulerChar K (Finset.Icc a b)) := by
  intro b hb
  induction b, hb using Int.leInduction with
  | base =>
    intro K _ _ hK
    have hK0 : IsZero K := (IsZero.iff_id_eq_zero _).2 (HomologicalComplex.hom_ext _ _ fun i ↦
      (K.isZero_X_of_notMem_Icc a (a - 1) (n := i) (by simp)).eq_of_src _ _)
    rw [Finset.Icc_eq_empty (by omega), SplitK0.eulerChar_empty, map_zero]
    refine of_eq_zero_of_isZero (IsZero.of_full_of_faithful_of_isZero
      (HomotopyCategory.Bounded.ι C) _ ?_)
    rw [ObjectProperty.ι_obj, HomotopyCategory.Bounded.quotient_obj_obj]
    exact Functor.map_isZero _ hK0
  | succ b hb ih =>
    intro K _ _ hK
    let X₃ := K.stupidTrunc (ComplexShape.embeddingUpIntLE b)
    have hb₁ : CochainComplex.bounded C ((single C (.up ℤ) (b + 1)).obj (K.X (b + 1))) :=
      (CochainComplex.bounded_iff _ _).2 ⟨b + 1, b + 1, inferInstance, inferInstance⟩
    have hb₃ : CochainComplex.bounded C X₃ :=
      (CochainComplex.bounded_iff _ _).2 ⟨a, b, inferInstance, inferInstance⟩
    let T := CochainComplex.trianglehOfDegreewiseSplit _ (K.topShortComplexSplitting b)
    have h₁ : HomotopyCategory.bounded C T.obj₁ :=
      (HomotopyCategory.bounded_quotient_obj_iff _).2 (by simpa using hb₁)
    have h₂ : HomotopyCategory.bounded C T.obj₂ :=
      (HomotopyCategory.bounded_quotient_obj_iff _).2 (by simpa using hK)
    have h₃ : HomotopyCategory.bounded C T.obj₃ :=
      (HomotopyCategory.bounded_quotient_obj_iff _).2 (by simpa using hb₃)
    have hT := of_fullSubcategory_distTriang (HomotopyCategory.bounded C)
      (CochainComplex.trianglehOfDegreewiseSplit_distinguished _ _) h₁ h₂ h₃
    -- The three vertices of the splitting triangle are the bounded homotopy classes of the top
    -- term in degree `b + 1`, of `K`, and of its truncation `X₃`.
    rw [of_bounded_eq_of_obj_eq (K := ⟨T.obj₂, h₂⟩)
        (L := (HomotopyCategory.Bounded.quotient C).obj ⟨K, hK⟩)
        (by simp [T, HomotopyCategory.Bounded.quotient_obj_obj]),
      of_bounded_eq_of_obj_eq (K := ⟨T.obj₁, h₁⟩)
        (L := (HomotopyCategory.Bounded.quotient C).obj ⟨_, hb₁⟩)
        (by simp [T, HomotopyCategory.Bounded.quotient_obj_obj]),
      of_bounded_eq_of_obj_eq (K := ⟨T.obj₃, h₃⟩)
        (L := (HomotopyCategory.Bounded.quotient C).obj ⟨X₃, hb₃⟩)
        (by simp [T, X₃, HomotopyCategory.Bounded.quotient_obj_obj]),
      ← of_boundedSingleFunctor_obj_eq_of_quotient_obj] at hT
    have hX₃ : SplitK0.eulerChar X₃ (Finset.Icc a b) = SplitK0.eulerChar K (Finset.Icc a b) := by
      rw [SplitK0.eulerChar_def, SplitK0.eulerChar_def]
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      have := K.isIso_πStupidTruncLE_f b (Finset.mem_Icc.1 hn).2
      rw [SplitK0.of_congr (asIso ((K.πStupidTruncLE b).f n))]
    have hIcc : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hT, of_boundedSingleFunctor_obj, ← SplitK0.toBoundedHomotopy_of, ← map_zsmul,
      ih X₃ inferInstance inferInstance hb₃, hX₃, hIcc, SplitK0.eulerChar_insert K (by simp),
      map_add]

/-- **The class of a bounded complex** in triangulated `K₀` of the bounded homotopy category is
the alternating sum of the classes of its terms, each placed in degree zero. The sum runs over any
finite set of degrees outside which the complex vanishes. -/
theorem of_bounded_quotient_obj (K : CochainComplex.Bounded C) {s : Finset ℤ}
    (hs : ∀ n ∉ s, IsZero (K.obj.X n)) :
    (of ((HomotopyCategory.Bounded.quotient C).obj K) :
      TriangulatedK0 (HomotopyCategory.Bounded C)) =
      ∑ n ∈ s, (n.negOnePow : ℤ) • of ((HomotopyCategory.Bounded.singleFunctor C 0).obj
        (K.obj.X n)) := by
  obtain ⟨a, b, ha, hb⟩ := (CochainComplex.bounded_iff _ _).1 K.property
  have hb' : K.obj.IsStrictlyLE (max b (a - 1)) := K.obj.isStrictlyLE_of_le b _ (le_max_left _ _)
  rw [of_bounded_quotient_obj_aux a _ (le_max_right _ _) K.obj ha hb' K.property,
    SplitK0.eulerChar_eq_eulerChar_of_isZero _
      (fun _ hn ↦ K.obj.isZero_X_of_notMem_Icc a (max b (a - 1)) hn) hs]
  simp [SplitK0.eulerChar_def, SplitK0.toBoundedHomotopy_of]

end TriangulatedK0

namespace SplitK0

variable (C) in
/-- **Split `K₀` of an additive category is triangulated `K₀` of its bounded homotopy category.**
The class of an object goes to the class of that object placed in degree zero, and in the inverse
direction the class of a bounded complex goes to its Euler characteristic, the alternating sum of
the classes of its terms. -/
noncomputable def boundedHomotopyEquiv :
    SplitK0 C ≃+ TriangulatedK0 (HomotopyCategory.Bounded C) :=
  AddMonoidHom.toAddEquiv (toBoundedHomotopy C)
    (TriangulatedK0.lift (boundedHomotopyEulerChar C))
    (hom_ext fun X ↦ by
      have h : CochainComplex.bounded C ((single C (.up ℤ) 0).obj X) :=
        (CochainComplex.bounded_iff _ _).2 ⟨0, 0, inferInstance, inferInstance⟩
      rw [AddMonoidHom.comp_apply, toBoundedHomotopy_of,
        TriangulatedK0.of_boundedSingleFunctor_obj_eq_of_quotient_obj 0 X h,
        TriangulatedK0.lift_of, boundedHomotopyEulerChar_obj_quotient (s := {0}) _
          fun n hn ↦ isZero_single_obj_X (.up ℤ) _ _ _ (by simpa using hn)]
      simp [eulerChar_def])
    (TriangulatedK0.hom_ext fun K ↦ by
      obtain ⟨K, rfl⟩ := HomotopyCategory.Bounded.quotient_obj_surjective K
      obtain ⟨s, hs⟩ := (CochainComplex.bounded_iff_exists_finset_isZero_X _ K.obj).1 K.property
      rw [AddMonoidHom.comp_apply, TriangulatedK0.lift_of,
        boundedHomotopyEulerChar_obj_quotient _ hs, AddMonoidHom.id_apply,
        TriangulatedK0.of_bounded_quotient_obj K hs]
      simp [eulerChar_def, toBoundedHomotopy_of])

/-- `TauCeti.SplitK0.boundedHomotopyEquiv` sends the class of an object to the class of that object
placed in degree zero. -/
@[simp]
lemma boundedHomotopyEquiv_of (X : C) :
    boundedHomotopyEquiv C (of X) =
      TriangulatedK0.of ((HomotopyCategory.Bounded.singleFunctor C 0).obj X) :=
  toBoundedHomotopy_of X

/-- The inverse of `TauCeti.SplitK0.boundedHomotopyEquiv` sends the class of a bounded complex to
its Euler characteristic, summed over any finite set of degrees outside which it vanishes. -/
theorem boundedHomotopyEquiv_symm_of_quotient_obj (K : CochainComplex.Bounded C) {s : Finset ℤ}
    (hs : ∀ n ∉ s, IsZero (K.obj.X n)) :
    (boundedHomotopyEquiv C).symm
        (TriangulatedK0.of ((HomotopyCategory.Bounded.quotient C).obj K)) =
      eulerChar K.obj s := by
  rw [boundedHomotopyEquiv, AddMonoidHom.toAddEquiv_symm_apply, TriangulatedK0.lift_of,
    boundedHomotopyEulerChar_obj_quotient _ hs]

/-- The inverse of `TauCeti.SplitK0.boundedHomotopyEquiv` sends the class of an object placed in
degree `n` to `(-1)ⁿ` times its class. -/
@[simp]
theorem boundedHomotopyEquiv_symm_of_singleFunctor_obj (n : ℤ) (X : C) :
    (boundedHomotopyEquiv C).symm
        (TriangulatedK0.of ((HomotopyCategory.Bounded.singleFunctor C n).obj X)) =
      (n.negOnePow : ℤ) • of X := by
  rw [TriangulatedK0.of_boundedSingleFunctor_obj, map_zsmul, ← boundedHomotopyEquiv_of,
    AddEquiv.symm_apply_apply]

end SplitK0

end TauCeti
