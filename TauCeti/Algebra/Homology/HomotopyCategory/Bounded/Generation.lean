/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.StupidTrunc
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Basic
public import TauCeti.CategoryTheory.Triangulated.FullSubcategory
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Bounded complexes are built from their terms

In the bounded homotopy category, a triangulated subcategory closed under isomorphisms which
contains the terms of a bounded complex, each placed in degree zero, contains the complex. Splitting
off the top term (`CochainComplex.topShortComplexSplitting`) is a degreewise split short exact
sequence, hence a distinguished triangle, and expresses a bounded complex as an extension of a
shorter complex by a complex concentrated in one degree; induction on the length concludes.

The induction is adapted from the proof of `TauCeti.TriangulatedK0.of_bounded_quotient_obj` in
`TauCeti/CategoryTheory/GrothendieckGroup/BoundedHomotopy/Basic.lean`, which splits off the top
term in the same way to express the class of a bounded complex in the triangulated Grothendieck
group. Both results now use `CochainComplex.bounded_induction` and
`TauCeti.HomotopyCategory.Bounded.exists_distTriang_top` from this file.

## Main results

* `CochainComplex.bounded_induction`: induction on bounded complexes, from zero complexes and by
  passing from the brutal truncation below the top degree to the complex.
* `TauCeti.HomotopyCategory.Bounded.exists_distTriang_top`: the distinguished triangle of the
  bounded homotopy category splitting off the top term of a bounded complex.
* `TauCeti.HomotopyCategory.Bounded.prop_quotient_obj`: a triangulated subcategory containing
  every term of a bounded complex in degree zero contains the complex.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
  HomologicalComplex

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The brutal truncation of a bounded complex in degrees `≤ b` is bounded. -/
lemma bounded_stupidTrunc_embeddingUpIntLE {K : CochainComplex C ℤ}
    (hK : CochainComplex.bounded C K) (b : ℤ) :
    CochainComplex.bounded C (K.stupidTrunc (ComplexShape.embeddingUpIntLE b)) := by
  obtain ⟨a, b', _, _⟩ := (CochainComplex.bounded_iff _ _).1 hK
  exact (CochainComplex.bounded_iff _ _).2 ⟨a, b, inferInstance, inferInstance⟩

/-- **Induction on bounded complexes by their top term.** A property of cochain complexes that
holds for zero complexes, and holds for a bounded complex vanishing above degree `b + 1` as soon
as it holds for its brutal truncation in degrees `≤ b`, holds for every bounded complex. -/
theorem bounded_induction {motive : CochainComplex C ℤ → Prop}
    (zero : ∀ K, IsZero K → motive K)
    (step : ∀ (K : CochainComplex C ℤ) (b : ℤ), CochainComplex.bounded C K →
      K.IsStrictlyLE (b + 1) → motive (K.stupidTrunc (ComplexShape.embeddingUpIntLE b)) →
        motive K)
    (K : CochainComplex C ℤ) (hK : CochainComplex.bounded C K) : motive K := by
  obtain ⟨a, b, ha, hb⟩ := (CochainComplex.bounded_iff _ _).1 hK
  -- Induct on an upper bound `b ≥ a - 1`, for complexes vanishing below `a`.
  suffices h : ∀ b, a - 1 ≤ b → ∀ (K : CochainComplex C ℤ), K.IsStrictlyGE a →
      K.IsStrictlyLE b → motive K from
    h _ (le_max_right _ (a - 1)) K ha (K.isStrictlyLE_of_le b _ (le_max_left _ _))
  intro b hb
  induction b, hb using Int.leInduction with
  | base =>
    intro K _ _
    exact zero K ((IsZero.iff_id_eq_zero _).2 (HomologicalComplex.hom_ext _ _ fun i ↦
      (K.isZero_X_of_notMem_Icc a (a - 1) (n := i) (by simp)).eq_of_src _ _))
  | succ b hb ih =>
    intro K _ hK
    exact step K b ((CochainComplex.bounded_iff _ _).2 ⟨a, b + 1, inferInstance, hK⟩) hK
      (ih _ inferInstance inferInstance)

end CochainComplex

namespace TauCeti


namespace HomotopyCategory.Bounded

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C] [HasZeroObject C]

/-- **Splitting off the top term**: for a bounded complex `K` vanishing above degree `b + 1`, there
is a distinguished triangle of the bounded homotopy category whose vertices are the top term
placed in degree `b + 1`, the complex `K`, and its brutal truncation in degrees `≤ b`. -/
theorem exists_distTriang_top (K : CochainComplex C ℤ) (hK : _root_.CochainComplex.bounded C K)
    (b : ℤ) [K.IsStrictlyLE (b + 1)] :
    ∃ T ∈ distTriang (HomotopyCategory.Bounded C),
      Nonempty (T.obj₁ ≅ (singleFunctor C (b + 1)).obj (K.X (b + 1))) ∧
      Nonempty (T.obj₂ ≅ (quotient C).obj ⟨K, hK⟩) ∧
      Nonempty (T.obj₃ ≅ (quotient C).obj
        ⟨_, CochainComplex.bounded_stupidTrunc_embeddingUpIntLE hK b⟩) := by
  let T₀ := _root_.CochainComplex.trianglehOfDegreewiseSplit _ (K.topShortComplexSplitting b)
  have h₁ : HomotopyCategory.bounded C T₀.obj₁ :=
    (HomotopyCategory.bounded_quotient_obj_iff _).2 (by
      simpa using (_root_.CochainComplex.bounded_iff _ _).2
        ⟨b + 1, b + 1, inferInstance, inferInstance⟩)
  have h₂ : HomotopyCategory.bounded C T₀.obj₂ :=
    (HomotopyCategory.bounded_quotient_obj_iff _).2 (by simpa using hK)
  obtain ⟨T, hT, ⟨e⟩⟩ := (HomotopyCategory.bounded C).exists_distTriang_mapTriangle_iso
    (_root_.CochainComplex.trianglehOfDegreewiseSplit_distinguished _ _) h₁ h₂
  refine ⟨T, hT, ⟨(fullyFaithfulι C).preimageIso (Triangle.π₁.mapIso e ≪≫ eqToIso ?_ ≪≫
      ((singleFunctorCompιIso C (b + 1)).app (K.X (b + 1))).symm)⟩,
    ⟨(fullyFaithfulι C).preimageIso (Triangle.π₂.mapIso e ≪≫ eqToIso ?_)⟩,
    ⟨(fullyFaithfulι C).preimageIso (Triangle.π₃.mapIso e ≪≫ eqToIso ?_)⟩⟩
  · simp [← _root_.HomotopyCategory.quotient_obj_singleFunctors_obj]
  · simp [quotient_obj_obj]
  · simp [quotient_obj_obj]

variable (P : ObjectProperty (HomotopyCategory.Bounded C)) [P.IsTriangulated]
  [P.IsClosedUnderIsomorphisms]

/-- A triangulated subcategory contains an object placed in any degree once it contains it in
degree zero. -/
private lemma prop_singleFunctor_obj (n : ℤ) {X : C}
    (hX : P ((singleFunctor C 0).obj X)) : P ((singleFunctor C n).obj X) := by
  rw [← P.prop_shift_iff_of_isStableUnderShift _ n]
  exact P.prop_of_iso (((singleFunctors C).shiftIso n 0 n (add_zero n)).app X).symm hX

/-- **A bounded complex lies in a triangulated subcategory containing its terms**: if a
triangulated subcategory of the bounded homotopy category, closed under isomorphisms, contains
each term of a bounded complex placed in degree zero, then it contains the complex. -/
theorem prop_quotient_obj (K : CochainComplex.Bounded C)
    (hK : ∀ n, P ((singleFunctor C 0).obj (K.obj.X n))) : P ((quotient C).obj K) := by
  refine CochainComplex.bounded_induction (motive := fun K ↦
    ∀ hK : _root_.CochainComplex.bounded C K,
      (∀ n, P ((singleFunctor C 0).obj (K.X n))) → P ((quotient C).obj ⟨K, hK⟩)) ?_ ?_
    K.obj K.property K.property hK
  · intro K hK0 hK _
    refine P.prop_of_isZero (IsZero.of_full_of_faithful_of_isZero (ι C) _ ?_)
    rw [ObjectProperty.ι_obj, quotient_obj_obj]
    exact Functor.map_isZero _ hK0
  · intro K b hK _ ih hK' hP
    obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_distTriang_top K hK' b
    -- The truncation has the terms of `K` in degrees `≤ b` and zero terms above.
    have h₃ := ih (CochainComplex.bounded_stupidTrunc_embeddingUpIntLE hK' b) fun n ↦ by
      by_cases hn : n ≤ b
      · have := K.isIso_πStupidTruncLE_f b hn
        exact P.prop_of_iso ((singleFunctor C 0).mapIso (asIso ((K.πStupidTruncLE b).f n)))
          (hP n)
      · exact P.prop_of_isZero ((singleFunctor C 0).map_isZero
          (K.isZero_stupidTrunc_embeddingUpIntLE_X b (by omega)))
    exact P.prop_of_iso e₂ (P.ext_of_isTriangulatedClosed₂ _ hT
      (P.prop_of_iso e₁.symm (prop_singleFunctor_obj P (b + 1) (hP _)))
      (P.prop_of_iso e₃.symm h₃))

end HomotopyCategory.Bounded

end TauCeti
