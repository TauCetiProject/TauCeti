/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.StupidTrunc
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Bounded complexes are built from their terms

In the bounded homotopy category, a triangulated subcategory closed under isomorphisms which
contains the terms of a bounded complex, each placed in degree zero, contains the complex. Splitting
off the top term (`CochainComplex.topShortComplexSplitting`) is a degreewise split short exact
sequence, hence a distinguished triangle, and expresses a bounded complex as an extension of a
shorter complex by a complex concentrated in one degree; induction on the length concludes.

## Main results

* `TauCeti.HomotopyCategory.Bounded.prop_quotient_obj`: a triangulated subcategory containing
  every term of a bounded complex in degree zero contains the complex.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
  HomologicalComplex

universe v u

namespace HomotopyCategory.Bounded

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C] [HasZeroObject C]
  (P : ObjectProperty (HomotopyCategory.Bounded C)) [P.IsTriangulated]
  [P.IsClosedUnderIsomorphisms]

/-- In a distinguished triangle of the homotopy category with bounded vertices, the middle vertex
satisfies a triangulated property of the bounded homotopy category when the outer ones do. -/
private lemma prop_obj₂ {T : Triangle (_root_.HomotopyCategory C (.up ℤ))}
    (hT : T ∈ distTriang _) (h₁ : HomotopyCategory.bounded C T.obj₁)
    (h₂ : HomotopyCategory.bounded C T.obj₂) (h₃ : HomotopyCategory.bounded C T.obj₃)
    (hP₁ : P ⟨T.obj₁, h₁⟩) (hP₃ : P ⟨T.obj₃, h₃⟩) : P ⟨T.obj₂, h₂⟩ := by
  -- Complete the first morphism to a distinguished triangle of the bounded homotopy category;
  -- its third vertex is isomorphic to `T.obj₃`.
  obtain ⟨Z, g, h, hT'⟩ := distinguished_cocone_triangle
    ((fullyFaithfulι C).preimage T.mor₁ : (⟨T.obj₁, h₁⟩ : HomotopyCategory.Bounded C) ⟶
      ⟨T.obj₂, h₂⟩)
  let e := Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ _ ((ι C).map_distinguished _ hT') hT
    (Iso.refl _) (Iso.refl _) (by simp))
  have hZ : P Z :=
    P.prop_of_iso ((fullyFaithfulι C).preimageIso (X := Z) (Y := ⟨T.obj₃, h₃⟩) e).symm hP₃
  exact P.ext_of_isTriangulatedClosed₂ _ hT' hP₁ hZ

/-- A triangulated subcategory contains an object placed in any degree once it contains it in
degree zero. -/
private lemma prop_singleFunctor_obj (n : ℤ) {X : C}
    (hX : P ((singleFunctor C 0).obj X)) : P ((singleFunctor C n).obj X) := by
  rw [← P.prop_shift_iff_of_isStableUnderShift _ n]
  exact P.prop_of_iso (((singleFunctors C).shiftIso n 0 n (add_zero n)).app X).symm hX

/-- The induction behind `TauCeti.HomotopyCategory.Bounded.prop_quotient_obj`, on the upper bound
of a complex. -/
private lemma prop_quotient_obj_aux (a : ℤ) : ∀ b, a - 1 ≤ b →
    ∀ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE a) (_ : K.IsStrictlyLE b)
      (hK : CochainComplex.bounded C K),
      (∀ n, a ≤ n → n ≤ b → P ((singleFunctor C 0).obj (K.X n))) →
      P ((quotient C).obj ⟨K, hK⟩) := by
  intro b hb
  induction b, hb using Int.leInduction with
  | base =>
    intro K _ _ hK _
    have hK0 : IsZero K := (IsZero.iff_id_eq_zero _).2 (HomologicalComplex.hom_ext _ _ fun i ↦
      (K.isZero_X_of_notMem_Icc a (a - 1) (n := i) (by simp)).eq_of_src _ _)
    refine P.prop_of_isZero (IsZero.of_full_of_faithful_of_isZero (ι C) _ ?_)
    rw [ObjectProperty.ι_obj, quotient_obj_obj]
    exact Functor.map_isZero _ hK0
  | succ b hb ih =>
    intro K _ _ hK hP
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
    -- The top term of `K` in degree `b + 1`.
    have hP₁ : P ⟨T.obj₁, h₁⟩ := by
      refine P.prop_of_iso ((fullyFaithfulι C).preimageIso
        (((singleFunctorCompιIso C (b + 1)).app (K.X (b + 1))) ≪≫ eqToIso ?_))
        (prop_singleFunctor_obj P (b + 1) (hP _ (by omega) le_rfl))
      simp [T, ← _root_.HomotopyCategory.quotient_obj_singleFunctors_obj]
    -- The truncation `X₃`, whose terms are those of `K` in degrees `≤ b` and zero above.
    have hP₃ : P ⟨T.obj₃, h₃⟩ := by
      have hX₃ : P ((quotient C).obj ⟨X₃, hb₃⟩) := ih X₃ inferInstance inferInstance hb₃
        fun n ha hn ↦ P.prop_of_iso ((singleFunctor C 0).mapIso
          (have := K.isIso_πStupidTruncLE_f b hn; asIso ((K.πStupidTruncLE b).f n))) (hP n ha
            (by omega))
      refine P.prop_of_iso ((fullyFaithfulι C).preimageIso (eqToIso ?_)) hX₃
      simp [T, X₃, quotient_obj_obj]
    have := prop_obj₂ P (CochainComplex.trianglehOfDegreewiseSplit_distinguished _ _) h₁ h₂ h₃
      hP₁ hP₃
    refine P.prop_of_iso ((fullyFaithfulι C).preimageIso (eqToIso ?_)) this
    simp [quotient_obj_obj]

/-- **A bounded complex lies in a triangulated subcategory containing its terms**: if a
triangulated subcategory of the bounded homotopy category, closed under isomorphisms, contains
each term of a bounded complex placed in degree zero, then it contains the complex. -/
theorem prop_quotient_obj (K : CochainComplex.Bounded C)
    (hK : ∀ n, P ((singleFunctor C 0).obj (K.obj.X n))) : P ((quotient C).obj K) := by
  obtain ⟨a, b, ha, hb⟩ := (CochainComplex.bounded_iff _ _).1 K.property
  have hb' : K.obj.IsStrictlyLE (max b (a - 1)) := K.obj.isStrictlyLE_of_le b _ (le_max_left _ _)
  exact prop_quotient_obj_aux P a _ (le_max_right _ _) K.obj ha hb' K.property
    fun n _ _ ↦ hK n

end HomotopyCategory.Bounded

end TauCeti
