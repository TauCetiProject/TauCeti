/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Splitting off the top term of a bounded cochain complex

For a cochain complex `K` over a category with zero morphisms and a zero object, the brutal
truncation `K.stupidTrunc (ComplexShape.embeddingUpIntLE n)` keeps the terms of `K` in degrees
`≤ n` and replaces the others by zero. The differentials of `K` go up in degree, so this truncation
is a quotient complex of `K`: the projection `CochainComplex.πStupidTruncLE K n` is an isomorphism
in every degree `≤ n`.

When `K` vanishes in degrees `> n + 1`, its top term `K.X (n + 1)` placed in degree `n + 1` is a
subcomplex, and in the preadditive setting the two maps form the short complex
`CochainComplex.topShortComplex K n`

```text
K.X (n + 1)[-(n + 1)] ⟶ K ⟶ K.stupidTrunc (embeddingUpIntLE n),
```

which is split in each degree (`CochainComplex.topShortComplexSplitting`). Degreewise split short
exact sequences of complexes give distinguished triangles in the homotopy category, so this is the
step of an induction on the length of a bounded complex: it expresses a bounded complex as an
extension of a shorter one by a complex concentrated in a single degree.

## Main definitions

* `CochainComplex.πStupidTruncLE K n`: the projection of `K` onto its brutal truncation in
  degrees `≤ n`.
* `CochainComplex.ιTop K n`: the inclusion of the top term of a complex vanishing in degrees
  `> n`.
* `CochainComplex.topShortComplex K n` and `CochainComplex.topShortComplexSplitting K n`: the
  degreewise split short complex splitting off the top term.
-/

public section

open CategoryTheory Limits HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C]

section HasZeroMorphisms

variable [HasZeroMorphisms C] [HasZeroObject C] (K : CochainComplex C ℤ) (n : ℤ)

/-- The projection of a cochain complex onto its brutal truncation in degrees `≤ n`. It is a map
of complexes because the differentials of a cochain complex go up in degree. -/
noncomputable def πStupidTruncLE : K ⟶ K.stupidTrunc (ComplexShape.embeddingUpIntLE n) :=
  (ComplexShape.embeddingUpIntLE n).liftExtend (𝟙 _) fun j hj ↦
    (hj.2 (j + 1) ((ComplexShape.embeddingUpIntLE n).rel (by simp))).elim

/-- In a retained degree, the projection is the inverse of the canonical identification with
the original complex. -/
@[simp]
lemma πStupidTruncLE_f {i : ℤ} (hi : i ≤ n) :
    (K.πStupidTruncLE n).f i =
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntLE n)
        (i := (n - i).natAbs) (i' := i) (by
          simp [Int.natAbs_of_nonneg (sub_nonneg.mpr hi)])).inv := by
  simp only [πStupidTruncLE, ComplexShape.Embedding.liftExtend]
  rw [ComplexShape.Embedding.liftExtend.f_eq
    (i := (n - i).natAbs)
    (hi := by simp [Int.natAbs_of_nonneg (sub_nonneg.mpr hi)])]
  dsimp [HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso]
  dsimp [CategoryTheory.Iso.trans]
  dsimp [HomologicalComplex.stupidTrunc]
  simp only [Category.id_comp]

/-- The brutal truncation in degrees `≤ n` vanishes in degrees `> n`. -/
lemma isZero_stupidTrunc_embeddingUpIntLE_X {i : ℤ} (hi : n < i) :
    IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntLE n)).X i) :=
  K.isZero_stupidTrunc_X _ i ((ComplexShape.notMem_range_embeddingUpIntLE_iff n i).2 hi)

/-- The projection onto the brutal truncation in degrees `≤ n` is an isomorphism in each degree
`≤ n`. -/
lemma isIso_πStupidTruncLE_f {i : ℤ} (hi : i ≤ n) : IsIso ((K.πStupidTruncLE n).f i) := by
  obtain ⟨j, hj⟩ : ∃ j, (ComplexShape.embeddingUpIntLE n).f j = i := by
    by_contra h
    push Not at h
    exact absurd ((ComplexShape.notMem_range_embeddingUpIntLE_iff n i).1 h) (not_lt.2 hi)
  exact ((ComplexShape.embeddingUpIntLE n).isIso_liftExtend_f_iff _ _ hj).2 inferInstance

variable [K.IsStrictlyLE n]

/-- The inclusion of the top term `K.X n`, placed in degree `n`, into a cochain complex `K`
vanishing in degrees `> n`. -/
noncomputable def ιTop : (single C (.up ℤ) n).obj (K.X n) ⟶ K :=
  mkHomFromSingle (𝟙 _) fun k hk ↦
    (K.isZero_of_isStrictlyLE n k (by simp at hk; omega)).eq_of_tgt _ _

/-- The inclusion of the top term is the identity in the top degree. -/
@[simp]
lemma ιTop_f : (K.ιTop n).f n = (singleObjXSelf (.up ℤ) n (K.X n)).hom := by
  simp [ιTop, mkHomFromSingle_f]

end HasZeroMorphisms

section Preadditive

variable [Preadditive C] [HasZeroObject C] (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyLE (n + 1)]

/-- The short complex splitting off the top term of a cochain complex `K` vanishing in degrees
`> n + 1`: the top term in degree `n + 1`, then `K`, then the brutal truncation of `K` in degrees
`≤ n`. -/
@[expose, simps]
noncomputable def topShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (K.ιTop (n + 1)) (K.πStupidTruncLE n) (by
    refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
    by_cases hi : i = n + 1
    · subst hi
      exact (K.isZero_stupidTrunc_embeddingUpIntLE_X n (by omega)).eq_of_tgt _ _
    · exact (isZero_single_obj_X (.up ℤ) _ _ _ hi).eq_of_src _ _)

/-- The short complex splitting off the top term is split in each degree: in degree `n + 1` its
first map is an isomorphism and its third term vanishes, and in every other degree its first term
vanishes and its second map is an isomorphism. -/
noncomputable def topShortComplexSplitting (i : ℤ) :
    ((K.topShortComplex n).map (eval C _ i)).Splitting := by
  by_cases hi : i = n + 1
  · subst hi
    refine .ofIsIsoOfIsZero _ ?_ (K.isZero_stupidTrunc_embeddingUpIntLE_X n (by omega))
    dsimp [topShortComplex]
    rw [ιTop_f]
    infer_instance
  · refine .ofIsZeroOfIsIso _ (isZero_single_obj_X (.up ℤ) _ _ _ hi) ?_
    dsimp [topShortComplex]
    by_cases hin : i ≤ n
    · exact K.isIso_πStupidTruncLE_f n hin
    · exact isIso_of_source_target_iso_zero _
        (K.isZero_of_isStrictlyLE (n + 1) i (by omega)).isoZero
        (K.isZero_stupidTrunc_embeddingUpIntLE_X n (by omega)).isoZero

end Preadditive

end CochainComplex
