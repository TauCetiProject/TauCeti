/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Brutal truncations of cochain complexes

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

In an abelian category, the kernel of `K ⟶ σ^{≤ n} K` is the brutal truncation `σ^{≥ n + 1} K`,
the subcomplex of the terms of `K` in degrees `> n`. These subcomplexes exhaust `K`: the
sequence `σ^{≥ 0} K ⟶ σ^{≥ -1} K ⟶ σ^{≥ -2} K ⟶ ⋯` has colimit `K`, because in each degree its
inclusions into `K` are eventually isomorphisms. This writes a complex which is bounded above as a
sequential colimit of bounded complexes.

## Main definitions

* `CochainComplex.πStupidTruncLE K n`: the projection of `K` onto its brutal truncation in
  degrees `≤ n`.
* `CochainComplex.ιTop K n`: the inclusion of the top term of a complex vanishing in degrees
  `> n`.
* `CochainComplex.topShortComplex K n` and `CochainComplex.topShortComplexSplitting K n`: the
  degreewise split short complex splitting off the top term.
* `CochainComplex.stupidTruncGESequence K`: the sequence of brutal truncations `σ^{≥ -m} K`,
  realized as the kernels of the projections `K ⟶ σ^{≤ -m-1} K`.
* `CochainComplex.isColimitStupidTruncGESequenceCocone K`: `K` is the colimit of this sequence.
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

/-- The inverse of the canonical identification of a retained term of the brutal truncation
factors through restriction and extension along the degree embedding. -/
private lemma stupidTruncXIso_embeddingUpIntLE_inv {i : ℤ} (hi : i ≤ n) :
    (K.stupidTruncXIso (ComplexShape.embeddingUpIntLE n)
      (i := (n - i).natAbs) (i' := i) (by
        simp [Int.natAbs_of_nonneg (sub_nonneg.mpr hi)])).inv =
      (K.restrictionXIso (ComplexShape.embeddingUpIntLE n)
        (i := (n - i).natAbs) (i' := i) (by
          simp [Int.natAbs_of_nonneg (sub_nonneg.mpr hi)])).inv ≫
      ((K.restriction (ComplexShape.embeddingUpIntLE n)).extendXIso
        (ComplexShape.embeddingUpIntLE n) (i := (n - i).natAbs) (i' := i) (by
          simp [Int.natAbs_of_nonneg (sub_nonneg.mpr hi)])).inv := by
  simp only [stupidTruncXIso, restrictionXIso, eqToIso.inv]
  rfl

/-- In a retained degree, the projection is the inverse of the canonical identification with
the original complex. -/
@[simp]
lemma πStupidTruncLE_f {i : ℤ} (hi : i ≤ n) :
    (K.πStupidTruncLE n).f i =
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntLE n)
        (i := (n - i).natAbs) (i' := i) (by
          simp [Int.natAbs_of_nonneg (sub_nonneg.mpr hi)])).inv := by
  refine (ComplexShape.Embedding.liftExtend_f _ _ _ (i := (n - i).natAbs)
    (by simp [Int.natAbs_of_nonneg (sub_nonneg.mpr hi)])).trans ?_
  simp only [HomologicalComplex.id_f, Category.id_comp]
  rw [← K.stupidTruncXIso_embeddingUpIntLE_inv n hi]

/-- The brutal truncation in degrees `≤ n` vanishes in degrees `> n`. -/
lemma isZero_stupidTrunc_embeddingUpIntLE_X {i : ℤ} (hi : n < i) :
    IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntLE n)).X i) :=
  K.isZero_stupidTrunc_X _ i ((ComplexShape.notMem_range_embeddingUpIntLE_iff n i).2 hi)

/-- In a degree above the truncation bound, the projection is zero. -/
@[simp]
lemma πStupidTruncLE_f_of_lt {i : ℤ} (hi : n < i) : (K.πStupidTruncLE n).f i = 0 :=
  (K.isZero_stupidTrunc_embeddingUpIntLE_X n hi).eq_of_tgt _ _

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

/-- Away from the top degree, the inclusion of the top term is zero. -/
@[simp]
lemma ιTop_f_of_ne {i : ℤ} (hi : i ≠ n) : (K.ιTop n).f i = 0 :=
  (isZero_single_obj_X (.up ℤ) _ _ _ hi).eq_of_src _ _

end HasZeroMorphisms

section Preadditive

variable [Preadditive C] [HasZeroObject C] (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyLE (n + 1)]

/-- The inclusion of the top term followed by the projection onto the brutal truncation below it
is zero. -/
@[reassoc (attr := simp)]
lemma ιTop_comp_πStupidTruncLE : K.ιTop (n + 1) ≫ K.πStupidTruncLE n = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
  by_cases hi : i = n + 1
  · subst hi
    exact (K.isZero_stupidTrunc_embeddingUpIntLE_X n (by omega)).eq_of_tgt _ _
  · exact (isZero_single_obj_X (.up ℤ) _ _ _ hi).eq_of_src _ _

/-- The short complex splitting off the top term of a cochain complex `K` vanishing in degrees
`> n + 1`: the top term in degree `n + 1`, then `K`, then the brutal truncation of `K` in degrees
`≤ n`. -/
noncomputable def topShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (K.ιTop (n + 1)) (K.πStupidTruncLE n) (K.ιTop_comp_πStupidTruncLE n)

/-- The short complex splitting off the top term is formed by the inclusion of the top term and
the projection onto the brutal truncation below it. -/
lemma topShortComplex_eq :
    K.topShortComplex n =
      ShortComplex.mk (K.ιTop (n + 1)) (K.πStupidTruncLE n) (K.ιTop_comp_πStupidTruncLE n) := by
  simp [topShortComplex]

/-- The first term of the short complex splitting off the top term is the top term placed in
degree `n + 1`. -/
@[simp]
lemma topShortComplex_X₁ :
    (K.topShortComplex n).X₁ = (single C (.up ℤ) (n + 1)).obj (K.X (n + 1)) := by
  simp [topShortComplex]

/-- The middle term of the short complex splitting off the top term is the complex itself. -/
@[simp]
lemma topShortComplex_X₂ : (K.topShortComplex n).X₂ = K := by
  simp [topShortComplex]

/-- The last term of the short complex splitting off the top term is the brutal truncation in
degrees `≤ n`. -/
@[simp]
lemma topShortComplex_X₃ :
    (K.topShortComplex n).X₃ = K.stupidTrunc (ComplexShape.embeddingUpIntLE n) := by
  simp [topShortComplex]

/-- The first map of the short complex splitting off the top term is the top-term inclusion. -/
@[simp]
lemma topShortComplex_f : HEq (K.topShortComplex n).f (K.ιTop (n + 1)) := by
  dsimp [topShortComplex]
  rfl

/-- The second map of the short complex splitting off the top term is the truncation projection. -/
@[simp]
lemma topShortComplex_g : HEq (K.topShortComplex n).g (K.πStupidTruncLE n) := by
  dsimp [topShortComplex]
  rfl

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

section Abelian

variable [Abelian C] (K : CochainComplex C ℤ) (n : ℤ)

/-- In degrees `≤ n`, the inclusion of the kernel of `K ⟶ σ^{≤ n} K` vanishes. -/
@[simp]
lemma kernel_ι_πStupidTruncLE_f_eq_zero {i : ℤ} (hi : i ≤ n) :
    (kernel.ι (K.πStupidTruncLE n)).f i = 0 := by
  have := K.isIso_πStupidTruncLE_f n hi
  rw [← cancel_mono ((K.πStupidTruncLE n).f i), zero_comp, ← comp_f, kernel.condition, zero_f]

/-- The kernel of `K ⟶ σ^{≤ n} K` vanishes in degrees `≤ n`. -/
lemma isZero_kernel_πStupidTruncLE_X {i : ℤ} (hi : i ≤ n) :
    IsZero ((kernel (K.πStupidTruncLE n)).X i) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_mono ((kernel.ι (K.πStupidTruncLE n)).f i),
    K.kernel_ι_πStupidTruncLE_f_eq_zero n hi, comp_zero, zero_comp]

/-- In degrees `> n`, the kernel of `K ⟶ σ^{≤ n} K` is the term of `K`. -/
lemma isIso_kernel_ι_πStupidTruncLE_f {i : ℤ} (hi : n < i) :
    IsIso ((kernel.ι (K.πStupidTruncLE n)).f i) :=
  KernelFork.IsLimit.isIso_ι _ (KernelFork.mapIsLimit _ (kernelIsKernel _) (eval C (.up ℤ) i))
    (K.πStupidTruncLE_f_of_lt n hi)

/-- The kernel of `K ⟶ σ^{≤ n} K` is a subcomplex of `K`, so it vanishes wherever `K` does. -/
instance (b : ℤ) [K.IsStrictlyLE b] : (kernel (K.πStupidTruncLE n)).IsStrictlyLE b :=
  (isStrictlyLE_iff _ _).2 fun i hi ↦ by
    rw [IsZero.iff_id_eq_zero, ← cancel_mono ((kernel.ι (K.πStupidTruncLE n)).f i)]
    exact (K.isZero_of_isStrictlyLE b i hi).eq_of_tgt _ _

/-- The sequence `σ^{≥ 0} K ⟶ σ^{≥ -1} K ⟶ ⋯` of brutal truncations of `K`. Its `m`-th term is
the kernel of `K ⟶ σ^{≤ -m-1} K`, the subcomplex of the terms of `K` in degrees `≥ -m`. -/
@[simps obj]
noncomputable abbrev stupidTruncGESequence : ℕ ⥤ CochainComplex C ℤ where
  obj m := kernel (K.πStupidTruncLE (-(m : ℤ) - 1))
  map {m m'} φ := kernel.lift _ (kernel.ι _) <| by
    ext i
    rw [comp_f, zero_f]
    by_cases hi : i ≤ -(m : ℤ) - 1
    · rw [K.kernel_ι_πStupidTruncLE_f_eq_zero _ hi, zero_comp]
    · have := leOfHom φ
      rw [K.πStupidTruncLE_f_of_lt _ (by omega), comp_zero]
  map_id m := by
    rw [← cancel_mono (kernel.ι _), kernel.lift_ι, Category.id_comp]
  map_comp φ ψ := by
    rw [← cancel_mono (kernel.ι _), kernel.lift_ι, Category.assoc, kernel.lift_ι, kernel.lift_ι]

/-- The transition maps of the sequence of brutal truncations are compatible with the
inclusions into `K`. -/
@[reassoc]
lemma stupidTruncGESequence_map_comp_ι {m m' : ℕ} (φ : m ⟶ m') :
    K.stupidTruncGESequence.map φ ≫ kernel.ι (K.πStupidTruncLE (-(m' : ℤ) - 1)) =
      kernel.ι (K.πStupidTruncLE (-(m : ℤ) - 1)) :=
  kernel.lift_ι _ _ _

/-- The inclusions `σ^{≥ -m} K ⟶ K` form a cocone over the sequence of brutal truncations. -/
@[simps pt]
noncomputable abbrev stupidTruncGESequenceCocone : Cocone K.stupidTruncGESequence where
  pt := K
  ι :=
    { app m := kernel.ι (K.πStupidTruncLE (-(m : ℤ) - 1))
      naturality _ _ φ := (K.stupidTruncGESequence_map_comp_ι φ).trans (Category.comp_id _).symm }

/-- The legs of the cocone of brutal truncations are the inclusions into `K`. -/
@[simp]
lemma stupidTruncGESequenceCocone_ι_app (m : ℕ) :
    K.stupidTruncGESequenceCocone.ι.app m = kernel.ι (K.πStupidTruncLE (-(m : ℤ) - 1)) := (rfl)

/-- A cochain complex is the colimit of its brutal truncations `σ^{≥ -m} K`: in degree `i` the
inclusions are isomorphisms as soon as `-m ≤ i`. -/
noncomputable def isColimitStupidTruncGESequenceCocone :
    IsColimit K.stupidTruncGESequenceCocone :=
  isColimitOfEval _ _ fun i ↦ by
    have hι (m : ℕ) (hm : i.natAbs ≤ m) :
        IsIso ((kernel.ι (K.πStupidTruncLE (-(m : ℤ) - 1))).f i) :=
      K.isIso_kernel_ι_πStupidTruncLE_f _ (by omega)
    -- from degree `|i|` on, the sequence is constant in degree `i`
    have h : (K.stupidTruncGESequence ⋙ eval C _ i).IsEventuallyConstantFrom i.natAbs :=
      fun m φ ↦ by
        have := hι _ le_rfl
        have := hι m (leOfHom φ)
        have w : (K.stupidTruncGESequence.map φ).f i ≫
            (kernel.ι (K.πStupidTruncLE (-(m : ℤ) - 1))).f i =
              (kernel.ι (K.πStupidTruncLE (-(i.natAbs : ℤ) - 1))).f i := by
          rw [← comp_f, stupidTruncGESequence_map_comp_ι]
        exact IsIso.of_isIso_fac_right w
    have : IsIso (((eval C _ i).mapCocone K.stupidTruncGESequenceCocone).ι.app i.natAbs) :=
      hι _ le_rfl
    exact h.isColimitOfIsIso _

end Abelian

end CochainComplex
