/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.Single

/-!
# Quasi-isomorphisms and single complexes under opposition

Mathlib's `CochainComplex.opEquivalence` reverses the degrees. It preserves and reflects
quasi-isomorphisms and sends a complex supported in one degree to the corresponding complex
supported in the negative degree.
-/

public section

open CategoryTheory Opposite Limits HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- Opposition identifies quasi-isomorphisms in degree `-i` with those in degree `i`. -/
@[simp]
theorem quasiIsoAt_opEquivalence_map_iff [CategoryWithHomology C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (i : ℤ) :
    QuasiIsoAt ((opEquivalence C).functor.map f.op) i ↔ QuasiIsoAt f (-i) := by
  rw [quasiIsoAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp),
    quasiIsoAt_iff' _ (-(i + 1)) (-i) (-(i - 1)) (by simp; omega) (by simp; omega)]
  -- The first three-term complex is the opposite of the second with its terms reversed.
  exact ShortComplex.quasiIso_opMap_iff
    ((shortComplexFunctor' C _ (-(i + 1)) (-i) (-(i - 1))).map f)

/-- The opposite equivalence preserves and reflects quasi-isomorphisms. -/
@[simp]
theorem quasiIso_opEquivalence_map_iff [CategoryWithHomology C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    QuasiIso ((opEquivalence C).functor.map f.op) ↔ QuasiIso f := by
  simp only [quasiIso_iff, quasiIsoAt_opEquivalence_map_iff]
  exact (Equiv.neg ℤ).forall_congr (fun _ ↦ Iff.rfl)

/-- Under the opposite equivalence, a single complex in degree `n` becomes a single complex
on the opposite object in degree `-n`. -/
noncomputable def opEquivalenceSingleIso [HasZeroObject C] (n : ℤ) (X : C) :
    (opEquivalence C).functor.obj (op ((single C (ComplexShape.up ℤ) n).obj X)) ≅
      (single Cᵒᵖ (ComplexShape.up ℤ) (-n)).obj (op X) := by
  refine Hom.isoOfComponents (fun i ↦ ?_) ?_
  · by_cases h : i = -n
    · have hn : -i = n := by omega
      exact (singleObjXIsoOfEq _ n X (-i) hn).symm.op ≪≫
        (singleObjXIsoOfEq _ (-n) (op X) i h).symm
    · have hn : -i ≠ n := by omega
      exact (isZero_single_obj_X _ n X (-i) hn).op.iso
        (isZero_single_obj_X _ (-n) (op X) i h)
  · intro i j _
    simp [opEquivalence, ChainComplex.cochainComplexEquivalence]

end CochainComplex
