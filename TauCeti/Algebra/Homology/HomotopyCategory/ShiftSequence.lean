/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Exactness and cycles of shifted cochain complexes

The shift `K⟦n⟧` of a cochain complex `K` has `K.X (i + n)` in degree `i` and differential
`(-1)ⁿ • d`. Mathlib identifies the short complex of `K⟦n⟧` in degree `i` with the short complex of
`K` in degree `n + i` (`CochainComplex.shiftShortComplexFunctorIso`). This file records the two
consequences used for degreewise arguments: exactness at `i` of `K⟦n⟧` is exactness at `n + i` of
`K`, so that shifting preserves and reflects acyclicity, and the cycles of `K⟦n⟧` in degree `i`
are the cycles of `K` in degree `n + i`.

## Main results

* `CochainComplex.exactAt_shift_iff`: `K⟦n⟧` is exact at `i` iff `K` is exact at `n + i`.
* `CochainComplex.acyclic_shift_iff`: `K⟦n⟧` is acyclic iff `K` is.
* `CochainComplex.shiftCyclesIso`: the isomorphism `(K⟦n⟧).cycles i ≅ K.cycles (n + i)`.
-/

public section

open CategoryTheory

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C] (K : CochainComplex C ℤ)

/-- The shift `K⟦n⟧` is exact in degree `i` exactly when `K` is exact in degree `i' = n + i`. -/
lemma exactAt_shift_iff (n i i' : ℤ) (hi : n + i = i') :
    (K⟦n⟧).ExactAt i ↔ K.ExactAt i' :=
  ShortComplex.exact_iff_of_iso ((shiftShortComplexFunctorIso C n i i' hi).app K)

/-- A shift of a cochain complex is acyclic exactly when the complex is. -/
@[simp]
lemma acyclic_shift_iff (n : ℤ) : (K⟦n⟧).Acyclic ↔ K.Acyclic :=
  ⟨fun h i ↦ (K.exactAt_shift_iff n (i - n) i (by lia)).1 (h _),
    fun h i ↦ (K.exactAt_shift_iff n i (n + i) rfl).2 (h _)⟩

variable [CategoryWithHomology C]

/-- The cycles of `K⟦n⟧` in degree `i` are the cycles of `K` in degree `i' = n + i`. -/
noncomputable def shiftCyclesIso (n i i' : ℤ) (hi : n + i = i') :
    (K⟦n⟧).cycles i ≅ K.cycles i' :=
  ShortComplex.cyclesMapIso ((shiftShortComplexFunctorIso C n i i' hi).app K)

/-- The isomorphism `CochainComplex.shiftCyclesIso` commutes with the inclusions of the cycles,
up to the identification `(K⟦n⟧).X i = K.X (i + n)`. -/
@[reassoc (attr := simp)]
lemma shiftCyclesIso_hom_iCycles (n i i' : ℤ) (hi : n + i = i') :
    (K.shiftCyclesIso n i i' hi).hom ≫ K.iCycles i' =
      (K⟦n⟧).iCycles i ≫ (K.shiftFunctorObjXIso n i i' (by lia)).hom := by
  refine (ShortComplex.cyclesMap_i ((shiftShortComplexFunctorIso C n i i' hi).hom.app K)).trans ?_
  simp [shiftShortComplexFunctorIso]
  -- `CategoryTheory.shiftFunctor` on cochain complexes is `CochainComplex.shiftFunctor`, and
  -- `HomologicalComplex.iCycles` is the inclusion of the cycles of `HomologicalComplex.sc`.
  rfl

end CochainComplex
