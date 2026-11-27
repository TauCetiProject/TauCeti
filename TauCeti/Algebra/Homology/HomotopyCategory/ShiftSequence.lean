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
are the cycles of `K` in degree `n + i`. It also states the naturality of Mathlib's identification
`(K⟦n⟧).homology i ≅ K.homology (n + i)` in terms of `HomologicalComplex.homologyMap`.

## Main results

* `CochainComplex.exactAt_shift_iff`: `K⟦n⟧` is exact at `i` iff `K` is exact at `n + i`.
* `CochainComplex.acyclic_shift_iff`: `K⟦n⟧` is acyclic iff `K` is.
* `CochainComplex.shiftCyclesIso`: the isomorphism `(K⟦n⟧).cycles i ≅ K.cycles (n + i)`.
* `CochainComplex.homologyMap_shift_comp_homologyFunctor_shiftIso_hom_app`: naturality of
  `(K⟦n⟧).homology i ≅ K.homology (n + i)` in `K`.
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

/-- The isomorphism `CochainComplex.shiftCyclesIso` is the map on cycles induced by the
isomorphism of short complexes `shiftShortComplexFunctorIso`. -/
lemma shiftCyclesIso_hom (n i i' : ℤ) (hi : n + i = i') :
    (K.shiftCyclesIso n i i' hi).hom =
      ShortComplex.cyclesMap ((shiftShortComplexFunctorIso C n i i' hi).hom.app K) :=
  (rfl)

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

/-- The isomorphism `CochainComplex.shiftCyclesIso` is natural in the complex. -/
@[reassoc]
lemma shiftCyclesIso_hom_naturality {L : CochainComplex C ℤ} (φ : K ⟶ L) (n i i' : ℤ)
    (hi : n + i = i') :
    HomologicalComplex.cyclesMap (φ⟦n⟧') i ≫ (L.shiftCyclesIso n i i' hi).hom =
      (K.shiftCyclesIso n i i' hi).hom ≫ HomologicalComplex.cyclesMap φ i' := by
  rw [← cancel_mono (L.iCycles i')]
  obtain rfl : i' = i + n := by lia
  simp [CochainComplex.shiftFunctor_map_f']

/-- The identification `(K⟦n⟧).homology i ≅ K.homology i'` of the shift sequence of the homology
functor is natural in the complex. The shifted homology functor
`(homologyFunctor C (up ℤ) 0).shift i` is `homologyFunctor C (up ℤ) i`
(`CochainComplex.homologyFunctor_shift`), so this is
`CategoryTheory.Functor.shiftIso_hom_naturality` stated with `HomologicalComplex.homologyMap`. -/
@[reassoc]
lemma homologyMap_shift_comp_homologyFunctor_shiftIso_hom_app {L : CochainComplex C ℤ}
    (φ : K ⟶ L) (n i i' : ℤ) (hi : n + i = i') :
    HomologicalComplex.homologyMap (φ⟦n⟧') i ≫
        ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso n i i' hi).hom.app
          L =
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso n i i' hi).hom.app
          K ≫ HomologicalComplex.homologyMap φ i' :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso_hom_naturality n i i' hi φ

end CochainComplex
