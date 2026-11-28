/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Units
public import TauCeti.NumberTheory.NumberField.Cyclotomic.InfinitePlace.Basic
import TauCeti.NumberTheory.Cyclotomic.Aut

/-!
# Reduction of cyclotomic labels of infinite places

In a tower of cyclotomic extensions with orders `m ∣ n`, restricting an infinite place to
the intermediate field reduces its label modulo `m`, provided the reference place is also
restricted. Thus congruence of labels can be read as equality of restricted places. This
applies in particular with `m` the prime-to-`p` part of `n`.

The labels have the convention of `New.Parameters.placeMulEquiv` and `New.Parameters.placeClass`
in `grh/src/New/Reduction/Data/FieldsAndPlaces.lean` of lsernau/grh-lean (`72fead1`): a label acts
on the reference embedding by precomposition with the corresponding cyclotomic automorphism.
-/

public section

namespace NumberField.InfinitePlace

open IsCyclotomicExtension Polynomial

variable {K F L : Type*} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [Subsingleton (InfinitePlace K)] {m n : ℕ}
  [IsCyclotomicExtension {m} K F] [IsCyclotomicExtension {n} K L]

/-- Restricting the place of label `a` in the `n`-th cyclotomic extension gives the place of
label `a mod m` in the `m`-th extension, relative to the restricted reference place. -/
theorem comap_equivUnitsZMod_symm_apply (w : InfinitePlace L) (hw : w.IsUnramified K)
    (hm : Irreducible (cyclotomic m K)) (hn : Irreducible (cyclotomic n K))
    (hmn : m ∣ n) (a : (ZMod n)ˣ) :
    ((w.equivUnitsZMod hw hn).symm a).comap (algebraMap F L) =
      ((w.comap (algebraMap F L)).equivUnitsZMod (hw.comap (K := F)) hm).symm
        (ZMod.unitsMap hmn a) := by
  let : NeZero m := ⟨by rintro rfl; simp at hm⟩
  let : NeZero n := ⟨by rintro rfl; simp at hn⟩
  simp only [equivUnitsZMod_symm_apply, smul_eq_comap, AlgEquiv.aut_inv, AlgEquiv.symm_symm,
    ← comap_comp]
  congr 1
  ext x
  exact (algebraMap_autEquivPow_symm_unitsMap_apply hm hn hmn a x).symm

/-- The label of a restricted infinite place is the reduction of its original label. -/
theorem equivUnitsZMod_comap (w : InfinitePlace L) (hw : w.IsUnramified K)
    (hm : Irreducible (cyclotomic m K)) (hn : Irreducible (cyclotomic n K))
    (hmn : m ∣ n) (v : InfinitePlace L) :
    (w.comap (algebraMap F L)).equivUnitsZMod (hw.comap (K := F)) hm
        (v.comap (algebraMap F L)) = ZMod.unitsMap hmn (w.equivUnitsZMod hw hn v) := by
  obtain ⟨a, rfl⟩ := (w.equivUnitsZMod hw hn).symm.surjective v
  simp only [w.comap_equivUnitsZMod_symm_apply hw hm hn hmn, Equiv.apply_symm_apply]

/-- Two infinite places restrict to the same intermediate place exactly when the quotient of
their labels is one modulo the intermediate cyclotomic order. -/
theorem comap_eq_comap_iff_unitsMap_div_eq_one (w : InfinitePlace L) (hw : w.IsUnramified K)
    (hm : Irreducible (cyclotomic m K)) (hn : Irreducible (cyclotomic n K))
    (hmn : m ∣ n) (u v : InfinitePlace L) :
    u.comap (algebraMap F L) = v.comap (algebraMap F L) ↔
      ZMod.unitsMap hmn (w.equivUnitsZMod hw hn u / w.equivUnitsZMod hw hn v) = 1 := by
  rw [← ((w.comap (algebraMap F L)).equivUnitsZMod (hw.comap (K := F)) hm).apply_eq_iff_eq,
    w.equivUnitsZMod_comap hw hm hn hmn, w.equivUnitsZMod_comap hw hm hn hmn, _root_.map_div,
    div_eq_one]

end NumberField.InfinitePlace
