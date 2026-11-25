/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Pi
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced
import TauCeti.Algebra.Algebra.Pi

/-!
# The root pairing of type `A₁`

This file base changes the pinned root datum of `SL₂`, `typeASimplyConnectedRootDatum 1`, to a
commutative ring `R` of characteristic zero. Its two roots `±(e₀ - e₁)` are indexed by the
ordered pairs `(0, 1)` and `(1, 0)` of distinct elements of `Fin 2`. Both the root and the coroot
spaces are `Fin 1 → R`, in which the root `e_a - e_b` is `±2` and its coroot is `±1`, with the
sign `+` for `a = 0`.

## Main definitions

* `TauCeti.DynkinType.sl2RootPairing`: the root pairing of type `A₁` over `R`.

## Main results

* `TauCeti.DynkinType.typeAIndex_one_eq_or_eq`: the two roots are indexed by `(0, 1)` and
  `(1, 0)`.
* `TauCeti.DynkinType.sl2RootPairing_root`, `sl2RootPairing_coroot` and
  `sl2RootPairing_pairing`: the roots `±2`, coroots `±1` and Cartan integers `±2`.
* The pairing is crystallographic, reduced over a domain, and a root system when `2` is
  invertible.
* `TauCeti.DynkinType.sl2RootPairing_eq_or_eq_reflectionPerm_self`: any two roots are equal or
  opposite.
-/

public section

namespace TauCeti.DynkinType

/-- The two roots of type `A₁` are indexed by the ordered pairs `(0, 1)` and `(1, 0)`. -/
theorem typeAIndex_one_eq_or_eq (p : TypeAIndex 1) :
    p = ⟨(0, 1), by decide⟩ ∨ p = ⟨(1, 0), by decide⟩ := by
  revert p; decide

variable (R : Type*) [CommRing R] [CharZero R]

/-- The root pairing of type `A₁` over `R`: the pinned root datum of `SL₂`, whose two roots
`±(e₀ - e₁)` are indexed by the ordered pairs `(0, 1)` and `(1, 0)`, base changed to `R`. Both
lattices become `Fin 1 → R`; the root `e_a - e_b` is `±2` and its coroot `±1`. -/
noncomputable def sl2RootPairing : RootPairing (Fin (1 * (1 + 1))) R (Fin 1 → R) (Fin 1 → R) :=
  rootPairingBaseChange R (typeASimplyConnectedRootDatum 1)
    toLinearMap_typeASimplyConnectedRootDatum

/-- The root pairing of `SL₂` is the base change of the pinned root datum of `SL₂`. The body of
`sl2RootPairing` is not exposed to importing modules, so use this equation to apply results on
base-changed pairings to it. -/
theorem sl2RootPairing_def :
    sl2RootPairing R = rootPairingBaseChange R (typeASimplyConnectedRootDatum 1)
      toLinearMap_typeASimplyConnectedRootDatum :=
  (rfl)

instance instIsCrystallographicSl2RootPairing : (sl2RootPairing R).IsCrystallographic :=
  isCrystallographic_rootPairingBaseChange ..

instance instIsReducedSl2RootPairing [IsDomain R] : (sl2RootPairing R).IsReduced :=
  isReduced_rootPairingBaseChange R _ _

variable {R}

/-- The pairing of the root pairing of `SL₂` is the dot product of `Fin 1 → R` with itself. -/
@[simp]
theorem sl2RootPairing_toLinearMap (x y : Fin 1 → R) :
    (sl2RootPairing R).toLinearMap x y = x ⬝ᵥ y :=
  toLinearMap_rootPairingBaseChange ..

/-- The reflection permutation of the root pairing of `SL₂` is that of the pinned root datum. -/
@[simp]
theorem sl2RootPairing_reflectionPerm :
    (sl2RootPairing R).reflectionPerm = (typeASimplyConnectedRootDatum 1).reflectionPerm :=
  reflectionPerm_rootPairingBaseChange ..

/-- The root `e_a - e_b` of `SL₂` is `2` if `a = 0`, and `-2` if `a = 1`. -/
@[simp]
theorem sl2RootPairing_root (k : Fin (1 * (1 + 1))) :
    (sl2RootPairing R).root k =
      fun _ ↦ if ((typeAIndexEquiv 1).symm k).val.1 = 0 then 2 else -2 := by
  obtain ⟨p, rfl⟩ := (typeAIndexEquiv 1).surjective k
  ext j
  rcases typeAIndex_one_eq_or_eq p with rfl | rfl <;>
    simp only [sl2RootPairing_def, root_rootPairingBaseChange, piAlgebraMap_apply,
      root_typeAIndexEquiv, Equiv.symm_apply_apply, Fin.fin_one_eq_zero j] <;> norm_num

/-- The coroot of `e_a - e_b` of `SL₂` is `1` if `a = 0`, and `-1` if `a = 1`. -/
@[simp]
theorem sl2RootPairing_coroot (k : Fin (1 * (1 + 1))) :
    (sl2RootPairing R).coroot k =
      fun _ ↦ if ((typeAIndexEquiv 1).symm k).val.1 = 0 then 1 else -1 := by
  obtain ⟨p, rfl⟩ := (typeAIndexEquiv 1).surjective k
  ext j
  rcases typeAIndex_one_eq_or_eq p with rfl | rfl <;>
    simp only [sl2RootPairing_def, coroot_rootPairingBaseChange, piAlgebraMap_apply,
      coroot_typeAIndexEquiv, Equiv.symm_apply_apply, Fin.fin_one_eq_zero j] <;> norm_num

/-- The root pairing of `SL₂` has Cartan integer `2` between equal roots and `-2` between
opposite ones. -/
@[simp]
theorem sl2RootPairing_pairing (k l : Fin (1 * (1 + 1))) :
    (sl2RootPairing R).pairing k l = if k = l then 2 else -2 := by
  rw [sl2RootPairing_def, pairing_rootPairingBaseChange]
  obtain ⟨p, rfl⟩ := (typeAIndexEquiv 1).surjective k
  obtain ⟨q, rfl⟩ := (typeAIndexEquiv 1).surjective l
  rcases typeAIndex_one_eq_or_eq p with rfl | rfl <;>
    rcases typeAIndex_one_eq_or_eq q with rfl | rfl <;>
    rw [pairing_typeAIndexEquiv] <;> simp [(typeAIndexEquiv 1).injective.eq_iff]

/-- Over a ring in which `2` is invertible, the roots `±2` of `SL₂` span `Fin 1 → R`, so the root
pairing of `SL₂` is a root system. -/
instance instIsRootSystemSl2RootPairing [Invertible (2 : R)] :
    (sl2RootPairing R).IsRootSystem where
  span_root_eq_top := by
    refine eq_top_iff.mpr fun v _ ↦ ?_
    have hv : v =
        (⅟2 * v 0) • (sl2RootPairing R).root (typeAIndexEquiv 1 ⟨(0, 1), by decide⟩) := by
      ext j
      rw [Fin.fin_one_eq_zero j, Pi.smul_apply, sl2RootPairing_root, Equiv.symm_apply_apply]
      simp only [smul_eq_mul, ite_true]
      linear_combination (-v 0) * invOf_mul_self (2 : R)
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  span_coroot_eq_top := by
    rw [sl2RootPairing_def]
    exact span_range_coroot_rootPairingBaseChange_eq_top R _ _
      (corootSpan_typeASimplyConnectedRootDatum_eq_top 1)

/-- The root `e_a - e_b` of `SL₂` takes the value `2 v` at `v` if `a = 0`, and `-2 v` if
`a = 1`. -/
theorem sl2RootPairing_root'_apply (k : Fin (1 * (1 + 1))) (v : Fin 1 → R) :
    (sl2RootPairing R).root' k v =
      (if ((typeAIndexEquiv 1).symm k).val.1 = 0 then 2 else -2) * v 0 := by
  obtain ⟨p, rfl⟩ := (typeAIndexEquiv 1).surjective k
  rcases typeAIndex_one_eq_or_eq p with rfl | rfl <;>
    simp only [sl2RootPairing_def, RootPairing.root', toLinearMap_rootPairingBaseChange,
      root_rootPairingBaseChange, dotProduct, Fin.sum_univ_one, piAlgebraMap_apply,
      root_typeAIndexEquiv, Equiv.symm_apply_apply] <;> norm_num

/-- The reflection in either root of `SL₂` sends each root `e_a - e_b` to `e_b - e_a`. -/
theorem typeAIndexEquiv_symm_sl2RootPairing_reflectionPerm (k l : Fin (1 * (1 + 1))) :
    ((typeAIndexEquiv 1).symm ((sl2RootPairing R).reflectionPerm k l)).val =
      (((typeAIndexEquiv 1).symm l).val.2, ((typeAIndexEquiv 1).symm l).val.1) := by
  obtain ⟨p, rfl⟩ := (typeAIndexEquiv 1).surjective k
  obtain ⟨q, rfl⟩ := (typeAIndexEquiv 1).surjective l
  rw [sl2RootPairing_def, reflectionPerm_rootPairingBaseChange, typeAIndexEquiv_symm_reflectionPerm,
    Equiv.symm_apply_apply]
  revert p q; decide

/-- Any two roots of `SL₂` are equal or opposite. -/
theorem sl2RootPairing_eq_or_eq_reflectionPerm_self (i j : Fin (1 * (1 + 1))) :
    j = i ∨ j = (sl2RootPairing R).reflectionPerm i i := by
  have h := typeAIndexEquiv_symm_sl2RootPairing_reflectionPerm (R := R) i i
  rw [← (typeAIndexEquiv 1).symm.injective.eq_iff, ← (typeAIndexEquiv 1).symm.injective.eq_iff,
    Subtype.ext_iff, Subtype.ext_iff, h]
  generalize (typeAIndexEquiv 1).symm i = p
  generalize (typeAIndexEquiv 1).symm j = q
  revert p q; decide


end TauCeti.DynkinType
