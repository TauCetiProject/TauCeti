/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AbsoluteValue.Place
public import TauCeti.NumberTheory.NumberField.PlacesOver.InfinitePlace.Basic
public import TauCeti.NumberTheory.NumberField.PlacesOver.Relative

import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.NumberTheory.NumberField.Global.Places.Rat
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic
import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace

/-!
# Places as normalised absolute values, compared with infinite and finite places

A place of a field `L` of characteristic zero is a `ℚ`-normalised absolute value
(`AbsoluteValue.Place L`). This file compares the places with Mathlib's two types of places.

* **Infinite places.** For any field `L` of characteristic zero, the infinite places of `L`
  (`¬ IsNonarchimedean w`) are exactly the underlying absolute values of Mathlib's
  `NumberField.InfinitePlace L`: every infinite place of `L` restricts to the real absolute value
  on `ℚ` (`NumberField.InfinitePlace.under_rat`), and an absolute value of `L` lying over the real
  absolute value of `ℚ` is an infinite place of `L` (Tau Ceti's
  `NumberField.isInfinitePlace_iff_of_liesOver`). This gives the bijection
  `AbsoluteValue.Place.infinitePlaceEquiv`.
* **Finite places.** For a number field `K`, Mathlib's `NumberField.FinitePlace K` is normalised by
  the absolute norm of its prime, not on `ℚ`. Its local-degree root over `ℚ`
  (`NumberField.FinitePlace.relativeAbsValue`) is a place (`NumberField.FinitePlace.toPlace`), and
  every finite place of `K` arises in this way from exactly one finite place of `K`
  (`AbsoluteValue.Place.finitePlaceEquiv`), by the classification of the absolute values over a
  finite place of `ℚ` (`NumberField.existsUnique_finitePlace_rpow_inv_eq_of_liesOver`).

## Main definitions

* `NumberField.InfinitePlace.toPlace`, `NumberField.FinitePlace.toPlace`: the place attached to an
  infinite or a finite place.
* `AbsoluteValue.Place.infinitePlaceEquiv`: the infinite places of a field `L` of characteristic
  zero correspond to `NumberField.InfinitePlace L`.
* `AbsoluteValue.Place.finitePlaceEquiv`: the finite places of a number field `K` correspond to
  `NumberField.FinitePlace K`.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Ch. II, §§3 and 8.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3.
-/

public section

open AbsoluteValue IsDedekindDomain Rat.HeightOneSpectrum

open scoped NumberField

namespace NumberField

/-! ### Infinite places -/

namespace InfinitePlace

variable {L : Type*} [Field L] [CharZero L]

/-- The place underlying an infinite place. -/
def toPlace (v : InfinitePlace L) : Place L :=
  ⟨v.val, by rw [under_rat]; exact .real⟩

@[simp]
theorem val_toPlace (v : InfinitePlace L) : v.toPlace.val = v.val := (rfl)

theorem toPlace_injective : Function.Injective (toPlace : InfinitePlace L → Place L) :=
  fun _ _ h ↦ Subtype.ext <| by rw [← Place.val_inj, val_toPlace, val_toPlace] at h; exact h

/-- The place underlying an infinite place is archimedean. -/
theorem not_isNonarchimedean_toPlace (v : InfinitePlace L) : ¬ IsNonarchimedean v.toPlace.val :=
  v.not_isNonarchimedean

end InfinitePlace

namespace _root_.AbsoluteValue.Place

variable {L : Type*} [Field L] [CharZero L]

/-- A place of `L` is an infinite place of `L` exactly when it is archimedean. -/
theorem isInfinitePlace_iff (w : Place L) : IsInfinitePlace w.val ↔ ¬ IsNonarchimedean w.val := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨v, hv⟩ := (NumberField.isInfinitePlace_iff w.val).mp h
    exact hv ▸ v.not_isNonarchimedean
  · have hreal : Rat.infinitePlace.val = Rat.AbsoluteValue.real := by
      ext q
      rw [← InfinitePlace.coe_apply, Rat.infinitePlace_apply, Rat.AbsoluteValue.real_eq_abs,
        Rat.cast_abs]
    rw [isInfinitePlace_iff_of_liesOver (w.val.under ℚ) w.val, w.not_isNonarchimedean_iff.mp h,
      ← hreal]
    exact Rat.infinitePlace.isInfinitePlace

variable (L) in
/-- **Infinite places.** The archimedean places of a field `L` of characteristic zero correspond
to Mathlib's infinite places of `L`, with the same underlying absolute values. -/
noncomputable def infinitePlaceEquiv :
    {w : Place L // ¬ IsNonarchimedean w.val} ≃ InfinitePlace L where
  toFun w := ⟨w.val.val, (isInfinitePlace_iff w.val).mpr w.property⟩
  invFun v := ⟨v.toPlace, v.not_isNonarchimedean_toPlace⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem val_infinitePlaceEquiv_apply (w : {w : Place L // ¬ IsNonarchimedean w.val}) :
    (infinitePlaceEquiv L w).val = w.val.val := (rfl)

@[simp]
theorem infinitePlaceEquiv_symm_apply (v : InfinitePlace L) :
    ((infinitePlaceEquiv L).symm v).val = v.toPlace := (rfl)

end _root_.AbsoluteValue.Place

/-- Mathlib's action of the Galois group on the infinite places agrees with the action on
places. -/
@[simp]
theorem InfinitePlace.toPlace_smul {k L : Type*} [Field k] [Field L] [CharZero L] [Algebra k L]
    (σ : L ≃ₐ[k] L) (v : InfinitePlace L) : (σ • v).toPlace = σ • v.toPlace :=
  Place.val_injective <| AbsoluteValue.ext fun x ↦ by
    simp [← coe_apply, AlgEquiv.smul_def, AlgEquiv.aut_inv]

/-! ### Finite places -/

namespace FinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-- The local-degree root over `ℚ` of a finite place restricts to a `p`-adic absolute value on
`ℚ`. -/
theorem isStandard_under_relativeAbsValue (v : FinitePlace K) :
    Rat.AbsoluteValue.IsStandard ((v.relativeAbsValue ℚ).under ℚ) := by
  have : Fact (primesEquiv (v.under ℚ).maximalIdeal : ℕ).Prime :=
    ⟨(primesEquiv (v.under ℚ).maximalIdeal).property⟩
  rw [LiesOver.under_eq (v.relativeAbsValue ℚ) (v.under ℚ).val, val_eq_padic]
  exact .padic _

/-- The place attached to a finite place `v` of a number field: its local-degree root over `ℚ`,
`x ↦ v x ^ (e * f)⁻¹`, which restricts to a `p`-adic absolute value on `ℚ`. -/
noncomputable def toPlace (v : FinitePlace K) : Place K :=
  ⟨v.relativeAbsValue ℚ, v.isStandard_under_relativeAbsValue⟩

@[simp]
theorem val_toPlace (v : FinitePlace K) : v.toPlace.val = v.relativeAbsValue ℚ := (rfl)

/-- The place attached to a finite place is equivalent to it. -/
theorem isEquiv_toPlace (v : FinitePlace K) : v.val.IsEquiv v.toPlace.val :=
  v.isEquiv_relativeAbsValue

/-- The place attached to a finite place is nonarchimedean. -/
theorem isNonarchimedean_toPlace (v : FinitePlace K) : IsNonarchimedean v.toPlace.val :=
  (isNonarchimedean_iff_of_liesOver (v.relativeAbsValue ℚ) (v.under ℚ).val).mpr (v.under ℚ).add_le

theorem toPlace_injective : Function.Injective (toPlace : FinitePlace K → Place K) :=
  fun _ _ h ↦ relativeAbsValue_injective (congrArg Subtype.val h)

/-- Every nonarchimedean place of a number field is the place attached to a finite place. -/
theorem exists_toPlace_eq {w : Place K} (hw : IsNonarchimedean w.val) :
    ∃ v : FinitePlace K, v.toPlace = w := by
  obtain ⟨p, _, hp⟩ := w.isNonarchimedean_iff.mp hw
  let 𝔭 := (primesEquiv (R := 𝓞 ℚ)).symm ⟨p, Fact.out⟩
  have : w.val.LiesOver (FinitePlace.mk 𝔭).val :=
    ⟨hp.trans (Nat.Primes.finitePlace_mk_val_eq_padic ⟨p, Fact.out⟩).symm⟩
  obtain ⟨𝔓, -, h𝔓⟩ :=
    (existsUnique_finitePlace_rpow_inv_eq_of_liesOver (𝔭 := 𝔭) (w := w.val)).exists
  refine ⟨FinitePlace.mk 𝔓, Place.val_injective <| AbsoluteValue.ext fun y ↦ ?_⟩
  simp only [val_toPlace, relativeAbsValue_apply, localDegree_def, maximalIdeal_mk, Nat.cast_mul,
    h𝔓]

end FinitePlace

namespace _root_.AbsoluteValue.Place

variable (K : Type*) [Field K] [NumberField K]

/-- **Finite places.** The nonarchimedean places of a number field `K` correspond to Mathlib's
finite places of `K`. A finite place `v` corresponds to its local-degree root over `ℚ`,
`NumberField.FinitePlace.toPlace v`, which differs from `v` unless `v` has local degree one over
`ℚ`. -/
noncomputable def finitePlaceEquiv : {w : Place K // IsNonarchimedean w.val} ≃ FinitePlace K :=
  .symm <| .ofBijective (fun v ↦ ⟨v.toPlace, v.isNonarchimedean_toPlace⟩)
    ⟨fun _ _ h ↦ FinitePlace.toPlace_injective (congrArg Subtype.val h),
      fun w ↦ (FinitePlace.exists_toPlace_eq w.property).imp fun _ h ↦ Subtype.ext h⟩

@[simp]
theorem toPlace_finitePlaceEquiv (w : {w : Place K // IsNonarchimedean w.val}) :
    (finitePlaceEquiv K w).toPlace = w.val :=
  congrArg Subtype.val ((finitePlaceEquiv K).symm_apply_apply w)

@[simp]
theorem finitePlaceEquiv_symm_apply (v : FinitePlace K) :
    ((finitePlaceEquiv K).symm v).val = v.toPlace := (rfl)

end _root_.AbsoluteValue.Place

end NumberField
