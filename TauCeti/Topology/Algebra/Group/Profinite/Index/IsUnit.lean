/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Nilpotent.NatCast
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex
public import TauCeti.Topology.Algebra.Group.Profinite.Order
import Mathlib.Data.Nat.Factorial.NatCast

/-!
# Indices of open subgroups of pro-order prime to `ℓ` are units

Let `K` be a compact group, such as a profinite group, and `ℓ` a prime whose exponent in the
supernatural order `profiniteOrder K` is zero. Every open subgroup `U` of `K` has finite index, and
that index divides the order of the finite continuous quotient `K ⧸ N` by the normal core `N` of
`U`, so it is prime to `ℓ`. Consequently, for a commutative ring `Λ` in which `ℓ` is nilpotent
(that is, `ℓ ^ m Λ = 0` for some `m`, an `ℓ`-power-torsion ring), the index of every open subgroup
is a unit of `Λ`. The same holds for the relative index `[L : U]` of `U` in any subgroup
`L ⊇ U`, which divides `[K : U]`. For an open normal subgroup the index is the order
`Nat.card (K ⧸ U)` of the finite quotient (`Subgroup.index_eq_card`).

Over a nonzero commutative ring in which `ℓ` is nilpotent the converse also holds: if every open
subgroup has invertible index, then `ℓ` has exponent zero in the supernatural order.

These are the normalising constants of finite-level averaging with coefficients in `Λ`: the
normalised Haar measure on `K` gives a coset of an open subgroup `U` the volume `[K : U]⁻¹`.

## Main results

* `TauCeti.profiniteOrder_apply_eq_zero_iff_forall_openSubgroup`: `ℓ` has exponent zero in the
  supernatural order of a compact group exactly when it divides the index of no open subgroup.
* `OpenSubgroup.not_dvd_relIndex_of_profiniteOrder_apply_eq_zero`: the same for the relative index
  of an open subgroup in an overgroup.
* `OpenSubgroup.isUnit_index_of_profiniteOrder_apply_eq_zero` and
  `OpenSubgroup.isUnit_relIndex_of_profiniteOrder_apply_eq_zero`: these indices are units of every
  commutative ring in which `ℓ` is nilpotent.
* `TauCeti.profiniteOrder_apply_eq_zero_iff_forall_isUnit_index`: over a nonzero commutative ring
  in which `ℓ` is nilpotent, the indices of all open subgroups are units exactly when `ℓ` has
  exponent zero.

## References

* P. Scholze, *Étale cohomology of diamonds*, Proposition 24.2 and its proof.
-/

public section

namespace TauCeti

variable {K : Type*} [Group K] [TopologicalSpace K] [SeparatelyContinuousMul K] [CompactSpace K]
  {ℓ : Nat.Primes}

/-- A prime `ℓ` has exponent zero in the supernatural order of a compact group exactly when it
divides the index of no open subgroup. -/
theorem profiniteOrder_apply_eq_zero_iff_forall_openSubgroup :
    profiniteOrder K ℓ = 0 ↔ ∀ U : OpenSubgroup K, ¬ (ℓ : ℕ) ∣ U.toSubgroup.index := by
  rw [profiniteOrder_apply_eq_zero_iff]
  refine ⟨fun h U hdvd ↦ ?_, fun h N ↦ h N.toOpenSubgroup⟩
  obtain ⟨N, hNU, -⟩ := U.exists_openNormalSubgroup_le
  exact h N (hdvd.trans (Subgroup.index_dvd_of_le hNU))

/-- If a prime `ℓ` has exponent zero in the supernatural order of a compact group, it does not
divide the relative index of an open subgroup `U` in any subgroup containing `U`. -/
theorem _root_.OpenSubgroup.not_dvd_relIndex_of_profiniteOrder_apply_eq_zero (U : OpenSubgroup K)
    (h : profiniteOrder K ℓ = 0) {L : Subgroup K} (hUL : U.toSubgroup ≤ L) :
    ¬ (ℓ : ℕ) ∣ U.toSubgroup.relIndex L := fun hdvd ↦
  profiniteOrder_apply_eq_zero_iff_forall_openSubgroup.mp h U
    (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hUL))

variable {Λ : Type*} [CommRing Λ]

/-- **Indices of open subgroups of pro-order prime to `ℓ` are units.** If a prime `ℓ` has exponent
zero in the supernatural order of a compact group `K` and `ℓ` is nilpotent in `Λ`, the index of
every open subgroup of `K` is a unit of `Λ`. -/
theorem _root_.OpenSubgroup.isUnit_index_of_profiniteOrder_apply_eq_zero (U : OpenSubgroup K)
    (h : profiniteOrder K ℓ = 0) (hΛ : IsNilpotent ((ℓ : ℕ) : Λ)) :
    IsUnit (U.toSubgroup.index : Λ) :=
  IsUnit.natCast_of_isNilpotent_of_coprime hΛ
    (ℓ.prop.coprime_iff_not_dvd.mpr (profiniteOrder_apply_eq_zero_iff_forall_openSubgroup.mp h U))

/-- If a prime `ℓ` has exponent zero in the supernatural order of a compact group `K` and `ℓ` is
nilpotent in `Λ`, the relative index of an open subgroup `U` in any subgroup containing `U` is a
unit of `Λ`. -/
theorem _root_.OpenSubgroup.isUnit_relIndex_of_profiniteOrder_apply_eq_zero (U : OpenSubgroup K)
    (h : profiniteOrder K ℓ = 0) (hΛ : IsNilpotent ((ℓ : ℕ) : Λ)) {L : Subgroup K}
    (hUL : U.toSubgroup ≤ L) : IsUnit (U.toSubgroup.relIndex L : Λ) :=
  IsUnit.natCast_of_isNilpotent_of_coprime hΛ
    (ℓ.prop.coprime_iff_not_dvd.mpr (U.not_dvd_relIndex_of_profiniteOrder_apply_eq_zero h hUL))

/-- Over a nonzero commutative ring `Λ` in which a prime `ℓ` is nilpotent, the indices of all open
subgroups of a compact group `K` are units of `Λ` exactly when `ℓ` has exponent zero in the
supernatural order of `K`. -/
theorem profiniteOrder_apply_eq_zero_iff_forall_isUnit_index [Nontrivial Λ]
    (hΛ : IsNilpotent ((ℓ : ℕ) : Λ)) :
    profiniteOrder K ℓ = 0 ↔ ∀ U : OpenSubgroup K, IsUnit (U.toSubgroup.index : Λ) := by
  simp only [hΛ.isUnit_natCast_iff_not_dvd ℓ.prop]
  exact profiniteOrder_apply_eq_zero_iff_forall_openSubgroup

end TauCeti
