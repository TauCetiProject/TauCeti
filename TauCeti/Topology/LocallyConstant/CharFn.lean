/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Sets.Compacts

/-!
# Characteristic functions of clopen and compact open sets

The characteristic function `1_U` of a clopen set `U` is a locally constant function (Mathlib's
`LocallyConstant.charFn`). With values in a ring `R`, these functions are idempotents of the ring
`LocallyConstant X R` which multiply like the sets intersect: `1_U * 1_V = 1_(U ∩ V)`
(`LocallyConstant.charFn_mul_charFn`).

In a Hausdorff space `X` a compact open set `U` is clopen, so it has a characteristic function
`TopologicalSpace.CompactOpens.charFn`, with the same multiplicative API. For a locally profinite
set `X`, the idempotents `1_U` are the basic tool for studying modules over `LocallyConstant X R`:
for example, multiplication by `1_U` projects such a module onto its part supported on `U`.
-/

public section

namespace LocallyConstant

variable {X : Type*} [TopologicalSpace X] (R : Type*) [MulZeroOneClass R] {U V : Set X}

/-- Characteristic functions of clopen sets multiply like the sets intersect. -/
theorem charFn_mul_charFn (hU : IsClopen U) (hV : IsClopen V) :
    charFn R hU * charFn R hV = charFn R (hU.inter hV) :=
  coe_injective (by simp [coe_charFn, Set.inter_indicator_one])

/-- The characteristic function of a clopen set is an idempotent. -/
theorem isIdempotentElem_charFn (hU : IsClopen U) : IsIdempotentElem (charFn R hU) :=
  coe_injective (by rw [coe_mul, coe_charFn, ← Set.inter_indicator_one, Set.inter_self])

@[simp]
theorem charFn_empty : charFn R (isClopen_empty : IsClopen (∅ : Set X)) = 0 :=
  ext fun x => by simp [coe_charFn]

@[simp]
theorem charFn_univ : charFn R (isClopen_univ : IsClopen (Set.univ : Set X)) = 1 :=
  ext fun x => by simp [coe_charFn]

/-- Over a nontrivial ring, `1_U = 1` exactly when `U` is the whole space. -/
theorem charFn_eq_one_iff [Nontrivial R] (hU : IsClopen U) : charFn R hU = 1 ↔ U = Set.univ := by
  refine ⟨fun h => Set.eq_univ_of_forall fun x => (charFn_eq_one R x hU).1 ?_, fun h => ?_⟩
  · rw [h, one_apply]
  · subst h
    exact charFn_univ R

end LocallyConstant

namespace TopologicalSpace.CompactOpens

variable {X : Type*} [TopologicalSpace X] [T2Space X] (R : Type*) [MulZeroOneClass R]

/-- The characteristic function `1_U` of a compact open subset `U` of a Hausdorff space, as a
locally constant function: `U` is clopen. -/
noncomputable def charFn (U : CompactOpens X) : LocallyConstant X R :=
  LocallyConstant.charFn R U.toClopens.isClopen

theorem coe_charFn (U : CompactOpens X) : ⇑(U.charFn R) = Set.indicator (U : Set X) 1 :=
  (rfl)

/-- `U.charFn R` is the characteristic function of the clopen set underlying `U`. -/
theorem charFn_def (U : CompactOpens X) :
    U.charFn R = LocallyConstant.charFn R U.toClopens.isClopen :=
  (rfl)

variable {R}

@[simp]
theorem charFn_apply_of_mem {U : CompactOpens X} {x : X} (hx : x ∈ U) : U.charFn R x = 1 := by
  simp [coe_charFn, Set.indicator_of_mem (show x ∈ (U : Set X) from hx)]

@[simp]
theorem charFn_apply_of_notMem {U : CompactOpens X} {x : X} (hx : x ∉ U) : U.charFn R x = 0 := by
  simp [coe_charFn, Set.indicator_of_notMem (show x ∉ (U : Set X) from hx)]

variable (R)

/-- Characteristic functions multiply like the sets intersect. -/
theorem charFn_inf (U V : CompactOpens X) : (U ⊓ V).charFn R = U.charFn R * V.charFn R :=
  (LocallyConstant.charFn_mul_charFn R U.toClopens.isClopen V.toClopens.isClopen).symm

/-- If `U ⊆ V` then `1_U * 1_V = 1_U`. -/
theorem charFn_mul_charFn_of_le {U V : CompactOpens X} (h : U ≤ V) :
    U.charFn R * V.charFn R = U.charFn R := by
  rw [← charFn_inf, inf_eq_left.2 h]

/-- If `U ⊆ V` then `1_V * 1_U = 1_U`. -/
theorem charFn_mul_charFn_of_ge {U V : CompactOpens X} (h : U ≤ V) :
    V.charFn R * U.charFn R = U.charFn R := by
  rw [← charFn_inf, inf_eq_right.2 h]

/-- A characteristic function is an idempotent. -/
theorem isIdempotentElem_charFn (U : CompactOpens X) : IsIdempotentElem (U.charFn R) :=
  LocallyConstant.isIdempotentElem_charFn R U.toClopens.isClopen

@[simp]
theorem charFn_bot : (⊥ : CompactOpens X).charFn R = 0 :=
  LocallyConstant.charFn_empty R

@[simp]
theorem charFn_top [CompactSpace X] : (⊤ : CompactOpens X).charFn R = 1 :=
  LocallyConstant.charFn_univ R

/-- Over a nontrivial ring, `1_U = 1` exactly when `U` is the whole space. -/
theorem charFn_eq_one_iff [Nontrivial R] {U : CompactOpens X} :
    U.charFn R = 1 ↔ (U : Set X) = Set.univ :=
  LocallyConstant.charFn_eq_one_iff R U.toClopens.isClopen

end TopologicalSpace.CompactOpens
