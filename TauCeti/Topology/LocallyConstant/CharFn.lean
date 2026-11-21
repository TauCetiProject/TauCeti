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
# Characteristic functions of compact open sets

In a Hausdorff space `X` a compact open set `U` is clopen, so its characteristic function `1_U` is
a locally constant function (`TopologicalSpace.CompactOpens.charFn`). With values in a ring `R`,
these functions are idempotents of the ring `LocallyConstant X R` which multiply like the sets
intersect: `1_U * 1_V = 1_(U ∩ V)`. For a locally profinite set `X`, the idempotents `1_U` are the
basic tool for studying modules over `LocallyConstant X R`: for example, multiplication by `1_U`
projects such a module onto its part supported on `U`.
-/

public section

namespace TopologicalSpace.CompactOpens

variable {X : Type*} [TopologicalSpace X] [T2Space X] (R : Type*) [MulZeroOneClass R]

/-- The characteristic function `1_U` of a compact open subset `U` of a Hausdorff space, as a
locally constant function: `U` is clopen. -/
noncomputable def charFn (U : CompactOpens X) : LocallyConstant X R :=
  LocallyConstant.charFn R U.toClopens.isClopen

theorem coe_charFn (U : CompactOpens X) : ⇑(U.charFn R) = Set.indicator (U : Set X) 1 :=
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
  LocallyConstant.coe_injective (by simp [coe_charFn, Set.inter_indicator_one])

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
  charFn_mul_charFn_of_le R le_rfl

@[simp]
theorem charFn_bot : (⊥ : CompactOpens X).charFn R = 0 :=
  LocallyConstant.ext fun x => charFn_apply_of_notMem (Set.notMem_empty x)

@[simp]
theorem charFn_top [CompactSpace X] : (⊤ : CompactOpens X).charFn R = 1 :=
  LocallyConstant.coe_injective (by simp [coe_charFn])

/-- Over a nontrivial ring, `1_U = 1` exactly when `U` is the whole space. -/
theorem charFn_eq_one_iff [Nontrivial R] {U : CompactOpens X} :
    U.charFn R = 1 ↔ (U : Set X) = Set.univ := by
  refine ⟨fun h => Set.eq_univ_of_forall fun x => ?_, fun h => LocallyConstant.ext fun x => ?_⟩
  · by_contra hx
    simpa [charFn_apply_of_notMem hx] using DFunLike.congr_fun h x
  · have hx : x ∈ (U : Set X) := h ▸ Set.mem_univ x
    simp [charFn_apply_of_mem hx]

end TopologicalSpace.CompactOpens
