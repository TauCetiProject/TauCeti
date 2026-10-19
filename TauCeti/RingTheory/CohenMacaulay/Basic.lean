/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.KrullDimension.Field
public import TauCeti.RingTheory.Depth

/-!
# Cohen–Macaulay modules over a local ring

A finite module `M` over a Noetherian local ring `R` is *Cohen–Macaulay* if `M = 0` or its depth
equals the dimension of its support (Stacks, Definition 10.103.1 (00N3)). Depth is Mathlib's
`IsLocalRing.depth`, defined through the vanishing of `Ext (R ⧸ 𝔪) M`, and the dimension of the
support is Mathlib's `Module.supportDim`. Since the depth of a finite nonzero module never exceeds
the dimension of its support (`IsLocalRing.depth_le_supportDim`), being Cohen–Macaulay is the
reverse inequality.

The zero module is Cohen–Macaulay by convention: its depth is `⊤` while its support dimension is
`⊥`, so the depth equation alone would exclude it.

## Main definitions and results

* `Module.IsCohenMacaulay R M`: the `R`-module `M` is Cohen–Macaulay.
* `Module.isCohenMacaulay_iff_supportDim_le_depth`: a finite nonzero module over a Noetherian local
  ring is Cohen–Macaulay if and only if the dimension of its support is at most its depth.
* `Module.isCohenMacaulay_quotSMulTop_iff`: for an `M`-regular element `x` of the maximal ideal,
  `M ⧸ x M` is Cohen–Macaulay if and only if `M` is (Stacks, Lemma 10.103.5 (0C6G)), and
  `Module.isCohenMacaulay_quotient_ofList_smul_iff` is the same for an `M`-regular sequence.
* `Module.isCohenMacaulay_of_krullDimLE_zero`: every finite module over a Noetherian local ring of
  dimension zero, such as a field, is Cohen–Macaulay.
* `Module.isCohenMacaulay_self_of_isDomain_of_krullDimLE_one`: a Noetherian local domain of
  dimension at most one, such as a discrete valuation ring, is Cohen–Macaulay over itself.
-/

public section

universe u v w

open IsLocalRing RingTheory.Sequence Pointwise

namespace Module

variable (R : Type u) [CommRing R] [IsLocalRing R] [Small.{v} R]
  (M : Type v) [AddCommGroup M] [Module R M]

/-- An `R`-module `M` over a local ring `R` is *Cohen–Macaulay* if it is zero or its depth equals
the dimension of its support. This is meant for finite modules over a Noetherian local ring, where
the depth never exceeds the dimension of the support. Stacks, Definition 10.103.1 (00N3). -/
@[stacks 00N3]
def IsCohenMacaulay : Prop :=
  Subsingleton M ∨ (depth (ModuleCat.of R M) : WithBot ℕ∞) = supportDim R M

/-- Unfolds `Module.IsCohenMacaulay`. -/
theorem isCohenMacaulay_iff : IsCohenMacaulay R M ↔
    Subsingleton M ∨ (depth (ModuleCat.of R M) : WithBot ℕ∞) = supportDim R M :=
  Iff.rfl

variable {R M}

/-- The zero module is Cohen–Macaulay. -/
theorem isCohenMacaulay_of_subsingleton [Subsingleton M] : IsCohenMacaulay R M :=
  Or.inl ‹_›

/-- A nonzero module is Cohen–Macaulay if and only if its depth equals the dimension of its
support. -/
theorem isCohenMacaulay_iff_depth_eq [Nontrivial M] :
    IsCohenMacaulay R M ↔ (depth (ModuleCat.of R M) : WithBot ℕ∞) = supportDim R M := by
  rw [isCohenMacaulay_iff, or_iff_right (not_subsingleton M)]

/-- The depth of a nonzero Cohen–Macaulay module equals the dimension of its support. -/
theorem IsCohenMacaulay.depth_eq [Nontrivial M] (h : IsCohenMacaulay R M) :
    (depth (ModuleCat.of R M) : WithBot ℕ∞) = supportDim R M :=
  isCohenMacaulay_iff_depth_eq.1 h

/-- A finite nonzero module over a Noetherian local ring is Cohen–Macaulay if and only if the
dimension of its support is at most its depth, the reverse inequality being
`IsLocalRing.depth_le_supportDim`. -/
theorem isCohenMacaulay_iff_supportDim_le_depth [IsNoetherianRing R] [Module.Finite R M]
    [Nontrivial M] :
    IsCohenMacaulay R M ↔ supportDim R M ≤ (depth (ModuleCat.of R M) : WithBot ℕ∞) := by
  rw [isCohenMacaulay_iff_depth_eq, le_antisymm_iff, and_iff_right depth_le_supportDim]

end Module

namespace LinearEquiv

variable {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R] [Small.{w} R]
  {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N]

/-- Being Cohen–Macaulay is invariant under linear equivalence. -/
theorem isCohenMacaulay_iff (e : M ≃ₗ[R] N) :
    Module.IsCohenMacaulay R M ↔ Module.IsCohenMacaulay R N := by
  rw [Module.isCohenMacaulay_iff, Module.isCohenMacaulay_iff, e.toEquiv.subsingleton_congr,
    depth_eq_of_linearEquiv e, Module.supportDim_eq_of_equiv e]

end LinearEquiv

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- For an `M`-regular element `x` of the maximal ideal, `M ⧸ x M` is Cohen–Macaulay if and only if
`M` is. Stacks, Lemma 10.103.5 (0C6G). -/
@[stacks 0C6G]
theorem isCohenMacaulay_quotSMulTop_iff {x : R} (reg : IsSMulRegular M x)
    (hx : x ∈ maximalIdeal R) : IsCohenMacaulay R (QuotSMulTop x M) ↔ IsCohenMacaulay R M := by
  cases subsingleton_or_nontrivial M
  · exact iff_of_true isCohenMacaulay_of_subsingleton isCohenMacaulay_of_subsingleton
  have := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  rw [isCohenMacaulay_iff_depth_eq, isCohenMacaulay_iff_depth_eq,
    ← depth_quotSMulTop_succ_eq_depth reg hx, ← supportDim_quotSMulTop_succ_eq_supportDim reg hx,
    WithBot.coe_add, WithBot.coe_one, ENat.WithBot.add_one_cancel]

/-- For an `M`-regular sequence `r₁, …, rₙ`, `M ⧸ (r₁, …, rₙ) M` is Cohen–Macaulay if and only if
`M` is. Stacks, Lemma 10.103.5 (0C6G), applied `n` times. -/
theorem isCohenMacaulay_quotient_ofList_smul_iff (rs : List R) (reg : IsRegular M rs) :
    IsCohenMacaulay R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) ↔ IsCohenMacaulay R M := by
  have := reg.nontrivial
  have := reg.quot_ofList_smul_nontrivial ⊤
  rw [isCohenMacaulay_iff_depth_eq, isCohenMacaulay_iff_depth_eq,
    ← depth_add_length_eq_depth_of_isRegular rs reg,
    ← supportDim_add_length_eq_supportDim_of_isRegular rs reg, WithBot.coe_add,
    WithBot.coe_natCast, ENat.WithBot.add_natCast_cancel]

/-- Every finite module over a Noetherian local ring of dimension zero is Cohen–Macaulay. -/
theorem isCohenMacaulay_of_krullDimLE_zero [Ring.KrullDimLE 0 R] : IsCohenMacaulay R M := by
  cases subsingleton_or_nontrivial M
  · exact isCohenMacaulay_of_subsingleton
  refine isCohenMacaulay_iff_supportDim_le_depth.2 <|
    (supportDim_le_ringKrullDim R M).trans <| (Ring.krullDimLE_iff.1 ‹_›).trans ?_
  exact_mod_cast zero_le

end Module

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]

/-- A Noetherian local domain of dimension at most one is Cohen–Macaulay over itself. -/
theorem isCohenMacaulay_self_of_isDomain_of_krullDimLE_one [Ring.KrullDimLE 1 R] :
    IsCohenMacaulay R R := by
  rw [isCohenMacaulay_iff_supportDim_le_depth, supportDim_self_eq_ringKrullDim]
  by_cases hm : maximalIdeal R = ⊥
  · rw [ringKrullDim_eq_zero_of_isField ((isField_iff_maximalIdeal_eq).2 hm)]
    exact_mod_cast zero_le
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  rw [← depth_quotSMulTop_succ_eq_depth (IsSMulRegular.of_ne_zero hx0) hx]
  refine (Ring.krullDimLE_iff.1 ‹_›).trans ?_
  exact_mod_cast le_add_self

example (K : Type u) [Field K] (V : Type u) [AddCommGroup V] [Module K V] [Module.Finite K V] :
    IsCohenMacaulay K V :=
  isCohenMacaulay_of_krullDimLE_zero

example (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] : IsCohenMacaulay A A :=
  isCohenMacaulay_self_of_isDomain_of_krullDimLE_one

end Module
