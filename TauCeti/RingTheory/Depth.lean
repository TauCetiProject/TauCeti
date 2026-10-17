/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.Category

/-!
# Depth of a module over a Noetherian local ring

Mathlib defines the depth `IsLocalRing.depth M` of a module over a local ring `R` through the
vanishing of `Ext (R ⧸ 𝔪) M`, and identifies it, for a finite nonzero module over a Noetherian local
ring, with the supremum of the lengths of `M`-regular sequences in `𝔪`. This file proves the two
basic facts relating depth to dimension and to quotients by regular sequences.

## Main results

* `IsLocalRing.depth_le_supportDim`: the depth of a finite nonzero module over a Noetherian local
  ring is at most the dimension of its support (Stacks, Lemma 10.72.3 (00LK)).
* `IsLocalRing.depth_quotSMulTop_succ_eq_depth`: dividing a finite module by an `M`-regular element
  of the maximal ideal lowers the depth by exactly one.
* `IsLocalRing.depth_add_length_eq_depth_of_isRegular`: dividing a finite module by an `M`-regular
  sequence `r₁, …, rₙ` lowers the depth by exactly `n`.

Together with Mathlib's `Module.supportDim_add_length_eq_supportDim_of_isRegular`, which says the
same for the dimension of the support, these are what make Cohen–Macaulayness stable under
quotients by regular sequences.
-/

public section

universe u v

open IsLocalRing RingTheory.Sequence Pointwise

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R]
  {M : Type v} [AddCommGroup M] [Module R M]

/-- The depth of a finite nonzero module `M` over a Noetherian local ring is at most the dimension
of its support. Stacks, Lemma 10.72.3 (00LK). -/
@[stacks 00LK]
theorem depth_le_supportDim [IsNoetherianRing R] [Module.Finite R M] [Nontrivial M] :
    (depth (ModuleCat.of R M) : WithBot ℕ∞) ≤ Module.supportDim R M := by
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.1 (Module.supportDim_ne_bot_of_nontrivial R M)
  rw [← hd, WithBot.coe_le_coe, depth_eq_sSup_length_isRegular]
  refine sSup_le ?_
  rintro _ ⟨rs, reg, -, rfl⟩
  have := reg.quot_ofList_smul_nontrivial ⊤
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.1
    (Module.supportDim_ne_bot_of_nontrivial R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)))
  have h := Module.supportDim_add_length_eq_supportDim_of_isRegular rs reg
  rw [← hd, ← he, ← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj] at h
  exact h ▸ le_add_self

/-- Dividing a module `M` by an `M`-regular element `x` lowers the depth by at most one. No
finiteness or Noetherian hypothesis is needed. -/
theorem depth_le_depth_quotSMulTop_succ {x : R} (reg : IsSMulRegular M x) :
    depth (ModuleCat.of R M) ≤ depth (ModuleCat.of R (QuotSMulTop x M)) + 1 := by
  have h := ModuleCat.depth_min_snd_fst_sub_one_le_trd_right
    (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) _
    (IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R M) reg)
  -- The long exact `Ext` sequence of `0 → M → M → M ⧸ x M → 0`; unfolding `smulShortComplex`
  -- exposes its three objects.
  simp only [ModuleCat.smulShortComplex] at h
  rw [min_eq_right tsub_le_self] at h
  exact tsub_le_iff_right.1 h

/-- Dividing a finite module `M` over a Noetherian local ring by an `M`-regular element `x` of the
maximal ideal lowers the depth by exactly one. -/
theorem depth_quotSMulTop_succ_eq_depth [IsNoetherianRing R] [Module.Finite R M]
    {x : R} (reg : IsSMulRegular M x) (hx : x ∈ maximalIdeal R) :
    depth (ModuleCat.of R (QuotSMulTop x M)) + 1 = depth (ModuleCat.of R M) := by
  refine le_antisymm ?_ (depth_le_depth_quotSMulTop_succ reg)
  cases subsingleton_or_nontrivial M
  · rw [depth_eq_top_of_subsingleton (ModuleCat.of R M)]
    exact le_top
  have := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  -- Prepending `x` to an `(M ⧸ x M)`-regular sequence gives an `M`-regular sequence.
  rw [depth_eq_sSup_length_isRegular, depth_eq_sSup_length_isRegular]
  refine (ENat.sSup_add ?_).trans_le (iSup₂_le ?_)
  · exact ⟨_, [], IsRegular.nil R _, by simp, rfl⟩
  · rintro _ ⟨rs, reg', mem, rfl⟩
    exact le_sSup ⟨x :: rs, reg'.cons reg, List.forall_mem_cons.2 ⟨hx, mem⟩, by simp⟩

/-- Dividing a finite module `M` over a Noetherian local ring by an `M`-regular sequence
`r₁, …, rₙ` lowers the depth by exactly `n`. -/
theorem depth_add_length_eq_depth_of_isRegular [IsNoetherianRing R] [Module.Finite R M]
    (rs : List R) (reg : IsRegular M rs) :
    depth (ModuleCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))) + rs.length =
      depth (ModuleCat.of R M) := by
  induction rs generalizing M with
  | nil =>
    rw [List.length_nil, Nat.cast_zero, add_zero]
    exact depth_eq_of_linearEquiv (Submodule.quotEquivOfEqBot _ (by simp))
  | cons x rs ih =>
    obtain ⟨hx, hrs⟩ := (isRegular_cons_iff M x rs).1 reg
    have mem : x ∈ maximalIdeal R := by
      simpa using fun isu ↦ reg.2 (by simp [Ideal.span_singleton_eq_top.mpr isu])
    rw [depth_eq_of_linearEquiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs),
      ← depth_quotSMulTop_succ_eq_depth hx mem, ← ih hrs, List.length_cons, Nat.cast_succ,
      add_assoc]

end IsLocalRing
