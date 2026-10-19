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
ring, with the supremum of the lengths of `M`-regular sequences in `𝔪`. This file relates depth
to dimension, quotients by regular sequences, and modules of linear maps.

## Main results

* `RingTheory.Sequence.IsRegular.mem_maximalIdeal`: over a local ring, every element of an
  `M`-regular sequence lies in the maximal ideal.
* `IsLocalRing.depth_le_supportDim`: the depth of a finite nonzero module over a Noetherian local
  ring is at most the dimension of its support (Stacks, Lemma 10.72.3 (00LK)).
* `IsLocalRing.depth_quotSMulTop_succ_eq_depth`: dividing a finite module by an `M`-regular element
  of the maximal ideal lowers the depth by exactly one.
* `IsLocalRing.depth_add_length_eq_depth_of_isRegular`: dividing a finite module by an `M`-regular
  sequence `r₁, …, rₙ` lowers the depth by exactly `n`.
* `IsLocalRing.depth_hom_ge`: depth at least one or two passes from the target module to the
  module of linear maps (Stacks, Lemma 15.24.10 (0AV5)).

Together with Mathlib's `Module.supportDim_add_length_eq_supportDim_of_isRegular`, which says the
same for the dimension of the support, these are what make Cohen–Macaulayness stable under
quotients by regular sequences.
-/

public section

universe u v

open IsLocalRing RingTheory.Sequence Pointwise

/-- Over a local ring, every element of an `M`-regular sequence lies in the maximal ideal. -/
theorem RingTheory.Sequence.IsRegular.mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {rs : List R} (reg : IsRegular M rs) {r : R}
    (hr : r ∈ rs) : r ∈ maximalIdeal R := by
  by_contra h
  refine reg.top_ne_smul ?_
  rw [Ideal.eq_top_of_isUnit_mem (Ideal.ofList rs) (Ideal.subset_span hr)
    (notMem_maximalIdeal.1 h), Submodule.top_smul]

/-- A regular element on the target is regular on the module of linear maps. -/
theorem IsSMulRegular.linearMap {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {scalar : R} (regular : IsSMulRegular N scalar) :
    IsSMulRegular (M →ₗ[R] N) scalar := by
  intro first second equality
  ext element
  exact regular (congrArg (fun linear ↦ linear element) equality)

section LinearMap

variable {R M N : Type*} [CommRing R] [AddCommMonoid M] [AddCommGroup N]
  [Module R M] [Module R N]

/-- The second element of a regular sequence on the target remains regular after quotienting
the module of linear maps by the first element. -/
theorem IsSMulRegular.quotSMulTop_linearMap {first second : R}
    (regular : IsSMulRegular N first)
    (quotientRegular : IsSMulRegular (QuotSMulTop first N) second) :
    IsSMulRegular (QuotSMulTop first (M →ₗ[R] N)) second := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro linear membership
  obtain ⟨other, -, equality⟩ :=
    (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 membership
  have pointwise (element : M) : linear element ∈ first • (⊤ : Submodule R N) := by
    apply mem_of_isSMulRegular_quotient_of_smul_mem quotientRegular
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
      ⟨other element, Submodule.mem_top, congrArg (fun map ↦ map element) equality⟩
  let multiplication : N →ₗ[R] N := LinearMap.lsmul R N first
  have inRange (element : M) : linear element ∈ LinearMap.range multiplication := by
    obtain ⟨value, -, equation⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (pointwise element)
    exact ⟨value, equation⟩
  refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
    ⟨linear.codRestrictOfInjective multiplication regular inRange, Submodule.mem_top, ?_⟩
  ext element
  exact linear.codRestrictOfInjective_comp_apply multiplication regular inRange element

/-- A weakly regular sequence of length at most two on the target is weakly regular on the
module of linear maps. -/
theorem RingTheory.Sequence.IsWeaklyRegular.linearMap {scalars : List R}
    (regular : IsWeaklyRegular N scalars) (length : scalars.length ≤ 2) :
    IsWeaklyRegular (M →ₗ[R] N) scalars := by
  cases scalars with
  | nil => exact .nil _ _
  | cons first tail =>
    obtain ⟨firstRegular, tailRegular⟩ := (isWeaklyRegular_cons_iff _ _ _).1 regular
    cases tail with
    | nil => exact (IsWeaklyRegular.nil _ _).cons firstRegular.linearMap
    | cons second rest =>
      have restEmpty : rest = [] := by
        have : rest.length = 0 := by simpa using length
        exact List.length_eq_zero_iff.mp this
      subst rest
      have secondRegular := (isWeaklyRegular_cons_iff _ _ _).1 tailRegular |>.1
      exact ((IsWeaklyRegular.nil _ _).cons
        (firstRegular.quotSMulTop_linearMap secondRegular)).cons firstRegular.linearMap

end LinearMap

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
  rw [← hd, ← he] at h
  have h' : e + rs.length = d := by exact_mod_cast h
  exact h' ▸ le_add_self

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
    rw [depth_eq_of_linearEquiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs),
      ← depth_quotSMulTop_succ_eq_depth hx (reg.mem_maximalIdeal List.mem_cons_self), ← ih hrs,
      List.length_cons, Nat.cast_succ, add_assoc]

/-- Over a Noetherian local ring, depth at least `n ≤ 2` passes from a finite target module
to the module of linear maps from a finite module. Stacks, Lemma 15.24.10 (0AV5). -/
@[stacks 0AV5]
theorem depth_hom_ge {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] {M N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Finite R M] [Module.Finite R N]
    {bound : ℕ} (bound_le_two : bound ≤ 2)
    (depth_bound : (bound : ℕ∞) ≤ depth (ModuleCat.of R N)) :
    (bound : ℕ∞) ≤ depth (ModuleCat.of R (M →ₗ[R] N)) := by
  classical
  cases subsingleton_or_nontrivial N
  · rw [depth_eq_top_of_subsingleton]
    exact le_top
  cases subsingleton_or_nontrivial (M →ₗ[R] N)
  · rw [depth_eq_top_of_subsingleton]
    exact le_top
  cases bound with
  | zero => exact zero_le
  | succ predecessor =>
    rw [depth_eq_sSup_length_isRegular] at depth_bound ⊢
    have strict := lt_of_lt_of_le
      (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self predecessor)) depth_bound
    obtain ⟨_, ⟨scalars, regular, membership, rfl⟩, strict⟩ := lt_sSup_iff.mp strict
    have length : predecessor + 1 ≤ scalars.length :=
      Nat.succ_le_of_lt (ENat.natCast_lt_natCast.mp strict)
    have prefixRegular : IsWeaklyRegular N (scalars.take (predecessor + 1)) := by
      constructor
      intro index index_lt
      have index_lt_length : index < scalars.length :=
        lt_of_lt_of_le index_lt (List.length_take_le' _ _)
      have index_le : index ≤ predecessor + 1 :=
        le_of_lt (lt_of_lt_of_le index_lt (List.length_take_le _ _))
      rw [List.getElem_take, List.take_take, Nat.min_eq_left index_le]
      exact regular.regular_mod_prev index index_lt_length
    have prefixMembership : ∀ scalar ∈ scalars.take (predecessor + 1),
        scalar ∈ maximalIdeal R :=
      fun scalar member ↦ membership scalar (List.mem_of_mem_take member)
    have homRegular : IsRegular (M →ₗ[R] N) (scalars.take (predecessor + 1)) :=
      (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal prefixMembership).2
        (prefixRegular.linearMap (by simpa [List.length_take, Nat.min_eq_left length]
          using bound_le_two))
    exact le_sSup ⟨scalars.take (predecessor + 1), homRegular, prefixMembership,
      by simp [List.length_take, Nat.min_eq_left length]⟩

end IsLocalRing
