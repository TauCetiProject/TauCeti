/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.Category
public import TauCeti.RingTheory.Ideal.AssociatedPrime.Basic
public import TauCeti.RingTheory.Ideal.AssociatedPrime.Localization
public import TauCeti.RingTheory.KrullDimension.Quotient
public import TauCeti.RingTheory.Regular.LinearMap
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Flat.Localization
import TauCeti.Algebra.Category.ModuleCat.Ext.Basic
import TauCeti.Data.ENat.Basic
import TauCeti.RingTheory.Localization.Module

/-!
# Basic depth of modules

Mathlib defines the depth `IsLocalRing.depth M` of a module over a local ring `R` through the
vanishing of `Ext (R ⧸ 𝔪) M`, and identifies it, for a finite nonzero module over a Noetherian local
ring, with the supremum of the lengths of `M`-regular sequences in `𝔪`. This file relates depth
to dimension, quotients by regular sequences, short exact sequences and modules of linear maps,
and, after localization, to associated primes. The short exact sequence bounds hold for
`Ideal.depth I` over any commutative ring; the other results are for Noetherian local rings
or, after localization, Noetherian rings.
The regular-sequence transfer lemmas for linear maps live in
`TauCeti.RingTheory.Regular.LinearMap`.

## Main results

* `RingTheory.Sequence.IsRegular.mem_maximalIdeal`: over a local ring, every element of an
  `M`-regular sequence lies in the maximal ideal.
* `RingTheory.Sequence.IsRegular.length_le_supportDim`: over a Noetherian local ring, the length
  of an `M`-regular sequence on a finite module `M` is at most the dimension of its support.
* `IsLocalRing.depth_le_supportDim`: the depth of a finite nonzero module over a Noetherian local
  ring is at most the dimension of its support (Stacks, Lemma 10.72.3 (00LK)).
* `Ideal.depth_min_snd_trd_add_one_le_fst_of_exact`,
  `Ideal.depth_min_snd_fst_sub_one_le_trd_of_exact`, and
  `Ideal.depth_min_fst_trd_le_snd_of_exact` (with `IsLocalRing.` specializations): the depth
  inequalities for short exact sequences of linear maps, across module universes. They are the
  linear-map forms of Mathlib's `ModuleCat.depth_min_snd_trd_add_one_le_fst_right`,
  `ModuleCat.depth_min_snd_fst_sub_one_le_trd_right` and
  `ModuleCat.depth_min_fst_trd_le_snd_right`, transported through
  `ModuleCat.shortComplexOfConj_shortExact`.
* `ModuleCat.depth_trd_add_one_le_fst_of_comp_mk₀_eq_zero`: for a short exact sequence
  `0 → X₁ → X₂ → X₃ → 0` whose first map induces zero on `Ext N - n` for every `n`, the depth
  of `X₁` is at least one more than that of `X₃`. This sharpens Mathlib's
  `ModuleCat.depth_min_snd_trd_add_one_le_fst_right`.
* `IsLocalRing.depth_prod` and `IsLocalRing.depth_eq_depth_self_of_free`: the depth of a product
  is the minimum of the depths, so a nonzero finite free module has the depth of the ring.
* `IsLocalRing.depth_add_one_le_depth_ker`: for a free presentation `0 → K → F → M → 0` with
  `K` finite free and `K ⊆ 𝔪 F`, `depth M + 1 ≤ depth K`.
* `IsLocalRing.depth_quotSMulTop_succ_eq_depth`: dividing a finite module by an `M`-regular element
  of the maximal ideal lowers the depth by exactly one.
* `IsLocalRing.depth_quotSMulTop_eq_of_surjective` and
  `IsLocalRing.depth_eq_add_one_of_surjective`: the same statements for a module `Q` presented as
  the target of a surjection with kernel `x M`.
* `IsLocalRing.depth_add_length_eq_depth_of_isRegular`: dividing a finite module by an `M`-regular
  sequence `r₁, …, rₙ` lowers the depth by exactly `n`.
* `IsLocalRing.depth_eq_depth_of_surjective`: along a surjective homomorphism of local rings
  `R → T`, a finite `T`-module has the same depth over `R` as over `T`.
* `RingEquiv.depth_self_eq`: isomorphic Noetherian local rings have the same depth over
  themselves.
* `IsLocalRing.depth_hom_ge`: depth at least one or two passes from the target
  module to the module of linear maps (Stacks, Lemma 15.24.10 (0AV5)).
* `IsLocalRing.mem_span_singleton_of_forall_mul_mem_of_two_le_depth`: in a Noetherian local ring
  of depth at least two, `𝔪 c ⊆ (b)` for a nonzerodivisor `b` forces `c ∈ (b)`, so the maximal
  ideal is not an associated prime of `R ⧸ (b)`.
* `IsLocalRing.depth_le_ringKrullDim_quotient_of_isAssociatedPrime`: the depth of a finite module
  is at most `dim (R ⧸ p)` for every associated prime `p` of the module (Matsumura, Theorem 17.2).
* `IsLocalRing.depth_eq_zero_iff_nontrivial_linearMap` and
  `IsLocalRing.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes`: the depth vanishes exactly
  when the residue field maps nontrivially to the module, that is, when the maximal ideal is an
  associated prime.
* `TauCeti.depth_localizedModule_eq_zero_iff`: `M_p` has depth zero exactly when `p` is an
  associated prime of `M`, and `TauCeti.one_le_depth_localizedModule_iff` is its negation. This
  combines the depth-zero criterion with
  `TauCeti.maximalIdeal_mem_associatedPrimes_localizedModule_iff` from
  `TauCeti.RingTheory.Ideal.AssociatedPrime.Localization`.
* `TauCeti.depth_localizedModule_quotSMulTop_add_one`: dividing a finite module by an `M`-regular
  element of a prime `p` lowers the depth of the localization at `p` by exactly one.

The two quotient-depth results, together with Mathlib's
`Module.supportDim_add_length_eq_supportDim_of_isRegular`, make Cohen–Macaulayness stable under
quotients by regular sequences.
-/

public section

universe u v w t

open IsLocalRing RingTheory.Sequence Pointwise

/-- Over a local ring, every element of an `M`-regular sequence lies in the maximal ideal. -/
theorem RingTheory.Sequence.IsRegular.mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {rs : List R} (reg : IsRegular M rs) {r : R}
    (hr : r ∈ rs) : r ∈ maximalIdeal R := by
  by_contra h
  refine reg.top_ne_smul ?_
  rw [Ideal.eq_top_of_isUnit_mem (Ideal.ofList rs) (Ideal.subset_span hr)
    (notMem_maximalIdeal.1 h), Submodule.top_smul]

/-- Over a Noetherian local ring, the length of an `M`-regular sequence on a finite module `M` is at
most the dimension of the support of `M`. -/
theorem RingTheory.Sequence.IsRegular.length_le_supportDim {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {rs : List R} (reg : IsRegular M rs) :
    (rs.length : WithBot ℕ∞) ≤ Module.supportDim R M := by
  have := reg.quot_ofList_smul_nontrivial ⊤
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.1
    (Module.supportDim_ne_bot_of_nontrivial R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)))
  rw [← Module.supportDim_add_length_eq_supportDim_of_isRegular rs reg, ← he]
  exact_mod_cast le_add_self

namespace ModuleCat

open CategoryTheory Abelian

variable {R : Type u} [CommRing R] [Small.{v} R]

/-- In a short exact sequence `0 → X₁ → X₂ → X₃ → 0` whose first map induces the zero map
`Ext N X₁ n → Ext N X₂ n` for every `n`, the depth of `X₁` with respect to `N` is at least one
more than that of `X₃`: the connecting maps `Ext N X₃ n → Ext N X₁ (n + 1)` are surjective. -/
theorem depth_trd_add_one_le_fst_of_comp_mk₀_eq_zero (N : ModuleCat.{v} R)
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    (h : ∀ (n : ℕ) (x : Ext N S.X₁ n), x.comp (Ext.mk₀ S.f) (add_zero n) = 0) :
    N.depth S.X₃ + 1 ≤ N.depth S.X₁ := by
  apply le_sSup
  intro i hi
  match i with
  | 0 =>
    -- `Hom (N, X₁) → Hom (N, X₂)` is injective, and zero by assumption.
    exact ⟨fun x y ↦ Ext.postcomp_mk₀_injective_of_mono N S.f (hf := hS.mono_f)
      ((h 0 x).trans (h 0 y).symm)⟩
  | i + 1 =>
    have hi' : (i : ℕ∞) < N.depth S.X₃ := by simpa using hi
    have := subsingleton_ext_of_lt_depth hi'
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ N hS x (h _ x) rfl
    obtain ⟨y₃, rfl⟩ := Ext.covariant_sequence_exact₁ N hS y (h _ y) rfl
    rw [Subsingleton.elim x₃ y₃]

end ModuleCat

namespace Ideal

section Exact

variable {R : Type u} [CommRing R] (I : Ideal R)
  {M : Type v} {N : Type w} {Q : Type t}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup Q] [Module R Q] [Small.{v} R] [Small.{w} R] [Small.{t} R]

private theorem depth_bounds_of_exact (first : M →ₗ[R] N) (second : N →ₗ[R] Q)
    (exactness : Function.Exact first second) (injective : Function.Injective first)
    (surjective : Function.Surjective second) :
    (Ideal.depth.{w, u} I (ModuleCat.of R N) ⊓ (Ideal.depth.{t, u} I (ModuleCat.of R Q) + 1) ≤
      Ideal.depth.{v, u} I (ModuleCat.of R M)) ∧
    (Ideal.depth.{w, u} I (ModuleCat.of R N) ⊓ (Ideal.depth.{v, u} I (ModuleCat.of R M) - 1) ≤
      Ideal.depth.{t, u} I (ModuleCat.of R Q)) ∧
    (Ideal.depth.{v, u} I (ModuleCat.of R M) ⊓ Ideal.depth.{t, u} I (ModuleCat.of R Q) ≤
      Ideal.depth.{w, u} I (ModuleCat.of R N)) := by
  let sourceEquiv : ULift.{max u v w t} M ≃ₗ[R] M := ULift.moduleEquiv
  let middleEquiv : ULift.{max u v w t} N ≃ₗ[R] N := ULift.moduleEquiv
  let targetEquiv : ULift.{max u v w t} Q ≃ₗ[R] Q := ULift.moduleEquiv
  have shortExact := ModuleCat.shortComplexOfConj_shortExact sourceEquiv middleEquiv
    targetEquiv first second exactness injective surjective
  have lower := ModuleCat.depth_min_snd_trd_add_one_le_fst_right
    (ModuleCat.of R (Shrink.{max u v w t} (R ⧸ I))) _ shortExact
  have upper := ModuleCat.depth_min_snd_fst_sub_one_le_trd_right
    (ModuleCat.of R (Shrink.{max u v w t} (R ⧸ I))) _ shortExact
  have middle := ModuleCat.depth_min_fst_trd_le_snd_right
    (ModuleCat.of R (Shrink.{max u v w t} (R ⧸ I))) _ shortExact
  have bounds :
      (Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} N)) ⊓
        (Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} Q)) + 1) ≤
        Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} M))) ∧
      (Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} N)) ⊓
        (Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} M)) - 1) ≤
        Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} Q))) ∧
      (Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} M)) ⊓
        Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} Q)) ≤
        Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} N))) := by
    -- `Ideal.depth` is `ModuleCat.depth` from the shrunk residue module. After unfolding, the
    -- goal is `lower`, `upper`, `middle` up to the projections `S.X₁`, `S.X₂`, `S.X₃` of the
    -- explicit short complex, which `exact` unfolds.
    simp only [Ideal.depth]
    exact ⟨lower, upper, middle⟩
  rwa [Ideal.depth_eq_of_linearEquiv I sourceEquiv, Ideal.depth_eq_of_linearEquiv I middleEquiv,
    Ideal.depth_eq_of_linearEquiv I targetEquiv] at bounds

/-- For a short exact sequence of linear maps, the source depth with respect to an ideal is at
least the minimum of the middle depth and one plus the target depth. The modules may lie in
different universes. -/
@[stacks 00LX "(3), for linear maps in different universes"]
theorem depth_min_snd_trd_add_one_le_fst_of_exact (first : M →ₗ[R] N) (second : N →ₗ[R] Q)
    (exactness : Function.Exact first second) (injective : Function.Injective first)
    (surjective : Function.Surjective second) :
    Ideal.depth.{w, u} I (ModuleCat.of R N) ⊓ (Ideal.depth.{t, u} I (ModuleCat.of R Q) + 1) ≤
      Ideal.depth.{v, u} I (ModuleCat.of R M) :=
  (depth_bounds_of_exact I first second exactness injective surjective).1

/-- For a short exact sequence of linear maps, the target depth with respect to an ideal is at
least the minimum of the middle depth and the source depth minus one. The modules may lie in
different universes. -/
@[stacks 00LX "(2), for linear maps in different universes"]
theorem depth_min_snd_fst_sub_one_le_trd_of_exact (first : M →ₗ[R] N) (second : N →ₗ[R] Q)
    (exactness : Function.Exact first second) (injective : Function.Injective first)
    (surjective : Function.Surjective second) :
    Ideal.depth.{w, u} I (ModuleCat.of R N) ⊓ (Ideal.depth.{v, u} I (ModuleCat.of R M) - 1) ≤
      Ideal.depth.{t, u} I (ModuleCat.of R Q) :=
  (depth_bounds_of_exact I first second exactness injective surjective).2.1

/-- For a short exact sequence of linear maps, the middle depth with respect to an ideal is at
least the minimum of the source and target depths. The modules may lie in different universes. -/
@[stacks 00LX "(1), for linear maps in different universes"]
theorem depth_min_fst_trd_le_snd_of_exact (first : M →ₗ[R] N) (second : N →ₗ[R] Q)
    (exactness : Function.Exact first second) (injective : Function.Injective first)
    (surjective : Function.Surjective second) :
    Ideal.depth.{v, u} I (ModuleCat.of R M) ⊓ Ideal.depth.{t, u} I (ModuleCat.of R Q) ≤
      Ideal.depth.{w, u} I (ModuleCat.of R N) :=
  (depth_bounds_of_exact I first second exactness injective surjective).2.2

end Exact

end Ideal

namespace IsLocalRing

section Exact

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {M : Type v} {N : Type w} {Q : Type t}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup Q] [Module R Q] [Small.{v} R] [Small.{w} R] [Small.{t} R]

/-- Local-ring form of `Ideal.depth_min_snd_trd_add_one_le_fst_of_exact`. -/
@[stacks 00LX "(3), for linear maps in different universes"]
theorem depth_min_snd_trd_add_one_le_fst_of_exact (first : M →ₗ[R] N) (second : N →ₗ[R] Q)
    (exactness : Function.Exact first second) (injective : Function.Injective first)
    (surjective : Function.Surjective second) :
    depth (ModuleCat.of R N) ⊓ (depth (ModuleCat.of R Q) + 1) ≤
      depth (ModuleCat.of R M) :=
  Ideal.depth_min_snd_trd_add_one_le_fst_of_exact
    (M := M) (N := N) (Q := Q) (maximalIdeal R) first second exactness injective
    surjective

/-- Local-ring form of `Ideal.depth_min_snd_fst_sub_one_le_trd_of_exact`. -/
@[stacks 00LX "(2), for linear maps in different universes"]
theorem depth_min_snd_fst_sub_one_le_trd_of_exact (first : M →ₗ[R] N) (second : N →ₗ[R] Q)
    (exactness : Function.Exact first second) (injective : Function.Injective first)
    (surjective : Function.Surjective second) :
    depth (ModuleCat.of R N) ⊓ (depth (ModuleCat.of R M) - 1) ≤
      depth (ModuleCat.of R Q) :=
  Ideal.depth_min_snd_fst_sub_one_le_trd_of_exact
    (M := M) (N := N) (Q := Q) (maximalIdeal R) first second exactness injective
    surjective

/-- Local-ring form of `Ideal.depth_min_fst_trd_le_snd_of_exact`. -/
@[stacks 00LX "(1), for linear maps in different universes"]
theorem depth_min_fst_trd_le_snd_of_exact (first : M →ₗ[R] N) (second : N →ₗ[R] Q)
    (exactness : Function.Exact first second) (injective : Function.Injective first)
    (surjective : Function.Surjective second) :
    depth (ModuleCat.of R M) ⊓ depth (ModuleCat.of R Q) ≤
      depth (ModuleCat.of R N) :=
  Ideal.depth_min_fst_trd_le_snd_of_exact
    (M := M) (N := N) (Q := Q) (maximalIdeal R) first second exactness injective
    surjective

end Exact

section Free

variable {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R]

/-- The depth of a product of two modules over a local ring is the minimum of their depths. -/
@[simp]
theorem depth_prod (M N : Type v) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    depth (ModuleCat.of R (M × N)) = depth (ModuleCat.of R M) ⊓ depth (ModuleCat.of R N) := by
  have hM := depth_min_snd_trd_add_one_le_fst_of_exact (LinearMap.inl R M N)
    (LinearMap.snd R M N) Function.Exact.inl_snd LinearMap.inl_injective LinearMap.snd_surjective
  have hN := depth_min_snd_trd_add_one_le_fst_of_exact (LinearMap.inr R M N)
    (LinearMap.fst R M N) Function.Exact.inr_fst LinearMap.inr_injective LinearMap.fst_surjective
  exact le_antisymm (le_inf (ENat.le_of_inf_le_of_inf_le hM hN) (ENat.le_of_inf_le_of_inf_le hN hM))
    (depth_min_fst_trd_le_snd_of_exact (LinearMap.inl R M N) (LinearMap.snd R M N)
      Function.Exact.inl_snd LinearMap.inl_injective LinearMap.snd_surjective)

/-- A nonzero finite free module over a local ring has the same depth as the ring. -/
theorem depth_eq_depth_self_of_free (M : Type v) [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] [Nontrivial M] :
    depth (ModuleCat.of R M) = depth (ModuleCat.of R R) := by
  have key (k : ℕ) (hk : 0 < k) :
      depth (ModuleCat.of R (Fin k → R)) = depth (ModuleCat.of R R) := by
    induction k, hk using Nat.le_induction with
    | base => exact depth_eq_of_linearEquiv (LinearEquiv.funUnique (Fin 1) R R)
    | succ k hk ih =>
      rw [← depth_eq_of_linearEquiv (Fin.consLinearEquiv R fun _ : Fin (k + 1) ↦ R), depth_prod,
        ih, inf_idem]
  let b := Module.Free.chooseBasis R M
  have := b.index_nonempty
  rw [depth_eq_of_linearEquiv (b.equivFun.trans
    (LinearEquiv.funCongrLeft R R (Fintype.equivFin _).symm)), key _ Fintype.card_pos]

open CategoryTheory Abelian in
/-- If `0 → K → F → M → 0` is a free presentation with `K` finite free and `K ⊆ 𝔪 F`, then
`depth M + 1 ≤ depth K`. -/
theorem depth_add_one_le_depth_ker {F M : Type v} [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M] {g : F →ₗ[R] M} (hg : Function.Surjective g)
    [Module.Free R (LinearMap.ker g)] [Module.Finite R (LinearMap.ker g)]
    (hker : LinearMap.ker g ≤ maximalIdeal R • ⊤) :
    depth (ModuleCat.of R M) + 1 ≤ depth (ModuleCat.of R (LinearMap.ker g)) := by
  have hI : maximalIdeal R ≤ Module.annihilator R (Shrink.{v} (R ⧸ maximalIdeal R)) := by
    rw [(Shrink.linearEquiv R _).annihilator_eq, Ideal.annihilator_quotient]
  have hrange : LinearMap.range (LinearMap.ker g).subtype ≤ maximalIdeal R • ⊤ := by
    rwa [Submodule.range_subtype]
  have key (n : ℕ) (x : Ext (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R)))
      (ModuleCat.of R (LinearMap.ker g)) n) :
      x.comp (Ext.mk₀ (ModuleCat.ofHom (LinearMap.ker g).subtype)) (add_zero n) = 0 :=
    Ext.comp_mk₀_eq_zero_of_range_le_smul_top hI _ hrange x
  have h := ModuleCat.depth_trd_add_one_le_fst_of_comp_mk₀_eq_zero
    (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) (LinearMap.shortExact_shortComplexKer hg) key
  unfold IsLocalRing.depth Ideal.depth
  exact h

end Free

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
  exact WithBot.coe_le_coe.1 (hd ▸ reg.length_le_supportDim)

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

/-- If `g : M → Q` is a surjective linear map with kernel `x M`, then `M ⧸ x M` and `Q` have the
same depth. -/
theorem depth_quotSMulTop_eq_of_surjective {Q : Type v} [AddCommGroup Q] [Module R Q] {x : R}
    (g : M →ₗ[R] Q) (hg : Function.Surjective g) (hker : LinearMap.ker g = x • ⊤) :
    depth (ModuleCat.of R (QuotSMulTop x M)) = depth (ModuleCat.of R Q) :=
  depth_eq_of_linearEquiv <| (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (g.quotKerEquivOfSurjective hg)

/-- Over a Noetherian local ring, let `x` in the maximal ideal be regular on a finite module `M`
and let `g : M → Q` be a surjective linear map with kernel `x M`. Then the depth of `M` is one
more than the depth of `Q`. This is `IsLocalRing.depth_quotSMulTop_succ_eq_depth` with the
quotient replaced by an isomorphic module. -/
theorem depth_eq_add_one_of_surjective [IsNoetherianRing R] [Module.Finite R M] {Q : Type v}
    [AddCommGroup Q] [Module R Q] {x : R} (hx : x ∈ maximalIdeal R) (reg : IsSMulRegular M x)
    (g : M →ₗ[R] Q) (hg : Function.Surjective g) (hker : LinearMap.ker g = x • ⊤) :
    depth (ModuleCat.of R M) = depth (ModuleCat.of R Q) + 1 := by
  rw [← depth_quotSMulTop_eq_of_surjective g hg hker, depth_quotSMulTop_succ_eq_depth reg hx]

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

omit [Small.{v} R] in
/-- The length of an `M`-regular sequence is at most `dim (R ⧸ p)` for every associated prime `p`
of `M`. -/
private theorem length_le_ringKrullDim_quotient_of_isRegular [IsNoetherianRing R]
    [Module.Finite R M] {rs : List R} (reg : IsRegular M rs) {p : Ideal R}
    (hp : IsAssociatedPrime p M) : (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  induction rs generalizing M p with
  | nil =>
    have := hp.isPrime
    simpa using ringKrullDim_nonneg_of_nontrivial (R := R ⧸ p)
  | cons x rs ih =>
    obtain ⟨hx, hrs⟩ := (isRegular_cons_iff M x rs).1 reg
    -- `p` lies in an associated prime `q` of `M ⧸ x M`. As `x` kills `M ⧸ x M` but is
    -- `M`-regular, `x ∈ q ∖ p`, so `dim (R ⧸ q) + 1 ≤ dim (R ⧸ p)`.
    obtain ⟨q, hq, hpq⟩ := hp.exists_le_isAssociatedPrime_quotSMulTop hx
      (maximalIdeal_le_jacobson _ (reg.mem_maximalIdeal List.mem_cons_self))
    have hxq : x ∈ q := hq.annihilator_le <| by
      rw [Submodule.annihilator_top]
      exact QuotSMulTop.mem_annihilator M x
    have hxp : x ∉ p := fun hxp ↦ by
      have hmem : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := Set.mem_biUnion hp hxp
      rw [biUnion_associatedPrimes_eq_compl_regular R M] at hmem
      exact hmem hx
    have := hp.isPrime
    calc ((x :: rs).length : WithBot ℕ∞) = rs.length + 1 := by simp
      _ ≤ ringKrullDim (R ⧸ q) + 1 := by gcongr; exact ih hrs hq
      _ ≤ ringKrullDim (R ⧸ p) := TauCeti.ringKrullDim_quotient_add_one_le_of_lt <|
        lt_of_le_of_ne hpq fun h ↦ hxp (h ▸ hxq)

/-- The depth of a finite module `M` over a Noetherian local ring is at most `dim (R ⧸ p)` for
every associated prime `p` of `M`. H. Matsumura, *Commutative Ring Theory*, Theorem 17.2. -/
theorem depth_le_ringKrullDim_quotient_of_isAssociatedPrime [IsNoetherianRing R]
    [Module.Finite R M] {p : Ideal R} (hp : IsAssociatedPrime p M) :
    (depth (ModuleCat.of R M) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  have : Nontrivial M :=
    not_subsingleton_iff_nontrivial.1 fun _ ↦ not_isAssociatedPrime_of_subsingleton hp
  have := hp.isPrime
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.1 <|
    ne_bot_of_le_ne_bot WithBot.zero_ne_bot (ringKrullDim_nonneg_of_nontrivial (R := R ⧸ p))
  rw [← hd, WithBot.coe_le_coe, depth_eq_sSup_length_isRegular]
  refine sSup_le ?_
  rintro _ ⟨rs, reg, -, rfl⟩
  exact WithBot.coe_le_coe.1 (hd ▸ length_le_ringKrullDim_quotient_of_isRegular reg hp)

/-- The depth of a module over a local ring is zero exactly when there is a nonzero linear map to
it from the residue field `R ⧸ 𝔪`. This is Mathlib's
`ModuleCat.depth_eq_zero_iff_nontrivial_linearMap` with the universe-adjusting `Shrink` in the
definition of `IsLocalRing.depth` removed. -/
theorem depth_eq_zero_iff_nontrivial_linearMap :
    depth (ModuleCat.of R M) = 0 ↔ Nontrivial (R ⧸ maximalIdeal R →ₗ[R] M) := by
  rw [depth, Ideal.depth, ModuleCat.depth_eq_zero_iff_nontrivial_linearMap]
  exact ((Shrink.linearEquiv R (R ⧸ maximalIdeal R)).arrowCongr
    (LinearEquiv.refl R M)).nontrivial_congr

/-- The depth of a module over a Noetherian local ring is zero exactly when the maximal ideal is
an associated prime of the module, that is, when some nonzero element is killed by the maximal
ideal. -/
theorem depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes [IsNoetherianRing R] :
    depth (ModuleCat.of R M) = 0 ↔ maximalIdeal R ∈ associatedPrimes R M := by
  have : IsSimpleModule R (R ⧸ maximalIdeal R) :=
    isSimpleModule_iff_quot_maximal.2 ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
  rw [depth_eq_zero_iff_nontrivial_linearMap, AssociatedPrimes.mem_iff,
    isAssociatedPrime_iff_exists_injective_linearMap,
    and_iff_right (maximalIdeal.isMaximal R).isPrime]
  -- A nonzero linear map out of the simple module `R ⧸ 𝔪` is injective.
  refine ⟨fun ⟨f, g, hfg⟩ ↦ ⟨f - g, ?_⟩, fun ⟨f, hf⟩ ↦ ⟨f, 0, fun h ↦ ?_⟩⟩
  · exact (f - g).injective_or_eq_zero.resolve_right (sub_ne_zero.2 hfg)
  · exact zero_ne_one (hf (by simp [h]) : (0 : R ⧸ maximalIdeal R) = 1)

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
    have prefixRegular : IsWeaklyRegular N (scalars.take (predecessor + 1)) :=
      ((isWeaklyRegular_append_iff N _ (scalars.drop (predecessor + 1))).1
        (by simpa only [List.take_append_drop] using regular.toIsWeaklyRegular)).1
    have prefixMembership : ∀ scalar ∈ scalars.take (predecessor + 1),
        scalar ∈ maximalIdeal R :=
      fun scalar member ↦ membership scalar (List.mem_of_mem_take member)
    have homRegular : IsRegular (M →ₗ[R] N) (scalars.take (predecessor + 1)) :=
      (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal prefixMembership).2
        (prefixRegular.linearMap (by simpa [List.length_take, Nat.min_eq_left length]
          using bound_le_two))
    exact le_sSup ⟨scalars.take (predecessor + 1), homRegular, prefixMembership,
      by simp [List.length_take, Nat.min_eq_left length]⟩

/-- Depth is unchanged under restriction of scalars along a surjective homomorphism of local rings
`R → T`: a finite `T`-module `M` has the same depth over `R` as over `T`. The `M`-regular
sequences in the maximal ideal of `T` are exactly the images of those in the maximal ideal of
`R`. -/
theorem depth_eq_depth_of_surjective [IsNoetherianRing R] {T : Type*} [CommRing T]
    [IsLocalRing T] [Algebra R T] [Small.{v} T] [Module T M] [IsScalarTower R T M]
    [Module.Finite T M] (hsurj : Function.Surjective (algebraMap R T)) :
    depth (ModuleCat.of R M) = depth (ModuleCat.of T M) := by
  have : IsLocalHom (algebraMap R T) := .of_surjective _ hsurj
  have : IsNoetherianRing T := isNoetherianRing_of_surjective R T (algebraMap R T) hsurj
  have : Module.Finite R T := .of_surjective (Algebra.linearMap R T) hsurj
  have : Module.Finite R M := .trans T M
  cases subsingleton_or_nontrivial M
  · rw [depth_eq_top_of_subsingleton, depth_eq_top_of_subsingleton]
  -- A sequence in `R` is `M`-regular in `𝔪_R` exactly when its image is `M`-regular in `𝔪_T`.
  have key (rs : List R) : (IsRegular M (rs.map (algebraMap R T)) ∧
      ∀ t ∈ rs.map (algebraMap R T), t ∈ maximalIdeal T) ↔
      (IsRegular M rs ∧ ∀ r ∈ rs, r ∈ maximalIdeal R) := by
    have hmem : (∀ t ∈ rs.map (algebraMap R T), t ∈ maximalIdeal T) ↔
        ∀ r ∈ rs, r ∈ maximalIdeal R := by
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact forall₂_congr fun r _ ↦ by rw [← Ideal.mem_comap, maximalIdeal_comap]
    rw [hmem, and_congr_left_iff]
    intro hm
    rw [isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hm,
      isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (hmem.2 hm),
      isWeaklyRegular_map_algebraMap_iff]
  rw [depth_eq_sSup_length_isRegular, depth_eq_sSup_length_isRegular]
  congr 1
  ext n
  refine ⟨fun ⟨rs, h, hm, hn⟩ ↦ ?_, fun ⟨ts, h, hm, hn⟩ ↦ ?_⟩
  · obtain ⟨h, hm⟩ := (key rs).2 ⟨h, hm⟩
    exact ⟨_, h, hm, by rw [List.length_map, hn]⟩
  · obtain ⟨rs, rfl⟩ : ∃ rs : List R, rs.map (algebraMap R T) = ts :=
      ⟨ts.map (Function.surjInv hsurj), by simp⟩
    obtain ⟨h, hm⟩ := (key rs).1 ⟨h, hm⟩
    exact ⟨rs, h, hm, by rw [← hn, List.length_map]⟩

/-- In a Noetherian local ring `R` of depth at least two, the maximal ideal is not an associated
prime of `R ⧸ (b)` for a nonzerodivisor `b`: if `𝔪 c ⊆ (b)`, then `c ∈ (b)`. -/
theorem mem_span_singleton_of_forall_mul_mem_of_two_le_depth {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (hdepth : 2 ≤ depth (ModuleCat.of R R)) {b c : R}
    (hb : IsSMulRegular R b) (hc : ∀ z ∈ maximalIdeal R, z * c ∈ Ideal.span {b}) :
    c ∈ Ideal.span {b} := by
  by_cases hbm : b ∈ maximalIdeal R
  swap
  · rw [Ideal.span_singleton_eq_top.2 (notMem_maximalIdeal.1 hbm)]
    exact Submodule.mem_top
  have hspan (x : R) : x ∈ b • (⊤ : Submodule R R) ↔ x ∈ Ideal.span {b} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  -- `depth (R ⧸ (b)) + 1 = depth R ≥ 2`, so no nonzero map `R ⧸ 𝔪 → R ⧸ (b)` exists
  have hdepth' : depth (ModuleCat.of R (QuotSMulTop b R)) ≠ 0 := fun h ↦ by
    have h1 := depth_quotSMulTop_succ_eq_depth hb hbm
    rw [h, zero_add] at h1
    exact absurd (h1 ▸ hdepth) (by decide)
  have : Subsingleton (R ⧸ maximalIdeal R →ₗ[R] QuotSMulTop b R) :=
    not_nontrivial_iff_subsingleton.1 (mt depth_eq_zero_iff_nontrivial_linearMap.2 hdepth')
  -- the map `r ↦ r c` is such a map, and it sends `1` to the class of `c`
  let g : R ⧸ maximalIdeal R →ₗ[R] QuotSMulTop b R :=
    (maximalIdeal R).liftQ (LinearMap.toSpanSingleton R _ (Submodule.Quotient.mk c))
      fun z hz ↦ by
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
          Submodule.Quotient.mk_eq_zero, hspan]
        exact hc z hz
  have hg : g (Submodule.Quotient.mk 1) = 0 := by
    rw [Subsingleton.elim g 0, LinearMap.zero_apply]
  rwa [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul,
    Submodule.Quotient.mk_eq_zero, hspan] at hg

end IsLocalRing

namespace RingEquiv

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-- A ring isomorphism carries regular sequences in the maximal ideal to regular sequences in the
maximal ideal, so it can only increase the depth of a Noetherian local ring over itself. -/
private theorem depth_self_le [IsNoetherianRing R] [IsNoetherianRing S] (e : R ≃+* S) :
    depth (ModuleCat.of R R) ≤ depth (ModuleCat.of S S) := by
  rw [depth_eq_sSup_length_isRegular, depth_eq_sSup_length_isRegular]
  refine sSup_le_sSup ?_
  rintro _ ⟨rs, reg, mem, rfl⟩
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.of_ringEquiv_symm e
  refine ⟨rs.map e, (e.toSemilinearEquiv.isRegular_congr' rs).1 reg, ?_, by simp⟩
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro r hr
  simpa [mem_maximalIdeal, mem_nonunits_iff] using mem r hr

/-- Isomorphic Noetherian local rings have the same depth over themselves. -/
theorem depth_self_eq [IsNoetherianRing R] (e : R ≃+* S) :
    depth (ModuleCat.of R R) = depth (ModuleCat.of S S) :=
  have : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  le_antisymm (depth_self_le e) (depth_self_le e.symm)

end RingEquiv

namespace TauCeti

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M]

open Module

/-- For a module `M` over a Noetherian ring `R` and a prime `p`, the localization `M_p` has depth
zero over `R_p` exactly when `p` is an associated prime of `M`. -/
theorem depth_localizedModule_eq_zero_iff {p : Ideal R} [p.IsPrime] :
    depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) = 0 ↔
      p ∈ associatedPrimes R M :=
  depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes.trans
    maximalIdeal_mem_associatedPrimes_localizedModule_iff

/-- For a module `M` over a Noetherian ring `R` and a prime `p`, the localization `M_p` has depth
at least one over `R_p` exactly when `p` is not an associated prime of `M`. -/
theorem one_le_depth_localizedModule_iff {p : Ideal R} [p.IsPrime] :
    1 ≤ depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) ↔
      p ∉ associatedPrimes R M := by
  rw [Order.one_le_iff_ne_zero, Ne, depth_localizedModule_eq_zero_iff]


/-- Let `M` be a finite module over a Noetherian ring and `a` an `M`-regular element of a prime
`p`. Dividing by `a` lowers the depth of the localization at `p` by exactly one:
`depth (M ⧸ a M)_p + 1 = depth M_p`. -/
theorem depth_localizedModule_quotSMulTop_add_one [Module.Finite R M] {a : R}
    (reg : IsSMulRegular M a) (p : Ideal R) [p.IsPrime] (ha : a ∈ p) :
    depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl (QuotSMulTop a M))) +
      1 = depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) := by
  let Rₚ := Localization.AtPrime p
  have hmax : algebraMap R Rₚ a ∈ maximalIdeal Rₚ :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ p a).2 ha
  -- Localization commutes with the quotient by `a`.
  rw [IsLocalRing.depth_eq_of_linearEquiv (localizedQuotSMulTopEquiv M a p.primeCompl)]
  exact depth_quotSMulTop_succ_eq_depth (reg.of_isLocalizedModule (S := Rₚ) p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)) hmax

end TauCeti
