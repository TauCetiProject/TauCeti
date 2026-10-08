/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

/-!
# Identities of unbundled `1`-cocycles

Facts about a `1`-cocycle `f : G → M` in the sense of Mathlib's unbundled
`groupCohomology.IsCocycle₁`, which need no topology and no representation:

* `groupCohomology.smul_apply_inv_mul_mul_of_isCocycle₁`: conjugating the argument by `k` and
  then acting by `k` adds `m • f k - f k` to the value at `m`, for any scalar multiplication of
  `G` on `M`: `k • f (k⁻¹ * m * k) = m • f k - f k + f m`.
* `groupCohomology.smul_zero_of_isCocycle₁`: an action admitting a `1`-cocycle fixes `0`.
* `groupCohomology.zeroLocus`: the zero locus `{g | f g = 0}` is a subgroup of `G`, for any group
  action (not necessarily distributive) admitting the cocycle. As a set it is `f ⁻¹' {0}`
  (`groupCohomology.coe_zeroLocus`). `GroupCohomology/Cocycle/Topology.lean` shows it is closed
  when `f` is continuous into a `T1` space, and deduces that such an `f` vanishing on a
  topological generating set vanishes everywhere.

* `TauCeti.isCocycle₁_ext_of_forall_mem_zpowers`: a one-cocycle on a cyclic group is
  determined by its value at a generator.
* `TauCeti.groupNorm`: the sum of the scalar actions of a finite group, as an additive
  homomorphism, with no topology or representation required. For a finite normal subgroup it
  commutes with the action of the ambient group (`TauCeti.groupNorm_smul`), and so is a
  `G`-equivariant additive endomorphism (`TauCeti.groupNormHom`).
* `TauCeti.sum_smul_apply_eq_zero_of_isCocycle₁`: on a finite group, the group norm kills
  every value of a one-cocycle.

Continuous cohomology uses the conjugation identity in the five-term sequence and in
transgression, and the cyclic-group facts in the vanishing criterion.
-/

public section

namespace groupCohomology

/-- Conjugating the argument of a `1`-cocycle by `k` and then acting by `k` adds `m • c k - c k`
to its value at `m`: `k • c (k⁻¹ * m * k) = m • c k - c k + c m`. Only a scalar multiplication
of `G` on `M` is needed, not an action. -/
theorem smul_apply_inv_mul_mul_of_isCocycle₁ {G M : Type*} [Group G] [AddCommGroup M] [SMul G M]
    {c : G → M} (hc : IsCocycle₁ c) (k m : G) :
    k • c (k⁻¹ * m * k) = m • c k - c k + c m := by
  have hmul : k * (k⁻¹ * m * k) = m * k := by group
  have h := hc k (k⁻¹ * m * k)
  rw [hmul, hc m k] at h
  rw [eq_sub_of_add_eq h.symm]
  abel

/-- A monoid action on an additive group that admits a `1`-cocycle fixes `0`. -/
theorem smul_zero_of_isCocycle₁ {G M : Type*} [Monoid G] [AddCommGroup M] [MulAction G M]
    {f : G → M} (hf : IsCocycle₁ f) (g : G) : g • (0 : M) = 0 := by
  simpa only [mul_one, map_one_of_isCocycle₁ hf, right_eq_add] using hf g 1

variable {G M : Type*} [Group G] [AddCommGroup M] [MulAction G M]

/-- **The zero locus of a `1`-cocycle**, `{g | f g = 0}`, as a subgroup of `G`, for any group
action (not necessarily distributive). -/
def zeroLocus {f : G → M} (hf : IsCocycle₁ f) : Subgroup G where
  carrier := {g | f g = 0}
  one_mem' := map_one_of_isCocycle₁ hf
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [hf g h, hg, hh, smul_zero_of_isCocycle₁ hf, add_zero]
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have h := map_inv_of_isCocycle₁ hf g
    rwa [hg, neg_zero, ← smul_zero_of_isCocycle₁ hf g, smul_left_cancel_iff] at h

/-- An element lies in the zero locus of a `1`-cocycle exactly when the cocycle vanishes there. -/
@[simp]
theorem mem_zeroLocus {f : G → M} (hf : IsCocycle₁ f) {g : G} : g ∈ zeroLocus hf ↔ f g = 0 :=
  Iff.rfl

/-- The zero locus of a `1`-cocycle is the preimage of `0`. -/
@[simp]
theorem coe_zeroLocus {f : G → M} (hf : IsCocycle₁ f) : (zeroLocus hf : Set G) = f ⁻¹' {0} :=
  (rfl)

end groupCohomology

namespace TauCeti

open groupCohomology

/-- The group norm, `m ↦ ∑ x, x • m`, as an additive homomorphism. It needs only a finite
scalar type and distributive scalar multiplication on an additive commutative monoid. -/
def groupNorm (G M : Type*) [Fintype G] [AddCommMonoid M] [DistribSMul G M] : M →+ M :=
  ∑ x : G, DistribSMul.toAddMonoidHom M x

/-- Applying the group norm sums the scalar translates of the argument. -/
@[simp]
theorem groupNorm_apply (G M : Type*) [Fintype G] [AddCommMonoid M] [DistribSMul G M]
    (m : M) : groupNorm G M m = ∑ x : G, x • m := by
  simp [groupNorm]

/-- The norm of a finite normal subgroup `N` of `G` commutes with the action of `G`: conjugation
by `g` permutes `N`. -/
theorem groupNorm_smul {G M : Type*} [Group G] [AddCommMonoid M] [DistribMulAction G M]
    (N : Subgroup G) [N.Normal] [Fintype N] (g : G) (m : M) :
    groupNorm N M (g • m) = g • groupNorm N M m := by
  simp only [groupNorm_apply, Finset.smul_sum, Subgroup.smul_def]
  exact Fintype.sum_equiv (MulAut.conjNormal g⁻¹).toEquiv _ _ fun n ↦ by
    simp [← mul_smul, mul_assoc]

/-- The norm of a finite normal subgroup `N` of `G`, as a `G`-equivariant additive endomorphism
of `M` (`TauCeti.groupNorm_smul`). -/
def groupNormHom {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [Fintype N] (M : Type*)
    [AddCommMonoid M] [DistribMulAction G M] : M →+[G] M :=
  { groupNorm N M with map_smul' := groupNorm_smul N }

/-- The equivariant norm `groupNormHom N M` is the group norm of `N`. -/
@[simp]
theorem groupNormHom_apply {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [Fintype N]
    (M : Type*) [AddCommMonoid M] [DistribMulAction G M] (m : M) :
    groupNormHom N M m = groupNorm N M m :=
  (rfl)

variable {G M : Type*} [Group G] [AddCommGroup M] [MulAction G M]

/-- Two one-cocycles on a cyclic group agree if they agree at a generator. No finiteness or
continuity hypothesis is needed, and the action need not be distributive. -/
theorem isCocycle₁_ext_of_forall_mem_zpowers {f f' : G → M} (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (hf : IsCocycle₁ f) (hf' : IsCocycle₁ f')
    (h : f g = f' g) : f = f' := by
  let S : Subgroup G :=
    { carrier := {x | f x = f' x}
      one_mem' := (map_one_of_isCocycle₁ hf).trans (map_one_of_isCocycle₁ hf').symm
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [hf x y, hf' x y, hx, hy]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [← smul_left_cancel_iff x]
        rw [map_inv_of_isCocycle₁ hf, map_inv_of_isCocycle₁ hf', hx] }
  have hle : Subgroup.zpowers g ≤ S := Subgroup.zpowers_le.mpr h
  funext x
  exact hle (hg x)

omit [MulAction G M] in
/-- The value of a one-cocycle on a finite group lies in the kernel of the group norm.
This holds at every group element, not just at a cyclic generator. Even associativity and
distributivity of the scalar multiplication are unnecessary for this identity. -/
theorem sum_smul_apply_eq_zero_of_isCocycle₁ [SMul G M] [Fintype G] {f : G → M}
    (g : G) (hf : IsCocycle₁ f) : ∑ x : G, x • f g = 0 := by
  have hsum : (∑ x : G, f x) = (∑ x : G, x • f g) + ∑ x : G, f x := by
    calc
      (∑ x : G, f x) = ∑ x : G, f (x * g) :=
        (Fintype.sum_bijective _ (Group.mulRight_bijective g) _ _ (fun _ ↦ rfl)).symm
      _ = _ := by simp only [hf _ _, Finset.sum_add_distrib]
  exact (add_right_cancel (hsum.symm.trans (zero_add _).symm))

end TauCeti
