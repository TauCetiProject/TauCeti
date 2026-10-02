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

Continuous cohomology uses the conjugation identity in the five-term sequence and in
transgression.
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
