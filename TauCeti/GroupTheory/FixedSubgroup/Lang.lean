/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Surjective Lang maps and fixed lifts

The Lang map is written in Mathlib's convention as `MonoidHom.commutatorMap F`, namely
`t ↦ t / F t`. On a commutative group, surjectivity for an iterate of `F` implies
surjectivity for `F`, by the telescoping product of the iterates. In particular, if an
iterate is a power map and the corresponding roots exist, the Lang map is surjective.

A surjective Lang map on an invariant subgroup corrects an element whose Frobenius defect
lies in that subgroup to a fixed element in the same coset. This is useful for lifting
fixed elements of a normalizer quotient; it does not require a finite kernel or claim
uniqueness of a fixed lift.

The telescoping calculation follows the argument of
`MonoidHom.FixedPointFree.prod_pow_eq_one` in Mathlib. The correction argument is the
usual torus correction in Steinberg, *Lectures on Chevalley Groups*, Chapter 11.
-/

public section

namespace MonoidHom

section CommGroup

variable {T : Type*} [CommGroup T]

/-- The Lang map of the product of the first `m` iterates telescopes to the Lang map
of the `m`-th iterate. -/
theorem commutatorMap_prod_range (F : T →* T) (m : ℕ) (t : T) :
    commutatorMap F (∏ i ∈ Finset.range m, (⇑F)^[i] t) = t / (⇑F)^[m] t := by
  simp only [commutatorMap_apply, map_prod, ← Finset.prod_div_distrib,
    ← Function.iterate_succ_apply']
  exact Finset.prod_range_div' (fun i ↦ (⇑F)^[i] t) m

/-- On a commutative group, surjectivity of the Lang map of any iterate implies
surjectivity of the Lang map of the original endomorphism. -/
theorem surjective_commutatorMap_of_iterate (F : T →* T) (m : ℕ)
    (h : Function.Surjective (commutatorMap ((⇑F)^[m]))) :
    Function.Surjective (commutatorMap F) := by
  intro a
  obtain ⟨t, ht⟩ := h a
  exact ⟨∏ i ∈ Finset.range m, (⇑F)^[i] t, (F.commutatorMap_prod_range m t).trans ht⟩

/-- If an iterate of `F` is the `Q`-th power map, and every element has a
`(Q - 1)`-st root, then the Lang map of `F` is surjective. -/
theorem surjective_commutatorMap_of_iterate_eq_pow (F : T →* T) {m Q : ℕ}
    (hQ : 0 < Q) (hF : ∀ t, (⇑F)^[m] t = t ^ Q)
    (hroot : Function.Surjective (fun t : T ↦ t ^ (Q - 1))) :
    Function.Surjective (commutatorMap F) := by
  apply F.surjective_commutatorMap_of_iterate m
  intro a
  obtain ⟨t, ht⟩ := hroot a⁻¹
  dsimp only at ht
  refine ⟨t, ?_⟩
  rw [commutatorMap_apply, hF, ← Nat.sub_add_cancel (by omega : 1 ≤ Q), pow_succ, ht]
  simp [div_eq_mul_inv, mul_comm]

end CommGroup

section Group

variable {T G : Type*} [Group T] [Group G]

/-- Correct an element to a fixed element by left multiplication from an invariant
subgroup with surjective Lang map. The defect must lie in the subgroup's image. -/
theorem exists_fixed_inv_mul_of_surjective_commutatorMap (ι : T →* G)
    (f : T →* T) (F : G →* G) (hι : ∀ t, F (ι t) = ι (f t))
    (hf : Function.Surjective (commutatorMap f)) {n : G}
    (hn : n / F n ∈ ι.range) :
    ∃ t : T, F ((ι t)⁻¹ * n) = (ι t)⁻¹ * n := by
  obtain ⟨d, hd⟩ := hn
  obtain ⟨t, ht⟩ := hf d
  simp only [commutatorMap_apply] at ht
  have hc : ι t / F (ι t) = n / F n := by
    rw [hι, ← map_div, ht, hd]
  refine ⟨t, ?_⟩
  apply mul_left_cancel (a := ι t)
  calc
    ι t * F ((ι t)⁻¹ * n) = (ι t / F (ι t)) * F n := by
      simp [div_eq_mul_inv, mul_assoc]
    _ = (n / F n) * F n := by rw [hc]
    _ = ι t * ((ι t)⁻¹ * n) := by simp

/-- An equivariant surjection admits fixed lifts if its kernel is parametrized by an
invariant group with surjective Lang map. The parametrization need not be injective. -/
theorem exists_fixed_lift_of_surjective_commutatorMap {H : Type*} [Group H]
    (ψ : G →* H) (j : T →* G) (hker : j.range = ψ.ker)
    (f : T →* T) (F : G →* G) (F' : H →* H)
    (hψ : ∀ x, ψ (F x) = F' (ψ x)) (hj : ∀ t, F (j t) = j (f t))
    (hsurj : Function.Surjective ψ) (hf : Function.Surjective (commutatorMap f))
    {y : H} (hy : F' y = y) :
    ∃ x : G, F x = x ∧ ψ x = y := by
  obtain ⟨n, hn⟩ := hsurj y
  have hd : n / F n ∈ j.range := by
    rw [hker, mem_ker, map_div, hψ, hn, hy, div_self']
  obtain ⟨t, ht⟩ := j.exists_fixed_inv_mul_of_surjective_commutatorMap f F hj hf hd
  refine ⟨(j t)⁻¹ * n, ht, ?_⟩
  have htker : ψ (j t) = 1 := mem_ker.mp (hker ▸ ⟨t, rfl⟩)
  simp [htker, hn]

end Group

end MonoidHom
