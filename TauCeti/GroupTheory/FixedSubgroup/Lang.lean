/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import TauCeti.GroupTheory.FixedSubgroup

/-!
# Surjective Lang maps and fixed lifts

The Lang map is written in Mathlib's convention as `MonoidHom.commutatorMap F`, namely
`t ↦ t / F t`, and in the algebraic-group convention as `t ↦ t⁻¹ * F t`; the two maps differ
by precomposition with inversion and therefore have the same surjectivity
(`MonoidHom.surjective_inv_mul_iff_surjective_commutatorMap`). On a commutative group, surjectivity
for an iterate of `F` implies surjectivity for `F`, by the telescoping product of the iterates. In
particular, if an iterate is a power map and the corresponding roots exist, the Lang map is
surjective.

Every fiber `{g | g⁻¹ * F g = a}` of the Lang map embeds into `TauCeti.fixedSubgroup F` via
right multiplication by the inverse of a chosen fiber point, so finiteness of `fixedSubgroup F`
makes every Lang fiber finite (`MonoidHom.finite_setOf_inv_mul_eq`).

A surjective Lang map on an invariant subgroup corrects an element whose Frobenius defect lies in
that subgroup to a fixed element in the same coset
(`exists_fixed_inv_mul_of_surjective_commutatorMap` for left multiplication and
`exists_fixed_mul_of_surjective_inv_mul` for a left coset `hJ`, without requiring `J` to be
normal). This is useful for lifting fixed elements of a normalizer or coset quotient; it does not
require a finite kernel or claim uniqueness of a fixed lift. For the induced bijection on fixed
left cosets `G^F ⧸ J^F ≃ (G ⧸ J)^F`, see `TauCeti.GroupTheory.FixedSubgroup.Quotient`.

The telescoping calculation follows the argument of
`MonoidHom.FixedPointFree.prod_pow_eq_one` in Mathlib. The correction argument is the
usual torus correction in Steinberg, *Lectures on Chevalley Groups*, Chapter 11; the non-normal
coset lifting form is used in X. He, *Cocenters of p-adic groups, I: Newton decomposition*,
Forum Math. Pi 6 (2018), e2 (arXiv:1610.04791v3, Lemma 4.5; published Lemma 15).
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
    (hF : ∀ t, (⇑F)^[m] t = t ^ Q)
    (hroot : Function.Surjective (fun t : T ↦ t ^ (Q - 1))) :
    Function.Surjective (commutatorMap F) := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · -- `Q = 0`: the root map is constant, so `T` is trivial
    intro a
    obtain ⟨t, ht⟩ := hroot a
    obtain rfl : a = 1 := by simpa using ht.symm
    exact ⟨1, by simp [commutatorMap_apply]⟩
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

/-- The Lang map `g ↦ g⁻¹ * F g` is surjective if and only if `commutatorMap F`
(`g ↦ g / F g`) is surjective: the two maps differ by precomposition with inversion. -/
theorem surjective_inv_mul_iff_surjective_commutatorMap (F : G →* G) :
    Function.Surjective (fun g : G ↦ g⁻¹ * F g) ↔ Function.Surjective (commutatorMap F) := by
  have hcomp : (fun g : G ↦ g⁻¹ * F g) = commutatorMap F ∘ Inv.inv := by
    ext g
    simp [commutatorMap_apply, div_eq_mul_inv]
  rw [hcomp]
  exact Function.Surjective.of_comp_iff (commutatorMap F) inv_surjective

/-- If the fixed subgroup of an endomorphism `F` is finite, then every fiber of the Lang map
`g ↦ g⁻¹ * F g` is finite: translating by the inverse of a chosen fiber point embeds the fiber
into `TauCeti.fixedSubgroup F`. -/
theorem finite_setOf_inv_mul_eq (F : G →* G) [Finite (TauCeti.fixedSubgroup F)] (a : G) :
    Finite {g : G | g⁻¹ * F g = a} := by
  by_cases hne : Nonempty {g : G | g⁻¹ * F g = a}
  · obtain ⟨⟨g₀, hg₀⟩⟩ := hne
    refine Finite.of_injective
      (fun g : {g : G | g⁻¹ * F g = a} ↦
        (⟨g.val * g₀⁻¹, by
          rw [TauCeti.mem_fixedSubgroup, map_mul, map_inv]
          have hgF : F g.val = g.val * a := eq_mul_of_inv_mul_eq g.property
          have hg₀F : F g₀ = g₀ * a := eq_mul_of_inv_mul_eq hg₀
          rw [hgF, hg₀F, mul_inv_rev, mul_assoc, mul_inv_cancel_left]⟩ :
          TauCeti.fixedSubgroup F))
      fun g₁ g₂ h => Subtype.ext (mul_right_cancel (congrArg Subtype.val h))
  · have : IsEmpty {g : G | g⁻¹ * F g = a} := not_nonempty_iff.mp hne
    infer_instance

/-- Fixed-coset lifting: if `J ≤ G` is a subgroup (not necessarily normal) such that every
element of `J` has the form `z⁻¹ * F z` with `z ∈ J`, then every left coset `hJ` satisfying
`h⁻¹ * F h ∈ J` contains an `F`-fixed element `h * z` with `z ∈ J`. -/
theorem exists_fixed_mul_of_surjective_inv_mul (F : G →* G) (J : Subgroup G)
    (hJ : ∀ d ∈ J, ∃ z ∈ J, z⁻¹ * F z = d) {h : G} (hh : h⁻¹ * F h ∈ J) :
    ∃ z ∈ J, F (h * z) = h * z := by
  obtain ⟨z, hzJ, hz⟩ := hJ _ hh
  refine ⟨z⁻¹, J.inv_mem hzJ, ?_⟩
  have hFh : F h = h * (z⁻¹ * F z) := eq_mul_of_inv_mul_eq hz.symm
  rw [map_mul, map_inv, hFh, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]

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
