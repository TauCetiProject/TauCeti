/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import TauCeti.GroupTheory.FixedSubgroup
import Mathlib.Tactic.Group
import TauCeti.Algebra.BigOperators.Finset.Range

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

A surjective homomorphism intertwining two maps transports surjectivity of the Lang map
`g ↦ g⁻¹ * F g` (`MonoidHom.surjective_inv_mul_of_semiconj`).

A surjective Lang map on an invariant subgroup corrects an element whose Frobenius defect lies in
that subgroup to a fixed element in the same coset
(`exists_fixed_inv_mul_of_surjective_commutatorMap` for left multiplication, and
`exists_fixed_mul_of_surjective_inv_mul` for a left coset `hJ` without requiring `J` to be normal
or `F`-invariant). This is useful for lifting fixed elements of a normalizer or coset quotient; it
does not require a finite kernel or claim uniqueness of a fixed lift. For the induced bijection on
fixed left cosets `G^F ⧸ J^F ≃ (G ⧸ J)^F`, see `TauCeti.GroupTheory.FixedSubgroup.Quotient`.

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

/-- On a commutative group, surjectivity of the Lang map of any iterate implies
surjectivity of the Lang map of the original endomorphism. -/
theorem surjective_commutatorMap_of_iterate (F : T →* T) (m : ℕ)
    (h : Function.Surjective (commutatorMap ((⇑F)^[m]))) :
    Function.Surjective (commutatorMap F) := by
  intro a
  obtain ⟨t, ht⟩ := h a
  refine ⟨∏ i ∈ Finset.range m, (⇑F)^[i] t, Eq.trans ?_ ht⟩
  simpa only [commutatorMap_apply, inv_div] using
    congrArg Inv.inv (TauCeti.map_prod_iterate_div F m t)

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
          rw [TauCeti.mem_fixedSubgroup, map_mul, map_inv,
            eq_mul_of_inv_mul_eq g.property, eq_mul_of_inv_mul_eq hg₀]
          group⟩ :
          TauCeti.fixedSubgroup F))
      fun g₁ g₂ h => Subtype.ext (mul_right_cancel (congrArg Subtype.val h))
  · have : IsEmpty {g : G | g⁻¹ * F g = a} := not_nonempty_iff.mp hne
    infer_instance

/-- **Fixed-coset lifting (without `F`-invariance)**: if `J ≤ G` is a subgroup (not necessarily
normal or `F`-invariant) such that every element of `J` has the form `z⁻¹ * F z` with `z ∈ J`,
then every left coset `hJ` satisfying `h⁻¹ * F h ∈ J` contains an `F`-fixed element `h * z` with
`z ∈ J`. Unlike `exists_fixed_inv_mul_of_surjective_commutatorMap`, no endomorphism `f : J →* J`
intertwining `F` is assumed. -/
theorem exists_fixed_mul_of_surjective_inv_mul (F : G →* G) (J : Subgroup G)
    (hJ : ∀ d ∈ J, ∃ z ∈ J, z⁻¹ * F z = d) {h : G} (hh : h⁻¹ * F h ∈ J) :
    ∃ z ∈ J, F (h * z) = h * z := by
  obtain ⟨z, hzJ, hz⟩ := hJ _ hh
  refine ⟨z⁻¹, J.inv_mem hzJ, ?_⟩
  have hFh : F h = h * (z⁻¹ * F z) := eq_mul_of_inv_mul_eq hz.symm
  rw [map_mul, map_inv, hFh]
  group

/-- Correct an element to a fixed element by left multiplication from an invariant
subgroup with surjective Lang map. The defect must lie in the subgroup's image. -/
@[to_additive exists_fixed_neg_add_of_surjective_id_sub
  /-- Correct an element to a fixed element by adding an element from an invariant subgroup
  on which the difference map `t ↦ t - f t` is surjective. -/]
theorem exists_fixed_inv_mul_of_surjective_commutatorMap (ι : T →* G)
    (f : T →* T) (F : G →* G) (hι : ∀ t, F (ι t) = ι (f t))
    (hf : Function.Surjective (fun t ↦ t / f t)) {n : G}
    (hn : n / F n ∈ ι.range) :
    ∃ t : T, F ((ι t)⁻¹ * n) = (ι t)⁻¹ * n := by
  obtain ⟨d, hd⟩ := hn
  obtain ⟨t, rfl⟩ := hf d
  have hc : ι t / F (ι t) = n / F n := by
    simpa only [hι, map_div] using hd
  refine ⟨t, ?_⟩
  apply mul_left_cancel (a := ι t)
  calc
    ι t * F ((ι t)⁻¹ * n) = (ι t / F (ι t)) * F n := by
      simp [div_eq_mul_inv, mul_assoc]
    _ = (n / F n) * F n := by rw [hc]
    _ = ι t * ((ι t)⁻¹ * n) := by simp

/-- Fixed points in the image of an equivariant map lift if its kernel is parametrized by an
invariant group with surjective Lang map. The parametrization need not be injective. -/
@[to_additive exists_fixed_lift_of_surjective_id_sub
  /-- A fixed point in the image lifts to a fixed point when the difference map
  `t ↦ t - f t` is surjective on a group parametrizing the kernel. -/]
theorem exists_fixed_lift_of_surjective_commutatorMap {H : Type*} [Group H]
    (ψ : G →* H) (j : T →* G) (hex : Function.MulExact j ψ)
    (f : T →* T) (F : G →* G) (F' : H →* H)
    (hψ : ∀ x, ψ (F x) = F' (ψ x)) (hj : ∀ t, F (j t) = j (f t))
    (hf : Function.Surjective (fun t ↦ t / f t)) {y : H} (hy_range : y ∈ Set.range ψ)
    (hy : F' y = y) :
    ∃ x : G, F x = x ∧ ψ x = y := by
  obtain ⟨n, hn⟩ := hy_range
  have hd : n / F n ∈ j.range := by
    apply (hex _).mp
    rw [map_div, hψ, hn, hy, div_self']
  obtain ⟨t, ht⟩ := j.exists_fixed_inv_mul_of_surjective_commutatorMap f F hj hf hd
  refine ⟨(j t)⁻¹ * n, ht, ?_⟩
  simp [hex.apply_apply_eq_one, hn]

/-- A surjective homomorphism intertwining two maps transports surjectivity of the Lang map
`g ↦ g⁻¹ * F g`. -/
theorem surjective_inv_mul_of_semiconj {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (e : G₁ →* G₂) (he : Function.Surjective e) {F₁ : G₁ → G₁} {F₂ : G₂ → G₂}
    (hF : Function.Semiconj e F₁ F₂)
    (hsurj : Function.Surjective fun g : G₁ => g⁻¹ * F₁ g) :
    Function.Surjective fun g : G₂ => g⁻¹ * F₂ g := by
  intro a
  obtain ⟨b, rfl⟩ := he a
  obtain ⟨g, hg⟩ := hsurj b
  refine ⟨e g, ?_⟩
  dsimp only at hg
  calc
    (e g)⁻¹ * F₂ (e g) = e g⁻¹ * e (F₁ g) := by rw [map_inv, hF g]
    _ = e (g⁻¹ * F₁ g) := (map_mul e _ _).symm
    _ = e b := by rw [hg]

end Group

end MonoidHom

/-- Fixed points in the image of an equivariant additive homomorphism lift when the difference map
`t ↦ f t - t` is surjective on a group parametrizing its kernel. -/
theorem AddMonoidHom.exists_fixed_lift_of_surjective_sub_id {T G H : Type*}
    [AddGroup T] [AddGroup G] [AddGroup H] (ψ : G →+ H) (j : T →+ G)
    (hex : Function.Exact j ψ) (f : T →+ T) (F : G →+ G) (F' : H →+ H)
    (hψ : ∀ x, ψ (F x) = F' (ψ x)) (hj : ∀ t, F (j t) = j (f t))
    (hf : Function.Surjective (fun t => f t - t)) {y : H} (hy_range : y ∈ Set.range ψ)
    (hy : F' y = y) : ∃ x : G, F x = x ∧ ψ x = y := by
  apply ψ.exists_fixed_lift_of_surjective_id_sub j hex f F F' hψ hj _ hy_range hy
  intro t
  obtain ⟨s, hs⟩ := hf (-t)
  exact ⟨s, by simpa only [neg_sub, neg_neg] using congrArg Neg.neg hs⟩
