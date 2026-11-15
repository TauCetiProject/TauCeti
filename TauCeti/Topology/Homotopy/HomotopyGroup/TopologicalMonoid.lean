/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.Topology.Homotopy.HomotopyGroup.Product

/-!
# Pointwise products of maps into a topological monoid on homotopy groups

Let `M` be a space with a continuous multiplication and a two-sided unit `1`, for instance a
topological group or a Moore loop space. Two based maps `f : X → M` and `g : Y → M`, sending the
base points to `1`, have the pointwise product `(p, q) ↦ f p * g q : X × Y → M`. This file shows
that in positive dimensions it acts on homotopy groups by

`(f * g)_* (a × b) = f_* a * g_* b`,

where `a × b` is the class of `X × Y` with coordinates `a` and `b` (`HomotopyGroup.prod`). Since
`1` is a strict unit, `(f * g)_* (a × 1) = f_* a` and `(f * g)_* (1 × b) = g_* b` already on
generalized loops, and the general formula follows because `(f * g)_*` is a homomorphism.

Consequently the pointwise product induces a bijection on a homotopy group as soon as one factor
induces a bijection there and the other factor has a trivial source group
(`HomotopyGroup.bijective_map_mul_of_bijective_of_subsingleton`). This is how a product of a map
realizing the low homotopy groups with a map realizing the high ones is recognized as a weak
homotopy equivalence, as for the splitting of the loop space of a complex projective space.

For loops, `f = g = id`, the formula is the first half of the Eckmann--Hilton argument, the
fundamental-group case of which is `FundamentalGroup.cast_map_prod_mul`.

## Main results

* `HomotopyGroup.map_mul_prod`: `(f * g)_* (a × b) = f_* a * g_* b`.
* `HomotopyGroup.bijective_map_mul_of_bijective_of_subsingleton`,
  `HomotopyGroup.bijective_map_mul_of_subsingleton_of_bijective`: the pointwise product is
  bijective on a homotopy group if one factor is and the source group of the other is trivial.
-/

public section

open scoped Topology.Homotopy

namespace HomotopyGroup

variable {N X Y M : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace M]
  [MulOneClass M] [ContinuousMul M] {x : X} {y : Y}

/-- The pointwise product `(p, q) ↦ f p * g q` of two maps sending the base points to `1` sends
the base point of `X × Y` to `1`. -/
theorem mul_comp_fst_comp_snd_apply_eq_one {f : C(X, M)} {g : C(Y, M)} (hf : f x = 1)
    (hg : g y = 1) :
    (f.comp ContinuousMap.fst * g.comp ContinuousMap.snd : C(X × Y, M)) (x, y) = 1 := by
  simp [hf, hg]

section Group

variable [DecidableEq N] [Nonempty N]

/-- Multiplying pointwise by a map sending the base point to the unit does not change the class of
a generalized loop: `(f * g)_* (a × 1) = f_* a`. -/
theorem map_mul_prod_one_right (f : C(X, M)) (g : C(Y, M)) (hf : f x = 1) (hg : g y = 1)
    (a : HomotopyGroup N X x) :
    map (f.comp ContinuousMap.fst * g.comp ContinuousMap.snd : C(X × Y, M))
        (mul_comp_fst_comp_snd_apply_eq_one hf hg) (prod a 1) = map f hf a := by
  induction a using Quotient.inductionOn with
  | h p =>
  rw [← mk_const_eq_one, prod_mk, map_mk, map_mk]
  exact congrArg _ (GenLoop.ext _ _ fun t ↦ by simp [GenLoop.map_apply, hg])

/-- Multiplying pointwise a map sending the base point to the unit does not change the class of a
generalized loop: `(f * g)_* (1 × b) = g_* b`. -/
theorem map_mul_prod_one_left (f : C(X, M)) (g : C(Y, M)) (hf : f x = 1) (hg : g y = 1)
    (b : HomotopyGroup N Y y) :
    map (f.comp ContinuousMap.fst * g.comp ContinuousMap.snd : C(X × Y, M))
        (mul_comp_fst_comp_snd_apply_eq_one hf hg) (prod 1 b) = map g hg b := by
  induction b using Quotient.inductionOn with
  | h q =>
  rw [← mk_const_eq_one, prod_mk, map_mk, map_mk]
  exact congrArg _ (GenLoop.ext _ _ fun t ↦ by simp [GenLoop.map_apply, hf])

/-- **The pointwise product of maps into a topological monoid acts on homotopy groups by the
product of the induced maps.** For based maps `f : X → M` and `g : Y → M` sending the base points
to the unit, the map `(p, q) ↦ f p * g q` sends the class with coordinates `a` and `b` to
`f_* a * g_* b`. -/
@[simp]
theorem map_mul_prod (f : C(X, M)) (g : C(Y, M)) (hf : f x = 1) (hg : g y = 1)
    (a : HomotopyGroup N X x) (b : HomotopyGroup N Y y) :
    map (f.comp ContinuousMap.fst * g.comp ContinuousMap.snd : C(X × Y, M))
        (mul_comp_fst_comp_snd_apply_eq_one hf hg) (prod a b) = map f hf a * map g hg b := by
  rw [← map_mul_prod_one_right f g hf hg, ← map_mul_prod_one_left f g hf hg, ← map_mul,
    ← prod_mul, mul_one, one_mul]

end Group

/-- The pointwise product `(p, q) ↦ f p * g q` induces a bijection on a homotopy group of positive
dimension if `f` does and the corresponding homotopy group of `Y` is trivial. -/
theorem bijective_map_mul_of_bijective_of_subsingleton [Nonempty N] {f : C(X, M)} {g : C(Y, M)}
    (hf : f x = 1) (hg : g y = 1) (hfb : Function.Bijective (map (N := N) f hf))
    [Subsingleton (HomotopyGroup N Y y)] :
    Function.Bijective (map (N := N) (f.comp ContinuousMap.fst * g.comp ContinuousMap.snd :
      C(X × Y, M)) (mul_comp_fst_comp_snd_apply_eq_one hf hg)) := by
  classical
  have : Unique (HomotopyGroup N Y y) := uniqueOfSubsingleton 1
  have h : map (N := N) (f.comp ContinuousMap.fst * g.comp ContinuousMap.snd : C(X × Y, M))
      (mul_comp_fst_comp_snd_apply_eq_one hf hg) = map f hf ∘ Prod.fst ∘ prodEquiv x y := by
    funext c
    obtain ⟨⟨a, b⟩, rfl⟩ := (prodEquiv x y).symm.surjective c
    rw [prodEquiv_symm_apply, map_mul_prod f g hf hg, Subsingleton.elim b 1, map_one, mul_one]
    simp
  rw [h]
  exact hfb.comp ((Equiv.prodUnique _ _).bijective.comp (prodEquiv x y).bijective)

/-- The pointwise product `(p, q) ↦ f p * g q` induces a bijection on a homotopy group of positive
dimension if `g` does and the corresponding homotopy group of `X` is trivial. -/
theorem bijective_map_mul_of_subsingleton_of_bijective [Nonempty N] {f : C(X, M)} {g : C(Y, M)}
    (hf : f x = 1) (hg : g y = 1) [Subsingleton (HomotopyGroup N X x)]
    (hgb : Function.Bijective (map (N := N) g hg)) :
    Function.Bijective (map (N := N) (f.comp ContinuousMap.fst * g.comp ContinuousMap.snd :
      C(X × Y, M)) (mul_comp_fst_comp_snd_apply_eq_one hf hg)) := by
  classical
  have : Unique (HomotopyGroup N X x) := uniqueOfSubsingleton 1
  have h : map (N := N) (f.comp ContinuousMap.fst * g.comp ContinuousMap.snd : C(X × Y, M))
      (mul_comp_fst_comp_snd_apply_eq_one hf hg) = map g hg ∘ Prod.snd ∘ prodEquiv x y := by
    funext c
    obtain ⟨⟨a, b⟩, rfl⟩ := (prodEquiv x y).symm.surjective c
    rw [prodEquiv_symm_apply, map_mul_prod f g hf hg, Subsingleton.elim a 1, map_one, one_mul]
    simp
  rw [h]
  exact hgb.comp ((Equiv.uniqueProd _ _).bijective.comp (prodEquiv x y).bijective)

end HomotopyGroup
