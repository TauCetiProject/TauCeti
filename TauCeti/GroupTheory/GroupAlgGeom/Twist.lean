/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Basic
public import Mathlib.Algebra.Group.End

/-!
# Twists of a free `G`-group by the powers of an element

Let `A` be an element of the free `G`-group `G[X] = G ∗ F(X)` and attach to every variable `v` a
pair of integers `(l, r)`. The substitution `v ↦ A ^ l * v * A ^ r` is a `G`-endomorphism
`twistHom A e` of `G[X]`. When all the substitutions for the powers `A ^ k` fix `A`, they form a
one-parameter group of `G`-automorphisms of `G[X]`: the automorphism `twist A e h` for `A` itself
has `k`-th power the substitution for `A ^ k` (`twist_zpow_apply`).

The Nielsen-type automorphisms used to parametrise the solutions of quadratic equations are of
this form: a block of variables is multiplied on the left or on the right, or conjugated, by a
word `A` that the substitution fixes. See [IFT], §7.1, Lemma 41, where the powers of such
automorphisms are computed.

## Main definitions

* `TauCeti.GroupAlgGeom.twistHom A e`: the `G`-endomorphism `v ↦ A ^ (e v).1 * v * A ^ (e v).2`.
* `TauCeti.GroupAlgGeom.twist A e h`: the same substitution as an automorphism of `G[X]`, when
  the substitutions for all powers of `A` fix `A`.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.1.
-/

public section

open Monoid.Coprod

namespace TauCeti.GroupAlgGeom

variable {G X : Type*} [Group G] {A B C : GX G X} {e : X → ℤ × ℤ}

/-- The `G`-endomorphism of `G[X]` substituting `A ^ l * v * A ^ r` for every variable `v`, where
`(l, r) = e v`. -/
def twistHom (A : GX G X) (e : X → ℤ × ℤ) : GX G X →* GX G X :=
  eval inl fun v => A ^ (e v).1 * inr (FreeGroup.of v) * A ^ (e v).2

@[simp]
theorem twistHom_inl (A : GX G X) (e : X → ℤ × ℤ) (g : G) : twistHom A e (inl g) = inl g := by
  simp [twistHom]

@[simp]
theorem twistHom_inr_of (A : GX G X) (e : X → ℤ × ℤ) (v : X) :
    twistHom A e (inr (FreeGroup.of v)) = A ^ (e v).1 * inr (FreeGroup.of v) * A ^ (e v).2 := by
  simp [twistHom]

/-- The twist by the identity element is the identity. -/
@[simp]
theorem twistHom_one (e : X → ℤ × ℤ) : twistHom (1 : GX G X) e = MonoidHom.id _ := by
  simp [twistHom]

/-- Twists by commuting elements compose to the twist by their product, when the outer twist
fixes the element of the inner one. -/
theorem twistHom_comp (hC : twistHom B e C = C) (hBC : Commute B C) :
    (twistHom B e).comp (twistHom C e) = twistHom (B * C) e := by
  refine hom_ext (by ext; simp) (FreeGroup.ext_hom _ _ fun v => ?_)
  simp only [MonoidHom.comp_apply, twistHom_inr_of, map_mul, map_zpow, hC, hBC.mul_zpow]
  rw [(hBC.zpow_zpow _ _).eq]
  simp only [mul_assoc]

/-- The automorphism of `G[X]` substituting `A ^ l * v * A ^ r` for every variable `v`, where
`(l, r) = e v`, when the substitutions for all powers of `A` fix `A`. -/
def twist (A : GX G X) (e : X → ℤ × ℤ) (h : ∀ k : ℤ, twistHom (A ^ k) e A = A) :
    MulAut (GX G X) :=
  MonoidHom.toMulEquiv (twistHom A e) (twistHom A⁻¹ e)
    (by simpa using twistHom_comp (by simpa using h (-1)) (Commute.refl A).inv_left)
    (by
      have h1 : twistHom A e A⁻¹ = A⁻¹ := by simpa using congrArg (·⁻¹) (h 1)
      simpa using twistHom_comp h1 (Commute.refl A).inv_right)

variable (h : ∀ k : ℤ, twistHom (A ^ k) e A = A)
include h

@[simp]
theorem twist_apply (w : GX G X) : twist A e h w = twistHom A e w := (rfl)

/-- The twist fixes the element it twists by. -/
theorem twist_self : twist A e h A = A := by simpa using h 1

/-- The substitutions for two powers of `A` compose to the substitution for the product. -/
theorem twistHom_zpow_comp (j k : ℤ) :
    (twistHom (A ^ j) e).comp (twistHom (A ^ k) e) = twistHom (A ^ (j + k)) e := by
  rw [zpow_add]
  exact twistHom_comp (by rw [map_zpow, h j]) ((Commute.refl A).zpow_zpow j k)

/-- The `k`-th power of the twist by `A` is the substitution `v ↦ (A ^ k) ^ l * v * (A ^ k) ^ r`,
for every integer `k`. -/
theorem twist_zpow_apply (k : ℤ) (w : GX G X) : (twist A e h ^ k) w = twistHom (A ^ k) e w := by
  have hnat (n : ℕ) (w : GX G X) : (twist A e h ^ n) w = twistHom (A ^ (n : ℤ)) e w := by
    induction n generalizing w with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, twist_apply, Int.natCast_succ, add_comm,
        ← twistHom_zpow_comp h 1 n, zpow_one, MonoidHom.comp_apply]
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · exact_mod_cast hnat n w
  · rw [zpow_neg, zpow_natCast, MulAut.inv_apply, eq_comm, MulEquiv.eq_symm_apply, hnat,
      ← MonoidHom.comp_apply, twistHom_zpow_comp h, add_neg_cancel, zpow_zero, twistHom_one,
      MonoidHom.id_apply]

end TauCeti.GroupAlgGeom
