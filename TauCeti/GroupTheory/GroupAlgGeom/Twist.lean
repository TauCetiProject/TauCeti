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
`twistHom A e` of `G[X]`; evaluating its image of a word at a point `u` is evaluating the word
at the point `v ↦ A(u) ^ l * u v * A(u) ^ r` (`eval_twistHom`). When the substitution for `A`
fixes `A`, so do the substitutions for the natural powers of `A` (`twistHom_pow_self`), and they
fix every element that the substitution for `A` fixes
(`twistHom_pow_apply_eq_self_of_apply_eq_self`). When the substitutions for `A` and for `A⁻¹`
fix `A`, so do the substitutions for all the powers `A ^ k` (`twistHom_zpow_self`), and these
form a one-parameter group of `G`-automorphisms of `G[X]`: the automorphism `twist A e h₁ h₂` for
`A` itself has `k`-th power the substitution for `A ^ k` (`twist_pow_apply`, `twist_zpow_apply`),
and its inverse is the substitution for `A⁻¹` (`twist_symm_apply`).

The Nielsen-type automorphisms used to parametrise the solutions of quadratic equations are of
this form: a block of variables is multiplied on the left or on the right, or conjugated, by a
word `A` that the substitution fixes. See [IFT], §7.1, Lemma 41, where the powers of such
automorphisms are computed.

## Main definitions

* `TauCeti.GroupAlgGeom.twistHom A e`: the `G`-endomorphism `v ↦ A ^ (e v).1 * v * A ^ (e v).2`.
* `TauCeti.GroupAlgGeom.twist A e h₁ h₂`: the same substitution as an automorphism of `G[X]`,
  when the substitutions for `A` and for `A⁻¹` fix `A`.

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

theorem twistHom_def (A : GX G X) (e : X → ℤ × ℤ) :
    twistHom A e = eval inl fun v => A ^ (e v).1 * inr (FreeGroup.of v) * A ^ (e v).2 := (rfl)

@[simp]
theorem twistHom_comp_inl (A : GX G X) (e : X → ℤ × ℤ) : (twistHom A e).comp inl = inl :=
  eval_comp_inl ..

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

/-- If the substitution for `A` fixes `A` and `w`, then the substitution for every natural power
of `A` fixes `w`. -/
theorem twistHom_pow_apply_eq_self_of_apply_eq_self (h₁ : twistHom A e A = A)
    {w : GX G X} (hw : twistHom A e w = w) (n : ℕ) : twistHom (A ^ n) e w = w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← twistHom_comp (by rw [map_pow, h₁]) (Commute.self_pow A n),
      MonoidHom.comp_apply, ih, hw]

/-- If the substitution for `A` fixes `A`, then so does the substitution for every natural power
of `A`. -/
theorem twistHom_pow_self (h₁ : twistHom A e A = A) (n : ℕ) : twistHom (A ^ n) e A = A :=
  twistHom_pow_apply_eq_self_of_apply_eq_self h₁ h₁ n

/-- If the substitution for `A` fixes `A`, then the substitutions for two natural powers of `A`
compose to the substitution for the product. -/
theorem twistHom_pow_comp (h₁ : twistHom A e A = A) (j k : ℕ) :
    (twistHom (A ^ j) e).comp (twistHom (A ^ k) e) = twistHom (A ^ (j + k)) e := by
  rw [pow_add]
  exact twistHom_comp (by rw [map_pow, twistHom_pow_self h₁ j]) ((Commute.refl A).pow_pow j k)

/-- If the substitutions for `A` and for `A⁻¹` fix `A`, then so does the substitution for every
integer power of `A`. -/
theorem twistHom_zpow_self (h₁ : twistHom A e A = A) (h₂ : twistHom A⁻¹ e A = A) (k : ℤ) :
    twistHom (A ^ k) e A = A := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · rw [zpow_natCast, twistHom_pow_self h₁]
  · rw [zpow_neg, zpow_natCast, ← inv_pow, ← inv_inj, ← map_inv,
      twistHom_pow_self (by rw [map_inv, h₂])]

/-- Evaluating the image of a word under the substitution `v ↦ A ^ l * v * A ^ r` at a point `u`
is evaluating the word at the point `v ↦ A(u) ^ l * u v * A(u) ^ r`. -/
@[simp]
theorem eval_twistHom {H : Type*} [Group H] (ι : G →* H) (u : X → H) (A : GX G X)
    (e : X → ℤ × ℤ) (w : GX G X) :
    eval ι u (twistHom A e w) =
      eval ι (fun v => eval ι u A ^ (e v).1 * u v * eval ι u A ^ (e v).2) w := by
  rw [twistHom_def, ← MonoidHom.comp_apply, MonoidHom.comp_eval, eval_comp_inl]
  simp [Function.comp_def]

/-- The automorphism of `G[X]` substituting `A ^ l * v * A ^ r` for every variable `v`, where
`(l, r) = e v`, when the substitutions for `A` and for `A⁻¹` fix `A`. Its inverse is the
substitution for `A⁻¹`. -/
def twist (A : GX G X) (e : X → ℤ × ℤ) (h₁ : twistHom A e A = A) (h₂ : twistHom A⁻¹ e A = A) :
    MulAut (GX G X) :=
  MonoidHom.toMulEquiv (twistHom A e) (twistHom A⁻¹ e)
    (by simpa using twistHom_comp h₂ (Commute.refl A).inv_left)
    (by simpa using twistHom_comp (C := A⁻¹) (by rw [map_inv, h₁]) (Commute.refl A).inv_right)

variable (h₁ : twistHom A e A = A) (h₂ : twistHom A⁻¹ e A = A)
include h₁ h₂

@[simp]
theorem twist_apply (w : GX G X) : twist A e h₁ h₂ w = twistHom A e w := (rfl)

/-- The inverse of the twist by `A` is the substitution for `A⁻¹`. -/
@[simp]
theorem twist_symm_apply (w : GX G X) : (twist A e h₁ h₂).symm w = twistHom A⁻¹ e w := (rfl)

/-- The twist fixes the element it twists by. -/
theorem twist_self : twist A e h₁ h₂ A = A := h₁

/-- The substitutions for two integer powers of `A` compose to the substitution for the product,
when the substitutions for `A` and for `A⁻¹` fix `A`. -/
theorem twistHom_zpow_comp (j k : ℤ) :
    (twistHom (A ^ j) e).comp (twistHom (A ^ k) e) = twistHom (A ^ (j + k)) e := by
  rw [zpow_add]
  exact twistHom_comp (by rw [map_zpow, twistHom_zpow_self h₁ h₂ j])
    ((Commute.refl A).zpow_zpow j k)

/-- The `n`-th power of the twist by `A` is the substitution `v ↦ (A ^ n) ^ l * v * (A ^ n) ^ r`,
for every natural number `n`. -/
@[simp]
theorem twist_pow_apply (n : ℕ) (w : GX G X) :
    (twist A e h₁ h₂ ^ n) w = twistHom (A ^ n) e w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, twist_apply, pow_succ',
      ← twistHom_comp (by rw [map_pow, h₁]) ((Commute.refl A).pow_right n), MonoidHom.comp_apply]

/-- The `k`-th power of the twist by `A` is the substitution `v ↦ (A ^ k) ^ l * v * (A ^ k) ^ r`,
for every integer `k`. -/
@[simp]
theorem twist_zpow_apply (k : ℤ) (w : GX G X) :
    (twist A e h₁ h₂ ^ k) w = twistHom (A ^ k) e w := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · simp
  · rw [zpow_neg, zpow_natCast, MulAut.inv_apply, eq_comm, MulEquiv.eq_symm_apply,
      twist_pow_apply, ← zpow_natCast, ← MonoidHom.comp_apply, twistHom_zpow_comp h₁ h₂,
      add_neg_cancel, zpow_zero, twistHom_one, MonoidHom.id_apply]

end TauCeti.GroupAlgGeom
