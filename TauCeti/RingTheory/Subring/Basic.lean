/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import TauCeti.Algebra.Group.Submonoid.Defs

/-!
# Basic facts about subrings

The inclusion of a subring into itself is the identity homomorphism. In a field, a common
denominator `a` of an element and its inverse clears the denominators of all integer powers of the
element: `a ^ N xⁿ` lies in the subring whenever `|n| ≤ N`, and the same holds for finite
products of integer powers. Moving elements past an element `z` to the right extends from
generators to the subring they generate, and then to powers of `z * w`.

## Main definitions

* `Subring.algebraOfMem`: the `Algebra S A` structure on a subring `A : Subring B` containing
  `algebraMap S B s` for all `s : S`.

## Main results

* `Subring.inclusion_rfl`: the inclusion `R ⊆ R` is `RingHom.id R`.
* `Subring.coe_algebraMap_algebraOfMem`, `Subring.coe_smul_algebraOfMem`: the algebra map and
  scalar action of `Subring.algebraOfMem` agree with those on `B`.
* `Subring.isScalarTower_algebraOfMem`: scalar towers on `B` lift to `Subring.algebraOfMem`.
* `Subring.pow_mul_zpow_mem`: if `a`, `a x` and `a x⁻¹` lie in a subring `A`, then
  `a ^ N xⁿ ∈ A` for every integer `n` with `|n| ≤ N`.
* `Subring.prod_pow_mul_prod_zpow_mem`: the same for a finite product `∏ⱼ xⱼ ^ nⱼ`, with the
  denominator `∏ⱼ aⱼ ^ Nⱼ`.
* `TauCeti.Subring.exists_mul_eq_mul_of_mem_closure`: if `s * z ⊆ z * closure s`, then
  `closure s * z ⊆ z * closure s`.
* `TauCeti.Subring.exists_mul_pow_eq_pow_mul_of_mem_closure_insert`: if `s * z ⊆ z * s` and
  `w ∈ closure (insert z s)`, then `(z * w) ^ n ∈ z ^ n * closure (insert z s)`.
-/

public section

namespace Subring

/-- The inclusion of a subring into itself is the identity homomorphism. -/
@[simp]
theorem inclusion_rfl {A : Type*} [Ring A] (R : Subring A) :
    R.inclusion le_rfl = RingHom.id R :=
  rfl

section Algebra

variable {S B : Type*} [CommSemiring S] [Ring B] [Algebra S B]

/-- A subring `A` of an `S`-algebra `B` containing the image of `algebraMap S B` inherits an
`S`-algebra structure whose algebra map and scalar action agree with those of `B`. -/
@[expose, instance_reducible]
def algebraOfMem (A : Subring B) (h : ∀ s : S, algebraMap S B s ∈ A) : Algebra S A where
  smul s f := ⟨s • (f : B), by
    rw [Algebra.smul_def]
    exact A.mul_mem (h s) f.property⟩
  algebraMap := (algebraMap S B).codRestrict A h
  commutes' s f := Subtype.ext <| by
    simpa only [Subring.coe_mul, RingHom.codRestrict_apply] using Algebra.commutes s (f : B)
  smul_def' s f := Subtype.ext <| by
    rw [Subring.coe_mul, RingHom.codRestrict_apply]
    exact Algebra.smul_def s (f : B)

/-- For `Subring.algebraOfMem`, the algebra map agrees with that of the ambient algebra `B`. -/
theorem coe_algebraMap_algebraOfMem {A : Subring B} (h : ∀ s : S, algebraMap S B s ∈ A) (s : S) :
    (@algebraMap S A _ _ (A.algebraOfMem h) s : B) = algebraMap S B s :=
  RingHom.codRestrict_apply _ _ _ s

/-- For `Subring.algebraOfMem`, scalars act as on the ambient algebra `B`. -/
theorem coe_smul_algebraOfMem {A : Subring B} (h : ∀ s : S, algebraMap S B s ∈ A) (s : S)
    (f : A) :
    ((@HSMul.hSMul S A A (@instHSMul _ _ (A.algebraOfMem h).toSMul) s f : A) : B) =
      s • (f : B) :=
  (rfl)

/-- Scalar towers on the ambient algebra `B` lift to `Subring.algebraOfMem`. -/
theorem isScalarTower_algebraOfMem {T : Type*} [CommSemiring T] [Algebra T B] [SMul S T]
    [IsScalarTower S T B] {A : Subring B} (hS : ∀ s : S, algebraMap S B s ∈ A)
    (hT : ∀ t : T, algebraMap T B t ∈ A) :
    @IsScalarTower S T A _ (A.algebraOfMem hT).toSMul (A.algebraOfMem hS).toSMul :=
  @IsScalarTower.mk S T A _ (A.algebraOfMem hT).toSMul (A.algebraOfMem hS).toSMul
    fun s t f ↦ Subtype.ext <| by
      simp only [coe_smul_algebraOfMem]
      exact smul_assoc s t (f : B)

end Algebra

/-- **Denominators of integer powers.** If `a ∈ A` is a common denominator of `x` and `x⁻¹`, that
is `a x ∈ A` and `a x⁻¹ ∈ A`, then `a ^ N xⁿ ∈ A` for every integer `n` with `|n| ≤ N`. -/
theorem pow_mul_zpow_mem {K : Type*} [Field K] (A : Subring K) {a x : K} (ha : a ∈ A)
    (hx : a * x ∈ A) (hx' : a * x⁻¹ ∈ A) {n : ℤ} {N : ℕ} (hn : n.natAbs ≤ N) :
    a ^ N * x ^ n ∈ A := by
  rcases Int.natAbs_eq n with h | h <;> rw [h, ← Nat.sub_add_cancel hn, pow_add, mul_assoc]
  · rw [zpow_natCast, ← mul_pow]
    exact mul_mem (pow_mem ha _) (pow_mem hx _)
  · rw [zpow_neg, zpow_natCast, ← inv_pow, ← mul_pow]
    exact mul_mem (pow_mem ha _) (pow_mem hx' _)

/-- **Denominators of products of integer powers.** If `aⱼ ∈ A` is a common denominator of `xⱼ`
and `xⱼ⁻¹` and `|nⱼ| ≤ Nⱼ` for each `j ∈ s`, then `(∏ⱼ aⱼ ^ Nⱼ) ∏ⱼ xⱼ ^ nⱼ ∈ A`. -/
theorem prod_pow_mul_prod_zpow_mem {K ι : Type*} [Field K] (A : Subring K) {s : Finset ι}
    {a x : ι → K} {n : ι → ℤ} {N : ι → ℕ} (ha : ∀ j ∈ s, a j ∈ A) (hx : ∀ j ∈ s, a j * x j ∈ A)
    (hx' : ∀ j ∈ s, a j * (x j)⁻¹ ∈ A) (hn : ∀ j ∈ s, (n j).natAbs ≤ N j) :
    (∏ j ∈ s, a j ^ N j) * ∏ j ∈ s, x j ^ n j ∈ A := by
  rw [← Finset.prod_mul_distrib]
  exact prod_mem fun j hj ↦ A.pow_mul_zpow_mem (ha j hj) (hx j hj) (hx' j hj) (hn j hj)

end Subring

namespace TauCeti.Subring

open _root_.Subring

variable {R : Type*} [Ring R]

/-- If every generator `a ∈ s` satisfies `a * z = z * b` for some `b ∈ closure s`, then every
element of `closure s` does. Only this direction of normalization is needed. -/
theorem exists_mul_eq_mul_of_mem_closure {s : Set R} {z a : R}
    (hz : ∀ a ∈ s, ∃ b ∈ closure s, a * z = z * b) (ha : a ∈ closure s) :
    ∃ b ∈ closure s, a * z = z * b := by
  induction ha using closure_induction with
  | mem a ha => exact hz a ha
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | one => exact ⟨1, one_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, hc, he⟩ := ha
    obtain ⟨d, hd, hf⟩ := hb
    exact ⟨c + d, (closure _).add_mem hc hd, by simp [add_mul, mul_add, he, hf]⟩
  | neg a _ ha =>
    obtain ⟨b, hb, he⟩ := ha
    exact ⟨-b, (closure _).neg_mem hb, by simp [he]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨c, hc, he⟩ := ha
    obtain ⟨d, hd, hf⟩ := hb
    refine ⟨c * d, (closure _).mul_mem hc hd, ?_⟩
    calc
      a * b * z = a * (b * z) := mul_assoc _ _ _
      _ = a * (z * d) := by rw [hf]
      _ = (a * z) * d := (mul_assoc _ _ _).symm
      _ = z * (c * d) := by rw [he, mul_assoc]

/-- If every `a ∈ s` satisfies `a * z = z * b` for some `b ∈ s`, then every element of
`closure (insert z s)` satisfies the same relation with `b ∈ closure (insert z s)`. -/
theorem exists_mul_eq_mul_of_mem_closure_insert {s : Set R} {z a : R}
    (hz : ∀ a ∈ s, ∃ b ∈ s, a * z = z * b)
    (ha : a ∈ closure (insert z s)) :
    ∃ b ∈ closure (insert z s), a * z = z * b := by
  refine exists_mul_eq_mul_of_mem_closure ?_ ha
  rintro a (rfl | ha)
  · exact ⟨a, subset_closure (Set.mem_insert _ _), rfl⟩
  · obtain ⟨b, hb, h⟩ := hz a ha
    exact ⟨b, subset_closure (Set.mem_insert_of_mem _ hb), h⟩

/-- If every `a ∈ s` satisfies `a * z = z * b` for some `b ∈ s`, then for every
`w ∈ closure (insert z s)` and `n : ℕ`, the power `(z * w) ^ n` equals `z ^ n * v` for some
`v ∈ closure (insert z s)`. The element `z` need not commute with `s`. -/
theorem exists_mul_pow_eq_pow_mul_of_mem_closure_insert {s : Set R} {z w : R}
    (hz : ∀ a ∈ s, ∃ b ∈ s, a * z = z * b)
    (hw : w ∈ closure (insert z s)) (n : ℕ) :
    ∃ v ∈ closure (insert z s), (z * w) ^ n = z ^ n * v :=
  exists_mul_pow_eq_pow_mul_of_mem
    (fun _ ha ↦ exists_mul_eq_mul_of_mem_closure_insert hz ha) hw n

end TauCeti.Subring
