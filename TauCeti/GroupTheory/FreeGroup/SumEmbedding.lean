/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Countable.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Embedding countably many further free generators into two

The free group on a set of letters `α` together with countably many further letters embeds in
the free group on `α` together with two further letters `b` and `c`, by a homomorphism fixing
the letters of `α`: the further letters are sent to the conjugates `cⁿ b c⁻ⁿ` for distinct
integers `n`. No hypothesis is made on `α`. For `α` empty this is the classical embedding of a
free group of countable rank into a free group of rank two
(`TauCeti.injective_freeGroup_lift_conj_zpow_of`).

## Main results

* `FreeGroup.injective_lift_sumElim_conj_zpow`: for an injective `k : ι → ℤ`, the homomorphism
  `FreeGroup (α ⊕ ι) →* FreeGroup (α ⊕ Fin 2)` fixing the letters of `α` and sending `i` to
  `cᵏ⁽ⁱ⁾ b c⁻ᵏ⁽ⁱ⁾` is injective.
* `FreeGroup.exists_injective_monoidHom_sum_fin_two`: for countable `ι`, there is an injective
  homomorphism `FreeGroup (α ⊕ ι) →* FreeGroup (α ⊕ Fin 2)` fixing the letters of `α`.

## Implementation notes

The letters of `α` and the conjugates `cⁿ b c⁻ⁿ` are distinct members of the free basis
`{cⁿ x c⁻ⁿ | x ∈ α ⊔ {b}, n ∈ ℤ}` of the kernel of the homomorphism `F(α ⊔ {b, c}) → ℤ` counting
the exponent of `c`. This is made concrete by the homomorphism from `F(α ⊔ {b, c})` to the
semidirect product `F(Option α × ℤ) ⋊ ℤ`, with `ℤ` shifting the second coordinate of the
letters, which sends `cⁿ x c⁻ⁿ` to the letter `(x, n)`.
-/

public section

namespace FreeGroup

variable {α ι : Type*}

variable (α) in
/-- The action of `ℤ` on `FreeGroup (α × ℤ)` by automorphisms, the integer `n` adding `n` to the
second coordinate of every letter. -/
private def shiftAction : Multiplicative ℤ →* MulAut (FreeGroup (α × ℤ)) where
  toFun n := freeGroupCongr ((Equiv.refl α).prodCongr (Equiv.addRight n.toAdd))
  map_one' := by
    ext
    simp
  map_mul' m n := by
    rw [MulAut.mul_def, freeGroupCongr_trans]
    congr 1
    ext ⟨x, z⟩ <;> simp [add_comm]

private theorem shiftAction_ofAdd_of (n : ℤ) (x : α) (m : ℤ) :
    shiftAction α (Multiplicative.ofAdd n) (of (x, m)) = of (x, m + n) := by
  simp [shiftAction]

variable (α) in
/-- The homomorphism from the free group on `α ⊕ {b, c}` (with `b = inr 0`, `c = inr 1`) to the
semidirect product `F(Option α × ℤ) ⋊ ℤ` sending a letter `a` of `α` to the letter `(some a, 0)`,
`b` to the letter `(none, 0)`, and `c` to the generator of `ℤ`. -/
private def toShiftSemidirect :
    FreeGroup (α ⊕ Fin 2) →* FreeGroup (Option α × ℤ) ⋊[shiftAction (Option α)] Multiplicative ℤ :=
  lift (Sum.elim (fun a => SemidirectProduct.inl (of (some a, 0)))
    ![SemidirectProduct.inl (of (none, 0)), SemidirectProduct.inr (Multiplicative.ofAdd 1)])

private theorem toShiftSemidirect_conj_zpow (n : ℤ) :
    toShiftSemidirect α (of (Sum.inr 1) ^ n * of (Sum.inr 0) * (of (Sum.inr 1) ^ n)⁻¹) =
      SemidirectProduct.inl (of (none, n)) := by
  -- `cⁿ` is sent to `n : ℤ`, and conjugation by `n` shifts the letter `(none, 0)` to `(none, n)`.
  have hc : toShiftSemidirect α (of (Sum.inr 1)) ^ n =
      SemidirectProduct.inr (Multiplicative.ofAdd n) := by
    simp [toShiftSemidirect, ← map_zpow, ← ofAdd_zsmul]
  rw [← zero_add n, ← shiftAction_ofAdd_of, SemidirectProduct.inl_aut, _root_.map_inv, ← hc]
  simp [toShiftSemidirect]

/- Composed with `toShiftSemidirect`, the homomorphism of `injective_lift_sumElim_conj_zpow` is
the one induced by the map of letters `inl a ↦ (some a, 0)`, `inr i ↦ (none, k i)`. -/
private theorem toShiftSemidirect_comp_lift_sumElim (k : ι → ℤ) :
    (toShiftSemidirect α).comp (lift (Sum.elim (fun a : α => of (Sum.inl a)) fun i =>
      of (Sum.inr 1) ^ k i * of (Sum.inr 0) * (of (Sum.inr 1) ^ k i)⁻¹)) =
      SemidirectProduct.inl.comp (map (Sum.elim (fun a => (some a, 0)) fun i => (none, k i))) :=
  ext_hom _ _ <| Sum.rec (fun a => by simp [toShiftSemidirect]) fun i => by
    simp [toShiftSemidirect_conj_zpow]

/-- Let `b = inr 0` and `c = inr 1` be the two further letters of `α ⊕ Fin 2`. For an injective
family of exponents `k : ι → ℤ`, the homomorphism `FreeGroup (α ⊕ ι) →* FreeGroup (α ⊕ Fin 2)`
fixing the letters of `α` and sending the letter `i` of `ι` to `cᵏ⁽ⁱ⁾ b c⁻ᵏ⁽ⁱ⁾` is injective.
For `α` empty this is `TauCeti.injective_freeGroup_lift_conj_zpow_of`. -/
theorem injective_lift_sumElim_conj_zpow {k : ι → ℤ} (hk : Function.Injective k) :
    Function.Injective (lift (Sum.elim (fun a : α => of (Sum.inl a)) fun i =>
      of (Sum.inr 1) ^ k i * of (Sum.inr 0) * (of (Sum.inr 1) ^ k i)⁻¹) :
        FreeGroup (α ⊕ ι) →* FreeGroup (α ⊕ Fin 2)) := by
  refine Function.Injective.of_comp (f := toShiftSemidirect α) ?_
  rw [← MonoidHom.coe_comp, toShiftSemidirect_comp_lift_sumElim, MonoidHom.coe_comp]
  refine SemidirectProduct.inl_injective.comp (map_injective ?_)
  rintro (a | i) (a' | i') h <;> simp_all [hk.eq_iff]

/-- The free group on the letters of `α` and countably many further letters embeds in the free
group on the letters of `α` and two further letters, by a homomorphism fixing the letters of
`α`. -/
theorem exists_injective_monoidHom_sum_fin_two (α ι : Type*) [Countable ι] :
    ∃ φ : FreeGroup (α ⊕ ι) →* FreeGroup (α ⊕ Fin 2),
      Function.Injective φ ∧ ∀ a : α, φ (of (Sum.inl a)) = of (Sum.inl a) := by
  obtain ⟨k, hk⟩ := Countable.exists_injective_nat ι
  exact ⟨_, injective_lift_sumElim_conj_zpow (Nat.cast_injective.comp hk), fun a => by simp⟩

end FreeGroup
