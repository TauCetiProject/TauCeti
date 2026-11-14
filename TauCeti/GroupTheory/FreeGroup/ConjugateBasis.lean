/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Conjugates of letters by the powers of another letter

Let `c` be a letter of the free group `F(α)`. The conjugates `cⁿ x c⁻ⁿ` of the letters `x ≠ c`
by the powers of `c`, for `n ∈ ℤ`, are pairwise distinct and freely generate a free subgroup of
`F(α)`. For `α = {a, b}` and `c = b` this is the classical embedding of a free group of countable
rank in the free group of rank two, sending the `i`-th generator to `bⁱ a b⁻ⁱ`.

## Main results

* `FreeGroup.injective_lift_conj_zpow`: for a family of letters `f : ι → α` avoiding `c` and a
  family of exponents `k : ι → ℤ` with the pairs `(f i, k i)` pairwise distinct, the
  homomorphism `FreeGroup ι →* FreeGroup α` sending `i` to `cᵏ⁽ⁱ⁾ f(i) c⁻ᵏ⁽ⁱ⁾` is injective.
* `TauCeti.injective_freeGroup_lift_conj_zpow_of`: the elements `bᵏ a b⁻ᵏ` for distinct `k`
  freely generate a free subgroup of `FreeGroup (Fin 2)`.

## Implementation notes

The conjugates `cⁿ x c⁻ⁿ`, for `x ≠ c` and `n ∈ ℤ`, form the Reidemeister–Schreier basis of the
kernel of the homomorphism `F(α) → ℤ` counting the exponent of `c`. Their freeness is made
concrete by the homomorphism from `F(α)` to the semidirect product `F(α × ℤ) ⋊ ℤ`, with `ℤ`
shifting the second coordinate of the letters, which sends `c` to the generator of `ℤ` and a
letter `x ≠ c` to the letter `(x, 0)`, hence `cⁿ x c⁻ⁿ` to the letter `(x, n)`.
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

/-- The homomorphism from `FreeGroup α` to the semidirect product `F(α × ℤ) ⋊ ℤ` sending the
letter `c` to the generator of `ℤ` and every other letter `x` to the letter `(x, 0)`. -/
private def toShiftSemidirect [DecidableEq α] (c : α) :
    FreeGroup α →* FreeGroup (α × ℤ) ⋊[shiftAction α] Multiplicative ℤ :=
  lift fun x => if x = c then SemidirectProduct.inr (Multiplicative.ofAdd 1)
    else SemidirectProduct.inl (of (x, 0))

private theorem toShiftSemidirect_conj_zpow [DecidableEq α] {c x : α} (hx : x ≠ c) (n : ℤ) :
    toShiftSemidirect c (of c ^ n * of x * (of c ^ n)⁻¹) = SemidirectProduct.inl (of (x, n)) := by
  -- `cⁿ` is sent to `n : ℤ`, and conjugation by `n` shifts the letter `(x, 0)` to `(x, n)`.
  have hc : toShiftSemidirect c (of c) ^ n = SemidirectProduct.inr (Multiplicative.ofAdd n) := by
    simp [toShiftSemidirect, ← map_zpow, ← ofAdd_zsmul]
  rw [← zero_add n, ← shiftAction_ofAdd_of, SemidirectProduct.inl_aut, _root_.map_inv, ← hc]
  simp [toShiftSemidirect, hx]

/- Composed with `toShiftSemidirect c`, the homomorphism of `injective_lift_conj_zpow` is the one
induced by the map of letters `i ↦ (f i, k i)`. -/
private theorem toShiftSemidirect_comp_lift_conj_zpow [DecidableEq α] {c : α} {f : ι → α}
    (hc : ∀ i, f i ≠ c) (k : ι → ℤ) :
    (toShiftSemidirect c).comp (lift fun i => of c ^ k i * of (f i) * (of c ^ k i)⁻¹) =
      SemidirectProduct.inl.comp (map fun i => (f i, k i)) :=
  ext_hom _ _ fun i => by simp [toShiftSemidirect_conj_zpow (hc i)]

/-- Let `c` be a letter of `α`, `f : ι → α` a family of letters different from `c`, and
`k : ι → ℤ` a family of exponents such that the pairs `(f i, k i)` are pairwise distinct. Then
the homomorphism `FreeGroup ι →* FreeGroup α` sending `i` to the conjugate `cᵏ⁽ⁱ⁾ f(i) c⁻ᵏ⁽ⁱ⁾`
is injective: these conjugates freely generate a free subgroup of `FreeGroup α`. -/
theorem injective_lift_conj_zpow {c : α} {f : ι → α} {k : ι → ℤ} (hc : ∀ i, f i ≠ c)
    (hfk : Function.Injective fun i => (f i, k i)) :
    Function.Injective (lift fun i => of c ^ k i * of (f i) * (of c ^ k i)⁻¹) := by
  classical
  refine Function.Injective.of_comp (f := toShiftSemidirect c) ?_
  rw [← MonoidHom.coe_comp, toShiftSemidirect_comp_lift_conj_zpow hc, MonoidHom.coe_comp]
  exact SemidirectProduct.inl_injective.comp (map_injective hfk)

end FreeGroup

namespace TauCeti

/-- For distinct integers `k i`, the elements `bᵏ⁽ⁱ⁾ a b⁻ᵏ⁽ⁱ⁾` of the free group `F(a, b)` freely
generate a free subgroup. In particular `FreeGroup (Fin n)` embeds in `FreeGroup (Fin 2)` by
sending the `i`-th generator to `bⁱ a b⁻ⁱ`. This is the case `c = b`, `f i = a` of
`FreeGroup.injective_lift_conj_zpow`. -/
theorem injective_freeGroup_lift_conj_zpow_of {ι : Type*} {k : ι → ℤ}
    (hk : Function.Injective k) :
    Function.Injective (FreeGroup.lift fun i =>
      (FreeGroup.of (1 : Fin 2) ^ k i * FreeGroup.of 0 * (FreeGroup.of 1 ^ k i)⁻¹)) :=
  FreeGroup.injective_lift_conj_zpow (f := fun _ => 0) (fun _ => zero_ne_one)
    fun _ _ h => hk (Prod.ext_iff.1 h).2

end TauCeti
