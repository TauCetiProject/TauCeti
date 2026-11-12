/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import TauCeti.Data.ZMod.MulCastHom
import Mathlib.Algebra.BigOperators.Pi
import TauCeti.GroupTheory.Coset.Fiber

/-!
# Sums over `ι → ZMod n` along reduction and multiplication

For `n = m * k`, the coordinatewise reduction `(ι → ZMod n) → (ι → ZMod k)` is a surjective
additive homomorphism whose fibers have `m ^ #ι` elements, so summing a function of the reduction
over `ι → ZMod n` counts every value `m ^ #ι` times. Dually, the vectors of `ι → ZMod n` killed by
`m` are exactly the images of `ι → ZMod m` under the coordinatewise multiplication by `k`
(`ZMod.mulCastHom`), each attained once, so a sum restricted to them is a sum over `ι → ZMod m`.

These are the two reindexings by which a character sum modulo `p ^ 2 * M` is reduced to one
modulo `M`.

## Main results

* `ZMod.sum_comp_castHom`: summing a function of the reduction modulo `k` over `ι → ZMod n`.
* `ZMod.sum_ite_natCast_smul_eq_zero`: summing over the vectors of `ι → ZMod n` killed by `m`.
-/

public section

open Finset

namespace ZMod

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m n : ℕ} (k : ℕ) (h : m * k = n)
  {R : Type*} [AddCommMonoid R]

/-- **Summing a function of the reduction.** For `n = m * k`, summing a function of the
coordinatewise reduction modulo `k` over `ι → ZMod n` counts every value `m ^ #ι` times. -/
theorem sum_comp_castHom [NeZero k] [NeZero n] (F : (ι → ZMod k) → R) :
    ∑ w : ι → ZMod n, F (fun i ↦ castHom (Dvd.intro_left m h) (ZMod k) (w i)) =
      m ^ Fintype.card ι • ∑ y, F y := by
  set φ : (ι → ZMod n) →+ (ι → ZMod k) :=
    AddMonoidHom.compLeft (castHom (Dvd.intro_left m h) (ZMod k)).toAddMonoidHom ι
  have hφ : Function.Surjective φ :=
    (ZMod.ringHom_surjective (castHom (Dvd.intro_left m h) (ZMod k))).comp_left
  have hsum := AddMonoidHom.sum_comp_of_surjective φ hφ F
  have hcard := AddMonoidHom.sum_comp_of_surjective φ hφ (fun _ ↦ (1 : ℕ))
  simp only [sum_const, card_univ, Fintype.card_pi, ZMod.card, prod_const, smul_eq_mul,
    mul_one, ← h, mul_pow] at hcard
  have hK : Nat.card φ.ker = m ^ Fintype.card ι :=
    (Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.pos_of_neZero k) _) hcard).symm
  rw [← hK]
  exact hsum

/-- **Summing over the vectors killed by `m`.** For `n = m * k`, the vectors `x ∈ (ℤ/n)^ι` with
`m • x = 0` are exactly the images of the vectors `w ∈ (ℤ/m)^ι` under the coordinatewise
multiplication by `k`, each attained once. -/
theorem sum_ite_natCast_smul_eq_zero [NeZero m] [NeZero n] (g : (ι → ZMod n) → R) :
    ∑ x : ι → ZMod n, (if (m : ZMod n) • x = 0 then g x else 0) =
      ∑ w : ι → ZMod m, g fun i ↦ mulCastHom k h (w i) := by
  have hk : k ≠ 0 := right_ne_zero_of_mul (h ▸ NeZero.ne n)
  have hrange (t : ZMod n) : (m : ZMod n) * t = 0 ↔ ∃ s, mulCastHom k h s = t :=
    (natCast_mul_eq_zero_iff k h (NeZero.ne m) t).trans (exact_mulCastHom_castHom k h t)
  let Φ : (ι → ZMod m) ↪ (ι → ZMod n) :=
    ⟨fun w i ↦ mulCastHom k h (w i),
      fun w w' hw ↦ funext fun i ↦ mulCastHom_injective k h hk (congrFun hw i)⟩
  have himage : univ.map Φ = univ.filter fun x : ι → ZMod n ↦ (m : ZMod n) • x = 0 := by
    ext x
    simp only [mem_map, mem_univ, true_and, mem_filter, funext_iff, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, hrange, Φ]
    exact ⟨fun ⟨w, hw⟩ i ↦ ⟨w i, hw i⟩, fun h ↦ Classical.skolem.1 h⟩
  rw [← sum_filter, ← himage, sum_map]
  rfl

end ZMod
