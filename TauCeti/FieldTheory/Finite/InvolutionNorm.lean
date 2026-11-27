/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Finite.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Index
import TauCeti.FieldTheory.Galois.Hilbert90

/-!
# The norm of an involution of a finite field is onto the fixed field

Let `K` be a finite field and `τ` an involutive ring endomorphism of `K` that moves some element,
so that `τ` generates the Galois group of `K` over its fixed field `K₀ = {a | τ a = a}`. The norm
from `K` to `K₀` is `x ↦ τ x * x`. This file proves that it is onto: every `a` with `τ a = a` is
`τ x * x` for some `x ∈ K`.

On units, the norm `N x = τ x * x` and the map `M y = y / τ y` are endomorphisms of the finite
group `Kˣ`. The kernel of `M` is `K₀ˣ`, Hilbert's Theorem 90 for an involution
(`TauCeti.exists_ne_zero_mul_apply_eq_of_apply_mul_self_eq_one`) says that the kernel of `N` is
the range of `M`, and the range of `N` lies in `K₀ˣ`. Counting kernels and ranges then shows that
the range of `N` has as many elements as `K₀ˣ`, so it is all of `K₀ˣ`.

This is the residue-field step of the corresponding statement for the units of a Henselian local
ring with an involution, `TauCeti.HenselianLocalRing.exists_apply_mul_self_eq`.

## Main results

* `TauCeti.FiniteField.exists_apply_mul_self_eq`: every `a` with `τ a = a` is `τ x * x`.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §2 (the norm of an unramified extension).
-/

public section

namespace TauCeti.FiniteField

variable {K : Type*} [Field K] [Finite K]

/-- **The norm of an involution of a finite field is onto the fixed field.** Let `τ` be an
involutive ring endomorphism of a finite field `K` that moves some element. Then every `a ∈ K`
with `τ a = a` is `τ x * x` for some `x ∈ K`. -/
theorem exists_apply_mul_self_eq {τ : K →+* K} (hτ : ∀ z, τ (τ z) = z) {d : K} (hd : τ d ≠ d)
    {a : K} (ha : τ a = a) : ∃ x, τ x * x = a := by
  rcases eq_or_ne a 0 with rfl | ha₀
  · exact ⟨0, by rw [mul_zero]⟩
  -- the conjugation `T`, the norm `N u = T u * u` and the map `M u = u / T u` on `Kˣ`
  let T : Kˣ →* Kˣ := Units.map τ.toMonoidHom
  have hT (u : Kˣ) : ((T u : Kˣ) : K) = τ u := Units.coe_map _ u
  have hTT (u : Kˣ) : T (T u) = u := Units.ext (by rw [hT, hT, hτ])
  let N : Kˣ →* Kˣ := T * MonoidHom.id Kˣ
  let M : Kˣ →* Kˣ := MonoidHom.id Kˣ / T
  have hN (u : Kˣ) : N u = T u * u := rfl
  have hM (u : Kˣ) : M u = u / T u := rfl
  -- the range of `N` lies in the kernel of `M`, the units fixed by `T`
  have hNM : N.range ≤ M.ker := by
    rintro _ ⟨u, rfl⟩
    rw [MonoidHom.mem_ker, hM, div_eq_one, hN, map_mul, hTT, mul_comm]
  -- Hilbert 90: the kernel of `N` is the range of `M`
  have hNker : N.ker = M.range := by
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro hu
      obtain ⟨y, hy₀, hy⟩ := exists_ne_zero_mul_apply_eq_of_apply_mul_self_eq_one hτ hd
        (x := u) (by rw [← hT, ← Units.val_mul, ← hN, hu, Units.val_one])
      refine ⟨Units.mk0 y hy₀, Units.ext ?_⟩
      rw [hM, Units.val_div_eq_div_val, hT, Units.val_mk0, div_eq_iff (by simpa using hy₀), hy]
    · rintro ⟨y, rfl⟩
      rw [hN, hM, map_div, hTT, div_mul_div_comm, mul_comm, div_self']
  -- counting: `#N.range * #M.range = #Kˣ = #M.ker * #M.range`, so `N.range = M.ker`
  have hcard : Nat.card N.range = Nat.card M.ker := by
    have h₁ := Subgroup.card_ker_mul_card_range N
    have h₂ := Subgroup.card_ker_mul_card_range M
    rw [hNker] at h₁
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [h₁, mul_comm, h₂])
  have hrange : N.range = M.ker := Subgroup.eq_of_le_of_card_ge hNM hcard.ge
  obtain ⟨u, hu⟩ : Units.mk0 a ha₀ ∈ N.range := by
    rw [hrange, MonoidHom.mem_ker, hM, div_eq_one]
    exact Units.ext (by rw [hT, Units.val_mk0, ha])
  exact ⟨u, by rw [← hT, ← Units.val_mul, ← hN, hu, Units.val_mk0]⟩

end TauCeti.FiniteField
