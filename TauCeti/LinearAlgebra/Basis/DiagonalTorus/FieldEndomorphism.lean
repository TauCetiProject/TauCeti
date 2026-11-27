/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Polynomial.Roots
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic

/-!
# Field endomorphisms intertwined with characters of a split torus

Consequences of the pinning equation `f (ξ(s) * u) = η(s) * f u` for characters `ξ, η` of `𝔾ₘ^κ`:
`AddMonoidHom.multiplierSubring` and `AddMonoidHom.multiplierRingHom` (the subring of left
multipliers on which a unital additive map acts multiplicatively, and its restricted ring
homomorphism), `AddMonoidHom.exists_pos_nsmul_eq_nsmul_of_map_torusCharacter_mul` and
`RingHom.exists_pos_nsmul_eq_nsmul_of_map_torusCharacter_eq` (over an infinite field, positive
rational proportionality `d • η = m • ξ`), `AddMonoidHom.toRingHomOfTorusCharacter`
(upgrading a unital additive map `f` with `f 1 = 1` and the intertwining equation to a ring
endomorphism when `s ↦ torusCharacter s ξ` is surjective onto `Kˣ`), and
`TauCeti.eq_of_map_torusCharacter_eq` (uniqueness of zero-preserving maps on a surjective
character).

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Mem. Amer. Math. Soc. **80** (1968),
  §§10–11; *Lectures on Chevalley Groups*, Chapter 10, Theorem 29.
-/

public section

open TauCeti

namespace AddMonoidHom

/-- The subring of left multipliers `x` on which a unital additive homomorphism `h : R →+ S`
(`h 1 = 1`) acts multiplicatively on all right factors, `h (x * y) = h x * h y`. -/
def multiplierSubring {R S : Type*} [Ring R] [Ring S] (h : R →+ S) (hh1 : h 1 = 1) :
    Subring R where
  carrier := {x : R | ∀ y : R, h (x * y) = h x * h y}
  one_mem' y := by rw [one_mul, hh1, one_mul]
  mul_mem' {x₁ x₂} hx₁ hx₂ y := by rw [mul_assoc, hx₁, hx₂, hx₁, mul_assoc]
  zero_mem' y := by rw [zero_mul, map_zero, zero_mul]
  add_mem' {x₁ x₂} hx₁ hx₂ y := by rw [add_mul, map_add, hx₁, hx₂, map_add, add_mul]
  neg_mem' {x} hx y := by rw [neg_mul, map_neg, hx, map_neg, neg_mul]

/-- Membership in `h.multiplierSubring hh1` is left-multiplicativity
`∀ y, h (x * y) = h x * h y`. -/
@[simp] theorem mem_multiplierSubring {R S : Type*} [Ring R] [Ring S] (h : R →+ S)
    (hh1 : h 1 = 1) {x : R} :
    x ∈ h.multiplierSubring hh1 ↔ ∀ y : R, h (x * y) = h x * h y :=
  Iff.rfl

/-- Restriction of a unital additive homomorphism `h : R →+ S` to its multiplier subring
`h.multiplierSubring hh1` as a ring homomorphism. -/
def multiplierRingHom {R S : Type*} [Ring R] [Ring S] (h : R →+ S) (hh1 : h 1 = 1) :
    h.multiplierSubring hh1 →+* S where
  toFun x := h x.val
  map_one' := hh1
  map_mul' x y := x.property y.val
  map_zero' := h.map_zero
  map_add' x y := h.map_add x.val y.val

/-- Pointwise evaluation of `h.multiplierRingHom hh1`. -/
@[simp] theorem multiplierRingHom_apply {R S : Type*} [Ring R] [Ring S] (h : R →+ S)
    (hh1 : h 1 = 1) (x : h.multiplierSubring hh1) :
    h.multiplierRingHom hh1 x = h x.val :=
  (rfl)

/-- **Intertwining a nonzero additive endomorphism of an infinite field with split-torus characters
forces positive rational proportionality.** -/
theorem exists_pos_nsmul_eq_nsmul_of_map_torusCharacter_mul {κ K : Type*} [Fintype κ] [Field K]
    [Infinite K] (f : K →+ K) (hf : f ≠ 0) {ξ η : κ → ℤ}
    (hscale : ∀ (s : κ → Kˣ) (u : K),
      f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u) :
    ∃ d m : ℕ, 0 < d ∧ 0 < m ∧ d • η = m • ξ := by
  classical
  obtain ⟨u₀, hu₀⟩ := DFunLike.ne_iff.mp hf; rw [zero_apply] at hu₀
  let h : K →+ K := AddMonoidHom.mk' (fun x => (f u₀)⁻¹ * f (u₀ * x)) fun x y => by
    rw [mul_add, map_add, mul_add]
  have hh1 : h 1 = 1 := by simp [h, inv_mul_cancel₀ hu₀]
  have hhscale (s : κ → Kˣ) (x : K) :
      h ((torusCharacter s ξ : K) * x) = (torusCharacter s η : K) * h x := by
    simp only [h, AddMonoidHom.mk'_apply]; rw [mul_left_comm u₀, hscale, mul_left_comm]
  have hhtorus (s : κ → Kˣ) : h (torusCharacter s ξ : K) = (torusCharacter s η : K) := by
    simpa only [mul_one, hh1] using hhscale s 1
  obtain ⟨d, hd, z, hz⟩ := exists_nsmul_eq_zsmul_of_torusCharacter_eq_one_imp (ξ := ξ) (η := η)
    fun s hs => Units.ext (by simpa [hs, hh1] using (hhtorus s).symm)
  by_cases hξ : ξ = 0
  · exact ⟨d, 1, hd, Nat.one_pos, by rw [hz, hξ, smul_zero, smul_zero]⟩
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hξ; let a : ℕ := (ξ i₀).natAbs
  have ha : 0 < a := Int.natAbs_pos.mpr hi₀; have had : 0 < a * d := Nat.mul_pos ha hd
  let E := h.multiplierSubring hh1
  let g := h.multiplierRingHom hh1
  let sOf (u : Kˣ) : κ → Kˣ := Pi.mulSingle i₀ (if 0 ≤ ξ i₀ then u else u⁻¹)
  have hsOf (u : Kˣ) : torusCharacter (sOf u) ξ = u ^ a := by
    rw [torusCharacter_mulSingle]; split_ifs with h0
    · rw [← zpow_natCast, Int.natAbs_of_nonneg h0]
    · rw [inv_zpow', ← zpow_natCast, Int.ofNat_natAbs_of_nonpos (le_of_not_ge h0)]
  have : Infinite E := E.infinite_of_pow_mem ha fun x => by
    by_cases hx : x = 0; · rw [hx, zero_pow ha.ne']; exact E.zero_mem
    refine (mem_multiplierSubring h hh1).mpr fun y => ?_
    simpa [hsOf (Units.mk0 x hx)] using
      (hhscale (sOf (Units.mk0 x hx)) y).trans (congrArg (· * h y) (hhtorus _).symm)
  -- Split on the sign of `z`: if `z ≤ 0`, then `g x ^ (a * d) * (x : K) ^ (a * (-z).toNat) = 1`
  -- on all nonzero `x ∈ E`, contradicting `not_forall_map_pow_mul_map_pow_eq_one` for the infinite
  -- subring `E`; if `z > 0`, then `m := z.toNat > 0` directly witnesses `d • η = m • ξ`.
  rcases le_or_gt z 0 with hzle | hzpos
  · refine (RingHom.not_forall_map_pow_mul_map_pow_eq_one g E.subtype (.inl had.ne')
      (n := a * (-z).toNat) fun x hx => ?_).elim
    have hxK : (x : K) ≠ 0 := fun h0 => hx (Subtype.ext h0); let u : Kˣ := Units.mk0 (x : K) hxK
    have hgx : g (x ^ a) = (torusCharacter (sOf u) η : K) := by
      simpa [g, u, hsOf] using hhtorus (sOf u)
    have hpow : g x ^ (a * d) = ((u ^ ((a : ℤ) * z) : Kˣ) : K) := by
      rw [pow_mul, ← map_pow, hgx, ← Units.val_pow_eq_pow_val, ← torusCharacter_nsmul, hz,
        torusCharacter_zsmul, hsOf, ← zpow_natCast, ← zpow_mul]
    have hzn : (a : ℤ) * z = -((a * (-z).toNat : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Int.toNat_of_nonneg (neg_nonneg.mpr hzle), mul_neg, neg_neg]
    rw [hzn, zpow_neg, zpow_natCast] at hpow
    simp [hpow, u, hxK]
  · exact ⟨d, z.toNat, hd, Int.lt_toNat.mpr hzpos, by
      rw [hz, ← natCast_zsmul, Int.toNat_of_nonneg hzpos.le]⟩

end AddMonoidHom

namespace RingHom

/-- **Intertwining a ring endomorphism of an infinite field with split-torus characters forces
positive rational proportionality.** -/
theorem exists_pos_nsmul_eq_nsmul_of_map_torusCharacter_eq {κ K : Type*} [Fintype κ] [Field K]
    [Infinite K] (g : K →+* K) {ξ η : κ → ℤ}
    (hmap : ∀ s : κ → Kˣ, g (torusCharacter s ξ : K) = (torusCharacter s η : K)) :
    ∃ d m : ℕ, 0 < d ∧ 0 < m ∧ d • η = m • ξ :=
  g.toAddMonoidHom.exists_pos_nsmul_eq_nsmul_of_map_torusCharacter_mul
    (fun h0 => (one_ne_zero (α := K)) (by simpa using congrArg (fun f : K →+ K => f 1) h0))
    fun s u => by simp [hmap s]

end RingHom

namespace AddMonoidHom
variable {κ K : Type*} [Fintype κ] [Field K] (f : K →+ K) {ξ η : κ → ℤ}
  (hsurj : Function.Surjective fun s : κ → Kˣ => torusCharacter s ξ) (hf1 : f 1 = 1)
  (hscale : ∀ (s : κ → Kˣ) (u : K),
    f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u)

/-- **Upgrading a unital additive map (`f 1 = 1`) intertwined with a surjective split-torus
character to a ring endomorphism.** -/
def toRingHomOfTorusCharacter : K →+* K where
  toFun := f; map_zero' := f.map_zero; map_add' := f.map_add; map_one' := hf1
  map_mul' x y := by
    by_cases hx : x = 0; · simp [hx]
    obtain ⟨s, hs⟩ := hsurj (Units.mk0 x hx)
    have hxval : (torusCharacter s ξ : K) = x := by simpa using congrArg Units.val hs
    have hfx : f x = (torusCharacter s η : K) := by simpa [hxval, hf1] using hscale s 1
    rw [← hxval, hscale s y, hxval, hfx]

/-- Function coercion of `toRingHomOfTorusCharacter` is `f`. -/
@[simp] theorem coe_toRingHomOfTorusCharacter :
    ⇑(f.toRingHomOfTorusCharacter hsurj hf1 hscale) = f := (rfl)

/-- Pointwise evaluation of `toRingHomOfTorusCharacter`. -/
@[simp] theorem toRingHomOfTorusCharacter_apply (x : K) :
    f.toRingHomOfTorusCharacter hsurj hf1 hscale x = f x := (rfl)

/-- Coercing `toRingHomOfTorusCharacter` back to an `AddMonoidHom` recovers `f`. -/
@[simp] theorem toAddMonoidHom_toRingHomOfTorusCharacter :
    (f.toRingHomOfTorusCharacter hsurj hf1 hscale : K →+ K) = f := (rfl)

/-- On torus character values of `ξ`, `toRingHomOfTorusCharacter` sends `ξ(s)` to `η(s)`. -/
theorem toRingHomOfTorusCharacter_torusCharacter (s : κ → Kˣ) :
    f.toRingHomOfTorusCharacter hsurj hf1 hscale (torusCharacter s ξ : K) =
      (torusCharacter s η : K) := by
  simpa only [toRingHomOfTorusCharacter_apply, mul_one, hf1] using hscale s 1

end AddMonoidHom

namespace TauCeti

/-- **A zero-preserving map out of a field `K` is uniquely determined by its values on a surjective
split-torus character.** -/
theorem eq_of_map_torusCharacter_eq {κ K F S : Type*} [Fintype κ] [Field K] [Zero S]
    [FunLike F K S] [ZeroHomClass F K S] {g₁ g₂ : F} {ξ : κ → ℤ}
    (hsurj : Function.Surjective fun s : κ → Kˣ => torusCharacter s ξ)
    (h : ∀ s : κ → Kˣ, g₁ (torusCharacter s ξ : K) = g₂ (torusCharacter s ξ : K)) :
    g₁ = g₂ := DFunLike.ext g₁ g₂ fun x => by
  by_cases hx : x = 0; · simp [hx]
  obtain ⟨s, hs⟩ := hsurj (Units.mk0 x hx)
  have hxval : (torusCharacter s ξ : K) = x := by simpa using congrArg Units.val hs
  simpa only [hxval] using h s

end TauCeti
