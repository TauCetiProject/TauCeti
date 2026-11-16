/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Ring.Hom
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic

/-!
# Field endomorphisms intertwined with characters of a split torus

Field-theoretic consequences of the pinning equation `f (ξ(s) * u) = η(s) * f u` for characters
`ξ, η` of `𝔾ₘ^κ`:

1. `RingHom.exists_pos_nsmul_eq_nsmul_of_map_torusCharacter_eq`: over an infinite field,
   `g (ξ(s)) = η(s)` forces `d • η = m • ξ` with `0 < d` and `0 < m`.
2. `AddMonoidHom.toRingHomOfTorusCharacter`: when `ξ ≠ 0` and `[RootableBy Kˣ ℕ]`, `f 1 = 1`
   upgrades `f` to a ring endomorphism with `g (ξ(s)) = η(s)`.
3. `TauCeti.ringHom_eq_of_torusCharacter_eq`: when `[RootableBy Kˣ ℕ]` and `ξ ≠ 0`, any ring
   homomorphism out of `K` is uniquely determined by its values on `ξ(s)`.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Mem. Amer. Math. Soc. **80** (1968),
  §§10–11.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29.
-/

public section

open TauCeti

namespace RingHom

/-- **Intertwining a ring endomorphism with split-torus characters forces positive rational
proportionality.** -/
theorem exists_pos_nsmul_eq_nsmul_of_map_torusCharacter_eq {κ : Type*} [Fintype κ] {K : Type*}
    [Field K] [Infinite K] (g : K →+* K) {ξ η : κ → ℤ}
    (hmap : ∀ s : κ → Kˣ, g (torusCharacter s ξ : K) = (torusCharacter s η : K)) :
    ∃ d m : ℕ, 0 < d ∧ 0 < m ∧ d • η = m • ξ := by
  classical
  obtain ⟨d, hd, z, hz⟩ := exists_nsmul_eq_zsmul_of_torusCharacter_eq_one_imp
    (ξ := ξ) (η := η) fun s hs => Units.ext (by simpa [hs] using (hmap s).symm)
  by_cases hξ : ξ = 0
  · exact ⟨d, 1, hd, Nat.one_pos, by rw [hz, hξ, smul_zero, smul_zero]⟩
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hξ; let a : ℕ := (ξ i₀).natAbs
  have had : 0 < a * d := Nat.mul_pos (Int.natAbs_pos.mpr hi₀) hd
  have hpow (u : Kˣ) : g u ^ (a * d) = ((u ^ ((a : ℤ) * z) : Kˣ) : K) := by
    let s : κ → Kˣ := Pi.mulSingle i₀ (if 0 ≤ ξ i₀ then u else u⁻¹)
    have hsξ : torusCharacter s ξ = u ^ a := by
      rw [torusCharacter_mulSingle]; split_ifs with h0
      · rw [← zpow_natCast, Int.natAbs_of_nonneg h0]
      · have hξa : ξ i₀ = -(a : ℤ) := by
          rw [Int.ofNat_natAbs_of_nonpos (le_of_not_ge h0), neg_neg]
        rw [hξa, inv_zpow', neg_neg, zpow_natCast]
    calc g u ^ (a * d) = (g ((u ^ a : Kˣ) : K)) ^ d := by
          rw [Units.val_pow_eq_pow_val, map_pow, pow_mul]
      _ = ((torusCharacter s η ^ d : Kˣ) : K) := by rw [← hsξ, hmap s, Units.val_pow_eq_pow_val]
      _ = ((u ^ ((a : ℤ) * z) : Kˣ) : K) := by
          rw [← torusCharacter_nsmul, hz, torusCharacter_zsmul, hsξ, ← zpow_natCast, ← zpow_mul]
  rcases le_or_gt z 0 with hz | hzpos
  · refine (g.not_forall_map_pow_mul_pow_eq_one (.inl had.ne') (n := a * (-z).toNat) fun x hx =>
      ?_).elim
    have hzn : (a : ℤ) * z = -((a * (-z).toNat : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Int.toNat_of_nonneg (neg_nonneg.mpr hz), mul_neg, neg_neg]
    have h1 := hpow (Units.mk0 x hx)
    simp only [Units.val_mk0, hzn, zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val] at h1
    simp [h1, hx]
  · exact ⟨d, z.toNat, hd, Int.lt_toNat.mpr hzpos, by
      rw [hz, ← natCast_zsmul, Int.toNat_of_nonneg hzpos.le]⟩

end RingHom

namespace AddMonoidHom

variable {κ : Type*} [Fintype κ] {K : Type*} [Field K] [RootableBy Kˣ ℕ]
  (f : K →+ K) {ξ η : κ → ℤ} (hξ : ξ ≠ 0) (hf1 : f 1 = 1)
  (hscale : ∀ (s : κ → Kˣ) (u : K),
    f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u)

/-- **Upgrading an additive map intertwined with split-torus characters to a ring endomorphism.** -/
def toRingHomOfTorusCharacter : K →+* K where
  toFun := f; map_zero' := f.map_zero; map_add' := f.map_add; map_one' := hf1
  map_mul' x y := by
    by_cases hx : x = 0; · simp [hx]
    obtain ⟨s, hs⟩ := torusCharacter_surjective hξ (Units.mk0 x hx)
    have hxval : (torusCharacter s ξ : K) = x := by simpa using congrArg Units.val hs
    have hfx : f x = (torusCharacter s η : K) := by
      simpa only [hxval, mul_one, hf1] using hscale s 1
    rw [← hxval, hscale s y, hxval, hfx]

/-- Function coercion of `toRingHomOfTorusCharacter` is `f`. -/
@[simp] theorem coe_toRingHomOfTorusCharacter :
    ⇑(f.toRingHomOfTorusCharacter hξ hf1 hscale) = f := (rfl)

/-- Pointwise evaluation of `toRingHomOfTorusCharacter`. -/
@[simp] theorem toRingHomOfTorusCharacter_apply (x : K) :
    f.toRingHomOfTorusCharacter hξ hf1 hscale x = f x := (rfl)

/-- Coercing `toRingHomOfTorusCharacter` back to an `AddMonoidHom` recovers `f`. -/
@[simp] theorem toAddMonoidHom_toRingHomOfTorusCharacter :
    (f.toRingHomOfTorusCharacter hξ hf1 hscale : K →+ K) = f := (rfl)

/-- On torus character values of `ξ`, `toRingHomOfTorusCharacter` sends `ξ(s)` to `η(s)`. -/
theorem toRingHomOfTorusCharacter_torusCharacter (s : κ → Kˣ) :
    f.toRingHomOfTorusCharacter hξ hf1 hscale (torusCharacter s ξ : K) =
      (torusCharacter s η : K) := by
  simpa only [toRingHomOfTorusCharacter_apply, mul_one, hf1] using hscale s 1

end AddMonoidHom

namespace TauCeti

/-- **A ring homomorphism out of `K` is uniquely determined by its values on a nonzero split-torus
character**, provided `Kˣ` is divisible. -/
theorem ringHom_eq_of_torusCharacter_eq {κ : Type*} [Fintype κ] {K : Type*} [Field K]
    [RootableBy Kˣ ℕ] {S : Type*} [NonAssocSemiring S] {g₁ g₂ : K →+* S} {ξ : κ → ℤ}
    (hξ : ξ ≠ 0) (h : ∀ s : κ → Kˣ, g₁ (torusCharacter s ξ : K) = g₂ (torusCharacter s ξ : K)) :
    g₁ = g₂ := RingHom.ext fun x => by
  by_cases hx : x = 0; · simp [hx]
  obtain ⟨s, hs⟩ := torusCharacter_surjective hξ (Units.mk0 x hx)
  have hxval : (torusCharacter s ξ : K) = x := by simpa using congrArg Units.val hs
  simpa only [hxval] using h s

end TauCeti
