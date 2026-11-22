/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.LCM
import Mathlib.Tactic.Ring

/-!
# The Chinese remainder theorem in gcd–lcm form

Mathlib's `ZMod.chineseRemainder` splits `ZMod (m * n)` as `ZMod m × ZMod n` for coprime `m` and
`n`. Without coprimality, `ZMod a × ZMod b` is still isomorphic to
`ZMod (gcd a b) × ZMod (lcm a b)`, as a ring and so in particular as an additive group
(`ZMod.nonempty_ringEquiv_gcd_lcm`). The second form is a divisibility chain,
`gcd a b ∣ lcm a b`, which is how a product of cyclic groups is brought into invariant-factor form.

The proof splits `a = u * y` and `b = v * w` with `lcm a b = u * v` and `gcd a b = y * w`, all
four pairs coprime, where `u` collects the prime powers of `a` at least those of `b` and `v` the
remaining prime powers of `b` (Mathlib's `Nat.factorizationLCMLeft` and
`Nat.factorizationLCMRight`); both sides are then `ZMod u × ZMod y × ZMod v × ZMod w`.
-/

public section

namespace ZMod

/-- **Chinese remainder theorem in gcd–lcm form.** For all natural numbers `a` and `b`, the rings
`ZMod a × ZMod b` and `ZMod (gcd a b) × ZMod (lcm a b)` are isomorphic. -/
theorem nonempty_ringEquiv_gcd_lcm (a b : ℕ) :
    Nonempty (ZMod a × ZMod b ≃+* ZMod (a.gcd b) × ZMod (a.lcm b)) := by
  -- Split `a = u * y` and `b = v * w` so that `lcm a b = u * v` and `gcd a b = y * w`, with the
  -- four products coprime; both sides are then `ZMod u × ZMod y × ZMod v × ZMod w`.
  suffices ∃ u y v w : ℕ, a = u * y ∧ b = v * w ∧ a.lcm b = u * v ∧ a.gcd b = y * w ∧
      u.Coprime y ∧ v.Coprime w ∧ u.Coprime v ∧ y.Coprime w by
    obtain ⟨u, y, v, w, ha, hb, hl, hg, huy, hvw, huv, hyw⟩ := this
    exact ⟨((ringEquivCongr ha).prodCongr (ringEquivCongr hb)).trans <|
      ((chineseRemainder huy).prodCongr (chineseRemainder hvw)).trans <|
      (RingEquiv.prodProdProdComm _ _ _ _).trans <|
      ((chineseRemainder huv).symm.prodCongr (chineseRemainder hyw).symm).trans <|
      RingEquiv.prodComm.trans <| (ringEquivCongr hg.symm).prodCongr (ringEquivCongr hl.symm)⟩
  rcases eq_or_ne a 0 with rfl | ha
  · exact ⟨0, 1, 1, b, by simp⟩
  rcases eq_or_ne b 0 with rfl | hb
  · exact ⟨1, a, 0, 1, by simp⟩
  -- `u` collects the prime powers of `a` at least those of `b`, and `v` the remaining ones of `b`.
  set u := Nat.factorizationLCMLeft a b
  set v := Nat.factorizationLCMRight a b
  have hu : u ∣ a := Nat.factorizationLCMLeft_dvd_left a b
  have hv : v ∣ b := Nat.factorizationLCMRight_dvd_right a b
  have huv : u.Coprime v := Nat.coprime_factorizationLCMLeft_factorizationLCMRight a b
  have hl : a.lcm b = u * v := (Nat.factorizationLCMLeft_mul_factorizationLCMRight ha hb).symm
  have hu0 : 0 < u := Nat.factorizationLCMLeft_pos a b
  have hv0 : 0 < v := Nat.factorizationLCMRight_pos a b
  have ha' : a = u * (a / u) := (Nat.mul_div_cancel' hu).symm
  have hb' : b = v * (b / v) := (Nat.mul_div_cancel' hv).symm
  -- A prime dividing `a / u` divides `v`, and a prime dividing `b / v` divides `u`, because
  -- `a` and `b` divide `lcm a b = u * v`.
  have hy (p : ℕ) (hp : p ∣ a / u) : p ∣ v := by
    refine Nat.dvd_of_mul_dvd_mul_left hu0 ?_
    rw [← hl]
    exact (Nat.mul_dvd_mul_left u hp).trans (ha' ▸ Nat.dvd_lcm_left a b)
  have hw (p : ℕ) (hp : p ∣ b / v) : p ∣ u := by
    refine Nat.dvd_of_mul_dvd_mul_left hv0 ?_
    rw [mul_comm v u, ← hl]
    exact (Nat.mul_dvd_mul_left v hp).trans (hb' ▸ Nat.dvd_lcm_right a b)
  have hcop {x y : ℕ} (h : ∀ p, p.Prime → p ∣ x → p ∣ y → p ∣ u ∧ p ∣ v) : x.Coprime y :=
    Nat.coprime_of_dvd fun p hp hx hy ↦ hp.ne_one <| Nat.eq_one_of_dvd_one <|
      huv.gcd_eq_one ▸ Nat.dvd_gcd (h p hp hx hy).1 (h p hp hx hy).2
  refine ⟨u, a / u, v, b / v, ha', hb', hl, ?_, hcop fun p _ h h' ↦ ⟨h, hy p h'⟩,
    hcop fun p _ h h' ↦ ⟨hw p h', h⟩, huv, hcop fun p _ h h' ↦ ⟨hw p h', hy p h⟩⟩
  refine Nat.eq_of_mul_eq_mul_right (Nat.lcm_pos (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)) ?_
  rw [Nat.gcd_mul_lcm, hl]
  nth_rw 1 [ha', hb']
  ring

end ZMod
