/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Multiplicity

import Mathlib.RingTheory.Ideal.Nonunits

/-!
# Rings of finite Krull dimension

A semiring whose Krull dimension is a natural number has finite Krull dimension. This is the form in
which finiteness of the dimension usually arises, from a computation `dim R = n`.

A surjection from a domain of finite Krull dimension is injective exactly when its target has at
least the same dimension: a nonzero kernel element would be a nonzerodivisor and so would lower the
dimension, while an injective surjection is an isomorphism.

In a domain of dimension at most one, a nonunit has finite multiplicity in every nonzero element.
This Krull intersection statement needs no Noetherian hypothesis; for valuation rings of rank at
most one it is the archimedean property of the value group.

## Main results

* `FiniteRingKrullDim.of_ringKrullDim_eq_natCast`: a semiring of Krull dimension `n : ℕ` has
  finite Krull dimension.
* `RingHom.injective_iff_ringKrullDim_le_of_surjective`: a surjection from a domain of finite
  Krull dimension is injective if and only if its target has at least the same dimension.
* `FiniteMultiplicity.of_not_isUnit_of_krullDimLE_one`: in a domain of dimension at most one, a
  nonunit has finite multiplicity in every nonzero element.
-/

public section

/-- A semiring whose Krull dimension is a natural number `n` has finite Krull dimension. -/
theorem FiniteRingKrullDim.of_ringKrullDim_eq_natCast {R : Type*} [CommSemiring R] {n : ℕ}
    (h : ringKrullDim R = n) : FiniteRingKrullDim R :=
  finiteRingKrullDim_iff_ne_bot_and_top.mpr
    (h ▸ ⟨WithBot.natCast_ne_bot _, WithBot.coe_inj.not.mpr (ENat.natCast_ne_top _)⟩)

/-- A surjective ring homomorphism from a domain of finite Krull dimension is injective if and
only if its target has at least the same dimension. -/
theorem RingHom.injective_iff_ringKrullDim_le_of_surjective {R S : Type*} [CommRing R]
    [IsDomain R] [FiniteRingKrullDim R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f) :
    Function.Injective f ↔ ringKrullDim R ≤ ringKrullDim S := by
  refine ⟨fun hinj ↦ ?_, fun hdim ↦ ?_⟩
  · -- An injective surjection is an isomorphism, so it preserves the dimension.
    exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective f ⟨hinj, hf⟩)).le
  refine (injective_iff_map_eq_zero f).2 fun r hr ↦ by_contra fun hr0 ↦ ?_
  -- A nonzero kernel element is a nonzerodivisor, so it would lower the dimension.
  have hlt := ringKrullDim_succ_le_of_surjective f hf (mem_nonZeroDivisors_of_ne_zero hr0) hr
  -- Write the finite dimension of `R` as a natural number `d`, so that `dim S < d ≤ dim S`.
  lift ringKrullDim R to ℕ∞ using ringKrullDim_ne_bot with d hd
  lift d to ℕ using by simpa [← hd] using ringKrullDim_ne_top (R := R)
  exact (ENat.WithBot.add_one_le_natCast_iff.mp hlt).not_ge hdim

/-- In a domain of dimension at most one, a nonunit `t` has finite multiplicity in every nonzero
element `a`: some power of `t` does not divide `a`. -/
theorem FiniteMultiplicity.of_not_isUnit_of_krullDimLE_one {R : Type*} [CommRing R] [IsDomain R]
    [Ring.KrullDimLE 1 R] {t a : R} (ht : ¬IsUnit t) (ha : a ≠ 0) : FiniteMultiplicity t a := by
  by_contra h
  rw [FiniteMultiplicity.not_iff_forall] at h
  obtain ⟨m, hm, htm⟩ := exists_max_ideal_of_mem_nonunits ht
  -- The only prime containing `a` inside `m` is `m` itself, so `(a)` meets `S · tᴺ`, `S = R \ m`.
  obtain ⟨y, hya, hyS⟩ : ∃ y ∈ Ideal.span {a}, y ∈ m.primeCompl ⊔ Submonoid.powers t := by
    by_contra hdisj
    obtain ⟨P, hP, haP, hPS⟩ := Ideal.exists_le_prime_disjoint (Ideal.span {a})
      (m.primeCompl ⊔ Submonoid.powers t)
      (Set.disjoint_left.mpr fun y hy hyS => hdisj ⟨y, hy, hyS⟩)
    have hP0 : P ≠ ⊥ := fun h0 =>
      ha ((Submodule.mem_bot R).mp (h0 ▸ haP (Ideal.mem_span_singleton_self a)))
    have hPm : P ≤ m := fun x hx => by_contra fun hxm =>
      Set.disjoint_left.mp hPS hx (Submonoid.mem_sup_left (Ideal.mem_primeCompl_iff.mpr hxm))
    have hPeq : P = m := (hP.isMaximal_of_ne_bot hP0).eq_of_le hm.ne_top hPm
    exact Set.disjoint_left.mp hPS (hPeq ▸ htm)
      (Submonoid.mem_sup_right (Submonoid.mem_powers t))
  obtain ⟨s, hs, _, ⟨k, rfl⟩, rfl⟩ := Submonoid.mem_sup.mp hyS
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hya
  obtain ⟨d, hd⟩ := h (k + 1)
  -- `s * t ^ k = t ^ k * (t * (d * c))`, so cancelling `t ^ k` puts `s` in `m`.
  have ht0 : t ^ k ≠ 0 := pow_ne_zero k fun ht0 => ha (zero_dvd_iff.mp (by simpa [ht0] using h 1))
  have hs' : s = t * (d * c) := mul_right_cancel₀ ht0 (by rw [← hc, hd]; ring)
  exact hs (hs' ▸ m.mul_mem_right _ htm)
