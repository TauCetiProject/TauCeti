/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Prismatic.Nygaard

/-!
# Checks for the Nygaard filtration and the divided Frobenius

The zeroth step of the Nygaard filtration is the whole ring. For the identity endomorphism, as
on `ℤ` with `φ = id` and `d = p` (a model of the crystalline prism `(ℤ_p, (p))`), the filtration
is `J`-adic and the divided Frobenius is division by `p ^ i`; for instance `φ_2 12 = 3` for
`p = 2`, while `6` lies in `Fil^1_N ℤ` but not in `Fil^2_N ℤ`. The divided Frobenius `φ_1` is not
multiplicative: on `Fil^1_N` one has `φ_1 (x * y) = d * φ_1 x * φ_1 y`, and on `ℤ` with `d = 2`
this is `φ_1 (2 * 2) = 2 ≠ 1 = φ_1 2 * φ_1 2`.
-/

namespace TauCeti.Prismatic.Nygaard

open Ideal

-- `Fil^0_N B = B` for every endomorphism and ideal.
example {B : Type*} [CommRing B] (φ : B →+* B) (J : Ideal B) : fil φ J 0 = ⊤ :=
  fil_zero

-- If `φ` is the identity, `Fil^i_N B = J ^ i`.
example {B : Type*} [CommRing B] (J : Ideal B) (i : ℕ) : fil (RingHom.id B) J i = J ^ i :=
  fil_id i

-- The element `2` of `ℤ` is a nonzerodivisor, so the divided Frobenius applies to it; the
-- checks below take this proof as the hypothesis `hd`.
example : IsRegular (2 : ℤ) :=
  .of_ne_zero two_ne_zero

-- On `ℤ` with `φ = id` and `d = 2`: `6 ∈ Fil^1_N`, `6 ∉ Fil^2_N`.
example :
    (6 : ℤ) ∈ fil (RingHom.id ℤ) (span {2}) 1 ∧ (6 : ℤ) ∉ fil (RingHom.id ℤ) (span {2}) 2 := by
  simp only [fil_id, span_singleton_pow, mem_span_singleton]
  decide

-- `φ_i (p ^ i * a) = a` on `ℤ` with `d = 2`: here `φ_2 12 = 3`.
example (hd : IsRegular (2 : ℤ)) (h : (12 : ℤ) ∈ fil (RingHom.id ℤ) (span {2}) 2) :
    dividedFrobenius (RingHom.id ℤ) hd 2 ⟨12, h⟩ = 3 := by
  rw [dividedFrobenius_eq_iff, RingHom.id_apply]
  norm_num

-- For every oriented ring and `x, y ∈ Fil^1_N`, `φ_1 (x * y) = d * φ_1 x * φ_1 y`.
example {B : Type*} [CommRing B] (φ : B →+* B) {d : B} (hd : IsRegular d) {x y : B}
    (hx : x ∈ fil φ (span {d}) 1) (hy : y ∈ fil φ (span {d}) 1) :
    dividedFrobenius φ hd 1 ⟨x * y, fil_antitone (by omega) (mul_mem_fil hx hy)⟩ =
      d * (dividedFrobenius φ hd 1 ⟨x, hx⟩ * dividedFrobenius φ hd 1 ⟨y, hy⟩) := by
  rw [dividedFrobenius_succ hd (mul_mem_fil hx hy), dividedFrobenius_mul hd hx hy]

-- `φ_1` is not multiplicative: on `ℤ` with `d = 2`, `φ_1 (2 * 2) = 2`, while `φ_1 2 = 1`.
example (hd : IsRegular (2 : ℤ)) (h₂ : (2 : ℤ) ∈ fil (RingHom.id ℤ) (span {2}) 1)
    (h₄ : (2 * 2 : ℤ) ∈ fil (RingHom.id ℤ) (span {2}) 1) :
    dividedFrobenius (RingHom.id ℤ) hd 1 ⟨2 * 2, h₄⟩ ≠
      dividedFrobenius (RingHom.id ℤ) hd 1 ⟨2, h₂⟩ *
        dividedFrobenius (RingHom.id ℤ) hd 1 ⟨2, h₂⟩ := by
  have h₄' : dividedFrobenius (RingHom.id ℤ) hd 1 ⟨2 * 2, h₄⟩ = 2 := by
    rw [dividedFrobenius_eq_iff, RingHom.id_apply]
    norm_num
  have h₂' : dividedFrobenius (RingHom.id ℤ) hd 1 ⟨2, h₂⟩ = 1 := by
    rw [dividedFrobenius_eq_iff, RingHom.id_apply]
    norm_num
  rw [h₄', h₂']
  norm_num

end TauCeti.Prismatic.Nygaard
