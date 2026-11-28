/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Cyclotomic.Level
public import TauCeti.RingTheory.WittVector.Regular.Sequence

/-!
# Regularity of the cyclotomic period elements

Let `S` be a ring of characteristic `p` and `ε ∈ S`. Whenever `ε - 1 ∈ S⁰`, the forward period
elements `μ = [ε] - 1`, `ξ'`, and `ξ'_r` are nonzerodivisors in `W(S)`. When `S` is perfect of
characteristic `p` and `ε - 1 ∈ S⁰`, `ξ` and `ξ_r` are also nonzerodivisors in `W(S)`, and the
quotients of `W(S)` by `μ`, `ξ`, `ξ'`, `ξ_r`, and `ξ'_r` are `p`-torsion-free. When in addition
`ε - 1` is not a unit of `S`, `[p, x]` and `[x, p]` are regular sequences on `W(S)` for
`x ∈ {μ, ξ, ξ'}` and for `x ∈ {ξ_r, ξ'_r}` with `r ≥ 1`.

## Main results

* `mem_nonZeroDivisors` for `μ`, `ξ'`, `ξ'_r` (for any ring of characteristic `p`) and for
  `ξ`, `ξ_r` (for a perfect ring of characteristic `p`).
* `isSMulRegular_quotient_natCast` for `μ`, `ξ`, `ξ'`, `ξ_r`, `ξ'_r`.
* `isRegular_pair` (in both orders) for `μ`, `ξ`, `ξ'`, `ξ_r` (`1 ≤ r`), and `ξ'_r` (`1 ≤ r`)
  under `ε - 1 ∈ S⁰` and `¬ IsUnit (ε - 1)`.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Proposition 3.17 and
  Lemma 3.23.
-/

public section

open _root_.WittVector RingTheory.Sequence
open scoped nonZeroDivisors

namespace TauCeti.WittVector

variable (p : ℕ) [hp : Fact p.Prime] {S : Type*} [CommRing S] [CharP S p]

local notation "𝕎" => _root_.WittVector p

/-- If `ε - 1 ∈ S⁰`, then `μ = [ε] - 1` is a nonzerodivisor in `W(S)`. -/
theorem cyclotomicMu_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) :
    cyclotomicMu p ε ∈ (𝕎 S)⁰ :=
  mem_nonZeroDivisors_of_coeff_zero (by simpa using hε)

/-- If `ε - 1 ∈ S⁰`, then `ξ'` is a nonzerodivisor in `W(S)`. -/
theorem cyclotomicXiTilde_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) :
    cyclotomicXiTilde p ε ∈ (𝕎 S)⁰ :=
  mem_nonZeroDivisors_of_coeff_zero (cyclotomicXiTilde_coeff_zero_mem_nonZeroDivisors p hε)

/-- If `ε - 1 ∈ S⁰`, then `ξ'_r` is a nonzerodivisor in `W(S)`. -/
theorem cyclotomicXiTildeLevel_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) (r : ℕ) :
    cyclotomicXiTildeLevel p ε r ∈ (𝕎 S)⁰ :=
  mem_nonZeroDivisors_of_coeff_zero (cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors p hε r)

section Perfect

variable [PerfectRing S p]

/-- If `ε - 1 ∈ S⁰`, then `ξ` is a nonzerodivisor in `W(S)`. -/
theorem cyclotomicXi_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) :
    cyclotomicXi p ε ∈ (𝕎 S)⁰ :=
  mem_nonZeroDivisors_of_coeff_zero (cyclotomicXi_coeff_zero_mem_nonZeroDivisors p hε)

/-- If `ε - 1 ∈ S⁰`, then `ξ_r` is a nonzerodivisor in `W(S)`. -/
theorem cyclotomicXiLevel_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) (r : ℕ) :
    cyclotomicXiLevel p ε r ∈ (𝕎 S)⁰ :=
  mem_nonZeroDivisors_of_coeff_zero (cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors p hε r)

/-- If `ε - 1 ∈ S⁰`, then `W(S) ⧸ (μ)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicMu {ε : S} (hε : ε - 1 ∈ S⁰) :
    IsSMulRegular (𝕎 S ⧸ Ideal.span {cyclotomicMu p ε}) (p : 𝕎 S) :=
  isSMulRegular_quotient_natCast_of_coeff_zero (by simpa using hε)

/-- If `ε - 1 ∈ S⁰`, then `W(S) ⧸ (ξ)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXi {ε : S} (hε : ε - 1 ∈ S⁰) :
    IsSMulRegular (𝕎 S ⧸ Ideal.span {cyclotomicXi p ε}) (p : 𝕎 S) :=
  isSMulRegular_quotient_natCast_of_coeff_zero
    (cyclotomicXi_coeff_zero_mem_nonZeroDivisors p hε)

/-- If `ε - 1 ∈ S⁰`, then `W(S) ⧸ (ξ')` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXiTilde {ε : S} (hε : ε - 1 ∈ S⁰) :
    IsSMulRegular (𝕎 S ⧸ Ideal.span {cyclotomicXiTilde p ε}) (p : 𝕎 S) :=
  isSMulRegular_quotient_natCast_of_coeff_zero
    (cyclotomicXiTilde_coeff_zero_mem_nonZeroDivisors p hε)

/-- If `ε - 1 ∈ S⁰`, then `W(S) ⧸ (ξ_r)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXiLevel {ε : S} (hε : ε - 1 ∈ S⁰) (r : ℕ) :
    IsSMulRegular (𝕎 S ⧸ Ideal.span {cyclotomicXiLevel p ε r}) (p : 𝕎 S) :=
  isSMulRegular_quotient_natCast_of_coeff_zero
    (cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors p hε r)

/-- If `ε - 1 ∈ S⁰`, then `W(S) ⧸ (ξ'_r)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXiTildeLevel {ε : S} (hε : ε - 1 ∈ S⁰)
    (r : ℕ) :
    IsSMulRegular (𝕎 S ⧸ Ideal.span {cyclotomicXiTildeLevel p ε r}) (p : 𝕎 S) :=
  isSMulRegular_quotient_natCast_of_coeff_zero
    (cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors p hε r)

/-- If `ε - 1 ∈ S⁰` and `¬ IsUnit (ε - 1)`, then `[p, μ]` is regular on `W(S)`. -/
theorem isRegular_pair_natCast_cyclotomicMu {ε : S} (hε : ε - 1 ∈ S⁰) (hnu : ¬ IsUnit (ε - 1)) :
    IsRegular (𝕎 S) [(p : 𝕎 S), cyclotomicMu p ε] :=
  isRegular_natCast_cons_singleton _ (by simpa using hε) (by simpa using hnu)

/-- If `ε - 1 ∈ S⁰` and `¬ IsUnit (ε - 1)`, then `[μ, p]` is regular on `W(S)`. -/
theorem isRegular_pair_cyclotomicMu_natCast {ε : S} (hε : ε - 1 ∈ S⁰) (hnu : ¬ IsUnit (ε - 1)) :
    IsRegular (𝕎 S) [cyclotomicMu p ε, (p : 𝕎 S)] :=
  isRegular_pair_of_coeff_zero (by simpa using hε) (by simpa using hnu)

/-- If `ε - 1 ∈ S⁰` and `¬ IsUnit (ε - 1)`, then `[p, ξ]` is regular on `W(S)`. -/
theorem isRegular_pair_natCast_cyclotomicXi {ε : S} (hε : ε - 1 ∈ S⁰) (hnu : ¬ IsUnit (ε - 1)) :
    IsRegular (𝕎 S) [(p : 𝕎 S), cyclotomicXi p ε] :=
  isRegular_natCast_cons_singleton _ (cyclotomicXi_coeff_zero_mem_nonZeroDivisors p hε)
    (not_isUnit_coeff_zero_cyclotomicXi p hnu)

/-- If `ε - 1 ∈ S⁰` and `¬ IsUnit (ε - 1)`, then `[ξ, p]` is regular on `W(S)`. -/
theorem isRegular_pair_cyclotomicXi_natCast {ε : S} (hε : ε - 1 ∈ S⁰) (hnu : ¬ IsUnit (ε - 1)) :
    IsRegular (𝕎 S) [cyclotomicXi p ε, (p : 𝕎 S)] :=
  isRegular_pair_of_coeff_zero (cyclotomicXi_coeff_zero_mem_nonZeroDivisors p hε)
    (not_isUnit_coeff_zero_cyclotomicXi p hnu)

/-- If `ε - 1 ∈ S⁰` and `¬ IsUnit (ε - 1)`, then `[p, ξ']` is regular on `W(S)`. -/
theorem isRegular_pair_natCast_cyclotomicXiTilde {ε : S} (hε : ε - 1 ∈ S⁰)
    (hnu : ¬ IsUnit (ε - 1)) :
    IsRegular (𝕎 S) [(p : 𝕎 S), cyclotomicXiTilde p ε] :=
  isRegular_natCast_cons_singleton _ (cyclotomicXiTilde_coeff_zero_mem_nonZeroDivisors p hε)
    (not_isUnit_coeff_zero_cyclotomicXiTilde p hnu)

/-- If `ε - 1 ∈ S⁰` and `¬ IsUnit (ε - 1)`, then `[ξ', p]` is regular on `W(S)`. -/
theorem isRegular_pair_cyclotomicXiTilde_natCast {ε : S} (hε : ε - 1 ∈ S⁰)
    (hnu : ¬ IsUnit (ε - 1)) :
    IsRegular (𝕎 S) [cyclotomicXiTilde p ε, (p : 𝕎 S)] :=
  isRegular_pair_of_coeff_zero (cyclotomicXiTilde_coeff_zero_mem_nonZeroDivisors p hε)
    (not_isUnit_coeff_zero_cyclotomicXiTilde p hnu)

/-- If `ε - 1 ∈ S⁰`, `¬ IsUnit (ε - 1)`, and `1 ≤ r`, then `[p, ξ_r]` is regular on `W(S)`. -/
theorem isRegular_pair_natCast_cyclotomicXiLevel {ε : S} (hε : ε - 1 ∈ S⁰)
    (hnu : ¬ IsUnit (ε - 1)) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎 S) [(p : 𝕎 S), cyclotomicXiLevel p ε r] :=
  isRegular_natCast_cons_singleton _ (cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors p hε r)
    (not_isUnit_coeff_zero_cyclotomicXiLevel p hnu hr)

/-- If `ε - 1 ∈ S⁰`, `¬ IsUnit (ε - 1)`, and `1 ≤ r`, then `[ξ_r, p]` is regular on `W(S)`. -/
theorem isRegular_pair_cyclotomicXiLevel_natCast {ε : S} (hε : ε - 1 ∈ S⁰)
    (hnu : ¬ IsUnit (ε - 1)) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎 S) [cyclotomicXiLevel p ε r, (p : 𝕎 S)] :=
  isRegular_pair_of_coeff_zero (cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors p hε r)
    (not_isUnit_coeff_zero_cyclotomicXiLevel p hnu hr)

/-- If `ε - 1 ∈ S⁰`, `¬ IsUnit (ε - 1)`, and `1 ≤ r`, then `[p, ξ'_r]` is regular on `W(S)`. -/
theorem isRegular_pair_natCast_cyclotomicXiTildeLevel {ε : S} (hε : ε - 1 ∈ S⁰)
    (hnu : ¬ IsUnit (ε - 1)) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎 S) [(p : 𝕎 S), cyclotomicXiTildeLevel p ε r] :=
  isRegular_natCast_cons_singleton _
    (cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors p hε r)
    (not_isUnit_coeff_zero_cyclotomicXiTildeLevel p hnu hr)

/-- If `ε - 1 ∈ S⁰`, `¬ IsUnit (ε - 1)`, and `1 ≤ r`, then `[ξ'_r, p]` is regular on `W(S)`. -/
theorem isRegular_pair_cyclotomicXiTildeLevel_natCast {ε : S} (hε : ε - 1 ∈ S⁰)
    (hnu : ¬ IsUnit (ε - 1)) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎 S) [cyclotomicXiTildeLevel p ε r, (p : 𝕎 S)] :=
  isRegular_pair_of_coeff_zero
    (cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors p hε r)
    (not_isUnit_coeff_zero_cyclotomicXiTildeLevel p hnu hr)

end Perfect

end TauCeti.WittVector
