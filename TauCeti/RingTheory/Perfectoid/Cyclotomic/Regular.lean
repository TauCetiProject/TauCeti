/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.Cyclotomic.Basic
public import TauCeti.RingTheory.WittVector.Cyclotomic.Regular

import TauCeti.RingTheory.Jacobson.Basic

/-!
# Regularity of cyclotomic periods in `A_inf`

Let `V` be a `p`-adically complete domain in which `p` is not a unit (for instance `O_C` or `C°`
for a complete algebraically closed extension `C` of `ℚ_p`), with tilt `V♭ = PreTilt V p` and
`A_inf(V) = W(V♭)`.

Whenever `ε : V♭` satisfies `ε ≠ 1`, `ε - 1` is a nonzerodivisor in `V♭`. Consequently `μ`, `ξ`,
`ξ'`, `ξ_r`, and `ξ'_r` are all nonzerodivisors in `A_inf(V)`, and the quotients of `A_inf(V)` by
each of them are `p`-torsion-free. When in addition `ε♯ = 1`, `ε - 1` lies in the Jacobson radical
of `V♭`, hence is a nonunit, so `[p, x]` and `[x, p]` are regular sequences on `A_inf(V)` for
`x ∈ {μ, ξ, ξ'}` and for `x ∈ {ξ_r, ξ'_r}` with `1 ≤ r`.

## Main results

* `TauCeti.WittVector.cyclotomicMu_mem_nonZeroDivisors_of_ne_one`,
  `TauCeti.WittVector.cyclotomicXi_mem_nonZeroDivisors_of_ne_one`,
  `TauCeti.WittVector.cyclotomicXiTilde_mem_nonZeroDivisors_of_ne_one`,
  `TauCeti.WittVector.cyclotomicXiLevel_mem_nonZeroDivisors_of_ne_one`,
  `TauCeti.WittVector.cyclotomicXiTildeLevel_mem_nonZeroDivisors_of_ne_one`: nonzerodivisors in
  `W(V♭)` for `ε ≠ 1`.
* `isSMulRegular_quotient_natCast_*_of_ne_one`: `p`-torsion-freeness of `W(V♭) ⧸ (x)`.
* `isRegular_pair_*_of_untilt_eq_one`: regular pairs `[p, x]` and `[x, p]` when `ε♯ = 1` and
  `ε ≠ 1`.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.10,
  Proposition 3.17, and Lemma 3.23.
-/

public section

open Ideal _root_.WittVector RingTheory.Sequence
open scoped nonZeroDivisors

namespace TauCeti.WittVector

section DomainRegularity

variable {p : ℕ} [hp : Fact p.Prime] {V : Type*} [CommRing V] [IsDomain V]
  [Fact ¬IsUnit (p : V)] [IsAdicComplete (span {(p : V)}) V]

local notation "𝕎♭" => _root_.WittVector p (PreTilt V p)

/-- If `ε : V♭` has `ε ≠ 1`, then `μ = [ε] - 1` is a nonzerodivisor in `W(V♭)`. -/
theorem cyclotomicMu_mem_nonZeroDivisors_of_ne_one {ε : PreTilt V p}
    (hne : ε ≠ 1) : cyclotomicMu p ε ∈ (𝕎♭)⁰ :=
  cyclotomicMu_mem_nonZeroDivisors p (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))

/-- If `ε : V♭` has `ε ≠ 1`, then `ξ` is a nonzerodivisor in `W(V♭)`. -/
theorem cyclotomicXi_mem_nonZeroDivisors_of_ne_one {ε : PreTilt V p}
    (hne : ε ≠ 1) : cyclotomicXi p ε ∈ (𝕎♭)⁰ :=
  cyclotomicXi_mem_nonZeroDivisors p (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))

/-- If `ε : V♭` has `ε ≠ 1`, then `ξ'` is a nonzerodivisor in `W(V♭)`. -/
theorem cyclotomicXiTilde_mem_nonZeroDivisors_of_ne_one {ε : PreTilt V p}
    (hne : ε ≠ 1) : cyclotomicXiTilde p ε ∈ (𝕎♭)⁰ :=
  cyclotomicXiTilde_mem_nonZeroDivisors p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))

/-- If `ε : V♭` has `ε ≠ 1`, then `ξ_r` is a nonzerodivisor in `W(V♭)`. -/
theorem cyclotomicXiLevel_mem_nonZeroDivisors_of_ne_one {ε : PreTilt V p}
    (hne : ε ≠ 1) (r : ℕ) : cyclotomicXiLevel p ε r ∈ (𝕎♭)⁰ :=
  cyclotomicXiLevel_mem_nonZeroDivisors p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne)) r

/-- If `ε : V♭` has `ε ≠ 1`, then `ξ'_r` is a nonzerodivisor in `W(V♭)`. -/
theorem cyclotomicXiTildeLevel_mem_nonZeroDivisors_of_ne_one {ε : PreTilt V p}
    (hne : ε ≠ 1) (r : ℕ) : cyclotomicXiTildeLevel p ε r ∈ (𝕎♭)⁰ :=
  cyclotomicXiTildeLevel_mem_nonZeroDivisors p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne)) r

/-- If `ε : V♭` has `ε ≠ 1`, then `W(V♭) ⧸ (μ)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicMu_of_ne_one {ε : PreTilt V p} (hne : ε ≠ 1) :
    IsSMulRegular (𝕎♭ ⧸ span {cyclotomicMu p ε}) (p : 𝕎♭) :=
  isSMulRegular_quotient_natCast_cyclotomicMu p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))

/-- If `ε : V♭` has `ε ≠ 1`, then `W(V♭) ⧸ (ξ)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXi_of_ne_one {ε : PreTilt V p} (hne : ε ≠ 1) :
    IsSMulRegular (𝕎♭ ⧸ span {cyclotomicXi p ε}) (p : 𝕎♭) :=
  isSMulRegular_quotient_natCast_cyclotomicXi p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))

/-- If `ε : V♭` has `ε ≠ 1`, then `W(V♭) ⧸ (ξ')` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXiTilde_of_ne_one {ε : PreTilt V p}
    (hne : ε ≠ 1) :
    IsSMulRegular (𝕎♭ ⧸ span {cyclotomicXiTilde p ε}) (p : 𝕎♭) :=
  isSMulRegular_quotient_natCast_cyclotomicXiTilde p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))

/-- If `ε : V♭` has `ε ≠ 1`, then `W(V♭) ⧸ (ξ_r)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXiLevel_of_ne_one {ε : PreTilt V p}
    (hne : ε ≠ 1) (r : ℕ) :
    IsSMulRegular (𝕎♭ ⧸ span {cyclotomicXiLevel p ε r}) (p : 𝕎♭) :=
  isSMulRegular_quotient_natCast_cyclotomicXiLevel p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne)) r

/-- If `ε : V♭` has `ε ≠ 1`, then `W(V♭) ⧸ (ξ'_r)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXiTildeLevel_of_ne_one {ε : PreTilt V p}
    (hne : ε ≠ 1) (r : ℕ) :
    IsSMulRegular (𝕎♭ ⧸ span {cyclotomicXiTildeLevel p ε r}) (p : 𝕎♭) :=
  isSMulRegular_quotient_natCast_cyclotomicXiTildeLevel p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne)) r

/-- If `ε : V♭` has `ε♯ = 1` and `ε ≠ 1`, then `[p, μ]` is a regular sequence on `W(V♭)`. -/
theorem isRegular_pair_natCast_cyclotomicMu_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) :
    IsRegular (𝕎♭) [(p : 𝕎♭), cyclotomicMu p ε] :=
  isRegular_pair_natCast_cyclotomicMu p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (TauCeti.Ring.not_isUnit_of_mem_jacobson (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1))

/-- If `ε : V♭` has `ε♯ = 1` and `ε ≠ 1`, then `[μ, p]` is a regular sequence on `W(V♭)`. -/
theorem isRegular_pair_cyclotomicMu_natCast_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) :
    IsRegular (𝕎♭) [cyclotomicMu p ε, (p : 𝕎♭)] :=
  isRegular_pair_cyclotomicMu_natCast p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (TauCeti.Ring.not_isUnit_of_mem_jacobson (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1))

/-- If `ε : V♭` has `ε♯ = 1` and `ε ≠ 1`, then `[p, ξ]` is a regular sequence on `W(V♭)`. -/
theorem isRegular_pair_natCast_cyclotomicXi_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) :
    IsRegular (𝕎♭) [(p : 𝕎♭), cyclotomicXi p ε] :=
  isRegular_pair_natCast_cyclotomicXi p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (TauCeti.Ring.not_isUnit_of_mem_jacobson (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1))

/-- If `ε : V♭` has `ε♯ = 1` and `ε ≠ 1`, then `[ξ, p]` is a regular sequence on `W(V♭)`. -/
theorem isRegular_pair_cyclotomicXi_natCast_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) :
    IsRegular (𝕎♭) [cyclotomicXi p ε, (p : 𝕎♭)] :=
  isRegular_pair_cyclotomicXi_natCast p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (TauCeti.Ring.not_isUnit_of_mem_jacobson (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1))

/-- If `ε : V♭` has `ε♯ = 1` and `ε ≠ 1`, then `[p, ξ']` is a regular sequence on `W(V♭)`. -/
theorem isRegular_pair_natCast_cyclotomicXiTilde_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) :
    IsRegular (𝕎♭) [(p : 𝕎♭), cyclotomicXiTilde p ε] :=
  isRegular_pair_natCast_cyclotomicXiTilde p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (TauCeti.Ring.not_isUnit_of_mem_jacobson (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1))

/-- If `ε : V♭` has `ε♯ = 1` and `ε ≠ 1`, then `[ξ', p]` is a regular sequence on `W(V♭)`. -/
theorem isRegular_pair_cyclotomicXiTilde_natCast_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) :
    IsRegular (𝕎♭) [cyclotomicXiTilde p ε, (p : 𝕎♭)] :=
  isRegular_pair_cyclotomicXiTilde_natCast p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (TauCeti.Ring.not_isUnit_of_mem_jacobson (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1))

/-- If `ε : V♭` has `ε♯ = 1`, `ε ≠ 1`, and `1 ≤ r`, then `[p, ξ_r]` is a regular sequence on
`W(V♭)`. -/
theorem isRegular_pair_natCast_cyclotomicXiLevel_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎♭) [(p : 𝕎♭), cyclotomicXiLevel p ε r] :=
  isRegular_pair_natCast_cyclotomicXiLevel p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (TauCeti.Ring.not_isUnit_of_mem_jacobson (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1))
    hr

/-- If `ε : V♭` has `ε♯ = 1`, `ε ≠ 1`, and `1 ≤ r`, then `[ξ_r, p]` is a regular sequence on
`W(V♭)`. -/
theorem isRegular_pair_cyclotomicXiLevel_natCast_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎♭) [cyclotomicXiLevel p ε r, (p : 𝕎♭)] :=
  isRegular_pair_cyclotomicXiLevel_natCast p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (TauCeti.Ring.not_isUnit_of_mem_jacobson (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1))
    hr

/-- If `ε : V♭` has `ε♯ = 1`, `ε ≠ 1`, and `1 ≤ r`, then `[p, ξ'_r]` is a regular sequence on
`W(V♭)`. -/
theorem isRegular_pair_natCast_cyclotomicXiTildeLevel_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎♭) [(p : 𝕎♭), cyclotomicXiTildeLevel p ε r] :=
  isRegular_pair_natCast_cyclotomicXiTildeLevel p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (TauCeti.Ring.not_isUnit_of_mem_jacobson (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1))
    hr

/-- If `ε : V♭` has `ε♯ = 1`, `ε ≠ 1`, and `1 ≤ r`, then `[ξ'_r, p]` is a regular sequence on
`W(V♭)`. -/
theorem isRegular_pair_cyclotomicXiTildeLevel_natCast_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎♭) [cyclotomicXiTildeLevel p ε r, (p : 𝕎♭)] :=
  isRegular_pair_cyclotomicXiTildeLevel_natCast p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (TauCeti.Ring.not_isUnit_of_mem_jacobson (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1))
    hr

end DomainRegularity

end TauCeti.WittVector
