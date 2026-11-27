/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.Cyclotomic.Period
public import TauCeti.RingTheory.Perfectoid.PreTilt.ValuationRing

import TauCeti.RingTheory.Perfectoid.Cyclotomic.Level
import TauCeti.RingTheory.WittVector.Complete
import TauCeti.RingTheory.WittVector.Units

/-!
# Prime elements, adic completeness and radicals in `A_inf`

Let `C` be a nontrivially normed ultrametric field whose valuation ring `O_C` is `p`-adically
complete with `p` not a unit, let `O_C♭` be the tilt of `O_C` and `A_inf = W(O_C♭)`. Since `O_C♭`
is a perfect valuation ring with a rank-one valuation (through the sharp map), the ideal theory of
`A_inf` is controlled by zeroth Witt coordinates:

* `p` is a prime element of `A_inf`, because `A_inf ⧸ (p) ≅ O_C♭` is a domain; this is the case
  `R = O_C♭` of `WittVector.prime_p`.
* If `C` is moreover complete and perfectoid, and `ε ∈ O_C♭` is such that the sharp of
  `ε ^ (1 / p)` is a primitive `p`-th root of unity, then Fontaine's map identifies `A_inf ⧸ (ξ)`
  with the domain `O_C`, so the cyclotomic period `ξ` is a prime element (`PreTilt.prime_xi`).
* If `p ≠ 0` in `C`, then `A_inf` is complete and separated for the `(a, c)`-adic topology for any
  two nonunits `a` and `c` (`PreTilt.isAdicComplete_span_pair_of_not_isUnit`). The zeroth Witt
  coordinates of `a` and `c` are comparable for divisibility; if `ϖ` is the one dividing the
  other, `O_C♭` is `ϖ`-adically complete, so `A_inf` is `(p, [ϖ])`-adically complete, and both `a`
  and `c` lie in `(p, [ϖ])`. This covers, for instance, the `(p, ξ)`-adic and `(p, μ)`-adic
  topologies.
* If `p ∤ δ`, every nonunit of `A_inf` lies in the radical of `(p, δ)`
  (`PreTilt.mem_radical_span_pair_of_not_dvd`): the zeroth Witt coordinate `δ₀` is nonzero and
  divides a power `a₀ ^ n` of the zeroth coordinate of a nonunit `a`, say `a₀ ^ n = δ₀ u`, and then
  `a ^ n - δ [u]` has zeroth coordinate zero, so lies in `(p)`.

## Main results

* `PreTilt.prime_xi`: `ξ` is a prime element of `A_inf`.
* `PreTilt.isAdicComplete_span_pair_of_not_isUnit`: for nonunits `a, c` of `A_inf`, `A_inf` is
  `(a, c)`-adically complete.
* `PreTilt.mem_radical_span_pair_of_not_dvd`: if `p ∤ δ`, every nonunit of `A_inf` lies in the
  radical of `(p, δ)`.

## Provenance

The statements follow `New.Period.Ainf.prime_p`, `New.Period.Ainf.prime_xi`,
`New.Period.Ainf.isAdicComplete_span_pair` and `New.Period.Ainf.mem_radical_of_not_isUnit` in
`src/Lib/PadicHodge/PeriodRings/Ainf.lean` of grh-lean (https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic, PBC), where they are proved for `C = ℂ_p`; the proofs here
go through zeroth Witt coordinates and the sharp map instead.

## References

* J.-M. Fontaine, *Le corps des périodes p-adiques*, Astérisque 223 (1994).
* X. Caruso, *An introduction to p-adic period rings* (2019), §2.
-/

public section

namespace PreTilt

open TauCeti.Perfectoid _root_.WittVector
open scoped NormedField Valued

variable {p : ℕ} [Fact p.Prime] {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  [Fact ¬IsUnit (p : 𝒪[C])] [IsAdicComplete (Ideal.span {(p : 𝒪[C])}) (𝒪[C])]

/-- **`ξ` is a prime element of `A_inf`.** For a complete perfectoid nonarchimedean field `C`
and `ε ∈ O_C♭` such that the sharp of `ε ^ (1 / p)` is a primitive `p`-th root of unity, the
cyclotomic period `ξ` generates the kernel of Fontaine's map onto the domain `O_C`. -/
theorem prime_xi [CompleteSpace C] [IsPerfectoidTateRing p C] (ε : PreTilt (𝒪[C]) p)
    (hε : IsPrimitiveRoot
      (untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε)) p) :
    Prime (xi p ε) := by
  rw [← Ideal.span_singleton_prime (xi_ne_zero p (ne_one_of_isPrimitiveRoot ε hε)),
    ← ker_fontaineTheta_eq_span_xi ε hε]
  exact RingHom.ker_isPrime _

/-- **`A_inf` is complete for the ideal of any two nonunits.** If `p ≠ 0` in `C`, then
`A_inf = W(O_C♭)` is `(a, c)`-adically complete and separated for all nonunits `a` and `c`. -/
theorem isAdicComplete_span_pair_of_not_isUnit (hp : (p : C) ≠ 0)
    {a c : WittVector p (PreTilt (𝒪[C]) p)} (ha : ¬IsUnit a) (hc : ¬IsUnit c) :
    IsAdicComplete (Ideal.span {a, c}) (WittVector p (PreTilt (𝒪[C]) p)) := by
  rw [isUnit_iff_isUnit_coeff_zero] at ha hc
  rcases ValuationRing.dvd_total (a.coeff 0) (c.coeff 0) with h | h
  · have := isAdicComplete_span_singleton_of_not_isUnit hp ha
    exact isAdicComplete_span_pair_of_dvd_coeff_zero dvd_rfl h
  · have := isAdicComplete_span_singleton_of_not_isUnit hp hc
    exact isAdicComplete_span_pair_of_dvd_coeff_zero h dvd_rfl

/-- **Nonunits of `A_inf` lie in the radical of `(p, δ)` for every `δ` not divisible by `p`.** -/
theorem mem_radical_span_pair_of_not_dvd {δ a : WittVector p (PreTilt (𝒪[C]) p)}
    (hδ : ¬(p : WittVector p (PreTilt (𝒪[C]) p)) ∣ δ) (ha : ¬IsUnit a) :
    a ∈ (Ideal.span {(p : WittVector p (PreTilt (𝒪[C]) p)), δ}).radical := by
  have hδ0 : δ.coeff 0 ≠ 0 := fun h ↦
    hδ (Ideal.mem_span_singleton.mp ((mem_span_p_iff_coeff_zero_eq_zero δ).mpr h))
  obtain ⟨n, u, hu⟩ :=
    exists_dvd_pow_of_not_isUnit (isUnit_iff_isUnit_coeff_zero.not.mp ha) hδ0
  -- `a ^ n - δ [u]` has zeroth Witt coordinate `a₀ ^ n - δ₀ u = 0`, so it is a multiple of `p`.
  have h : a ^ n - δ * teichmuller p u ∈ Ideal.span {(p : WittVector p (PreTilt (𝒪[C]) p))} := by
    rw [mem_span_p_iff_coeff_zero_eq_zero, ← constantCoeff_apply, map_sub, map_mul, map_pow]
    simp only [constantCoeff_apply, teichmuller_coeff_zero, hu, sub_self]
  refine ⟨n, ?_⟩
  rw [← sub_add_cancel (a ^ n) (δ * teichmuller p u)]
  exact add_mem (Ideal.span_mono (by simp) h)
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

end PreTilt
