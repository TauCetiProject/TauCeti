/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.Cyclotomic.Level
public import TauCeti.RingTheory.WittVector.RegularSequence

/-!
# Regularity of the cyclotomic periods

Let `S` be a perfect domain of characteristic `p` and `ε ≠ 1` in `S`. The cyclotomic periods `μ`,
`ξ`, `xiTilde = φ(ξ)` and their finite Frobenius products `ξ_r` and `xiTilde_r` are
nonzerodivisors of `W(S)`, and `p` is a nonzerodivisor on `W(S) ⧸ (ξ)`. For a `p`-adically
complete domain `A` and `ε ∈ A♭` such that the sharp of `ε ^ (1 / p)` is a primitive `p`-th root
of unity, the pairs `(p, μ)`, `(p, ξ)`, `(p, xiTilde)`, `(p, ξ_r)` and `(p, xiTilde_r)` for
`r ≥ 1` are regular sequences of `W(A♭)`.

Everything is read off from zeroth Witt coordinates: the zeroth coordinate of `μ` is
`ε - 1 ≠ 0`, and the factorizations `μ = ξ_r * φ^(-r)(μ)` and `φ^r(ξ_r) = xiTilde_r` propagate
this to the other periods. Each of them is killed by `θ` or by the shifted map `θ ∘ φ^(-1)`, so
it is not a unit.

## Main results

* `TauCeti.Perfectoid.mu_mem_nonZeroDivisors`, `TauCeti.Perfectoid.xi_mem_nonZeroDivisors`,
  `TauCeti.Perfectoid.xiLevel_mem_nonZeroDivisors`,
  `TauCeti.Perfectoid.xiTilde_mem_nonZeroDivisors`,
  `TauCeti.Perfectoid.xiTildeLevel_mem_nonZeroDivisors`: over a perfect domain the periods are
  nonzerodivisors.
* `TauCeti.Perfectoid.mk_natCast_mem_nonZeroDivisors_quotient_span_xi`: `p` is a nonzerodivisor
  on `W(S) ⧸ (ξ)`.
* `PreTilt.isRegular_natCast_mu`, `PreTilt.isRegular_natCast_xi`,
  `PreTilt.isRegular_natCast_xiTilde`, `PreTilt.isRegular_natCast_xiLevel`,
  `PreTilt.isRegular_natCast_xiTildeLevel`: the regular pairs.

## References

* Bhatt, Morrow and Scholze, *Integral p-adic Hodge theory*, arXiv:1602.03148v3, Lemma 3.10,
  Proposition 3.17 and Lemma 3.23.
-/

public section

open _root_.WittVector RingTheory.Sequence
open scoped nonZeroDivisors

namespace TauCeti.Perfectoid

section Domain

variable (p : ℕ) [Fact p.Prime] {S : Type*} [CommRing S] [IsDomain S] [CharP S p]
  [PerfectRing S p] {ε : S}

omit [PerfectRing S p] in
/-- Over a perfect domain, `μ` is a nonzerodivisor of `W(S)` for `ε ≠ 1`. -/
theorem mu_mem_nonZeroDivisors (hε : ε ≠ 1) : mu p ε ∈ (WittVector p S)⁰ :=
  mem_nonZeroDivisors_of_ne_zero (mu_ne_zero p hε)

/-- Over a perfect domain, `ξ` is a nonzerodivisor of `W(S)` for `ε ≠ 1`. -/
theorem xi_mem_nonZeroDivisors (hε : ε ≠ 1) : xi p ε ∈ (WittVector p S)⁰ :=
  mem_nonZeroDivisors_of_ne_zero (xi_ne_zero p hε)

/-- Over a perfect domain, every finite product `ξ_r` is a nonzerodivisor of `W(S)` for
`ε ≠ 1`. -/
theorem xiLevel_mem_nonZeroDivisors (hε : ε ≠ 1) (r : ℕ) : xiLevel p ε r ∈ (WittVector p S)⁰ :=
  mem_nonZeroDivisors_of_ne_zero (xiLevel_ne_zero p hε r)

/-- Over a perfect domain, `xiTilde` is a nonzerodivisor of `W(S)` for `ε ≠ 1`. -/
theorem xiTilde_mem_nonZeroDivisors (hε : ε ≠ 1) : xiTilde p ε ∈ (WittVector p S)⁰ :=
  mem_nonZeroDivisors_of_ne_zero (xiTilde_ne_zero p hε)

/-- Over a perfect domain, every twisted product `xiTilde_r` is a nonzerodivisor of `W(S)` for
`ε ≠ 1`. -/
theorem xiTildeLevel_mem_nonZeroDivisors (hε : ε ≠ 1) (r : ℕ) :
    xiTildeLevel p ε r ∈ (WittVector p S)⁰ :=
  mem_nonZeroDivisors_of_ne_zero (xiTildeLevel_ne_zero p hε r)

/-- Over a perfect domain, `p` is a nonzerodivisor on `W(S) ⧸ (ξ)` for `ε ≠ 1`. -/
theorem mk_natCast_mem_nonZeroDivisors_quotient_span_xi (hε : ε ≠ 1) :
    Ideal.Quotient.mk (Ideal.span {xi p ε}) (p : WittVector p S) ∈
      (WittVector p S ⧸ Ideal.span {xi p ε})⁰ :=
  mk_natCast_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero (coeff_zero_xi_ne_zero p hε))

end Domain

end TauCeti.Perfectoid

namespace PreTilt

open TauCeti.Perfectoid

section RegularPairs

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [IsDomain A] [Fact ¬IsUnit (p : A)]
  [IsAdicComplete (Ideal.span {(p : A)}) A]

/-- **The regular pair `(p, μ)`.** -/
theorem isRegular_natCast_mu (ε : PreTilt A p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    IsRegular (WittVector p (PreTilt A p)) [(p : WittVector p (PreTilt A p)), mu p ε] :=
  isRegular_natCast_cons_singleton_of_map_eq_zero _
    (mem_nonZeroDivisors_of_ne_zero (coeff_zero_mu_ne_zero p (ε.ne_one_of_isPrimitiveRoot hε)))
    (fontaineTheta A p) (fontaineTheta_mu_eq_zero ε (ε.untilt_eq_one_of_isPrimitiveRoot hε))

/-- **The regular pair `(p, ξ)`.** -/
theorem isRegular_natCast_xi (ε : PreTilt A p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    IsRegular (WittVector p (PreTilt A p)) [(p : WittVector p (PreTilt A p)), xi p ε] :=
  isRegular_natCast_cons_singleton_of_map_eq_zero _
    (mem_nonZeroDivisors_of_ne_zero (coeff_zero_xi_ne_zero p (ε.ne_one_of_isPrimitiveRoot hε)))
    (fontaineTheta A p) (fontaineTheta_xi_eq_zero ε hε)

/-- **The regular pairs `(p, ξ_r)`**, for `r ≥ 1`. -/
theorem isRegular_natCast_xiLevel (ε : PreTilt A p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (WittVector p (PreTilt A p)) [(p : WittVector p (PreTilt A p)), xiLevel p ε r] := by
  refine isRegular_natCast_cons_singleton_of_map_eq_zero _ (mem_nonZeroDivisors_of_ne_zero
    (coeff_zero_xiLevel_ne_zero p (ε.ne_one_of_isPrimitiveRoot hε) r)) (fontaineTheta A p) ?_
  obtain ⟨c, hc⟩ := xi_dvd_xiLevel p ε hr
  rw [hc, map_mul, fontaineTheta_xi_eq_zero ε hε, zero_mul]

omit [IsDomain A] [IsAdicComplete (Ideal.span {(p : A)}) A] in
/-- The zeroth Witt coordinate of `φ^r(x)` is the `p ^ r`-th power of that of `x`. -/
private theorem coeff_zero_iterate_frobeniusEquiv (x : WittVector p (PreTilt A p)) (r : ℕ) :
    ((frobeniusEquiv p (PreTilt A p))^[r] x).coeff 0 = x.coeff 0 ^ p ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', pow_succ, pow_mul, ← ih]
    exact coeff_frobenius_charP p _ 0

/-- **The regular pair `(p, xiTilde)`.** -/
theorem isRegular_natCast_xiTilde (ε : PreTilt A p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    IsRegular (WittVector p (PreTilt A p)) [(p : WittVector p (PreTilt A p)), xiTilde p ε] := by
  refine isRegular_natCast_cons_singleton_of_map_eq_zero _ (mem_nonZeroDivisors_of_ne_zero ?_)
    (fontaineThetaShifted A p) (fontaineThetaShifted_xiTilde_eq_zero ε hε)
  rw [xiTilde_eq, WittVector.frobeniusEquiv_apply, coeff_frobenius_charP]
  exact pow_ne_zero p (coeff_zero_xi_ne_zero p (ε.ne_one_of_isPrimitiveRoot hε))

/-- **The regular pairs `(p, xiTilde_r)`**, for `r ≥ 1`. -/
theorem isRegular_natCast_xiTildeLevel (ε : PreTilt A p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (WittVector p (PreTilt A p))
      [(p : WittVector p (PreTilt A p)), xiTildeLevel p ε r] := by
  refine isRegular_natCast_cons_singleton_of_map_eq_zero _ (mem_nonZeroDivisors_of_ne_zero ?_)
    (fontaineThetaShifted A p) ?_
  · rw [← iterate_frobeniusEquiv_xiLevel, coeff_zero_iterate_frobeniusEquiv]
    exact pow_ne_zero _ (coeff_zero_xiLevel_ne_zero p (ε.ne_one_of_isPrimitiveRoot hε) r)
  · obtain ⟨c, hc⟩ := xiTilde_dvd_xiTildeLevel p ε hr
    rw [hc, map_mul, fontaineThetaShifted_xiTilde_eq_zero ε hε, zero_mul]

end RegularPairs

end PreTilt
