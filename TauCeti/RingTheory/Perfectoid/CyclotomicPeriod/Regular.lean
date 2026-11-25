/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.CyclotomicPeriod.SpecializationKernel
public import TauCeti.RingTheory.WittVector.RegularSequence

import TauCeti.RingTheory.WittVector.Units

/-!
# Regularity of the cyclotomic periods

Let `A` be a `p`-adically complete ring in which `p` is not a unit, with tilt `A♭`, and let
`ε ∈ A♭` be such that the sharp of `ε ^ (1 / p)` is a primitive `p`-th root of unity. We show
that the cyclotomic periods `μ`, `ξ`, `xiTilde = φ(ξ)` and their finite Frobenius products
`ξ_r` and `xiTilde_r` are nonzero in `W(A♭)`, and nonzerodivisors when `A` is a domain. For a
domain `A` the pairs `(p, μ)`, `(p, ξ)` and `(p, xiTilde)` are regular sequences of `W(A♭)`. For
the valuation ring `O_C` of a complete algebraically closed field, `p` is a nonzerodivisor on
`A_inf / (ξ) ≅ O_C`.

Everything is read off from zeroth Witt coordinates: the zeroth coordinate of `μ` is
`ε - 1 ≠ 0`, and the factorizations `μ = ξ_r * φ^(-r)(μ)` and `φ^r(μ) = xiTilde_r * μ` propagate
this to the other periods. Each of `μ`, `ξ`, `xiTilde` is killed by `θ` or by the shifted map
`θ ∘ φ^(-1)`, so it is not a unit, and neither is its zeroth coordinate.

## Main results

* `PreTilt.mu_ne_zero`, `PreTilt.xi_ne_zero`, `PreTilt.xiLevel_ne_zero`,
  `PreTilt.xiTilde_ne_zero`, `PreTilt.xiTildeLevel_ne_zero`: the periods are nonzero.
* `PreTilt.mu_mem_nonZeroDivisors`, `PreTilt.xiLevel_mem_nonZeroDivisors`,
  `PreTilt.xiTildeLevel_mem_nonZeroDivisors`: over a domain they are nonzerodivisors.
* `PreTilt.isRegular_natCast_mu`, `PreTilt.isRegular_natCast_xi`,
  `PreTilt.isRegular_natCast_xiTilde`: the regular pairs `(p, μ)`, `(p, ξ)`, `(p, xiTilde)`.
* `PreTilt.mk_natCast_mem_nonZeroDivisors_quotient_span_xi`: `p` is a nonzerodivisor on
  `A_inf / (ξ)` for `O_C`.

## References

* Bhatt, Morrow and Scholze, *Integral p-adic Hodge theory*, arXiv:1602.03148v3, Lemma 3.10,
  Proposition 3.17 and Lemma 3.23.
-/

public section

namespace PreTilt

open TauCeti.Perfectoid _root_.WittVector RingTheory.Sequence
open scoped nonZeroDivisors

section Nonzero

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [Fact ¬IsUnit (p : A)]
  [IsAdicComplete (Ideal.span {(p : A)}) A] {ε : PreTilt A p}

/-- A primitive root makes `μ` nonzero. -/
theorem mu_ne_zero
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    mu p ε ≠ 0 := fun h ↦ coeff_zero_mu_ne_zero hε (by rw [h, zero_coeff])

/-- A primitive root makes the zeroth Witt coordinate of `ξ` nonzero. -/
theorem coeff_zero_xi_ne_zero
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    (xi p ε).coeff 0 ≠ 0 := fun h ↦ coeff_zero_mu_ne_zero hε (by
  rw [mu_eq_xi_mul_frobeniusEquiv_symm, mul_coeff_zero, h, zero_mul])

/-- A primitive root makes `ξ` nonzero. -/
theorem xi_ne_zero
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    xi p ε ≠ 0 := fun h ↦ coeff_zero_xi_ne_zero hε (by rw [h, zero_coeff])

/-- A primitive root makes every finite generator `ξ_r` nonzero. -/
theorem xiLevel_ne_zero
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) (r : ℕ) :
    xiLevel p ε r ≠ 0 := fun h ↦ mu_ne_zero hε (by rw [mu_eq_xiLevel_mul p ε r, h, zero_mul])

/-- A primitive root makes every twisted generator `xiTilde_r` nonzero. -/
theorem xiTildeLevel_ne_zero
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) (r : ℕ) :
    xiTildeLevel p ε r ≠ 0 := by
  intro h
  have h0 := iterate_frobeniusEquiv_mu_eq_xiTildeLevel_mul p ε r
  rw [h, zero_mul, ← iterate_map_zero (frobeniusEquiv p (PreTilt A p)) r] at h0
  exact mu_ne_zero hε ((frobeniusEquiv p (PreTilt A p)).injective.iterate r h0)

/-- A primitive root makes `xiTilde` nonzero. -/
theorem xiTilde_ne_zero
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    xiTilde p ε ≠ 0 := by
  simpa using xiTildeLevel_ne_zero hε 1

end Nonzero

section Domain

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [IsDomain A] [Fact ¬IsUnit (p : A)]
  [IsAdicComplete (Ideal.span {(p : A)}) A] {ε : PreTilt A p}

/-- Over a domain, `μ` is a nonzerodivisor of `W(A♭)`. -/
theorem mu_mem_nonZeroDivisors
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    mu p ε ∈ (WittVector p (PreTilt A p))⁰ :=
  mem_nonZeroDivisors_of_ne_zero (mu_ne_zero hε)

/-- Over a domain, every finite generator `ξ_r`, in particular `ξ = ξ_1`, is a nonzerodivisor of
`W(A♭)`. -/
theorem xiLevel_mem_nonZeroDivisors
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) (r : ℕ) :
    xiLevel p ε r ∈ (WittVector p (PreTilt A p))⁰ :=
  mem_nonZeroDivisors_of_ne_zero (xiLevel_ne_zero hε r)

/-- Over a domain, every twisted generator `xiTilde_r`, in particular `xiTilde = xiTilde_1`, is a
nonzerodivisor of `W(A♭)`. -/
theorem xiTildeLevel_mem_nonZeroDivisors
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) (r : ℕ) :
    xiTildeLevel p ε r ∈ (WittVector p (PreTilt A p))⁰ :=
  mem_nonZeroDivisors_of_ne_zero (xiTildeLevel_ne_zero hε r)

/-- A Witt vector killed by a ring homomorphism to a nontrivial ring is not a unit, and neither is
its zeroth coordinate; with a nonzero zeroth coordinate over a domain, `(p, x)` is regular. -/
private theorem isRegular_natCast_of_map_eq_zero {B : Type*} [CommRing B] [Nontrivial B]
    {x : WittVector p (PreTilt A p)} (f : WittVector p (PreTilt A p) →+* B) (hf : f x = 0)
    (hx : x.coeff 0 ≠ 0) :
    IsRegular (WittVector p (PreTilt A p)) [(p : WittVector p (PreTilt A p)), x] := by
  refine isRegular_natCast_cons_singleton (mem_nonZeroDivisors_of_ne_zero hx) fun hu ↦ ?_
  have := (isUnit_iff_isUnit_coeff_zero.mpr hu).map f
  rw [hf] at this
  exact not_isUnit_zero this

/-- **The regular pair `(p, μ)`.** -/
theorem isRegular_natCast_mu
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    IsRegular (WittVector p (PreTilt A p)) [(p : WittVector p (PreTilt A p)), mu p ε] :=
  isRegular_natCast_of_map_eq_zero (fontaineTheta A p)
    (fontaineTheta_mu_eq_zero ε (untilt_eq_one_of_isPrimitiveRoot hε)) (coeff_zero_mu_ne_zero hε)

/-- **The regular pair `(p, ξ)`.** -/
theorem isRegular_natCast_xi
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    IsRegular (WittVector p (PreTilt A p)) [(p : WittVector p (PreTilt A p)), xi p ε] :=
  isRegular_natCast_of_map_eq_zero (fontaineTheta A p) (fontaineTheta_xi_eq_zero ε hε)
    (coeff_zero_xi_ne_zero hε)

/-- **The regular pair `(p, xiTilde)`.** -/
theorem isRegular_natCast_xiTilde
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    IsRegular (WittVector p (PreTilt A p)) [(p : WittVector p (PreTilt A p)), xiTilde p ε] := by
  refine isRegular_natCast_of_map_eq_zero (fontaineThetaShifted A p)
    (fontaineThetaShifted_xiTilde_eq_zero ε hε) ?_
  rw [xiTilde_eq, WittVector.frobeniusEquiv_apply, coeff_frobenius_charP]
  exact pow_ne_zero p (coeff_zero_xi_ne_zero hε)

end Domain

section AlgebraicallyClosed

open scoped NormedField Valued

variable {p : ℕ} [Fact p.Prime] {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  [CompleteSpace C] [IsAlgClosed C]
  [Fact ¬IsUnit (p : 𝒪[C])] [IsAdicComplete (Ideal.span {(p : 𝒪[C])}) (𝒪[C])]

/-- **`A_inf / (ξ) ≅ O_C` is `p`-torsion free.** The image of `p` in `A_inf / (ξ)` is a
nonzerodivisor: if `p * y ∈ (ξ) = ker θ`, then `p * θ(y) = 0` in the domain `O_C`, where
`p ≠ 0` because `O_C` contains a primitive `p`-th root of unity. -/
theorem mk_natCast_mem_nonZeroDivisors_quotient_span_xi (ε : PreTilt (𝒪[C]) p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε)) p) :
    Ideal.Quotient.mk (Ideal.span {xi p ε}) (p : WittVector p (PreTilt (𝒪[C]) p)) ∈
      (WittVector p (PreTilt (𝒪[C]) p) ⧸ Ideal.span {xi p ε})⁰ := by
  have hp0 : (p : 𝒪[C]) ≠ 0 := hε.neZero'.out
  refine mem_nonZeroDivisors_iff_left.mpr fun y hy ↦ ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← ker_fontaineTheta_eq_span_xi ε hε,
    RingHom.mem_ker, map_mul, map_natCast] at hy
  rw [Ideal.Quotient.eq_zero_iff_mem, ← ker_fontaineTheta_eq_span_xi ε hε, RingHom.mem_ker]
  exact (mul_eq_zero.mp hy).resolve_left hp0

end AlgebraicallyClosed

end PreTilt
