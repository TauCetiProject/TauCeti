/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.ShiftedTheta
public import TauCeti.RingTheory.Perfectoid.Pair
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.RingTheory.Huber.Normed
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuedField

import TauCeti.RingTheory.Huber.ValuedField
import TauCeti.RingTheory.WittVector.Frobenius
import TauCeti.RingTheory.WittVector.Units

/-!
# Cyclotomic periods

The periods `μ = [ε] - 1`, `ξ = ∑ j < p, [ε^(1/p)]^j`, and `xiTilde = φ(ξ)`
are defined in Witt vectors without division. When the sharp of `ε^(1/p)` is a primitive
`p`-th root of unity, `ξ` generates Fontaine's kernel on perfectoid integer rings.

Frobenius acts on `μ` and `xiTilde` by replacing `ε` with `ε ^ p`, and the zeroth Witt coordinate
of `μ` is `ε - 1`, so `μ ≠ 0` for `ε ≠ 1`.

## Main results

* `TauCeti.Perfectoid.mu_eq_xi_mul_frobeniusEquiv_symm`: `μ = ξ * φ^(-1)(μ)`.
* `TauCeti.Perfectoid.iterate_frobeniusEquiv_mu`: `φ^j(μ(ε)) = μ(ε ^ p ^ j)`.
* `TauCeti.Perfectoid.iterate_frobeniusEquiv_xiTilde`: `φ^j(xiTilde(ε)) = xiTilde(ε ^ p ^ j)`.
* `TauCeti.Perfectoid.coeff_zero_mu`: the zeroth Witt coordinate of `μ` is `ε - 1`.
* `TauCeti.Perfectoid.mu_ne_zero`: for `ε ≠ 1`, `μ ≠ 0`.
* `TauCeti.Perfectoid.map_xi`: base change of `ξ` between perfect rings.
* `PreTilt.fontaineTheta_iterate_frobeniusEquiv_mu_eq_zero`,
  `PreTilt.fontaineTheta_iterate_frobeniusEquiv_succ_xi`: values of `θ ∘ φ^j` on `μ` and `ξ`.
* `PreTilt.ker_fontaineTheta_eq_span_xi`: `ξ` generates Fontaine's kernel on the valuation ring
  of a complete perfectoid field.

## References

* Bhatt, Morrow and Scholze, *Integral p-adic Hodge theory*, arXiv:1602.03148v3,
  Example 3.16 and Proposition 3.17.
-/

public section

namespace TauCeti.Perfectoid

open _root_.WittVector

section Periods

variable (p : ℕ) [Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]

/-- The cyclotomic period `μ = [ε] - 1`. -/
noncomputable def mu (ε : S) : WittVector p S := teichmuller p ε - 1

/-- The polynomial cyclotomic period `ξ`, defined without division in the Witt ring. -/
noncomputable def xi (ε : S) : WittVector p S :=
  ∑ j ∈ Finset.range p, teichmuller p ((_root_.frobeniusEquiv S p).symm ε) ^ j

/-- The Frobenius translate of `ξ`. -/
noncomputable def xiTilde (ε : S) : WittVector p S := (frobeniusEquiv p S) (xi p ε)

omit [CharP S p] [PerfectRing S p] in
/-- The defining equation of `μ`. -/
theorem mu_eq (ε : S) : mu p ε = teichmuller p ε - 1 := (rfl)

/-- The polynomial formula for `ξ`. -/
theorem xi_eq (ε : S) : xi p ε =
    ∑ j ∈ Finset.range p, teichmuller p ((_root_.frobeniusEquiv S p).symm ε) ^ j := (rfl)

/-- The defining equation of `xiTilde`. -/
theorem xiTilde_eq (ε : S) : xiTilde p ε = (frobeniusEquiv p S) (xi p ε) := (rfl)

/-- Frobenius carries the polynomial expression for `ξ` to the geometric sum in `[ε]`. -/
theorem xiTilde_eq_sum (ε : S) : xiTilde p ε =
    ∑ j ∈ Finset.range p, teichmuller p ε ^ j := by
  simp only [xiTilde, xi, map_sum, map_pow, WittVector.frobeniusEquiv_apply,
    frobenius_eq_map_frobenius, map_teichmuller]
  simp only [← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

/-- The geometric-sum factorization of `μ`, expressed entirely inside the Witt ring. -/
theorem mu_eq_xi_mul_frobeniusEquiv_symm (ε : S) :
    mu p ε = xi p ε * (frobeniusEquiv p S).symm (mu p ε) := by
  rw [mu_eq, xi_eq, map_sub, frobeniusEquiv_symm_teichmuller, map_one, geom_sum_mul]
  congr 1
  rw [← map_pow]
  congr 1
  exact (frobenius_apply_frobeniusEquiv_symm S p ε).symm

/-- Applying Frobenius gives the second cyclotomic factorization. -/
theorem frobeniusEquiv_mu_eq_xiTilde_mul (ε : S) :
    (frobeniusEquiv p S) (mu p ε) = xiTilde p ε * mu p ε := by
  conv_lhs => rw [mu_eq_xi_mul_frobeniusEquiv_symm]
  rw [map_mul, RingEquiv.apply_symm_apply, xiTilde_eq]

omit [CharP S p] [PerfectRing S p] in
/-- The trivial root system gives zero `μ`. -/
@[simp]
theorem mu_one : mu p (1 : S) = 0 := by simp [mu_eq]

/-- Iterated Frobenius on `μ` replaces `ε` by `ε ^ p ^ j`. -/
theorem iterate_frobeniusEquiv_mu (ε : S) (j : ℕ) :
    ((frobeniusEquiv p S)^[j]) (mu p ε) = mu p (ε ^ p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [mu_eq, map_sub, map_one, WittVector.frobeniusEquiv_apply, frobenius_teichmuller,
      ← map_pow, ← pow_mul, ← pow_succ]

/-- Iterated Frobenius on `xiTilde` replaces `ε` by `ε ^ p ^ j`. -/
theorem iterate_frobeniusEquiv_xiTilde (ε : S) (j : ℕ) :
    ((frobeniusEquiv p S)^[j]) (xiTilde p ε) = xiTilde p (ε ^ p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h (δ : S) : frobeniusEquiv p S (xiTilde p δ) = xiTilde p (δ ^ p) := by
      simp only [xiTilde_eq_sum, map_sum, map_pow, WittVector.frobeniusEquiv_apply,
        frobenius_teichmuller]
    rw [Function.iterate_succ_apply', ih, h, ← pow_mul, ← pow_succ]

omit [CharP S p] [PerfectRing S p] in
/-- The zeroth Witt coordinate of `μ = [ε] - 1` is `ε - 1`. -/
@[simp]
theorem coeff_zero_mu (ε : S) : (mu p ε).coeff 0 = ε - 1 := by
  simp [mu_eq, sub_coeff_zero]

omit [CharP S p] [PerfectRing S p] in
/-- For `ε ≠ 1`, the zeroth Witt coordinate of `μ` is nonzero. -/
theorem coeff_zero_mu_ne_zero {ε : S} (hε : ε ≠ 1) : (mu p ε).coeff 0 ≠ 0 := by
  rwa [coeff_zero_mu, sub_ne_zero]

omit [CharP S p] [PerfectRing S p] in
/-- For `ε ≠ 1`, `μ` is nonzero. -/
theorem mu_ne_zero {ε : S} (hε : ε ≠ 1) : mu p ε ≠ 0 :=
  fun h ↦ coeff_zero_mu_ne_zero p hε (by rw [h, zero_coeff])

end Periods

section Naturality

variable (p : ℕ) [Fact p.Prime] {S T : Type*} [CommRing S] [CharP S p] [PerfectRing S p]
  [CommRing T] [CharP T p] [PerfectRing T p]

/-- Base change of `ξ` between perfect rings replaces `ε` by its image. -/
@[simp]
theorem map_xi (f : S →+* T) (ε : S) : WittVector.map f (xi p ε) = xi p (f ε) := by
  simp [xi_eq, map_sum, map_teichmuller, RingHom.map_frobeniusEquiv_symm]

end Naturality

end TauCeti.Perfectoid

namespace PreTilt

open TauCeti.Perfectoid _root_.WittVector

section FontaineValues

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [Fact ¬IsUnit (p : A)]
  [IsAdicComplete (Ideal.span {(p : A)}) A]

/-- Fontaine's value on `μ`. -/
@[simp]
theorem fontaineTheta_mu (ε : PreTilt A p) :
    fontaineTheta A p (mu p ε) = ε.untilt - 1 := by
  rw [mu_eq, map_sub, fontaineTheta_teichmuller, map_one]

/-- The shifted Fontaine value on `μ`. -/
@[simp]
theorem fontaineThetaShifted_mu (ε : PreTilt A p) :
    fontaineThetaShifted A p (mu p ε) =
      PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε) - 1 := by
  rw [mu_eq, map_sub, fontaineThetaShifted_teichmuller, map_one]

/-- Fontaine's value on the polynomial period. -/
@[simp]
theorem fontaineTheta_xi (ε : PreTilt A p) :
    fontaineTheta A p (xi p ε) =
      ∑ j ∈ Finset.range p,
        PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε) ^ j := by
  simp only [xi_eq, map_sum, map_pow, fontaineTheta_teichmuller]

/-- A primitive root makes the polynomial period lie in Fontaine's kernel. -/
@[simp high]
theorem fontaineTheta_xi_eq_zero [IsDomain A] (ε : PreTilt A p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    fontaineTheta A p (xi p ε) = 0 := by
  rw [fontaineTheta_xi]
  exact hε.geom_sum_eq_zero (Fact.out : p.Prime).one_lt

/-- If the sharp of `ε ^ (1 / p)` is a primitive `p`-th root of unity, then `ε♯ = 1`. -/
theorem untilt_eq_one_of_isPrimitiveRoot (ε : PreTilt A p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    ε.untilt = 1 := by
  rw [← untilt_iterate_frobeniusEquiv_symm_pow ε 1, pow_one, Function.iterate_one,
    hε.pow_eq_one]

/-- If the sharp of `ε ^ (1 / p)` is a primitive `p`-th root of unity, then `ε ≠ 1`. -/
theorem ne_one_of_isPrimitiveRoot (ε : PreTilt A p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    ε ≠ 1 := by
  rintro rfl
  exact hε.ne_one (Fact.out : p.Prime).one_lt (by rw [map_one, map_one])

/-- A root system with sharp one gives `θ(μ) = 0`. -/
@[simp high]
theorem fontaineTheta_mu_eq_zero (ε : PreTilt A p) (hε : ε.untilt = 1) :
    fontaineTheta A p (mu p ε) = 0 := by rw [fontaineTheta_mu, hε, sub_self]

/-- Fontaine's map sends `xiTilde` to `p` when the root system has sharp one. -/
@[simp]
theorem fontaineTheta_xiTilde (ε : PreTilt A p) (hε : ε.untilt = 1) :
    fontaineTheta A p (xiTilde p ε) = p := by
  simp [xiTilde_eq_sum, map_sum, map_pow, fontaineTheta_teichmuller, hε]

/-- The shifted map on `xiTilde` agrees with Fontaine's map on `ξ`. -/
@[simp]
theorem fontaineThetaShifted_xiTilde (ε : PreTilt A p) :
    fontaineThetaShifted A p (xiTilde p ε) = fontaineTheta A p (xi p ε) := by
  rw [fontaineThetaShifted_apply, xiTilde_eq, RingEquiv.symm_apply_apply]

/-- Primitivity makes `xiTilde` lie in the shifted Fontaine kernel. -/
@[simp high]
theorem fontaineThetaShifted_xiTilde_eq_zero [IsDomain A] (ε : PreTilt A p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    fontaineThetaShifted A p (xiTilde p ε) = 0 := by
  rw [fontaineThetaShifted_xiTilde, fontaineTheta_xi_eq_zero ε hε]

/-- If `ε♯ = 1`, then Fontaine's map kills every Frobenius iterate of `μ`. -/
theorem fontaineTheta_iterate_frobeniusEquiv_mu_eq_zero (ε : PreTilt A p) (hε : ε.untilt = 1)
    (j : ℕ) : fontaineTheta A p (((frobeniusEquiv p (PreTilt A p))^[j]) (mu p ε)) = 0 := by
  rw [iterate_frobeniusEquiv_mu]
  exact fontaineTheta_mu_eq_zero _ (by rw [map_pow, hε, one_pow])

/-- If `ε♯ = 1`, then Fontaine's map sends `φ^(j + 1)(ξ)` to `p`. -/
theorem fontaineTheta_iterate_frobeniusEquiv_succ_xi (ε : PreTilt A p) (hε : ε.untilt = 1)
    (j : ℕ) :
    fontaineTheta A p (((frobeniusEquiv p (PreTilt A p))^[j + 1]) (xi p ε)) = p := by
  rw [Function.iterate_succ_apply, ← xiTilde_eq, iterate_frobeniusEquiv_xiTilde]
  exact fontaineTheta_xiTilde _ (by rw [map_pow, hε, one_pow])

end FontaineValues


section Distinguished

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [Fact ¬IsUnit (p : A)]
  [IsAdicComplete (Ideal.span {(p : A)}) A]

/-- The cyclotomic sum is distinguished whenever the sharp of its root has `p`-th power one. -/
theorem isDistinguished_xi (ε : PreTilt A p)
    (hε : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε) ^ p = 1) :
    (xi p ε).IsDistinguished := by
  -- The reduction of that root differs from one by a nilpotent, so the first Witt coordinate of
  -- the sum reduces to the first coordinate of `p`, namely one.
  let a := (_root_.frobeniusEquiv (PreTilt A p) p).symm ε
  have ha : (PreTilt.coeff 0 a) ^ p = 1 := by
    simpa only [map_pow, PreTilt.mk_untilt_eq_coeff_zero, map_one] using
      congrArg (Ideal.Quotient.mk (Ideal.span {(p : A)})) hε
  have hd := WittVector.isDistinguished_sum_teichmuller_pow_of_pow_eq_one (PreTilt.coeff 0 a) ha
  have hm : WittVector.map (PreTilt.coeff 0) (xi p ε) =
      ∑ j ∈ Finset.range p, teichmuller p (PreTilt.coeff 0 a) ^ j := by
    simp only [xi_eq, map_sum, map_pow, map_teichmuller, a]
  rw [WittVector.isDistinguished_iff]
  apply isUnit_of_map_unit (PreTilt.coeff (O := A) (p := p) 0)
  have hc := hd
  rw [← hm, WittVector.isDistinguished_iff, WittVector.map_coeff] at hc
  exact hc

end Distinguished

end PreTilt

namespace TauCeti.Perfectoid

open _root_.WittVector

section Kernels

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R]
  [IsUniformAddGroup R] [IsTopologicalRing R] [Huber.IsTateRing R] [CompleteSpace R] [T2Space R]
  [IsPerfectoidTateRing p R] {Rplus : Subring R} [IsDomain Rplus]
  [Fact ¬IsUnit (p : Rplus)] [IsAdicComplete (Ideal.span {(p : Rplus)}) Rplus]

/-- The cyclotomic polynomial period generates Fontaine's kernel on a ring of integral
elements whenever the sharp of `ε^(1/p)` is a primitive `p`-th root. -/
theorem ker_fontaineTheta_eq_span_xi_of_isRingOfIntegralElements
    (hplus : Huber.IsRingOfIntegralElements Rplus) (ε : PreTilt Rplus p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt Rplus p) p).symm ε)) p) :
    RingHom.ker (fontaineTheta Rplus p) = Ideal.span {xi p ε} := by
  apply (hplus.ker_fontaineTheta_eq_span_iff_isDistinguished
    (RingHom.mem_ker.mpr (ε.fontaineTheta_xi_eq_zero hε))).mpr
  exact ε.isDistinguished_xi hε.pow_eq_one

end Kernels

end TauCeti.Perfectoid

namespace PreTilt

open TauCeti TauCeti.Perfectoid _root_.WittVector
open scoped _root_.NormedField Valued

section PerfectoidField

variable {p : ℕ} [Fact p.Prime] {C : Type*} [NontriviallyNormedField C]
  [IsUltrametricDist C] [CompleteSpace C] [IsPerfectoidTateRing p C]
  [Fact ¬IsUnit (p : 𝒪[C])] [IsAdicComplete (Ideal.span {(p : 𝒪[C])}) (𝒪[C])]

/-- For a complete perfectoid nonarchimedean field of residue characteristic `p`, the cyclotomic
polynomial `ξ` generates the Fontaine kernel on its valuation ring. Primitivity excludes the
trivial root system. -/
theorem ker_fontaineTheta_eq_span_xi (ε : PreTilt (𝒪[C]) p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε)) p) :
    RingHom.ker (fontaineTheta (𝒪[C]) p) = Ideal.span {xi p ε} :=
  ker_fontaineTheta_eq_span_xi_of_isRingOfIntegralElements
    (Huber.isRingOfIntegralElements_integer C) ε hε

/-- On the valuation ring of a complete perfectoid nonarchimedean field,
`xiTilde` generates the shifted Fontaine kernel. -/
theorem ker_fontaineThetaShifted_eq_span_xiTilde (ε : PreTilt (𝒪[C]) p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε)) p) :
    RingHom.ker (fontaineThetaShifted (𝒪[C]) p) = Ideal.span {xiTilde p ε} := by
  rw [xiTilde_eq]
  exact WittVector.ker_fontaineThetaShifted_eq_span (ker_fontaineTheta_eq_span_xi ε hε)

end PerfectoidField

end PreTilt
