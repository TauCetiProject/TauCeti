/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.MvPowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
-- Proof-only: coefficients of products of series with coefficients in ideals.
import Mathlib.RingTheory.PowerSeries.CoeffMulMem
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.RingTheory.QuotSMulTop

/-!
# The kernel of the coefficientwise map of power series

For a ring homomorphism `f : R →+* S` with finitely generated kernel, the kernel of the induced
map `R⟦X⟧ →+* S⟦X⟧` is the extension of `ker f` along the constant embedding `C`. This is the
one-variable form of `MvPowerSeries.ker_map_of_fg`.

Applied to the quotient map `R → R ⧸ (r)`, whose kernel is principal, this identifies
`R⟦X⟧ ⧸ (r)` with `(R ⧸ (r))⟦X⟧`. Hence a constant series `C r` is a prime element of `R⟦X⟧`
exactly when `r` is a prime element of `R`, as for polynomials (`Polynomial.prime_C_iff`). Over a
local domain with a prime `ϖ`, a series with nonzero reduction modulo the maximal ideal is not
divisible by `C ϖ`, so it acts injectively on `R⟦X⟧ ⧸ (ϖ ^ m)`.

A series whose coefficients lie in an ideal `J` has square zero modulo any ideal containing
`J * J`. For a finitely generated ideal `I`, the same kernel computation describes `I.map C` by
its coefficients and shows that it is prime when `I` is.

## Main results

* `PowerSeries.ker_map_of_fg`: `ker (map f) = (ker f).map C` when `ker f` is finitely generated.
* `PowerSeries.mem_map_C_iff_of_fg`, `PowerSeries.isPrime_map_C_of_fg`: for a finitely generated
  ideal `I`, the series in `I.map C` are those with all coefficients in `I`, and `I.map C` is prime
  when `I` is.
* `PowerSeries.prime_C_iff`: `C r` is prime in `R⟦X⟧` if and only if `r` is prime in `R`.
* `PowerSeries.torsionBy_quotient_span_C_pow_eq_bot`: a series with nonzero reduction modulo the
  maximal ideal has no nonzero torsion on `R⟦X⟧ ⧸ (ϖ ^ m)` for a prime `ϖ` of a local domain.
* `PowerSeries.sq_map_mk_eq_zero_of_coeff_mem`: a series with coefficients in `J` squares to zero
  in `(R ⧸ K)⟦X⟧` when `J * J ≤ K`.
-/

public section

namespace PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]

/-- If `f : R →+* S` has finitely generated kernel, the kernel of the coefficientwise map
`R⟦X⟧ →+* S⟦X⟧` is the extension of `ker f` along the constant embedding. -/
theorem ker_map_of_fg (f : R →+* S) (hf : (RingHom.ker f).FG) :
    RingHom.ker (map f) = (RingHom.ker f).map C := by
  -- `PowerSeries.map` is `MvPowerSeries.map` over `Unit`, and `C` is `MvPowerSeries.C`.
  rw [map, MvPowerSeries.ker_map_of_fg _ hf]
  rfl

/-- For a finitely generated ideal `I`, a power series lies in the extension `I.map C` iff all of
its coefficients lie in `I`. -/
theorem mem_map_C_iff_of_fg {I : Ideal R} (hI : I.FG) {f : R⟦X⟧} :
    f ∈ I.map C ↔ ∀ n, coeff n f ∈ I := by
  rw [← Ideal.mk_ker (I := I), ← ker_map_of_fg _ (by rwa [Ideal.mk_ker]), RingHom.mem_ker,
    PowerSeries.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

/-- The extension `I.map C` of a finitely generated prime ideal `I` of `R` is a prime ideal of
`R⟦X⟧`: it is the kernel of `R⟦X⟧ → (R ⧸ I)⟦X⟧`, whose target is a domain. -/
theorem isPrime_map_C_of_fg {I : Ideal R} [I.IsPrime] (hI : I.FG) :
    (I.map (C : R →+* R⟦X⟧)).IsPrime := by
  rw [← Ideal.mk_ker (I := I), ← ker_map_of_fg _ (by rwa [Ideal.mk_ker])]
  exact RingHom.ker_isPrime _

/-- A constant power series `C r` is a prime element of `R⟦X⟧` if and only if `r` is a prime
element of `R`. -/
theorem prime_C_iff {r : R} : Prime (C r) ↔ Prime r := by
  refine ⟨comap_prime C constantCoeff constantCoeff_C, fun hr ↦ ?_⟩
  have hspan : (Ideal.span {r}).IsPrime := (Ideal.span_singleton_prime hr.ne_zero).2 hr
  have hker : RingHom.ker (map (Ideal.Quotient.mk (Ideal.span {r}))) = Ideal.span {C r} := by
    rw [ker_map_of_fg _ (by rw [Ideal.mk_ker]; exact ⟨{r}, by simp⟩), Ideal.mk_ker,
      Ideal.map_span, Set.image_singleton]
  refine (Ideal.span_singleton_prime ((map_ne_zero_iff C C_injective).2 hr.ne_zero)).1 ?_
  exact hker ▸ RingHom.ker_isPrime _

/-- Over a local domain `R` with a prime `ϖ`, a power series `g` with nonzero reduction modulo the
maximal ideal acts injectively on `R⟦X⟧ ⧸ (ϖ ^ m)`. In Iwasawa theory these are the vertical
blocks of an elementary module. -/
theorem torsionBy_quotient_span_C_pow_eq_bot [IsDomain R] [IsLocalRing R] {ϖ : R} (hϖ : Prime ϖ)
    {g : R⟦X⟧} (hg : g.map (IsLocalRing.residue R) ≠ 0) (m : ℕ) :
    Submodule.torsionBy R⟦X⟧ (R⟦X⟧ ⧸ Ideal.span {C (ϖ ^ m)}) g = ⊥ := by
  rw [← isSMulRegular_iff_torsionBy_eq_bot, map_pow]
  refine (prime_C_iff.2 hϖ).isSMulRegular_quotient_span_pow (fun ⟨k, hk⟩ ↦ hg ?_) m
  -- `ϖ` lies in the maximal ideal, so `C ϖ * k` reduces to zero.
  rw [hk, map_mul, map_C, (IsLocalRing.residue_eq_zero_iff ϖ).2 hϖ.not_isUnit, map_zero, zero_mul]

/-- A series whose coefficients lie in an ideal `J` squares to zero in `(R ⧸ K)⟦X⟧` for any ideal
`K` containing `J * J`. -/
theorem sq_map_mk_eq_zero_of_coeff_mem {J K : Ideal R} (hJK : J * J ≤ K) {f : R⟦X⟧}
    (hf : ∀ n, coeff n f ∈ J) : (f.map (Ideal.Quotient.mk K)) ^ 2 = 0 := by
  ext n
  rw [sq, ← map_mul, coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact hJK (coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' hf hf n)

end PowerSeries
