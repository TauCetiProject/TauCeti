/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PrincipalIdealDomain
public import TauCeti.RingTheory.Iwasawa.Char.Divisor

import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.OrderOfVanishing.Basic
import TauCeti.NumberTheory.Padics.PowerSeriesIdeal
import TauCeti.RingTheory.FittingIdeal.Basic
import TauCeti.RingTheory.RegularLocalRing.PowerSeries
import TauCeti.RingTheory.RegularLocalRing.UniqueFactorization

/-!
# The characteristic ideal of a torsion module

Let `M` be a finitely generated torsion module over a noetherian ring `A`. Its *characteristic
ideal* is the finite product

  `char_A(M) = ∏_𝔭 𝔭 ^ length_{A_𝔭}(M_𝔭)`

over the primes `𝔭` of height one, with the exponents read off the characteristic divisor
`div_A(M)`. Over a noetherian unique factorization domain, such as the Iwasawa algebra
`Λ = O⟦T⟧`, every height-one prime is principal, so `char_A(M)` is a principal ideal, and the
characteristic ideal of a cyclic module `A ⧸ (f)` is `(f)`. It is the invariant of torsion
Iwasawa modules that the main conjectures compare with `p`-adic `L`-functions.

Because it is read off `div_A(M)`, the characteristic ideal sees only the localizations of `M` at
height-one primes: it is multiplicative in short exact sequences, invariant under
pseudo-isomorphism, and equal to `A` exactly for pseudo-null modules. It is in general different
from the initial Fitting ideal: for `Λ = ℤ_p⟦T⟧` the finite module `Λ ⧸ (p, T)` has characteristic
ideal `Λ` and Fitting ideal `(p, T)`.

## Main definitions

* `TauCeti.Iwasawa.charIdeal A M`: the characteristic ideal of `M`, the product of the
  height-one primes raised to their multiplicities in `div_A(M)`.

## Main results

* `TauCeti.Iwasawa.charIdeal_eq_mul_of_exact`: `char_A` is multiplicative in short exact
  sequences.
* `TauCeti.Iwasawa.IsPseudoIsomorphism.charIdeal_eq`: `char_A` is invariant under
  pseudo-isomorphism, and in particular under linear equivalence (`LinearEquiv.charIdeal_eq`).
* `TauCeti.Iwasawa.charIdeal_eq_top_iff`: `char_A(M) = A` iff `M` is pseudo-null.
* `TauCeti.Iwasawa.charIdeal_quotient_of_height_eq_one`: `char_A(A ⧸ 𝔭) = 𝔭` for a prime `𝔭` of
  height one.
* `TauCeti.Iwasawa.charIdeal_isPrincipal`: over a unique factorization domain the characteristic
  ideal is principal.
* `TauCeti.Iwasawa.charIdeal_quotient_span_singleton`: over a noetherian unique factorization
  domain, `char_A(A ⧸ (f)) = (f)` for `f ≠ 0`.

The examples at the end of the file are over `Λ = ℤ_p⟦T⟧`, which is factorial: the characteristic
ideal of `Λ ⧸ (T² - p)` is `(T² - p)`, and the finite module `Λ ⧸ (p, T)` has characteristic ideal
`Λ` but initial Fitting ideal `(p, T)`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Definition 13.3
  and Lemma 13.6.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (5.1.8) and (5.3.9).
-/

public section

namespace TauCeti.Iwasawa

variable (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]

/-- The *characteristic ideal* `char_A(M) = ∏_𝔭 𝔭 ^ length_{A_𝔭}(M_𝔭)` of a module `M` over a
commutative ring `A`, the product running over the primes `𝔭` of height one, with exponents the
multiplicities of the characteristic divisor `div_A(M)`. It is meant for finitely generated
torsion modules over a noetherian ring, where the product is finite, and it is principal over a
unique factorization domain (`charIdeal_isPrincipal`). -/
noncomputable def charIdeal : Ideal A :=
  (charDivisor A M).prod fun 𝔭 n ↦ 𝔭.asIdeal ^ n

variable {A M}

/-- The characteristic ideal is the product of the primes in the support of the characteristic
divisor, raised to their multiplicities. -/
theorem charIdeal_def : charIdeal A M = (charDivisor A M).prod fun 𝔭 n ↦ 𝔭.asIdeal ^ n := (rfl)

/-- The characteristic ideal is the unit ideal exactly when the characteristic divisor vanishes:
each prime in the support of the divisor contributes a proper factor. -/
theorem charIdeal_eq_top_iff_charDivisor_eq_zero : charIdeal A M = ⊤ ↔ charDivisor A M = 0 := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [charIdeal_def, h]⟩
  by_contra hne
  obtain ⟨𝔭, h𝔭⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hle : charIdeal A M ≤ 𝔭.asIdeal := by
    rw [charIdeal_def, Finsupp.prod, ← Finset.prod_erase_mul _ _ h𝔭]
    exact Ideal.mul_le_right.trans (Ideal.pow_le_self (Finsupp.mem_support_iff.mp h𝔭))
  exact 𝔭.isPrime.ne_top (top_le_iff.mp (h ▸ hle))

/-- The characteristic ideal of a pseudo-null module is the unit ideal. -/
@[simp]
theorem IsPseudoNull.charIdeal_eq_top (h : IsPseudoNull A M) : charIdeal A M = ⊤ :=
  charIdeal_eq_top_iff_charDivisor_eq_zero.mpr h.charDivisor_eq_zero

/-- The characteristic ideal of the zero module is the unit ideal. -/
@[simp]
theorem charIdeal_of_subsingleton [Subsingleton M] : charIdeal A M = ⊤ :=
  IsPseudoNull.of_subsingleton.charIdeal_eq_top

/-- A finitely generated torsion module over a noetherian ring has characteristic ideal `A` iff it
is pseudo-null. -/
theorem charIdeal_eq_top_iff [IsNoetherianRing A] [Module.Finite A M] (hM : Module.IsTorsion A M) :
    charIdeal A M = ⊤ ↔ IsPseudoNull A M := by
  rw [charIdeal_eq_top_iff_charDivisor_eq_zero, charDivisor_eq_zero_iff hM]

variable {N P : Type*} [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]

/-- The characteristic ideal is invariant under pseudo-isomorphism. -/
theorem IsPseudoIsomorphism.charIdeal_eq {f : M →ₗ[A] N} (hf : IsPseudoIsomorphism f) :
    charIdeal A M = charIdeal A N := by
  rw [charIdeal_def, charIdeal_def, hf.charDivisor_eq]

/-- **Multiplicativity of the characteristic ideal.** In a short exact sequence
`0 → M → N → P → 0` of finitely generated torsion modules over a noetherian ring,
`char_A(N) = char_A(M) * char_A(P)`. -/
theorem charIdeal_eq_mul_of_exact [IsNoetherianRing A] [Module.Finite A N]
    (hN : Module.IsTorsion A N) {f : M →ₗ[A] N} {g : N →ₗ[A] P} (hfg : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    charIdeal A N = charIdeal A M * charIdeal A P := by
  rw [charIdeal_def, charIdeal_def, charIdeal_def, charDivisor_eq_add_of_exact hN hfg hf hg,
    Finsupp.prod_add_index' (by simp) fun _ _ _ ↦ pow_add _ _ _]

end TauCeti.Iwasawa

/-- The characteristic ideal is invariant under linear equivalence. -/
theorem LinearEquiv.charIdeal_eq {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) :
    TauCeti.Iwasawa.charIdeal A M = TauCeti.Iwasawa.charIdeal A N :=
  (TauCeti.Iwasawa.IsPseudoIsomorphism.of_bijective e.bijective).charIdeal_eq

namespace TauCeti.Iwasawa

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- Over a unique factorization domain every prime of height one is principal, so the
characteristic ideal is principal. -/
instance charIdeal_isPrincipal [IsDomain A] [UniqueFactorizationMonoid A] :
    (charIdeal A M).IsPrincipal := by
  rw [charIdeal_def, Finsupp.prod, ← Ideal.mem_isPrincipalSubmonoid_iff]
  refine prod_mem fun 𝔭 h𝔭 ↦ pow_mem ?_ _
  have h : 𝔭.asIdeal.height = 1 := by
    by_contra hne
    exact Finsupp.mem_support_iff.mp h𝔭 (charDivisor_apply_of_height_ne_one hne)
  exact UniqueFactorizationMonoid.isPrincipal_of_height_eq_one h

/-- For a prime `𝔭` of height one in a commutative ring, the characteristic ideal of `A ⧸ 𝔭` is
`𝔭`. -/
@[simp]
theorem charIdeal_quotient_of_height_eq_one {𝔭 : Ideal A} [𝔭.IsPrime] (h : 𝔭.height = 1) :
    charIdeal A (A ⧸ 𝔭) = 𝔭 := by
  rw [charIdeal_def, charDivisor_quotient_of_height_eq_one h, Finsupp.prod_single_index (by simp),
    pow_one]

open scoped Pointwise in
/-- **The characteristic ideal of a cyclic torsion module.** Over a noetherian unique
factorization domain, the characteristic ideal of `A ⧸ (f)` is `(f)` for every `f ≠ 0`. -/
@[simp]
theorem charIdeal_quotient_span_singleton [IsDomain A] [IsNoetherianRing A]
    [UniqueFactorizationMonoid A] {f : A} (hf : f ≠ 0) :
    charIdeal A (A ⧸ Ideal.span {f}) = Ideal.span {f} := by
  induction f using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hf
  | h₂ u hu =>
    rw [Ideal.span_singleton_eq_top.mpr hu]
    exact charIdeal_of_subsingleton
  | h₃ a p ha hp ih =>
    -- Multiplication by `p` gives the exact sequence `0 → A ⧸ (a) → A ⧸ (p a) → A ⧸ (p) → 0`,
    -- and `(p)` is a prime of height one.
    have hpa : p • Ideal.span {a} = Ideal.span {p * a} := by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul,
        Ideal.span_singleton_mul_span_singleton]
    have hp₀ : p ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero hp.ne_zero
    have hN : Module.IsTorsion A (A ⧸ p • Ideal.span {a}) := fun x ↦
      ⟨⟨p * a, mem_nonZeroDivisors_of_ne_zero hf⟩,
        (Module.isTorsionBy_quotient_iff _ _).mpr
          (fun y ↦ hpa ▸ Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self _)) (x := x)⟩
    have := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    rw [← (Submodule.quotEquivOfEq _ _ hpa).charIdeal_eq,
      charIdeal_eq_mul_of_exact hN (Ideal.exact_mulQuot_quotOfMul _)
        (Ideal.mulQuot_injective _ hp₀) (Ideal.quotOfMul_surjective _),
      ih ha, charIdeal_quotient_of_height_eq_one
        (Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors hp₀ hp.not_isUnit),
      Ideal.span_singleton_mul_span_singleton, mul_comm]

open _root_.PowerSeries in
-- Over the factorial ring `Λ = ℤ_p⟦T⟧`, the characteristic ideal of `Λ ⧸ (T² - p)` is `(T² - p)`.
example (p : ℕ) [Fact p.Prime] :
    charIdeal ℤ_[p]⟦X⟧ (ℤ_[p]⟦X⟧ ⧸ Ideal.span {X ^ 2 - C (p : ℤ_[p])}) =
      Ideal.span {X ^ 2 - C (p : ℤ_[p])} := by
  have := TauCeti.IsRegularLocalRing.uniqueFactorizationMonoid (R := ℤ_[p]⟦X⟧)
    TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing.le
  refine charIdeal_quotient_span_singleton fun h ↦ ?_
  simpa [-map_natCast, coeff_C] using congrArg (coeff 2) h

open _root_.PowerSeries in
-- The finite module `Λ ⧸ (p, T) = 𝔽_p` is pseudo-null, so its characteristic ideal is `Λ`, while
-- its initial Fitting ideal is `(p, T)`: the two invariants differ.
example (p : ℕ) [Fact p.Prime] :
    charIdeal ℤ_[p]⟦X⟧ (ℤ_[p]⟦X⟧ ⧸ Ideal.span {C (p : ℤ_[p]), X}) = ⊤ ∧
      fittingIdeal ℤ_[p]⟦X⟧ (ℤ_[p]⟦X⟧ ⧸ Ideal.span {C (p : ℤ_[p]), X}) 0 =
        Ideal.span {C (p : ℤ_[p]), X} :=
  ⟨IsPseudoNull.charIdeal_eq_top ((isPseudoNull_quotient_iff _).mpr fun 𝔮 h𝔮 ↦
    PadicInt.one_lt_height_of_C_p_mem_of_X_mem (h𝔮 (Ideal.subset_span (by simp)))
      (h𝔮 (Ideal.subset_span (by simp)))), fittingIdeal_quotient_zero _⟩

end TauCeti.Iwasawa

end
