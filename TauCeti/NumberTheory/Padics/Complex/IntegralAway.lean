/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.NumberTheory.Padics.Cardinality
import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Elements integral away from a natural number

Let `R` be a commutative ring and `q` a natural number. An element `z ∈ R` is *integral away
from `q`* if `‖ι z‖ ≤ 1` for every prime `ℓ` not dividing `q` and every ring homomorphism
`ι : R →+* ℂ_[ℓ]`; that is, `z` lies in the preimage `ι⁻¹(𝓞_ℂ_[ℓ])` of the integers of `ℂ_[ℓ]`
for all such `ℓ` and `ι`. These elements form the subring `TauCeti.integralAway R q`. For `R = ℂ`
it controls the denominators of complex numbers, such as values of theta functions, at all primes
not dividing `q` and through all `ℓ`-adic embeddings `ℂ →+* ℂ_[ℓ]` at once.

Being a subring, `integralAway R q` contains the integers and is closed under the ring
operations. It contains every element integral over `ℤ`, in particular every root of unity
(through `IsOfFinOrder.isIntegral`), it is carried into `integralAway S q` by every ring
homomorphism `R →+* S`, for instance by every automorphism of `ℂ`, and it grows with `q` for
divisibility; every element is integral away from `0`. A prime `ℓ` for which `R` has no ring
homomorphism to `ℂ_[ℓ]` imposes no condition, so for instance in positive characteristic every
element is integral away from every `q`.

The definition is not vacuous for `R = ℂ`: since `ℂ` embeds into `ℂ_[ℓ]`, the inverse of a
nonzero natural number `n` is integral away from `q` exactly when every prime factor of `n`
divides `q`. In particular, for a prime `ℓ`, `1 / ℓ` is integral away from `q` iff `ℓ ∣ q`.

## Main definitions

* `TauCeti.integralAway R q`: the subring of elements of `R` integral away from `q`.

## Main results

* `TauCeti.mem_integralAway`: `z` is integral away from `q` iff `‖ι z‖ ≤ 1` for every prime
  `ℓ ∤ q` and every `ι : R →+* ℂ_[ℓ]`.
* `TauCeti.integralAway_le_comap`: for a prime `ℓ ∤ q` and `ι : R →+* ℂ_[ℓ]`, `integralAway R q`
  lies in the preimage of `𝓞_ℂ_[ℓ]` under `ι`.
* `TauCeti.integralAway_mono`, `TauCeti.integralAway_zero`: monotonicity in `q` for divisibility,
  and `integralAway R 0 = ⊤`.
* `TauCeti.mem_integralAway_of_isIntegral`: elements integral over `ℤ` are integral away from
  every `q`.
* `TauCeti.apply_mem_integralAway`: ring homomorphisms preserve integrality away from `q`.
* `TauCeti.inv_natCast_mem_integralAway`, `TauCeti.inv_natCast_mem_integralAway_iff`: `1 / n` is
  integral away from `q` when every prime factor of `n` divides `q`, and in `ℂ` only then.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/New/UpperBound/Seesaw/AdmissibleCombinations.lean` (declaration `New.Seesaw.integralAway`);
  Apache 2.0, Copyright 2026 Anthropic, PBC. The notion of integrality away from `q` is the one
  used there for complex numbers.
-/

public section

namespace TauCeti

variable (R : Type*) [CommRing R]

/-- The subring of elements `z` of `R` that are *integral away from `q`*: `‖ι z‖ ≤ 1` for every
prime `ℓ` not dividing `q` and every ring homomorphism `ι : R →+* ℂ_[ℓ]`, i.e. `z` lies in the
preimage under `ι` of the integers `𝓞_ℂ_[ℓ]` of `ℂ_[ℓ]`. -/
noncomputable def integralAway (q : ℕ) : Subring R :=
  ⨅ (ℓ : ℕ) (_ : Fact ℓ.Prime) (_ : ¬ℓ ∣ q) (ι : R →+* ℂ_[ℓ]), (𝓞_ℂ_[ℓ]).toSubring.comap ι

variable {R} {S : Type*} [CommRing S] {q : ℕ} {z : R}

/-- An element is integral away from `q` iff all its images in the `ℂ_[ℓ]`, for the primes
`ℓ ∤ q`, have norm at most `1`. -/
theorem mem_integralAway :
    z ∈ integralAway R q ↔ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ q → ∀ ι : R →+* ℂ_[ℓ], ‖ι z‖ ≤ 1 := by
  simp [integralAway, Subring.mem_iInf]

/-- For a prime `ℓ ∤ q` and a ring homomorphism `ι : R →+* ℂ_[ℓ]`, the elements integral away
from `q` lie in the ring `ι⁻¹(𝓞_ℂ_[ℓ])` of the `z` with `‖ι z‖ ≤ 1`. -/
theorem integralAway_le_comap {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ¬ℓ ∣ q) (ι : R →+* ℂ_[ℓ]) :
    integralAway R q ≤ (𝓞_ℂ_[ℓ]).toSubring.comap ι := fun _ hz ↦
  PadicComplexInt.mem_iff_norm_le_one.2 (mem_integralAway.1 hz ℓ hℓ ι)

/-- Integrality away from `q` is weaker than integrality away from a divisor of `q`. -/
theorem integralAway_mono {q q' : ℕ} (h : q ∣ q') : integralAway R q ≤ integralAway R q' :=
  fun _ hz ↦ mem_integralAway.2 fun ℓ _ hℓ ι ↦
    mem_integralAway.1 hz ℓ (fun hq ↦ hℓ (hq.trans h)) ι

/-- Every element is integral away from `0`, since every prime divides `0`. -/
@[simp]
theorem integralAway_zero : integralAway R 0 = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ mem_integralAway.2 fun _ _ hℓ ↦ (hℓ (dvd_zero _)).elim

/-- An element integral over `ℤ`, such as an algebraic integer or a root of unity
(`IsOfFinOrder.isIntegral`), is integral away from every `q`. -/
theorem mem_integralAway_of_isIntegral (hz : IsIntegral ℤ z) : z ∈ integralAway R q := by
  refine mem_integralAway.2 fun _ _ _ ι ↦
    IsUltrametricDist.norm_le_one_of_isIntegral (fun _ _ _ ↦ norm_pow _ _) ?_
  -- Instance search finds the `ℤ`-algebra structure of `ℂ_[ℓ]` as a completion, while the norm
  -- bound uses the one of a general ring; they are equal but not by unification, so instead of
  -- `IsIntegral.map` we map the monic polynomial by hand.
  obtain ⟨p, hp, hpz⟩ := hz
  refine ⟨p, hp, ?_⟩
  have h := congrArg ι hpz
  rw [Polynomial.hom_eval₂, map_zero] at h
  convert h using 2
  exact RingHom.ext_int _ _

/-- A ring homomorphism, for instance an automorphism of `ℂ`, carries elements integral away from
`q` to elements integral away from `q`. -/
theorem apply_mem_integralAway (f : R →+* S) (hz : z ∈ integralAway R q) :
    f z ∈ integralAway S q :=
  mem_integralAway.2 fun ℓ _ hℓ ι ↦ mem_integralAway.1 hz ℓ hℓ (ι.comp f)

/-- The inverse of a natural number all of whose prime factors divide `q` is integral away from
`q`. -/
theorem inv_natCast_mem_integralAway {K : Type*} [Field K] {n : ℕ}
    (h : ∀ ℓ, ℓ.Prime → ℓ ∣ n → ℓ ∣ q) : (n : K)⁻¹ ∈ integralAway K q := by
  refine mem_integralAway.2 fun ℓ hℓ hℓq ι ↦ ?_
  have hn : ‖(n : ℚ_[ℓ])‖ = 1 := Padic.norm_natCast_eq_one_iff.2 <|
    (Nat.Prime.coprime_iff_not_dvd hℓ.out).2 fun hℓn ↦ hℓq (h ℓ hℓ.out hℓn)
  rw [map_inv₀, map_natCast, norm_inv, norm_natCast_eq_norm_padic (p := ℓ), hn, inv_one]

/-- The inverse of a nonzero natural number `n` is integral away from `q` exactly when every
prime factor of `n` divides `q`. The forward direction uses that `ℂ` embeds into every `ℂ_[ℓ]`;
for instance `1 / ℓ` is not integral away from `q` when `ℓ` is a prime not dividing `q`. -/
theorem inv_natCast_mem_integralAway_iff {n : ℕ} (hn : n ≠ 0) :
    (n : ℂ)⁻¹ ∈ integralAway ℂ q ↔ ∀ ℓ, ℓ.Prime → ℓ ∣ n → ℓ ∣ q := by
  refine ⟨fun h ℓ hℓ hℓn ↦ ?_, inv_natCast_mem_integralAway⟩
  by_contra hℓq
  have : Fact ℓ.Prime := ⟨hℓ⟩
  -- `ℂ` is isomorphic to an algebraic closure of `ℚ_[ℓ]`, which lies in `ℂ_[ℓ]`.
  obtain ⟨e⟩ := TauCeti.Padic.nonempty_ringEquiv_complex ℓ (PadicAlgCl ℓ)
  have hle := mem_integralAway.1 h ℓ hℓq ((algebraMap (PadicAlgCl ℓ) ℂ_[ℓ]).comp e.symm)
  rw [map_inv₀, map_natCast, norm_inv, norm_natCast_eq_norm_padic (p := ℓ)] at hle
  have hlt : ‖(n : ℚ_[ℓ])‖ < 1 := Padic.norm_natCast_lt_one_iff.2 hℓn
  have hpos : 0 < ‖(n : ℚ_[ℓ])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hn)
  exact hle.not_gt ((one_lt_inv₀ hpos).2 hlt)

-- Sanity checks: for a prime `ℓ`, `1 / ℓ` is integral away from `q` exactly when `ℓ ∣ q`.
example {ℓ : ℕ} (hℓ : ℓ.Prime) (hq : ¬ℓ ∣ q) : (ℓ : ℂ)⁻¹ ∉ integralAway ℂ q :=
  fun h ↦ hq ((inv_natCast_mem_integralAway_iff hℓ.ne_zero).1 h ℓ hℓ dvd_rfl)

example {ℓ : ℕ} (hℓ : ℓ.Prime) (hq : ℓ ∣ q) : (ℓ : ℂ)⁻¹ ∈ integralAway ℂ q :=
  inv_natCast_mem_integralAway fun _ hp hpℓ ↦ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 hpℓ) ▸ hq

end TauCeti
