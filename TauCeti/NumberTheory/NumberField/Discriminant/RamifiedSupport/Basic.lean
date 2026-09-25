/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Discriminant.Ramification

/-!
# The ramified support of an extension of number fields

The primes of `𝓞 K` that ramify in `L` are exactly those dividing the relative discriminant
`relDiscr (𝓞 K) (𝓞 L)`, and there are finitely many of them. This file collects them into a
`Finset` of height-one primes, the **ramified support** of `L / K`.

Finiteness is not an extra hypothesis: the relative discriminant of a separable extension is
nonzero (`TauCeti.relDiscr_ne_bot`), and a nonzero ideal of a Dedekind domain has
finitely many prime divisors (`Ideal.finite_factors`). For number fields the separability is
automatic.

## Main definitions

* `TauCeti.NumberField.ramifiedSupport`: the primes of `𝓞 K` dividing `relDiscr (𝓞 K) (𝓞 L)`.

## Main results

* `TauCeti.NumberField.mem_ramifiedSupport`: membership is divisibility of the relative
  discriminant.
* `TauCeti.NumberField.mem_ramifiedSupport_iff_exists`: equivalently, some prime of `𝓞 L` above
  `v` has ramification index greater than one — so the name is honest.
* `TauCeti.NumberField.ramifiedSupport_self`: nothing ramifies in the identity extension, so the
  support of `K / K` is empty.
* `TauCeti.NumberField.isUnramifiedAway_ramifiedSupport`: primes outside the ramified support are
  unramified throughout the extension.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, §2.
-/

public section

open scoped NumberField nonZeroDivisors

open IsDedekindDomain

namespace TauCeti.NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (K L) in
/-- **The ramified support of `L / K`**: the height-one primes of `𝓞 K` dividing the relative
discriminant `relDiscr (𝓞 K) (𝓞 L)`.

This is a `Finset` because the relative discriminant is nonzero, a nonzero ideal of a Dedekind
domain having only finitely many prime divisors. -/
noncomputable def ramifiedSupport : Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors (TauCeti.relDiscr_ne_bot (A := 𝓞 K) (B := 𝓞 L))).toFinset

/-- A prime lies in the ramified support exactly when it divides the relative discriminant. -/
@[simp]
theorem mem_ramifiedSupport {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ ramifiedSupport K L ↔ v.asIdeal ∣ TauCeti.relDiscr (𝓞 K) (𝓞 L) :=
  Set.Finite.mem_toFinset _

/-- **The ramified support consists of the primes that actually ramify.** A prime lies in it
exactly when some prime of `𝓞 L` above it has ramification index greater than one. -/
theorem mem_ramifiedSupport_iff_exists {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ ramifiedSupport K L ↔
      ∃ P : (v.asIdeal).primesOver (𝓞 L), 1 < (P : Ideal (𝓞 L)).ramificationIdx (𝓞 K) := by
  rw [mem_ramifiedSupport]
  exact dvd_relDiscr_iff_exists_one_lt_ramificationIdx v.ne_bot

variable (K) in
/-- **Nothing ramifies in the identity extension**: the ramified support of `K / K` is empty. -/
@[simp]
theorem ramifiedSupport_self : ramifiedSupport K K = ∅ := by
  -- Mathlib checks by `rfl` that this ring-of-integers algebra instance is `Algebra.id`;
  -- specializing `relDiscr_self` here relies on that definitional equality.
  have hrel :
      @TauCeti.relDiscr (𝓞 K) (𝓞 K) inferInstance inferInstance inferInstance inferInstance
        (NumberField.inst_ringOfIntegersAlgebra K K) inferInstance inferInstance = ⊤ :=
    TauCeti.relDiscr_self
  refine Finset.eq_empty_iff_forall_notMem.mpr fun v hv => ?_
  rw [mem_ramifiedSupport, hrel, ← Ideal.one_eq_top] at hv
  exact v.prime.not_dvd_one hv

/-- **Every prime outside the ramified support is unramified.** If a finite place `v` does not
divide the relative discriminant of `L/K`, then every prime of `L` above `v` is unramified over
`K`. This is the unramified-away hypothesis that specializations of the Artin map consume. -/
theorem isUnramifiedAway_ramifiedSupport :
    ∀ v : HeightOneSpectrum (𝓞 K), v ∉ ramifiedSupport K L →
      ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal],
        Algebra.IsUnramifiedAt (𝓞 K) Q := by
  intro v hv Q _ _
  by_contra hQ
  apply hv
  rw [mem_ramifiedSupport, TauCeti.dvd_relDiscr_iff_exists_not_isUnramifiedAt v.ne_bot]
  exact ⟨⟨Q, inferInstance, inferInstance⟩, hQ⟩

end TauCeti.NumberField
