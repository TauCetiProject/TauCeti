/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.SInteger
public import TauCeti.NumberTheory.NumberField.RestrictedRamification.Basic
import TauCeti.NumberTheory.NumberField.Kummer.Ramification

/-!
# Roots of units and of `S`-units in `K_S`

Let `K` be a number field, `Ω` an extension of `K` and `S` a set of finite places of `K`. If
`xⁿ = a` with `n ≠ 0` and `a ∈ K`, and every finite place `v ∉ S` has `n ∉ v` and `v(a) = 1`, then
`K(x)` is unramified outside `S` (main's
`TauCeti.NumberField.isUnramifiedIn_adjoin_simple_of_pow_eq_of_valuation_eq_one`, by the
derivative of `Xⁿ - a`), so `x` lies in the maximal extension `K_S` unramified outside `S`. In
particular:

* every `n`-th root of unity lies in `K_S` once `S` contains the places dividing `n`
  (`TauCeti.RestrictedRamification.mem_maxUnramifiedOutside_of_pow_eq_one`), so adjoining `μ_n` is
  unramified outside the places dividing `n`;
* an `n`-th root of an `S`-unit lies in `K_{S ∪ {v ∣ n}}`
  (`TauCeti.RestrictedRamification.mem_maxUnramifiedOutside_of_pow_eq_of_mem_unit`).

No roots of unity in `K` are needed.

## Main results

* `TauCeti.RestrictedRamification.mem_maxUnramifiedOutside_of_pow_eq`: roots of `v`-units outside
  `S` and `n` lie in `K_S`.
* `TauCeti.RestrictedRamification.mem_maxUnramifiedOutside_of_pow_eq_one`: roots of unity.
* `TauCeti.RestrictedRamification.mem_maxUnramifiedOutside_of_pow_eq_of_mem_unit`: roots of
  `S`-units.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, §4.
-/

public section

open IntermediateField IsDedekindDomain

open scoped NumberField

namespace TauCeti.RestrictedRamification

variable {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {x : Ω} {n : ℕ}

/-- **Roots of `v`-units lie in `K_S`.** If `xⁿ = a` with `n ≠ 0`, and every finite place `v ∉ S`
has `n ∉ v` and `v(a) = 1`, then `x` lies in the maximal extension `K_S` unramified outside
`S`. -/
theorem mem_maxUnramifiedOutside_of_pow_eq {a : K} (hx : x ^ n = algebraMap K Ω a) (hn : n ≠ 0)
    (h : ∀ v ∉ S, (n : 𝓞 K) ∉ v.asIdeal ∧ v.valuation K a = 1) :
    x ∈ maxUnramifiedOutside K Ω S := by
  have hint : IsIntegral K x :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hx ▸ isIntegral_algebraMap)
  have := adjoin.finiteDimensional hint
  exact le_maxUnramifiedOutside (L := K⟮x⟯)
    (fun v hv ↦ NumberField.isUnramifiedIn_adjoin_simple_of_pow_eq_of_valuation_eq_one hx
      (h v hv).1 (h v hv).2)
    (mem_adjoin_simple_self K x)

/-- **Roots of unity lie in `K_S`.** If `xⁿ = 1` with `n ≠ 0` and `S` contains every finite place
dividing `n`, then `x` lies in `K_S`: adjoining `n`-th roots of unity is unramified outside the
places dividing `n`. -/
theorem mem_maxUnramifiedOutside_of_pow_eq_one (hx : x ^ n = 1) (hn : n ≠ 0)
    (h : ∀ v ∉ S, (n : 𝓞 K) ∉ v.asIdeal) :
    x ∈ maxUnramifiedOutside K Ω S :=
  mem_maxUnramifiedOutside_of_pow_eq (a := 1) (by rw [hx, map_one]) hn fun v hv ↦
    ⟨h v hv, map_one _⟩

/-- **Roots of `S`-units lie in `K_{S ∪ {v ∣ n}}`.** If `u` is an `S`-unit and `xⁿ = u` with
`n ≠ 0`, then `x` lies in the maximal extension unramified outside `S` and the places dividing
`n`. -/
theorem mem_maxUnramifiedOutside_of_pow_eq_of_mem_unit {u : Kˣ} (hu : u ∈ S.unit K)
    (hx : x ^ n = algebraMap K Ω u) (hn : n ≠ 0) :
    x ∈ maxUnramifiedOutside K Ω (S ∪ {v | (n : 𝓞 K) ∈ v.asIdeal}) :=
  mem_maxUnramifiedOutside_of_pow_eq hx hn fun v hv ↦
    ⟨fun h ↦ hv (Or.inr h), hu v fun h ↦ hv (Or.inl h)⟩

end TauCeti.RestrictedRamification
