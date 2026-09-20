/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Rigidity of the pre-Schwarzian derivative

The **pre-Schwarzian derivative** of a holomorphic function `f` is `logDeriv (deriv f) = f'' / f'`.
Postcomposing `f` with `w ↦ a * w + b` for `a ≠ 0` leaves it unchanged, and this file proves the
converse: on a domain -- an open preconnected subset of `ℂ` -- two holomorphic functions with
nonvanishing derivatives and the same pre-Schwarzian derivative differ by exactly such a
postcomposition.

Both steps are available in Mathlib. Equality of the logarithmic derivatives of the two first
derivatives identifies those derivatives up to a nonzero constant (`logDeriv_eqOn_iff`), and two
functions with equal derivatives on a domain differ by an additive constant
(`IsOpen.exists_eq_add_of_deriv_eq`).

This is the statement that integrates a pre-Schwarzian differential equation, such as the
Schwarz--Christoffel equation `f'' / f' = ∑ i, e i / (z - a i)`, back to its solutions.

## Main result

* `TauCeti.exists_eqOn_const_mul_add_iff_logDeriv_deriv_eqOn` -- two holomorphic functions with
  nonvanishing derivatives on a domain have the same pre-Schwarzian derivative exactly when one
  is `w ↦ a * w + b` applied to the other, for some `a ≠ 0`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
-/

public section

namespace TauCeti

open Set

/-- **Rigidity of the pre-Schwarzian derivative.** Two holomorphic functions with nonvanishing
derivatives on a domain have equal pre-Schwarzian derivatives exactly when one is obtained from
the other by postcomposition with `w ↦ a * w + b` for a nonzero constant `a`.

The additive constant disappears after one differentiation. The multiplicative constant is then
detected by Mathlib's `logDeriv_eqOn_iff`, applied to the two first derivatives. -/
theorem exists_eqOn_const_mul_add_iff_logDeriv_deriv_eqOn {Ω : Set ℂ} (hΩopen : IsOpen Ω)
    (hΩconn : IsPreconnected Ω) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hg : DifferentiableOn ℂ g Ω)
    (hfn : ∀ z ∈ Ω, deriv f z ≠ 0) (hgn : ∀ z ∈ Ω, deriv g z ≠ 0) :
    (∃ a : ℂ, a ≠ 0 ∧ ∃ b : ℂ, EqOn f (fun z => a * g z + b) Ω) ↔
      EqOn (logDeriv (deriv f)) (logDeriv (deriv g)) Ω := by
  rw [logDeriv_eqOn_iff (hf.deriv hΩopen) (hg.deriv hΩopen) hΩopen hΩconn hgn hfn]
  constructor
  · rintro ⟨a, ha, b, hfg⟩
    refine ⟨a, ha, fun z hz => ?_⟩
    have hderiv := hfg.deriv hΩopen hz
    simpa [deriv_const_mul_field] using hderiv
  · rintro ⟨a, ha, hderiv⟩
    refine ⟨a, ha, ?_⟩
    have hag : DifferentiableOn ℂ (fun z => a * g z) Ω :=
      fun z hz => (hg z hz).const_mul a
    obtain ⟨b, hb⟩ := hΩopen.exists_eq_add_of_deriv_eq hΩconn hf hag fun z hz => by
      simpa [deriv_const_mul_field] using hderiv hz
    exact ⟨b, hb⟩

end TauCeti
