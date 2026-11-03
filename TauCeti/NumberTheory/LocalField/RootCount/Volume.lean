/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.IntegerRing.Volume
public import TauCeti.NumberTheory.LocalField.RootCount.Fibre

/-!
# The volume of the polynomials with a root near a uniformizer

Let `L/K` be a totally ramified separable extension of nonarchimedean local fields of degree
`n = e(L/K)`, with discriminant exponent `d`, and let `ξ` be a uniformizer of `L`. Identify a
monic polynomial of degree `n` over `𝒪[K]` with its `n` lower coefficients, and equip the
coefficient space `Fin n → K` with a left-invariant measure normalized on the integer box. For
`d < r`, the monic polynomials having a root in the ball `v_L(z - ξ) ≥ r` have volume
`q ^ (-(r + d))`, where `q` is the residue cardinality of `K`.

This combines two facts. By the local fibre criterion
(`TauCeti.IsTotallyRamified.exists_isRoot_le_addVal_iff`), a root lies in that ball exactly when
`v_L(g(ξ)) ≥ r + d`. In the coordinates given by the powers of `ξ`, the last condition cuts out a
ball of `𝒪[L]` (`MeasureTheory.Measure.measure_image_setOf_le_addVal_aeval_monicOfCoeff`), of
volume `q ^ (-(r + d))`. These are the coefficient fibres whose volumes evaluate the integral of
the root count in Serre's proof of his mass formula.

## Main results

* `MeasureTheory.Measure.measure_image_setOf_exists_aeval_monicOfCoeff_eq_zero_le_addVal`: the
  monic polynomials of degree `n` over `𝒪[K]` with a root in the ball `v_L(z - ξ) ≥ r` have
  volume `q ^ (-(r + d))` when `d < r`.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Lemma 1 and §3.
-/

public section

open ValuativeRel MeasureTheory Polynomial TauCeti TauCeti.Polynomial
open IsDiscreteValuationRing (addVal)
open scoped ENNReal

namespace MeasureTheory.Measure

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Algebra.IsSeparable K L] {ξ : 𝒪[L]} {n : ℕ}
  [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K))
  [μ.IsAddLeftInvariant]

/-- **The volume of a local fibre.** Let `L/K` be totally ramified and separable, with
`n = e(L/K) = [L : K]` and discriminant exponent `d`, let `ξ` be a uniformizer of `L`, and let
`d < r`. For a left-invariant measure on `Fin n → K` normalized on the integer box, the monic
polynomials of degree `n` over `𝒪[K]` having a root in the ball `v_L(z - ξ) ≥ r`, identified with
their lower coefficients, have volume `q ^ (-(r + d))`, where `q = Nat.card 𝓀[K]`. -/
theorem measure_image_setOf_exists_aeval_monicOfCoeff_eq_zero_le_addVal
    (h : IsTotallyRamified K L) (hμ : μ (integerBox K (Fin n)) = 1) (hξ : Irreducible ξ)
    (hn : ramificationIndex K L = n) {r : ℕ} (hr : discriminantExponent K L < r) :
    μ ((fun c : Fin n → 𝒪[K] ↦ fun i ↦ (c i : K)) ''
        {c | ∃ z : 𝒪[L], aeval z (monicOfCoeff c) = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)}) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (r + discriminantExponent K L) := by
  have hfibre : {c : Fin n → 𝒪[K] |
      ∃ z : 𝒪[L], aeval z (monicOfCoeff c) = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)} =
        {c | ((r + discriminantExponent K L : ℕ) : ℕ∞) ≤
          addVal 𝒪[L] (aeval ξ (monicOfCoeff c))} := by
    ext c
    exact h.exists_isRoot_le_addVal_iff hξ (monic_monicOfCoeff c)
      ((natDegree_monicOfCoeff c).trans hn.symm) hr
  rw [hfibre]
  exact measure_image_setOf_le_addVal_aeval_monicOfCoeff μ h hμ hξ hn _

end MeasureTheory.Measure
