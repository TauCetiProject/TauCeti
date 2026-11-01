/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Infinite
public import TauCeti.NumberTheory.LocalField.MassFormula.Main
public import TauCeti.RingTheory.LaurentSeries.LocalField

/-!
# Totally ramified extensions of `𝔽_q((X))`

For a finite field `F` of characteristic `p`, the Laurent series field `F⸨X⸩` is a nonarchimedean
local field of characteristic `p` (`TauCeti.LaurentSeries.isNonarchimedeanLocalField`), with
residue field `F`. It is the equal-characteristic case of Serre's finiteness dichotomy: whenever
`0 < n` and `p ∣ n`, the family `σ_{F⸨X⸩}(n)` of totally ramified subextensions of degree `n` of
a separable closure is infinite. Serre's mass formula nevertheless gives the weighted series
`∑_{L ∈ σ_{F⸨X⸩}(n)} q ^ (-c(L))` the finite value `n`, where `q` is the cardinality of `F`
(`TauCeti.LaurentSeries.natCard_residueField`), so the real series converges although it has
infinitely many terms. These are the two halves of Serre's Remarque 1° on one example.

## Main results

* `TauCeti.infinite_totallyRamifiedOfDegree_laurentSeries`: if `0 < n` and the characteristic of
  `F` divides `n`, then `σ_{F⸨X⸩}(n)` is infinite.
* `TauCeti.tsum_one_div_natCard_pow_wildExponent_laurentSeries`: Serre's mass formula
  `∑_{L ∈ σ_{F⸨X⸩}(n)} q ^ (-c(L)) = n` in `ℝ≥0∞`, with `q` the cardinality of `F`.
* `TauCeti.hasSum_one_div_natCard_pow_wildExponent_laurentSeries`: the real series
  `∑_{L ∈ σ_{F⸨X⸩}(n)} q ^ (-c(L))` converges to `n`, also when `σ_{F⸨X⸩}(n)` is infinite.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Remarque 1°.
-/

public section

open scoped LaurentSeries ENNReal

namespace TauCeti

variable (F : Type*) [Field F] [Finite F]

/-- **Infinitely many totally ramified extensions of `𝔽_q((X))`.** If `0 < n` and the
characteristic of the finite field `F` divides `n`, then `F⸨X⸩` has infinitely many totally
ramified extensions of degree `n` inside a separable closure. -/
theorem infinite_totallyRamifiedOfDegree_laurentSeries {n : ℕ} (hn : 0 < n)
    (hp : ringChar F ∣ n) : (totallyRamifiedOfDegree F⸨X⸩ n).Infinite := by
  refine infinite_totallyRamifiedOfDegree hn ?_
  rw [← map_natCast (algebraMap F F⸨X⸩), (ringChar.spec F n).2 hp, map_zero]

/-- **The equal-characteristic worked example.** For a finite field `F` of characteristic `p`,
the Laurent series field `F⸨X⸩` has infinitely many totally ramified extensions of degree `p`
inside a separable closure. -/
theorem infinite_totallyRamifiedOfDegree_ringChar_laurentSeries :
    (totallyRamifiedOfDegree F⸨X⸩ (ringChar F)).Infinite :=
  infinite_totallyRamifiedOfDegree_laurentSeries F
    (Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite F)) dvd_rfl

/-- **Serre's mass formula over `𝔽_q((X))`**: the totally ramified degree-`n` subextensions `L`
of a separable closure of `F⸨X⸩` satisfy `∑_L q ^ (-c(L)) = n` in `ℝ≥0∞`, where `q` is the
cardinality of the finite field `F` and `c(L)` is the wild exponent. -/
theorem tsum_one_div_natCard_pow_wildExponent_laurentSeries {n : ℕ} :
    ∑' L : totallyRamifiedOfDegree F⸨X⸩ n, 1 / (Nat.card F : ℝ≥0∞) ^ L.1.wildExponent = n := by
  rw [← LaurentSeries.natCard_residueField F]
  exact tsum_one_div_natCard_residueField_pow_wildExponent

/-- **The equal-characteristic convergence example.** The real series
`∑_{L ∈ σ_{F⸨X⸩}(n)} q ^ (-c(L))`, with `q` the cardinality of `F`, converges to `n`. When `0 < n`
and the characteristic of `F` divides `n`, it has infinitely many terms
(`TauCeti.infinite_totallyRamifiedOfDegree_laurentSeries`). -/
theorem hasSum_one_div_natCard_pow_wildExponent_laurentSeries {n : ℕ} :
    HasSum (fun L : totallyRamifiedOfDegree F⸨X⸩ n ↦
      1 / (Nat.card F : ℝ) ^ L.1.wildExponent) n := by
  rw [← LaurentSeries.natCard_residueField F]
  exact hasSum_one_div_natCard_residueField_pow_wildExponent

end TauCeti
