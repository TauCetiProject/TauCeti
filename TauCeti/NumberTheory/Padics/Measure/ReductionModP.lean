/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.PhiPsi
public import TauCeti.RingTheory.PowerSeries.ResiduePsi

/-!
# Reduction of series psi modulo `p`

Reducing the coefficients of an integral power series modulo `p` turns the series psi operator
`TauCeti.psiSeries` on `ℤ_p⟦X⟧` into the residue averaging operator
`TauCeti.IwasawaResidue.residuePsi` on `𝔽_p⟦X⟧`, the alternating sum of the `p` Cartier
components:
`ρ (ψ F) = ψ₀ (ρ F)`, where `ρ` is coefficientwise reduction along `PadicInt.toZMod`.

## Main results

* `AbstractMeasure.toZMod_apply_eq_zero`: an integral measure sends a test function that vanishes
  modulo `p` to a multiple of `p`.
* `TauCeti.map_toZMod_psiSeries`: reduction modulo `p` intertwines series psi with residue
  averaging.

## Implementation notes

Writing `F` as the Amice transform of a measure `μ`, the `n`-th coefficients of the two sides are
the reductions of `μ (χ · (mahler n ∘ (· / p)))` and of `μ (∑_{i < p} (-1) ^ i mahler (p n + i))`,
where `χ` is the characteristic function of `pℤ_p`. The two test functions are congruent modulo
`p`: on natural numbers this is the identity for the Dirac measures, where both operators send
`(1 + X) ^ m` to `(1 + X) ^ (m / p)` or to `0`, and it extends to `ℤ_p` by density since both sides
are locally constant. An integral measure respects congruences of test functions modulo `p`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.3–5 and
  Lemma 12.13.
-/

public section

open PowerSeries
open scoped AbstractMeasure

variable {p : ℕ} [Fact p.Prime]

namespace AbstractMeasure

/-- An integral measure sends a test function that vanishes modulo `p` to a multiple of `p`. -/
theorem toZMod_apply_eq_zero {X : Type*} [TopologicalSpace X] (μ : D(X, ℤ_[p]))
    {f : C(X, ℤ_[p])} (hf : ∀ x, PadicInt.toZMod (f x) = 0) : PadicInt.toZMod (μ f) = 0 := by
  have hf' : f = (p : ℤ_[p]) • (PadicInt.divideByP p).comp f := by
    ext x
    simp [PadicInt.mul_divideByP p ((PadicInt.toZMod_eq_zero_iff_dvd _).mp (hf x))]
  rw [hf', map_smul, smul_eq_mul, map_mul, map_natCast, ZMod.natCast_self, zero_mul]

end AbstractMeasure

namespace TauCeti

open AbstractMeasure IwasawaResidue

/-- Each coefficient of either side of the reduction identity, applied to an Amice transform, is
the reduction of the integral of a fixed test function. -/
private theorem exists_coeff_eq_toZMod_apply (n : ℕ) :
    ∃ f g : C(ℤ_[p], ℤ_[p]), ∀ μ : D(ℤ_[p], ℤ_[p]),
      (map PadicInt.toZMod (psiSeries p μ.amiceTransform)).coeff n = PadicInt.toZMod (μ f) ∧
      (residuePsi p (map PadicInt.toZMod μ.amiceTransform)).coeff n =
        PadicInt.toZMod (μ g) := by
  refine ⟨pMultiplesIndicator p ℤ_[p] * (mahler n).comp (PadicInt.divideByP p),
    ∑ i ∈ Finset.range p, (-1 : ℤ_[p]) ^ i • mahler (p * n + i), fun μ ↦ ⟨?_, ?_⟩⟩
  · simp [coeff_amiceTransform]
  · simp [coeff_amiceTransform, map_sum]

/-- **Reduction of series psi modulo `p`.** Reducing coefficients modulo `p` intertwines series
psi on `ℤ_p⟦X⟧` with residue averaging on `𝔽_p⟦X⟧`. -/
theorem map_toZMod_psiSeries (F : ℤ_[p]⟦X⟧) :
    map PadicInt.toZMod (psiSeries p F) = residuePsi p (map PadicInt.toZMod F) := by
  obtain ⟨μ, rfl⟩ := amiceTransformEquiv.surjective F
  rw [amiceTransformEquiv_apply]
  ext n
  obtain ⟨f, g, hfg⟩ := exists_coeff_eq_toZMod_apply (p := p) n
  rw [(hfg μ).1, (hfg μ).2, ← sub_eq_zero, ← map_sub, ← map_sub]
  refine toZMod_apply_eq_zero μ fun x ↦ ?_
  -- Both sides of the congruence are continuous, so it suffices to check it at natural numbers,
  -- where it is the identity for the Dirac measure, whose Amice transform is `(1 + X) ^ m`.
  refine congrFun (PadicInt.denseRange_natCast.equalizer
    (PadicInt.continuous_toZMod.comp (map_continuous (f - g))) continuous_const
    (funext fun m ↦ ?_)) x
  have hm := congr(coeff n $(congr_arg (PowerSeries.map PadicInt.toZMod)
    (psiSeries_one_add_X_pow (p := p) m)))
  have hδ := hfg (dirac ℤ_[p] m)
  rw [amiceTransform_dirac, binomialSeries_nat] at hδ
  simp only [Function.comp_apply, ContinuousMap.sub_apply, map_sub, sub_eq_zero]
  rw [← dirac_apply (R := ℤ_[p]) (m : ℤ_[p]) f, ← dirac_apply (R := ℤ_[p]) (m : ℤ_[p]) g,
    ← hδ.1, ← hδ.2, hm]
  split_ifs <;> simp_all

end TauCeti
