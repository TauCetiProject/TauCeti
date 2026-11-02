/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Finite
public import TauCeti.NumberTheory.LocalField.MassFormula.Representative
public import TauCeti.NumberTheory.LocalField.MassFormula.Weight
import Mathlib.MeasureTheory.Measure.Haar.Basic
import TauCeti.NumberTheory.LocalField.MassFormula.Integral
import TauCeti.NumberTheory.LocalField.MassFormula.Total

/-!
# Serre's mass formulas

Let `K` be a nonarchimedean local field whose residue field has `q` elements, and let `σ_K(n)` be
the set of totally ramified subextensions of degree `n` of a separable closure of `K`. For
`L ∈ σ_K(n)` with discriminant exponent `d(L)`, the wild exponent is `c(L) = d(L) - n + 1`.
Serre's first mass formula states that
`∑_{L ∈ σ_K(n)} q ^ (-c(L)) = n`.
The sum is taken in `ℝ≥0∞`, so the equation also asserts that it is finite. For `n = 0` both
sides vanish, since `σ_K(0)` is empty.

The proof integrates root counts over the Eisenstein region of coefficient space against Haar
measure normalized on the integer box. Almost every Eisenstein polynomial is separable and
irreducible of degree `n`, and each of its roots generates exactly one member of `σ_K(n)`, so its
numbers of roots in the members of `σ_K(n)` add up to `n`. Hence the root-count integrals add up
to `n` times the volume of the region. The root count of `L` integrates to
`q ^ (-(d(L) + 1)) (1 - q⁻¹)`, which is `q ^ (-c(L))` times that volume.

The remaining statements of Serre's note follow from the first formula and the reductions
already proved for the weighted count:

* for `0 < n`, regrouping along isomorphism classes gives the second mass formula
  `∑_{M ∈ R} 1 / (#Aut_K(M) · q ^ c(M)) = 1` for every set of representatives `R`;
* for `0 < n`, `σ_K(n)` is infinite exactly when `K` has equal characteristic `p` and `p ∣ n`;
* the real series `∑_{L ∈ σ_K(n)} q ^ (-c(L))` converges to `n`, also when `σ_K(n)` is infinite;
* if the residue characteristic does not divide `n`, then `σ_K(n)` has exactly `n` elements.

## Main results

* `TauCeti.tsum_one_div_natCard_residueField_pow_wildExponent`: the first mass formula.
* `IsRepresentativeSet.tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_wildExponent`:
  the second mass formula.
* `TauCeti.infinite_totallyRamifiedOfDegree_iff`: the finiteness dichotomy.
* `TauCeti.hasSum_one_div_natCard_residueField_pow_wildExponent` and
  `TauCeti.summable_one_div_natCard_residueField_pow_wildExponent`: convergence of the real series.
* `TauCeti.encard_totallyRamifiedOfDegree_of_not_dvd`: the tame count.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Théorèmes 1 and 2,
  Remarques 1° and 3°.
-/

public section

open MeasureTheory ValuativeRel
open scoped ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ}

/-- **Serre's first mass formula**: the totally ramified degree-`n` subextensions `L` of a
separable closure of `K` satisfy `∑_L q ^ (-c(L)) = n`, where `q` is the residue cardinality of
`K` and `c(L)` is the wild exponent. -/
theorem tsum_one_div_natCard_residueField_pow_wildExponent :
    ∑' L : totallyRamifiedOfDegree K n, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [totallyRamifiedOfDegree_zero]
  -- Integrate against Haar measure on `Fin n → K` normalized on the integer box.
  let : MeasurableSpace (Fin n → K) := borel _
  have : BorelSpace (Fin n → K) := ⟨rfl⟩
  let B : TopologicalSpace.PositiveCompacts (Fin n → K) :=
    ⟨⟨integerBox K (Fin n), isCompact_integerBox⟩, by
      rw [isOpen_integerBox.interior_eq]
      exact ⟨0, by simp⟩⟩
  have hμ : Measure.addHaarMeasure B (integerBox K (Fin n)) = 1 := Measure.addHaarMeasure_self
  exact tsum_one_div_natCard_residueField_pow_wildExponent_eq_of_lintegral_rootCount_eq hn _ hμ
    fun L hL ↦ L.lintegral_rootCount hL _ hμ

/-- **Serre's second mass formula**: for `0 < n` and every set `R` of representatives of the
`K`-isomorphism classes in `σ_K(n)`, `∑_{M ∈ R} 1 / (#Aut_K(M) · q ^ c(M)) = 1`. -/
theorem IsRepresentativeSet.tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_wildExponent
    {R : Set (IntermediateField K (SeparableClosure K))} (hR : IsRepresentativeSet n R)
    (hn : 0 < n) :
    ∑' M : R, 1 / ((Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) *
      (Nat.card 𝓀[K] : ℝ≥0∞) ^ M.1.wildExponent) = 1 :=
  (tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_wildExponent_eq_one_iff hR
    hn).2 tsum_one_div_natCard_residueField_pow_wildExponent

/-- **Serre's finiteness dichotomy**: for `0 < n`, there are infinitely many totally ramified
degree-`n` subextensions of a separable closure of `K` exactly when `K` has equal
characteristic `p`, the residue characteristic, and `p ∣ n`. -/
theorem infinite_totallyRamifiedOfDegree_iff (hn : 0 < n) :
    (totallyRamifiedOfDegree K n).Infinite ↔
      ringChar K = ringChar 𝓀[K] ∧ ringChar 𝓀[K] ∣ n := by
  rw [infinite_totallyRamifiedOfDegree_iff_or_tsum_eq_top hn,
    tsum_one_div_natCard_residueField_pow_wildExponent]
  simp

/-- **The real form of the first mass formula**: the real series
`∑_{L ∈ σ_K(n)} q ^ (-c(L))` converges to `n`, also when `σ_K(n)` is infinite. -/
theorem hasSum_one_div_natCard_residueField_pow_wildExponent :
    HasSum (fun L : totallyRamifiedOfDegree K n ↦
      1 / (Nat.card 𝓀[K] : ℝ) ^ L.1.wildExponent) n := by
  have h := tsum_one_div_natCard_residueField_pow_wildExponent (K := K) (n := n)
  rw [← ENNReal.coe_natCast] at h
  simpa using (hasSum_one_div_natCard_residueField_pow_wildExponent_iff (s := n)).2 h

/-- **Convergence of the weighted count**: the real series
`∑_{L ∈ σ_K(n)} q ^ (-c(L))` converges, also when `σ_K(n)` is infinite. -/
theorem summable_one_div_natCard_residueField_pow_wildExponent :
    Summable fun L : totallyRamifiedOfDegree K n ↦
      1 / (Nat.card 𝓀[K] : ℝ) ^ L.1.wildExponent :=
  hasSum_one_div_natCard_residueField_pow_wildExponent.summable

/-- **The tame count**: if the residue characteristic of `K` does not divide `n`, then a
separable closure of `K` has exactly `n` totally ramified subextensions of degree `n`. -/
theorem encard_totallyRamifiedOfDegree_of_not_dvd (hp : ¬ ringChar 𝓀[K] ∣ n) :
    (totallyRamifiedOfDegree K n).encard = n := by
  have h := tsum_one_div_natCard_residueField_pow_wildExponent_eq_encard (K := K) hp
  rw [tsum_one_div_natCard_residueField_pow_wildExponent] at h
  exact_mod_cast h.symm

end TauCeti
