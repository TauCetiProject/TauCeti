/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.NumberTheory.LocalField.HaarCharacter
public import TauCeti.NumberTheory.LocalField.Padic

/-!
# Form measures on the multiplicative group need convergence factors

Let `K` be a nonarchimedean local field whose residue field has `q` elements, and let `μ` be the
additive Haar measure on `K` with `μ 𝒪[K] = 1`. The invariant form `ω = dx/x` on `𝔾_m` defines the
local measure `|ω| = |x|_K⁻¹ μ`, the measure with density `|x|_K⁻¹` with respect to `μ`. On the
units `𝒪[K]ˣ = {x | v(x) = 1}` the density is `1`, and the maximal ideal `ϖ 𝒪[K]` has mass `q⁻¹`,
so the units have mass `1 - q⁻¹` for both `μ`
(`MeasureTheory.Measure.addHaar_setOf_valuation_eq_one`) and `|ω|`
(`MeasureTheory.Measure.withDensity_inv_normalizedAbsoluteValue_setOf_valuation_eq_one`).

For `K = ℚ_[p]` this mass is `1 - p⁻¹`, and the product of these local masses over all primes is
`0`: the partial products `∏_{p ≤ n} (1 - p⁻¹)` tend to `0`, because the sum of the reciprocals of
the primes diverges (`Nat.tendsto_prod_primesLE_filter_notMem_one_sub_inv_atTop_nhds_zero`). This
is why the Tamagawa measure of `𝔾_m` uses the convergence factors `(1 - p⁻¹)⁻¹`.

Separately, since `1 - q⁻¹ ≠ 1`, the local measures `|ω|_p` do not give the units `ℤ_p^×` mass
`1` at all but finitely many primes, and no single rescaling `c • |ω|_p` repairs this
(`TauCeti.not_eventually_smul_withDensity_setOf_valuation_eq_one`). This is the analogue, for these
measures on the additive field `K`, of the normalization hypothesis of the restricted product of
Haar measures (`TauCeti.restrictedHaar`). The multiplicative Haar measure on `Kˣ` that `|ω|`
restricts to, and the application to `TauCeti.restrictedHaar`, are not formalized here.

## Main declarations

* `MeasureTheory.Measure.withDensity_inv_normalizedAbsoluteValue_setOf_valuation_eq_one`: the
  form measure `|x|_K⁻¹ μ` gives the units of `𝒪[K]` mass `(1 - q⁻¹) μ 𝒪[K]`.
* `TauCeti.withDensity_inv_nnnorm_setOf_norm_eq_one`: over `ℚ_[p]`, the form measure of `ℤ_p^×` is
  `1 - p⁻¹`.
* `TauCeti.not_eventually_smul_withDensity_setOf_valuation_eq_one`: for local fields each of whose
  residue cardinalities occurs only finitely often, such as the `ℚ_[p]`, no rescaling of the form
  measures gives the units mass one at all but finitely many places.

## References

* Z. Rosengarten, *Tamagawa numbers and other invariants of pseudo-reductive groups over global
  function fields*, arXiv:1806.10723v3, §1, p. 2.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §5.5, p. 21.
-/

public section

open MeasureTheory Measure Filter Topology TauCeti ValuativeRel
open scoped NNReal ENNReal Pointwise

namespace MeasureTheory.Measure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsAddHaarMeasure]

/-- **The form measure of the units.** The measure `|dx/x|_K`, with density `|x|_K⁻¹` with respect
to an additive Haar measure `μ`, gives the units of `𝒪[K]` the mass `(1 - q⁻¹) μ 𝒪[K]`, since the
density is `1` there. -/
theorem withDensity_inv_normalizedAbsoluteValue_setOf_valuation_eq_one :
    (μ.withDensity fun x ↦ ((normalizedAbsoluteValue K x : ℝ≥0) : ℝ≥0∞)⁻¹)
        {x : K | valuation K x = 1} =
      (1 - (Nat.card 𝓀[K] : ℝ≥0∞)⁻¹) * μ 𝒪[K] := by
  rw [withDensity_apply _ measurableSet_setOf_valuation_eq_one,
    setLIntegral_congr_fun (g := fun _ ↦ 1) measurableSet_setOf_valuation_eq_one fun x hx ↦ by
      simp [(normalizedAbsoluteValue_eq_one_iff x).2 hx],
    setLIntegral_one, addHaar_setOf_valuation_eq_one]

end MeasureTheory.Measure

namespace TauCeti

section Padic

variable (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]

/-- **The form measure of `ℤ_p^×`.** For the additive Haar measure `μ` on `ℚ_[p]` with
`μ ℤ_[p] = 1`, the measure `|dx/x|_p` with density `‖x‖⁻¹` gives the units `‖x‖ = 1` the mass
`1 - p⁻¹`. -/
theorem withDensity_inv_nnnorm_setOf_norm_eq_one (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]
    (hμ : μ 𝒪[ℚ_[p]] = 1) :
    (μ.withDensity fun x ↦ (‖x‖₊ : ℝ≥0∞)⁻¹) {x : ℚ_[p] | ‖x‖ = 1} = 1 - (p : ℝ≥0∞)⁻¹ := by
  have hset : {x : ℚ_[p] | ‖x‖ = 1} = {x : ℚ_[p] | valuation ℚ_[p] x = 1} := by
    ext x
    simpa using (Padic.valuation_eq_valuation_iff_norm_eq (x := x) (y := 1)).symm
  have h := μ.withDensity_inv_normalizedAbsoluteValue_setOf_valuation_eq_one
  simp only [Padic.normalizedAbsoluteValue_eq_nnnorm, Padic.natCard_residueField, hμ, mul_one] at h
  rwa [hset]

end Padic

/-- A rescaling `c (1 - n⁻¹)` takes the value `1` for at most one positive natural `n`. -/
private theorem eq_of_mul_one_sub_inv_eq_one {c : ℝ≥0∞} {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h₁ : c * (1 - (a : ℝ≥0∞)⁻¹) = 1) (h₂ : c * (1 - (b : ℝ≥0∞)⁻¹) = 1) : a = b := by
  have h := (ENNReal.eq_inv_of_mul_eq_one_left h₁).symm.trans (ENNReal.eq_inv_of_mul_eq_one_left h₂)
  rwa [inv_inj, ENNReal.sub_right_inj ENNReal.one_ne_top
    (ENNReal.inv_le_one.2 (by exact_mod_cast ha)) (ENNReal.inv_le_one.2 (by exact_mod_cast hb)),
    inv_inj, Nat.cast_inj] at h

/-- **Form measures need convergence factors.** Let `K i` be a family of nonarchimedean local
fields, indexed by an infinite type, such that each residue cardinality `q` is taken by only
finitely many `K i`, for instance the `ℚ_[p]` (`Padic.natCard_residueField`) or the completions of
a number field at its finite places, and let `μ i` be the additive Haar measure on `K i` with
`μ i 𝒪[K i] = 1`. No single rescaling `c • |dx/x|_i` of the form measures gives the units of
`𝒪[K i]` mass one for all but finitely many `i`: their masses are `c (1 - q_i⁻¹)`, which take the
value `1` only for the `i` sharing a single value of `q_i`. This is the analogue, for the
measures `|x|⁻¹ μ i` on the additive fields `K i`, of the normalization hypothesis of the
restricted product of Haar measures (`TauCeti.restrictedHaar`); the Haar measures on the
`(K i)ˣ` that these would restrict to are not constructed here. -/
theorem not_eventually_smul_withDensity_setOf_valuation_eq_one {ι : Type*} [Infinite ι]
    {K : ι → Type*} [∀ i, Field (K i)] [∀ i, ValuativeRel (K i)] [∀ i, TopologicalSpace (K i)]
    [∀ i, IsNonarchimedeanLocalField (K i)] [∀ i, MeasurableSpace (K i)]
    [∀ i, BorelSpace (K i)] (μ : ∀ i, Measure (K i)) [∀ i, (μ i).IsAddHaarMeasure]
    (hμ : ∀ i, μ i 𝒪[K i] = 1) (hq : ∀ n, {i | Nat.card 𝓀[K i] = n}.Finite) (c : ℝ≥0∞) :
    ¬ ∀ᶠ i in cofinite,
      (c • (μ i).withDensity fun x ↦ ((normalizedAbsoluteValue (K i) x : ℝ≥0) : ℝ≥0∞)⁻¹)
        {x : K i | valuation (K i) x = 1} = 1 := by
  intro h
  simp only [smul_apply, withDensity_inv_normalizedAbsoluteValue_setOf_valuation_eq_one, hμ,
    mul_one, smul_eq_mul] at h
  have hinf := Set.infinite_of_finite_compl (Filter.mem_cofinite.1 h)
  obtain ⟨i, hi⟩ := hinf.nonempty
  exact hinf <| (hq (Nat.card 𝓀[K i])).subset fun j hj ↦
    eq_of_mul_one_sub_inv_eq_one Nat.card_pos Nat.card_pos hj hi

end TauCeti
