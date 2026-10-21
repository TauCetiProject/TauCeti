/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.LocalFieldScaling
public import TauCeti.NumberTheory.LocalField.Monogenic
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff

/-!
# Volumes of balls of `𝒪[L]` in uniformizer coordinates

Let `L/K` be an extension of nonarchimedean local fields with ramification index `n = e(L/K)`, let
`ϖ` be a uniformizer of `L`, and write `q = Nat.card 𝓀[K]`. A coefficient vector
`c : Fin n → 𝒪[K]` represents the element `∑ i, c i * ϖ ^ i` of `𝒪[L]`. Equip the coefficient
space `Fin n → K` with a left-invariant measure normalized on the integer box. This file computes
the volume of the coefficient vectors representing the elements of a valuation ball of `𝒪[L]`:
the ball of radius `r` has volume `q ^ (-r)`.

The ball is a box: by orthogonality of the terms `c i * ϖ ^ i`, whose valuations are distinct
modulo `n`, the coefficient vectors with `r ≤ v_L(∑ i, c i * ϖ ^ i)` are those with
`c i ∈ 𝓂[K] ^ ((r - i) ⌈/⌉ n)` (`TauCeti.le_addVal_sum_algebraMap_mul_pow_iff_of_irreducible`).
That box has volume `q ^ (-∑ i, (r - i) ⌈/⌉ n)`
(`MeasureTheory.Measure.measure_univ_pi_image_maximalIdeal_pow`), and the exponent is `r` by
Hermite's identity (`Nat.sum_range_sub_ceilDiv`).

When `L/K` is totally ramified, the powers `1, ϖ, …, ϖ ^ (n - 1)` form a basis of `𝒪[L]` over
`𝒪[K]`, so every ball `y + 𝓂[L] ^ r` of `𝒪[L]` is a translate of the ball around `0` in these
coordinates and has the same volume. Two consequences are recorded: the sphere
`v_L(x - y) = r` has volume `q ^ (-r) (1 - q⁻¹)`, and so, at `y = 0` and `r = 1`, the
uniformizers of `L` have volume `q⁻¹ (1 - q⁻¹)`; and, for monic polynomials `g` of degree `n` over
`𝒪[K]` identified with their lower coefficients through `TauCeti.Polynomial.monicOfCoeff`, the
condition `r ≤ v_L(g(ϖ))` cuts out a set of volume `q ^ (-r)`, since `g(ϖ) - ϖ ^ n` is the
element with coordinates the lower coefficients of `g`.

These volumes are the measure computations in Serre's proof of his mass formula: in the local fibre
count, the monic polynomials with a root close to a given uniformizer form a set of the second
kind, and the uniformizers of `L` are partitioned into balls of the first kind.

## Main results

* `TauCeti.image_setOf_le_addVal_sum_algebraMap_mul_pow_eq_pi`: the ball of radius `r` in
  uniformizer coordinates is the box with factors `𝓂[K] ^ ((r - i) ⌈/⌉ n)`.
* `TauCeti.measure_image_setOf_le_addVal_sum_algebraMap_mul_pow`: the ball has volume `q ^ (-r)`.
* `TauCeti.IsTotallyRamified.measure_image_setOf_le_addVal_sum_algebraMap_mul_pow_sub`: so does
  the ball of radius `r` around any `y ∈ 𝒪[L]`, in a totally ramified extension.
* `TauCeti.IsTotallyRamified.measure_image_setOf_addVal_sum_algebraMap_mul_pow_sub_eq`: the sphere
  of radius `r` around `y` has volume `q ^ (-r) (1 - q⁻¹)`.
* `TauCeti.IsTotallyRamified.measure_image_setOf_le_addVal_aeval_monicOfCoeff`: the monic
  polynomials `g` of degree `n` with `r ≤ v_L(g(ϖ))` have volume `q ^ (-r)`.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §3.
-/

public section

open Set ValuativeRel MeasureTheory Polynomial TauCeti.Polynomial
open IsDiscreteValuationRing (addVal)
open scoped ENNReal Pointwise

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] {ϖ : 𝒪[L]} {n : ℕ}

/-- **Balls in uniformizer coordinates are boxes.** For a uniformizer `ϖ` of `L` and
`n = e(L/K)`, the coefficient vectors `c : Fin n → 𝒪[K]` with `r ≤ v_L(∑ i, c i * ϖ ^ i)` form,
in `Fin n → K`, the box whose `i`-th factor is `𝓂[K] ^ ((r - i) ⌈/⌉ n)`. -/
theorem image_setOf_le_addVal_sum_algebraMap_mul_pow_eq_pi (hϖ : Irreducible ϖ)
    (hn : ramificationIndex K L = n) (r : ℕ) :
    (fun c : Fin n → 𝒪[K] ↦ fun i ↦ (c i : K)) ''
        {c | (r : ℕ∞) ≤ addVal 𝒪[L] (∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ϖ ^ (i : ℕ))} =
      univ.pi fun i : Fin n ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ ((r - (i : ℕ)) ⌈/⌉ n)) := by
  subst hn
  ext a
  simp only [mem_image, mem_ofPred_eq, mem_univ_pi,
    le_addVal_sum_algebraMap_mul_pow_iff_of_irreducible hϖ le_rfl]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨c, hc, rfl⟩ i
    exact ⟨c i, hc i, rfl⟩
  · choose c hc hca using h
    exact ⟨c, hc, funext hca⟩

section Measure

variable [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K))
  [μ.IsAddLeftInvariant]

/-- **The volume of a ball in uniformizer coordinates.** For a uniformizer `ϖ` of `L` and
`n = e(L/K)`, and a left-invariant measure on `Fin n → K` normalized on the integer box, the
coefficient vectors `c : Fin n → 𝒪[K]` with `r ≤ v_L(∑ i, c i * ϖ ^ i)` have volume `q ^ (-r)`,
where `q = Nat.card 𝓀[K]`. -/
theorem measure_image_setOf_le_addVal_sum_algebraMap_mul_pow
    (hμ : μ (integerBox K (Fin n)) = 1) (hϖ : Irreducible ϖ) (hn : ramificationIndex K L = n)
    (r : ℕ) :
    μ ((fun c : Fin n → 𝒪[K] ↦ fun i ↦ (c i : K)) ''
        {c | (r : ℕ∞) ≤ addVal 𝒪[L] (∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ϖ ^ (i : ℕ))}) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ r := by
  rw [image_setOf_le_addVal_sum_algebraMap_mul_pow_eq_pi hϖ hn,
    Measure.measure_univ_pi_image_maximalIdeal_pow μ hμ,
    Fin.sum_univ_eq_sum_range (fun i ↦ (r - i) ⌈/⌉ n),
    Nat.sum_range_sub_ceilDiv r (hn ▸ ramificationIndex_pos)]

end Measure

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- At `ϖ ∈ 𝒪[L]`, the value of the monic polynomial with lower coefficients `c : Fin n → 𝒪[K]`
is the element with coordinates `c` in the powers of `ϖ`, minus `-ϖ ^ n`. -/
private theorem setOf_le_addVal_aeval_monicOfCoeff_eq (r : ℕ) :
    {c : Fin n → 𝒪[K] | (r : ℕ∞) ≤ addVal 𝒪[L] (aeval ϖ (monicOfCoeff c))} =
      {c : Fin n → 𝒪[K] |
        (r : ℕ∞) ≤ addVal 𝒪[L] (∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ϖ ^ (i : ℕ) - -ϖ ^ n)} := by
  ext c
  rw [mem_ofPred_eq, mem_ofPred_eq, ← eval_map_algebraMap, map_monicOfCoeff, eval_monicOfCoeff,
    sub_neg_eq_add, add_comm]

namespace IsTotallyRamified

/-- In a totally ramified extension, every element of `𝒪[L]` has coordinates in the powers
`1, ϖ, …, ϖ ^ (n - 1)` of a uniformizer, where `n = e(L/K)`. -/
private theorem exists_sum_algebraMap_mul_pow_eq (h : IsTotallyRamified K L)
    (hϖ : Irreducible ϖ) (hn : ramificationIndex K L = n) (y : 𝒪[L]) :
    ∃ t : Fin n → 𝒪[K], ∑ i, algebraMap 𝒪[K] 𝒪[L] (t i) * ϖ ^ (i : ℕ) = y := by
  let b := (h.integralPowerBasis hϖ).basis.reindex
    (finCongr ((h.integralPowerBasis_dim hϖ).trans hn))
  refine ⟨b.repr y, ?_⟩
  conv_rhs => rw [← b.sum_repr y]
  simp [b, Algebra.smul_def]

/-- In a totally ramified extension, the ball of radius `r` around `y ∈ 𝒪[L]` is, in uniformizer
coordinates, a translate of the ball of radius `r` around `0`. -/
private theorem exists_image_setOf_le_addVal_sum_algebraMap_mul_pow_sub_eq_vadd
    (h : IsTotallyRamified K L) (hϖ : Irreducible ϖ) (hn : ramificationIndex K L = n)
    (y : 𝒪[L]) (r : ℕ) :
    ∃ x : Fin n → K, (fun c : Fin n → 𝒪[K] ↦ fun i ↦ (c i : K)) ''
        {c | (r : ℕ∞) ≤ addVal 𝒪[L] (∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ϖ ^ (i : ℕ) - y)} =
      x +ᵥ (fun c : Fin n → 𝒪[K] ↦ fun i ↦ (c i : K)) ''
        {c | (r : ℕ∞) ≤ addVal 𝒪[L] (∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ϖ ^ (i : ℕ))} := by
  obtain ⟨t, rfl⟩ := exists_sum_algebraMap_mul_pow_eq h hϖ hn y
  refine ⟨fun i ↦ (t i : K), ?_⟩
  -- Subtracting the expansion of `y` subtracts its coordinates.
  have hsub (c : Fin n → 𝒪[K]) :
      ∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ϖ ^ (i : ℕ) -
          ∑ i, algebraMap 𝒪[K] 𝒪[L] (t i) * ϖ ^ (i : ℕ) =
        ∑ i, algebraMap 𝒪[K] 𝒪[L] ((c - t) i) * ϖ ^ (i : ℕ) := by
    simp [← Finset.sum_sub_distrib, sub_mul]
  ext a
  simp only [hsub, mem_image, mem_ofPred_eq, mem_vadd_set, vadd_eq_add]
  refine ⟨?_, ?_⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c - t, hc, rfl⟩, funext fun i ↦ by simp⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨t + c, by simpa using hc, funext fun i ↦ by simp⟩

variable [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K))
  [μ.IsAddLeftInvariant]

/-- In a totally ramified extension, the ball of radius `r` around `y ∈ 𝒪[L]`, in uniformizer
coordinates, is a measurable subset of `Fin n → K`, where `n = e(L/K)`. -/
theorem measurableSet_image_setOf_le_addVal_sum_algebraMap_mul_pow_sub
    (h : IsTotallyRamified K L) (hϖ : Irreducible ϖ) (hn : ramificationIndex K L = n)
    (y : 𝒪[L]) (r : ℕ) :
    MeasurableSet ((fun c : Fin n → 𝒪[K] ↦ fun i ↦ (c i : K)) ''
      {c | (r : ℕ∞) ≤ addVal 𝒪[L] (∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ϖ ^ (i : ℕ) - y)}) := by
  obtain ⟨x, hx⟩ := exists_image_setOf_le_addVal_sum_algebraMap_mul_pow_sub_eq_vadd h hϖ hn y r
  rw [hx, image_setOf_le_addVal_sum_algebraMap_mul_pow_eq_pi hϖ hn]
  exact ((isClosed_univ_pi_image_maximalIdeal_pow _).vadd x).measurableSet

/-- **The volume of a ball of `𝒪[L]`.** In a totally ramified extension `L/K` with uniformizer
`ϖ` and `n = e(L/K) = [L : K]`, and for a left-invariant measure on `Fin n → K` normalized on the
integer box, the coefficient vectors `c : Fin n → 𝒪[K]` with `r ≤ v_L(∑ i, c i * ϖ ^ i - y)` have
volume `q ^ (-r)`, where `q = Nat.card 𝓀[K]`, for every center `y ∈ 𝒪[L]`. -/
theorem measure_image_setOf_le_addVal_sum_algebraMap_mul_pow_sub
    (h : IsTotallyRamified K L) (hμ : μ (integerBox K (Fin n)) = 1) (hϖ : Irreducible ϖ)
    (hn : ramificationIndex K L = n) (y : 𝒪[L]) (r : ℕ) :
    μ ((fun c : Fin n → 𝒪[K] ↦ fun i ↦ (c i : K)) ''
        {c | (r : ℕ∞) ≤ addVal 𝒪[L] (∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ϖ ^ (i : ℕ) - y)}) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ r := by
  obtain ⟨x, hx⟩ := exists_image_setOf_le_addVal_sum_algebraMap_mul_pow_sub_eq_vadd h hϖ hn y r
  rw [hx, measure_vadd, measure_image_setOf_le_addVal_sum_algebraMap_mul_pow μ hμ hϖ hn]

/-- **The volume of a sphere of `𝒪[L]`.** In a totally ramified extension `L/K` with uniformizer
`ϖ` and `n = e(L/K) = [L : K]`, and for a left-invariant measure on `Fin n → K` normalized on the
integer box, the coefficient vectors `c : Fin n → 𝒪[K]` with `v_L(∑ i, c i * ϖ ^ i - y) = r` have
volume `q ^ (-r) (1 - q⁻¹)`, where `q = Nat.card 𝓀[K]`, for every center `y ∈ 𝒪[L]`. At `y = 0`
and `r = 1` these are the coordinates of the uniformizers of `L`. -/
theorem measure_image_setOf_addVal_sum_algebraMap_mul_pow_sub_eq
    (h : IsTotallyRamified K L) (hμ : μ (integerBox K (Fin n)) = 1) (hϖ : Irreducible ϖ)
    (hn : ramificationIndex K L = n) (y : 𝒪[L]) (r : ℕ) :
    μ ((fun c : Fin n → 𝒪[K] ↦ fun i ↦ (c i : K)) ''
        {c | addVal 𝒪[L] (∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ϖ ^ (i : ℕ) - y) = r}) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ r * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  set j := fun c : Fin n → 𝒪[K] ↦ fun i ↦ (c i : K)
  set v := fun c : Fin n → 𝒪[K] ↦
    addVal 𝒪[L] (∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ϖ ^ (i : ℕ) - y)
  have hj : Function.Injective j := fun c d hcd ↦
    funext fun i ↦ Subtype.ext (congrFun hcd i)
  -- The sphere of radius `r` is the ball of radius `r` minus the ball of radius `r + 1`.
  have hsphere : {c | v c = r} = {c | (r : ℕ∞) ≤ v c} \ {c | ((r + 1 : ℕ) : ℕ∞) ≤ v c} := by
    ext c
    simp only [mem_ofPred_eq, mem_sdiff, not_le, Nat.cast_add, Nat.cast_one,
      ENat.lt_add_one_iff (ENat.natCast_ne_top r)]
    exact ⟨fun hc ↦ ⟨hc.ge, hc.le⟩, fun hc ↦ le_antisymm hc.2 hc.1⟩
  have hsub : {c | ((r + 1 : ℕ) : ℕ∞) ≤ v c} ⊆ {c | (r : ℕ∞) ≤ v c} :=
    ofPred_subset_ofPred.2 fun c hc ↦ le_trans (by norm_cast; omega) hc
  have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  have hball (s : ℕ) : μ (j '' {c | (s : ℕ∞) ≤ v c}) = 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ s :=
    measure_image_setOf_le_addVal_sum_algebraMap_mul_pow_sub μ h hμ hϖ hn y s
  rw [hsphere, image_sdiff hj, measure_sdiff (image_mono hsub)
    (measurableSet_image_setOf_le_addVal_sum_algebraMap_mul_pow_sub h hϖ hn y _).nullMeasurableSet
    (hball _ ▸ ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq)), hball, hball]
  simp only [one_div]
  rw [ENNReal.mul_sub fun _ _ ↦ ENNReal.inv_ne_top.2 (pow_ne_zero _ hq), mul_one, pow_succ,
    ENNReal.mul_inv (.inl (pow_ne_zero _ hq))
      (.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]

/-- In a totally ramified extension, with `n = e(L/K)`, the monic polynomials `g` of degree `n`
over `𝒪[K]` with `r ≤ v_L(g(ϖ))`, identified with their lower coefficients, form a measurable
subset of `Fin n → K`. -/
theorem measurableSet_image_setOf_le_addVal_aeval_monicOfCoeff (h : IsTotallyRamified K L)
    (hϖ : Irreducible ϖ) (hn : ramificationIndex K L = n) (r : ℕ) :
    MeasurableSet ((fun c : Fin n → 𝒪[K] ↦ fun i ↦ (c i : K)) ''
      {c | (r : ℕ∞) ≤ addVal 𝒪[L] (aeval ϖ (monicOfCoeff c))}) := by
  rw [setOf_le_addVal_aeval_monicOfCoeff_eq]
  exact measurableSet_image_setOf_le_addVal_sum_algebraMap_mul_pow_sub h hϖ hn _ r

/-- **The volume of the monic polynomials with a small value at a uniformizer.** In a totally
ramified extension `L/K` with uniformizer `ϖ` and `n = e(L/K) = [L : K]`, and for a left-invariant
measure on `Fin n → K` normalized on the integer box, the monic polynomials `g` of degree `n` over
`𝒪[K]` with `r ≤ v_L(g(ϖ))`, identified with their lower coefficients, have volume `q ^ (-r)`,
where `q = Nat.card 𝓀[K]`. -/
theorem measure_image_setOf_le_addVal_aeval_monicOfCoeff (h : IsTotallyRamified K L)
    (hμ : μ (integerBox K (Fin n)) = 1) (hϖ : Irreducible ϖ) (hn : ramificationIndex K L = n)
    (r : ℕ) :
    μ ((fun c : Fin n → 𝒪[K] ↦ fun i ↦ (c i : K)) ''
        {c | (r : ℕ∞) ≤ addVal 𝒪[L] (aeval ϖ (monicOfCoeff c))}) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ r := by
  rw [setOf_le_addVal_aeval_monicOfCoeff_eq]
  exact measure_image_setOf_le_addVal_sum_algebraMap_mul_pow_sub μ h hμ hϖ hn _ r

end IsTotallyRamified

end TauCeti
