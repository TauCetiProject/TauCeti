module

public import TauCeti.Probability.Exchangeability.L2.Covariance

/-!
# Two-window L² bounds for block averages of a contractable sequence

This file continues the Layer 3 (L²) lane of the Exchangeability roadmap
(`TauCetiRoadmap/Exchangeability/README.md`, "Layer 3: L² averaging library and the
standard-Borel de Finetti route"), building the "two-window L² bounds for block averages"
milestone (`l2_bound_two_windows_uniform`) on top of the uniform covariance structure of a
contractable L² sequence (`contractable_covariance_structure`).

For a real-valued process `X : ℕ → Ω → ℝ` and an injective finite selection `k : Fin n → ℕ`,
the *block average* `blockAverage X k = n⁻¹ • ∑ i, X (k i)` is the empirical mean of the block
`(X (k i))ᵢ`. When `X` is contractable with `L²` coordinates, its second-moment structure is
uniform: all coordinate variances agree and all off-diagonal covariances agree
(`contractable_covariance_structure`). Writing `v = Var[X 0]` and `c = cov[X 0, X 1]`, this
uniformity forces the block average to have the explicit variance

```text
Var[blockAverage X k] = (v - c) / n + c,
```

and any two blocks over *disjoint* index sets to have covariance exactly `c`. Consequently two
disjoint block averages of equal length `n` differ, in `L²`, by an amount that vanishes like
`1 / n`:

```text
Var[blockAverage X k - blockAverage X k'] = 2 (v - c) / n,
```

and, since contractability makes the two averages share the common mean `μ[X 0]`, this is the
squared `L²` distance `∫ (blockAverage X k - blockAverage X k')² dμ` itself. This two-window
bound is the analytic engine that later drives the L² convergence of block averages toward the
directing measure.

The covariance/variance bilinearity (`ProbabilityTheory.covariance_sum_sum`,
`variance_sum`, `covariance_smul_left`, `variance_const_mul`) and the integral manipulations are
Mathlib's; the contractability input is the Layer 0/3 API in
`TauCeti.Probability.Exchangeability.Contractability` and
`TauCeti.Probability.Exchangeability.L2.Covariance`. No material from
`cameronfreer/exchangeability` is reused: the source carries the block-average bounds through a
different, sequence-specific `L²` development, whereas this file records the closed-form
second-moment identities directly.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The **block average** of a real-valued process `X` over a finite selection `k : Fin n → ℕ`:
the empirical mean `n⁻¹ • ∑ i, X (k i)` of the block `(X (k i))ᵢ`. -/
def blockAverage (X : ℕ → Ω → ℝ) {n : ℕ} (k : Fin n → ℕ) : Ω → ℝ :=
  (n : ℝ)⁻¹ • ∑ i, X (k i)

omit [MeasurableSpace Ω] in
@[simp]
theorem blockAverage_apply {n : ℕ} (k : Fin n → ℕ) (ω : Ω) :
    blockAverage X k ω = (n : ℝ)⁻¹ * ∑ i, X (k i) ω := by
  simp [blockAverage, Finset.sum_apply]

/-- A block average of `L²` coordinates is itself `L²`. -/
theorem memLp_blockAverage (hX_L2 : ∀ n, MemLp (X n) 2 μ) {n : ℕ} (k : Fin n → ℕ) :
    MemLp (blockAverage X k) 2 μ :=
  (memLp_finsetSum' _ fun i _ => hX_L2 (k i)).const_smul _

/-- The double sum of block covariances splits along the diagonal into the common variance and
the common off-diagonal covariance of a contractable `L²` sequence. -/
private theorem sum_sum_cov_eq (hX : Contractable μ X)
    (hmeas : ∀ m, AEMeasurable (X m) μ) {n : ℕ} {k : Fin n → ℕ} (hk : Function.Injective k) :
    ∑ i, ∑ j, cov[X (k i), X (k j); μ]
      = (n : ℝ) ^ 2 * cov[X 0, X 1; μ] + n * (Var[X 0; μ] - cov[X 0, X 1; μ]) := by
  have hcov : ∀ i j : Fin n, cov[X (k i), X (k j); μ]
      = cov[X 0, X 1; μ] + (if i = j then Var[X 0; μ] - cov[X 0, X 1; μ] else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, covariance_self (hmeas _), hX.variance_coord_eq (hmeas _) (hmeas 0)]
      ring
    · rw [if_neg hij, hX.covariance_eq_of_ne (hmeas _) (hmeas _) (hmeas 0) (hmeas 1)
        (fun h => hij (hk h)) (by norm_num)]
      ring
  simp_rw [hcov]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The variance of a block average of a contractable L² sequence.** For a contractable
real-valued process with `L²` coordinates and an injective selection `k : Fin n → ℕ` (`0 < n`),
the block average has the closed-form variance `(v - c) / n + c`, where `v = Var[X 0]` is the
common coordinate variance and `c = cov[X 0, X 1]` is the common off-diagonal covariance. -/
theorem Contractable.variance_blockAverage [IsFiniteMeasure μ] (hX : Contractable μ X)
    (hX_L2 : ∀ n, MemLp (X n) 2 μ) {n : ℕ} (hn : 0 < n) {k : Fin n → ℕ}
    (hk : Function.Injective k) :
    Var[blockAverage X k; μ] = (Var[X 0; μ] - cov[X 0, X 1; μ]) / n + cov[X 0, X 1; μ] := by
  have hmeas : ∀ m, AEMeasurable (X m) μ := fun m => (hX_L2 m).aestronglyMeasurable.aemeasurable
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [blockAverage, variance_smul, variance_sum (fun i => hX_L2 (k i)),
    sum_sum_cov_eq hX hmeas hk]
  field_simp
  ring

/-- **The mean of a block average of a contractable process.** A block average over any injective
selection of length `0 < n` has the common coordinate mean `μ[X 0]`. -/
theorem Contractable.integral_blockAverage [IsFiniteMeasure μ] (hX : Contractable μ X)
    (hX_L2 : ∀ n, MemLp (X n) 2 μ) {n : ℕ} (hn : 0 < n) {k : Fin n → ℕ} :
    μ[blockAverage X k] = μ[X 0] := by
  have hint : ∀ m, Integrable (X m) μ := fun m => (hX_L2 m).integrable one_le_two
  have hmeas : ∀ m, AEMeasurable (X m) μ := fun m => (hX_L2 m).aestronglyMeasurable.aemeasurable
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp_rw [blockAverage_apply]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hint (k i))]
  simp_rw [fun i => hX.integral_coord_eq (hmeas (k i)) (hmeas 0)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hne, one_mul]

/-- **The covariance of two disjoint block averages of a contractable L² sequence.** Two block
averages over injective selections `k, k' : Fin n → ℕ` with disjoint ranges (`0 < n`) have
covariance exactly the common off-diagonal covariance `c = cov[X 0, X 1]`. -/
theorem Contractable.covariance_blockAverage_disjoint [IsFiniteMeasure μ] (hX : Contractable μ X)
    (hX_L2 : ∀ n, MemLp (X n) 2 μ) {n : ℕ} (hn : 0 < n) {k k' : Fin n → ℕ}
    (hdisj : ∀ i j, k i ≠ k' j) :
    cov[blockAverage X k, blockAverage X k'; μ] = cov[X 0, X 1; μ] := by
  have hmeas : ∀ m, AEMeasurable (X m) μ := fun m => (hX_L2 m).aestronglyMeasurable.aemeasurable
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [blockAverage, blockAverage, covariance_smul_left, covariance_smul_right,
    covariance_sum_sum (fun i => hX_L2 (k i)) (fun j => hX_L2 (k' j))]
  simp_rw [fun i j => hX.covariance_eq_of_ne (hmeas (k i)) (hmeas (k' j)) (hmeas 0) (hmeas 1)
    (hdisj i j) (by norm_num : (0 : ℕ) ≠ 1)]
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    nsmul_eq_mul]
  field_simp

/-- **The two-window L² bound for block averages.** For a contractable real-valued process with
`L²` coordinates, two block averages over injective selections `k, k' : Fin n → ℕ` of the same
length with disjoint ranges (`0 < n`) satisfy

```text
Var[blockAverage X k - blockAverage X k'] = 2 (v - c) / n,
```

where `v = Var[X 0]` and `c = cov[X 0, X 1]`. The bound vanishes like `1 / n`, which is the
analytic core of the L² route to de Finetti's theorem. -/
theorem l2_bound_two_windows_uniform [IsFiniteMeasure μ] (hX : Contractable μ X)
    (hX_L2 : ∀ n, MemLp (X n) 2 μ) {n : ℕ} (hn : 0 < n) {k k' : Fin n → ℕ}
    (hk : Function.Injective k) (hk' : Function.Injective k') (hdisj : ∀ i j, k i ≠ k' j) :
    Var[blockAverage X k - blockAverage X k'; μ] = 2 * (Var[X 0; μ] - cov[X 0, X 1; μ]) / n := by
  rw [variance_sub (memLp_blockAverage hX_L2 k) (memLp_blockAverage hX_L2 k'),
    hX.variance_blockAverage hX_L2 hn hk, hX.variance_blockAverage hX_L2 hn hk',
    hX.covariance_blockAverage_disjoint hX_L2 hn hdisj]
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

/-- **The two-window L² distance for block averages.** Since two disjoint block averages of a
contractable process share the common mean `μ[X 0]`, the two-window variance bound is the
squared `L²` distance between them:

```text
∫ (blockAverage X k - blockAverage X k')² dμ = 2 (v - c) / n.
```
-/
theorem integral_sq_blockAverage_sub_of_disjoint [IsFiniteMeasure μ] (hX : Contractable μ X)
    (hX_L2 : ∀ n, MemLp (X n) 2 μ) {n : ℕ} (hn : 0 < n) {k k' : Fin n → ℕ}
    (hk : Function.Injective k) (hk' : Function.Injective k') (hdisj : ∀ i j, k i ≠ k' j) :
    ∫ ω, (blockAverage X k ω - blockAverage X k' ω) ^ 2 ∂μ
      = 2 * (Var[X 0; μ] - cov[X 0, X 1; μ]) / n := by
  have hmean : μ[blockAverage X k - blockAverage X k'] = 0 := by
    simp only [Pi.sub_apply]
    rw [integral_sub ((memLp_blockAverage hX_L2 k).integrable one_le_two)
      ((memLp_blockAverage hX_L2 k').integrable one_le_two),
      hX.integral_blockAverage hX_L2 hn (k := k), hX.integral_blockAverage hX_L2 hn (k := k'),
      sub_self]
  have hae : AEMeasurable (blockAverage X k - blockAverage X k') μ :=
    ((memLp_blockAverage hX_L2 k).sub
      (memLp_blockAverage hX_L2 k')).aestronglyMeasurable.aemeasurable
  have hvar := variance_eq_integral (μ := μ) (X := blockAverage X k - blockAverage X k') hae
  rw [hmean] at hvar
  simp only [Pi.sub_apply, sub_zero] at hvar
  rw [← hvar, l2_bound_two_windows_uniform hX hX_L2 hn hk hk' hdisj]

end Probability

end TauCeti
