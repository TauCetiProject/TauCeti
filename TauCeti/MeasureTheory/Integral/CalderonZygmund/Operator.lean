/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.CalderonZygmund.InnerProductSpace
public import TauCeti.MeasureTheory.Function.L2Space

/-!
# Calderón–Zygmund operators

A **Calderón–Zygmund operator** on a finite-dimensional real inner product space `V` of dimension
`n` is a bounded linear operator `T` on `L²(V)` which, away from the support of its argument, is
integration against a **standard kernel** `K`: `‖K x y‖ ≤ C / dist x y ^ n`, `K` is `δ`-Hölder in
each variable off the diagonal at the scale of `dist x y`, and `T f x = ∫ K x y f y dy` for almost
every `x` outside a compact set carrying `f` (`TauCeti.HasStandardKernel`). This file proves the
basic theorems about this class.

* **Adjoints.** The adjoint of an `L²` operator with an off-diagonal kernel `k` has the transposed
  kernel `(x, y) ↦ (k y x)†` (`ContinuousLinearMap.ae_adjoint_apply_eq_integral`), in any proper
  metric measure space and for operator-valued kernels; only boundedness of `k` away from the
  diagonal is needed. Hence the adjoint of a Calderón–Zygmund operator with kernel `K` is a
  Calderón–Zygmund operator with the kernel `(x, y) ↦ conj (K y x)` and the same constants
  (`TauCeti.HasStandardKernel.adjoint`).
* **The Calderón–Zygmund theorem.** A Calderón–Zygmund operator is of weak type `(1, 1)`
  (`TauCeti.HasStandardKernel.exists_mul_volume_lt_enorm_le`) and bounded in the `Lᵖ` norm for
  every `1 < p < ∞` (`TauCeti.HasStandardKernel.exists_eLpNorm_le`). These are the real
  Calderón–Zygmund theorems on `V`
  (`ContinuousLinearMap.exists_mul_volume_lt_enorm_le_of_norm_sub_le_mul_rpow`,
  `ContinuousLinearMap.exists_eLpNorm_le_of_norm_sub_le_mul_rpow`), whose hypotheses on the
  adjoint the adjoint theorem supplies.
* **Examples.** The identity has the kernel `0` (`TauCeti.hasStandardKernel_id`), and the Riesz
  transforms are Calderón–Zygmund operators (`TauCeti.hasStandardKernel_rieszTransform`).

The definition asks nothing of `K` on the diagonal, and no measurability: the smoothness estimate
makes `K` continuous off the diagonal (`TauCeti.HasStandardKernel.continuousOn_uncurry`), which is
all the measure theory needs. Boundedness on `L²` is part of the definition, since the kernel
estimates do not imply it: multiplication by `x` on `ℝ` has the kernel `0` off the diagonal and is
unbounded.

## References

* E. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory Integrals*,
  Chapter I, §6, and Chapter VII, §3.
* L. Grafakos, *Classical Fourier Analysis*, Section 5.3 (standard kernels and the
  Calderón–Zygmund theorem, Theorem 5.3.3).
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate Topology

namespace ContinuousLinearMap

section Integrability

variable {𝕜 V H K : Type*} [RCLike 𝕜] [MeasurableSpace V] {μ : Measure V}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-- An operator-valued function, bounded on `t`, applied to an integrable function vanishing
outside `t` is integrable. -/
private theorem integrable_apply_of_norm_le {A : V → H →L[𝕜] K} (hA : StronglyMeasurable A)
    {f : V → H} (hf : Integrable f μ) {t : Set V} {M : ℝ} (hM : ∀ y ∈ t, ‖A y‖ ≤ M)
    (hft : ∀ᵐ y ∂μ, y ∉ t → f y = 0) : Integrable (fun y ↦ A y (f y)) μ := by
  refine (hf.norm.const_mul M).mono'
    ((isBoundedBilinearMap_apply.continuous).comp_aestronglyMeasurable
      (hA.aestronglyMeasurable.prodMk hf.aestronglyMeasurable)) ?_
  filter_upwards [hft] with y hy
  by_cases hyt : y ∈ t
  · exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hM y hyt) (norm_nonneg _))
  · simp [hy hyt]

/-- The integrand `⟪g z, k z y (φ y)⟫` of the double integral pairing `g` with `T φ` is integrable
on the product when `g` and `φ` are integrable and vanish outside sets on whose product `k` is
bounded. -/
private theorem integrable_inner_apply {k : V → V → H →L[𝕜] K}
    (hkm : StronglyMeasurable (Function.uncurry k)) {s t : Set V} {M : ℝ}
    (hM : ∀ x ∈ s, ∀ y ∈ t, ‖k x y‖ ≤ M) {g : V → K} (hgi : Integrable g μ)
    (hg : ∀ᵐ x ∂μ, x ∉ s → g x = 0) {φ : V → H} (hφi : Integrable φ μ)
    (hφ : ∀ᵐ x ∂μ, x ∉ t → φ x = 0) :
    Integrable (fun p : V × V ↦ ⟪g p.1, k p.1 p.2 (φ p.2)⟫_𝕜) (μ.prod μ) := by
  have hm : AEStronglyMeasurable (fun p : V × V ↦ k p.1 p.2 (φ p.2)) (μ.prod μ) :=
    (isBoundedBilinearMap_apply.continuous).comp_aestronglyMeasurable
      (hkm.aestronglyMeasurable.prodMk
        (hφi.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))
  refine ((hgi.norm.mul_prod hφi.norm).const_mul M).mono'
    ((hgi.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst).inner hm) ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hg,
    Measure.quasiMeasurePreserving_snd.ae hφ] with p hp₁ hp₂
  by_cases h₁ : p.1 ∈ s
  · by_cases h₂ : p.2 ∈ t
    · calc ‖⟪g p.1, k p.1 p.2 (φ p.2)⟫_𝕜‖ ≤ ‖g p.1‖ * (‖k p.1 p.2‖ * ‖φ p.2‖) :=
            (norm_inner_le_norm _ _).trans
              (mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _))
        _ ≤ ‖g p.1‖ * (M * ‖φ p.2‖) := by
            gcongr
            exact hM _ h₁ _ h₂
        _ = M * (‖g p.1‖ * ‖φ p.2‖) := by ring
    · simp [hp₂ h₂]
  · simp [hp₁ h₁]

end Integrability

section Adjoint

variable {𝕜 V H K : Type*} [RCLike 𝕜] [MetricSpace V] [ProperSpace V] [MeasurableSpace V]
  [BorelSpace V] {μ : Measure V} [IsFiniteMeasureOnCompacts μ]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] [NormedSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K] [NormedSpace ℝ K]

omit [BorelSpace V] in
/-- The pairing identity behind `ContinuousLinearMap.ae_adjoint_apply_eq_integral`: against a test
function `φ` vanishing outside a compact set `t` disjoint from the compact set `s` outside which
`g` vanishes, `T† g` pairs like the integral of the transposed kernel. -/
private theorem integral_inner_adjoint_apply_eq (T : Lp H 2 μ →L[𝕜] Lp K 2 μ)
    {k : V → V → H →L[𝕜] K} (hkm : StronglyMeasurable (Function.uncurry k))
    (hrep : ∀ (f : Lp H 2 μ) (s : Set V), IsCompact s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → T f x = ∫ z, k x z (f z) ∂μ)
    {s t : Set V} (hs : IsCompact s) (ht : IsCompact t) (hst : Disjoint s t) {M : ℝ}
    (hM : ∀ x ∈ s, ∀ y ∈ t, ‖k x y‖ ≤ M) {g : Lp K 2 μ} (hg : ∀ᵐ x ∂μ, x ∉ s → g x = 0)
    {φ : Lp H 2 μ} (hφ : ∀ᵐ x ∂μ, x ∉ t → φ x = 0) :
    ∫ y, ⟪adjoint T g y, φ y⟫_𝕜 ∂μ = ∫ y, ⟪∫ z, adjoint (k z y) (g z) ∂μ, φ y⟫_𝕜 ∂μ := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs.measure_lt_top.ne
  have : IsFiniteMeasure (μ.restrict t) := isFiniteMeasure_restrict.2 ht.measure_lt_top.ne
  have hgi : Integrable g μ := IntegrableOn.integrable_of_ae_notMem_eq_zero
    (((Lp.memLp g).restrict s).integrable one_le_two) hg
  have hφi : Integrable φ μ := IntegrableOn.integrable_of_ae_notMem_eq_zero
    (((Lp.memLp φ).restrict t).integrable one_le_two) hφ
  calc ∫ y, ⟪adjoint T g y, φ y⟫_𝕜 ∂μ = ⟪adjoint T g, φ⟫_𝕜 := (L2.inner_def _ _).symm
    _ = ⟪g, T φ⟫_𝕜 := adjoint_inner_left _ _ _
    _ = ∫ z, ⟪g z, T φ z⟫_𝕜 ∂μ := L2.inner_def _ _
    _ = ∫ z, ∫ y, ⟪g z, k z y (φ y)⟫_𝕜 ∂μ ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hg, hrep φ t ht hφ] with z hgz hTz
      by_cases hz : z ∈ s
      · rw [hTz (disjoint_left.1 hst hz)]
        exact (integral_inner (integrable_apply_of_norm_le
          (hkm.comp_measurable measurable_prodMk_left) hφi (hM z hz) hφ) (g z)).symm
      · simp [hgz hz]
    _ = ∫ y, ∫ z, ⟪g z, k z y (φ y)⟫_𝕜 ∂μ ∂μ :=
      integral_integral_swap (integrable_inner_apply hkm hM hgi hg hφi hφ)
    _ = ∫ y, ⟪∫ z, adjoint (k z y) (g z) ∂μ, φ y⟫_𝕜 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hφ] with y hy
      by_cases hyt : y ∈ t
      · have hint : Integrable (fun z ↦ adjoint (k z y) (g z)) μ :=
          integrable_apply_of_norm_le
            ((adjoint : (H →L[𝕜] K) ≃ₗᵢ⋆[𝕜] (K →L[𝕜] H)).continuous.comp_stronglyMeasurable
              (hkm.comp_measurable measurable_prodMk_right)) hgi
            (fun z hz ↦ (LinearIsometryEquiv.norm_map _ _).trans_le (hM z hz y hyt)) hg
        simp_rw [← adjoint_inner_left (k _ y)]
        rw [← inner_conj_symm, ← integral_inner hint, ← integral_conj]
        simp_rw [inner_conj_symm]
      · simp [hy hyt]

omit [NormedSpace ℝ K] in
/-- On a compact set `t` such that `k` is bounded on `s × t`, where `g` vanishes outside `s`, the
transposed kernel integral `x ↦ ∫ (k z x)† (g z) dz` is bounded, so its restriction to `t` lies in
`L²`. -/
private theorem memLp_indicator_integral_adjoint_apply {k : V → V → H →L[𝕜] K}
    (hkm : StronglyMeasurable (Function.uncurry k)) {s t : Set V} (hs : IsCompact s)
    (ht : IsCompact t) {M : ℝ} (hM : ∀ x ∈ s, ∀ y ∈ t, ‖k x y‖ ≤ M) {g : Lp K 2 μ}
    (hg : ∀ᵐ x ∂μ, x ∉ s → g x = 0) :
    MemLp (t.indicator fun x ↦ ∫ z, adjoint (k z x) (g z) ∂μ) 2 μ := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs.measure_lt_top.ne
  have : IsFiniteMeasure (μ.restrict t) := isFiniteMeasure_restrict.2 ht.measure_lt_top.ne
  refine (memLp_indicator_iff_restrict ht.measurableSet.nullMeasurableSet).2 ?_
  refine MemLp.of_bound (C := M * ∫ z, ‖g z‖ ∂μ) (AEStronglyMeasurable.restrict ?_)
    ((ae_restrict_iff' ht.measurableSet).2 (.of_forall fun x hx ↦ ?_))
  · exact AEStronglyMeasurable.integral_prod_right'
      (f := fun p : V × V ↦ adjoint (k p.2 p.1) (g p.2))
      ((isBoundedBilinearMap_apply.continuous).comp_aestronglyMeasurable
        (((adjoint : (H →L[𝕜] K) ≃ₗᵢ⋆[𝕜] (K →L[𝕜] H)).continuous.comp_stronglyMeasurable
          (hkm.comp_measurable measurable_swap)).aestronglyMeasurable.prodMk
          ((Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving
            Measure.quasiMeasurePreserving_snd)))
  · rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le ((IntegrableOn.integrable_of_ae_notMem_eq_zero
      (((Lp.memLp g).restrict s).integrable one_le_two) hg).norm.const_mul M) ?_
    filter_upwards [hg] with z hz
    by_cases hzs : z ∈ s
    · refine (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact (LinearIsometryEquiv.norm_map _ _).trans_le (hM z hzs x hx)
    · simp [hz hzs]

/-- The local form of `ContinuousLinearMap.ae_adjoint_apply_eq_integral`: the identity holds almost
everywhere on every compact set `t` disjoint from `s`. -/
private theorem ae_adjoint_apply_eq_integral_of_disjoint (T : Lp H 2 μ →L[𝕜] Lp K 2 μ)
    {k : V → V → H →L[𝕜] K} (hkm : StronglyMeasurable (Function.uncurry k))
    (hrep : ∀ (f : Lp H 2 μ) (s : Set V), IsCompact s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → T f x = ∫ z, k x z (f z) ∂μ)
    {s t : Set V} (hs : IsCompact s) (ht : IsCompact t) (hst : Disjoint s t) {M : ℝ}
    (hM : ∀ x ∈ s, ∀ y ∈ t, ‖k x y‖ ≤ M) {g : Lp K 2 μ} (hg : ∀ᵐ x ∂μ, x ∉ s → g x = 0) :
    ∀ᵐ x ∂μ, x ∈ t → adjoint T g x = ∫ z, adjoint (k z x) (g z) ∂μ := by
  have hψ := memLp_indicator_integral_adjoint_apply hkm hs ht hM hg
  -- `w = T† g - ψ` is orthogonal to its restriction `φ` to `t`, so `φ = 0`.
  set w := adjoint T g - hψ.toLp _
  have hφ := (Lp.memLp w).indicator (s := t) ht.measurableSet.nullMeasurableSet
  have hφt : ∀ᵐ x ∂μ, x ∉ t → hφ.toLp _ x = 0 := by
    filter_upwards [hφ.coeFn_toLp] with x hx hxt
    rw [hx, indicator_of_notMem hxt]
  have hwφ : ⟪w, hφ.toLp _⟫_𝕜 = 0 := by
    rw [inner_sub_left, L2.inner_def, L2.inner_def,
      integral_inner_adjoint_apply_eq T hkm hrep hs ht hst hM hg hφt, sub_eq_zero]
    refine integral_congr_ae ?_
    filter_upwards [hψ.coeFn_toLp, hφt] with x hx hxφ
    by_cases hxt : x ∈ t
    · rw [hx, indicator_of_mem hxt]
    · rw [hxφ hxt, inner_zero_right, inner_zero_right]
  have hφ0 : ∀ᵐ x ∂μ, hφ.toLp _ x = 0 := by
    have : hφ.toLp _ = 0 := by
      refine (inner_self_eq_zero (𝕜 := 𝕜)).1 ?_
      rw [← hwφ, L2.inner_def, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hφ.coeFn_toLp] with x hx
      by_cases hxt : x ∈ t
      · rw [hx, indicator_of_mem hxt]
      · rw [hx, indicator_of_notMem hxt, inner_zero_left, inner_zero_right]
    rw [this]
    filter_upwards [Lp.coeFn_zero H 2 μ] with x hx
    rw [hx, Pi.zero_apply]
  filter_upwards [hφ.coeFn_toLp, hφ0, hψ.coeFn_toLp, Lp.coeFn_sub (adjoint T g) (hψ.toLp _)]
    with x hxφ hx0 hxψ hxw hxt
  rw [hx0, indicator_of_mem hxt, hxw, Pi.sub_apply, hxψ, indicator_of_mem hxt, eq_comm,
    sub_eq_zero] at hxφ
  exact hxφ

/-- **The kernel of the adjoint.** Let `T` be a bounded operator `L²(V, H) → L²(V, K)` given by a
kernel `k` away from the support of its argument: if `f` vanishes outside a compact set `s`, then
`T f x = ∫ k x z (f z) dz` for almost every `x ∉ s`. If `k` is bounded on the pairs of points at
distance at least `r`, for every `r > 0`, then the adjoint is given in the same way by the
transposed kernel `(x, z) ↦ (k z x)†`: if `g` vanishes outside a compact set `s`, then
`T† g x = ∫ (k z x)† (g z) dz` for almost every `x ∉ s`.

For scalar kernels this is the familiar statement that the adjoint of an integral operator with
kernel `K (x, y)` has the kernel `conj (K (y, x))`. Only the kernel of `T` enters, and no size or
smoothness estimate beyond boundedness away from the diagonal. -/
theorem ae_adjoint_apply_eq_integral (T : Lp H 2 μ →L[𝕜] Lp K 2 μ)
    {k : V → V → H →L[𝕜] K} (hkm : StronglyMeasurable (Function.uncurry k))
    (hk : ∀ r > 0, ∃ M, ∀ x y, r ≤ dist x y → ‖k x y‖ ≤ M)
    (hrep : ∀ (f : Lp H 2 μ) (s : Set V), IsCompact s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → T f x = ∫ z, k x z (f z) ∂μ)
    (g : Lp K 2 μ) {s : Set V} (hs : IsCompact s) (hg : ∀ᵐ x ∂μ, x ∉ s → g x = 0) :
    ∀ᵐ x ∂μ, x ∉ s → adjoint T g x = ∫ z, adjoint (k z x) (g z) ∂μ := by
  -- The complement of `s` is covered by the compact sets `t m` at distance at least `1 / (m + 1)`
  -- from `s`, and the identity holds almost everywhere on each of them.
  set t : ℕ → Set V := fun m ↦ compactCovering V m ∩ {x | ∀ y ∈ s, ((m : ℝ) + 1)⁻¹ ≤ dist x y}
  have hloc : ∀ m, ∀ᵐ x ∂μ, x ∈ t m → adjoint T g x = ∫ z, adjoint (k z x) (g z) ∂μ := by
    intro m
    have hc : (0 : ℝ) < ((m : ℝ) + 1)⁻¹ := by positivity
    have ht : IsCompact (t m) := by
      refine (isCompact_compactCovering V m).inter_right ?_
      simp only [ofPred_forall]
      exact isClosed_biInter fun y _ ↦ isClosed_le continuous_const
        (continuous_id.dist continuous_const)
    have hst : Disjoint s (t m) := disjoint_left.2 fun x hxs hxt ↦
      (hc.trans_le (hxt.2 x hxs)).ne' (dist_self x)
    obtain ⟨M, hM⟩ := hk _ hc
    exact ae_adjoint_apply_eq_integral_of_disjoint T hkm hrep hs ht hst
      (fun x hx y hy ↦ hM x y (by rw [dist_comm]; exact hy.2 x hx)) hg
  filter_upwards [ae_all_iff.2 hloc] with x hx hxs
  obtain ⟨m₁, hm₁⟩ := exists_mem_compactCovering x
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hs.isClosed.isOpen_compl x hxs
  obtain ⟨m₂, hm₂⟩ := exists_nat_one_div_lt hε
  refine hx (max m₁ m₂) ⟨compactCovering_subset V (le_max_left _ _) hm₁, fun y hy ↦ ?_⟩
  refine le_trans ?_ (not_lt.1 fun hlt ↦ hball (mem_ball'.2 hlt) hy)
  rw [← one_div]
  refine hm₂.le.trans' (one_div_le_one_div_of_le (by positivity) ?_)
  exact_mod_cast Nat.succ_le_succ (le_max_right m₁ m₂)

end Adjoint

end ContinuousLinearMap

namespace TauCeti

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **Calderón–Zygmund operators.** A bounded operator `T` on `L²(V, F)` **has the standard kernel**
`K` with constant `C` and exponent `δ > 0` when, writing `n` for the dimension of `V`,

* `K` satisfies the size estimate `‖K x y‖ ≤ C / dist x y ^ n` for `x ≠ y`;
* `K` satisfies the smoothness estimate in both variables,
  `‖K x y - K x y'‖ + ‖K y x - K y' x‖ ≤ C dist y y' ^ δ / dist x y ^ (n + δ)` whenever
  `2 dist y y' < dist x y`;
* `T` is given by `K` away from the support of its argument: if `f` vanishes outside a compact
  set `s`, then `T f x = ∫ K x y • f y dy` for almost every `x ∉ s`.

Such a `T` is a **Calderón–Zygmund operator**. Boundedness on `L²` is part of the data, since the
kernel estimates alone do not imply it: multiplication by `x` on `ℝ` has the kernel `0` off the
diagonal but is unbounded on `L²`. The kernel acts on `F`-valued functions by scalar
multiplication, as the Riesz transforms do. -/
structure HasStandardKernel (T : Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V))
    (K : V → V → ℂ) (C : ℝ≥0) (δ : ℝ) : Prop where
  /-- The smoothness exponent is positive. -/
  exponent_pos : 0 < δ
  /-- The size estimate. -/
  norm_le : ∀ x y, x ≠ y → ‖K x y‖ ≤ C / dist x y ^ Module.finrank ℝ V
  /-- The smoothness estimate in both variables. -/
  norm_sub_add_norm_sub_le : ∀ x y y', 2 * dist y y' < dist x y →
    ‖K x y - K x y'‖ + ‖K y x - K y' x‖ ≤
      C * dist y y' ^ δ / dist x y ^ (Module.finrank ℝ V + δ)
  /-- `T` is integration against `K` away from the support of its argument. -/
  ae_apply_eq_integral : ∀ (f : Lp F 2 (volume : Measure V)) (s : Set V), IsCompact s →
    (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → T f x = ∫ y, K x y • f y

namespace HasStandardKernel

variable {T : Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V)} {K : V → V → ℂ}
  {C : ℝ≥0} {δ : ℝ}

/-- The estimates of a standard kernel persist under a larger constant. -/
theorem mono (h : HasStandardKernel T K C δ) {C' : ℝ≥0} (hC : C ≤ C') :
    HasStandardKernel T K C' δ where
  exponent_pos := h.exponent_pos
  norm_le x y hxy := (h.norm_le x y hxy).trans (by gcongr)
  norm_sub_add_norm_sub_le x y y' hy := (h.norm_sub_add_norm_sub_le x y y' hy).trans (by gcongr)
  ae_apply_eq_integral := h.ae_apply_eq_integral

/-- A standard kernel is continuous off the diagonal. -/
theorem continuousOn_uncurry (h : HasStandardKernel T K C δ) :
    ContinuousOn (Function.uncurry K) {p : V × V | p.1 ≠ p.2} := by
  rintro ⟨x₀, y₀⟩ (hxy : x₀ ≠ y₀)
  refine ContinuousAt.continuousWithinAt ?_
  have hd : 0 < dist x₀ y₀ := dist_pos.2 hxy
  set n : ℝ := (Module.finrank ℝ V : ℝ)
  -- The two smoothness estimates bound the oscillation of `K` near `(x₀, y₀)` by `b`.
  set b : V × V → ℝ := fun p ↦ C * dist p.2 y₀ ^ δ / dist p.1 p.2 ^ (n + δ) +
    C * dist p.1 x₀ ^ δ / dist y₀ p.1 ^ (n + δ)
  have hδ := h.exponent_pos
  have hb : ContinuousAt b (x₀, y₀) := by
    have hpow : ∀ {f : V × V → ℝ}, Continuous f → (∀ p, 0 ≤ f p) → ∀ {e : ℝ}, 0 ≤ e →
        Continuous fun p ↦ f p ^ e := fun hf _ _ he ↦ hf.rpow_const fun _ ↦ Or.inr he
    refine ContinuousAt.add (ContinuousAt.div ?_ ?_ ?_) (ContinuousAt.div ?_ ?_ ?_)
    · exact (continuous_const.mul (hpow (continuous_snd.dist continuous_const)
        (fun _ ↦ dist_nonneg) hδ.le)).continuousAt
    · exact (hpow (continuous_fst.dist continuous_snd) (fun _ ↦ dist_nonneg)
        (by positivity)).continuousAt
    · exact (Real.rpow_pos_of_pos hd _).ne'
    · exact (continuous_const.mul (hpow (continuous_fst.dist continuous_const)
        (fun _ ↦ dist_nonneg) hδ.le)).continuousAt
    · exact (hpow (continuous_const.dist continuous_fst) (fun _ ↦ dist_nonneg)
        (by positivity)).continuousAt
    · exact (Real.rpow_pos_of_pos (dist_comm x₀ y₀ ▸ hd) _).ne'
  have hb0 : b (x₀, y₀) = 0 := by simp [b, Real.zero_rpow hδ.ne']
  have h₁ : ∀ᶠ p : V × V in 𝓝 (x₀, y₀), 2 * dist p.2 y₀ < dist p.1 p.2 :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hd)
  have h₂ : ∀ᶠ p : V × V in 𝓝 (x₀, y₀), 2 * dist p.1 x₀ < dist y₀ p.1 :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa [dist_comm] using hd)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ (hb0 ▸ hb.tendsto)
  filter_upwards [h₁, h₂] with ⟨x, y⟩ hp₁ hp₂
  calc ‖K x y - K x₀ y₀‖ ≤ ‖K x y - K x y₀‖ + ‖K x y₀ - K x₀ y₀‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ b (x, y) := add_le_add
        ((le_add_of_nonneg_right (norm_nonneg _)).trans (h.norm_sub_add_norm_sub_le x y y₀ hp₁))
        ((le_add_of_nonneg_left (norm_nonneg _)).trans (h.norm_sub_add_norm_sub_le y₀ x x₀ hp₂))

/-! ### The kernel modified on the diagonal

The estimates say nothing about `K` on the diagonal, where it need not even be measurable. The
real Calderón–Zygmund theorems take a strongly measurable operator-valued kernel, so they are
applied to `K` set to `0` on the diagonal, which is continuous off the diagonal. The change is
invisible in the integrals `∫ K x y • f y dy` for `x` outside the set carrying `f`. -/

open scoped Classical in
/-- The kernel `K` set to `0` on the diagonal. -/
private def offDiag (K : V → V → ℂ) (x y : V) : ℂ := if x = y then 0 else K x y

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
private theorem offDiag_of_ne {x y : V} (hxy : x ≠ y) : offDiag K x y = K x y := by
  simp [offDiag, hxy]

private theorem stronglyMeasurable_offDiag (h : HasStandardKernel T K C δ) :
    StronglyMeasurable (Function.uncurry (offDiag K)) := by
  classical
  have : Function.uncurry (offDiag K) =
      {p : V × V | p.1 ≠ p.2}.piecewise (Function.uncurry K) 0 := by
    ext ⟨x, y⟩
    by_cases hxy : x = y <;> simp [offDiag, hxy, Set.piecewise]
  rw [this]
  exact (h.continuousOn_uncurry.measurable_piecewise continuousOn_const
    (isOpen_ne_fun continuous_fst continuous_snd).measurableSet).stronglyMeasurable

/-- Changing a kernel on the diagonal does not change its integrals at points outside the set
carrying the integrand. -/
private theorem integral_offDiag_smul (K : V → V → ℂ) {f : V → F} {s : Set V}
    (hf : ∀ᵐ y, y ∉ s → f y = 0) {x : V} (hx : x ∉ s) :
    ∫ y, offDiag K x y • f y = ∫ y, K x y • f y := by
  refine integral_congr_ae ?_
  filter_upwards [hf] with y hy
  by_cases hxy : x = y
  · subst hxy
    simp [hy hx]
  · rw [offDiag_of_ne hxy]

private theorem norm_offDiag_le (h : HasStandardKernel T K C δ) {x y : V} (hxy : x ≠ y) :
    ‖offDiag K x y‖ ≤ C * dist x y ^ (-(Module.finrank ℝ V : ℝ)) := by
  rw [offDiag_of_ne hxy, Real.rpow_neg dist_nonneg, Real.rpow_natCast, ← div_eq_mul_inv]
  exact h.norm_le x y hxy

private theorem norm_offDiag_sub_le (h : HasStandardKernel T K C δ) {x y y' : V}
    (hy : 2 * dist y y' < dist x y') :
    ‖offDiag K x y - offDiag K x y'‖ ≤
      C * (dist y y' ^ δ * dist x y' ^ (-(Module.finrank ℝ V + δ))) := by
  have hxy' : x ≠ y' := dist_pos.1 ((mul_nonneg zero_le_two dist_nonneg).trans_lt hy)
  have hxy : x ≠ y := by
    rintro rfl
    linarith [dist_nonneg (x := x) (y := y')]
  rw [offDiag_of_ne hxy, offDiag_of_ne hxy', norm_sub_rev, Real.rpow_neg dist_nonneg,
    ← mul_assoc, ← div_eq_mul_inv, dist_comm y y']
  exact (le_add_of_nonneg_right (norm_nonneg _)).trans
    (h.norm_sub_add_norm_sub_le x y' y (by rwa [dist_comm y' y]))

variable (F) in
/-- The kernel as an `ℝ`-linear operator-valued kernel, set to `0` on the diagonal, in the form
taken by the real Calderón–Zygmund theorems. -/
private def realKernel (K : V → V → ℂ) (x y : V) : F →L[ℝ] F :=
  offDiag K x y • ContinuousLinearMap.id ℝ F

private theorem stronglyMeasurable_realKernel (h : HasStandardKernel T K C δ) :
    StronglyMeasurable (Function.uncurry (realKernel F K)) :=
  h.stronglyMeasurable_offDiag.smul_const _

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
private theorem norm_realKernel_le' (x y : V) : ‖realKernel F K x y‖ ≤ ‖offDiag K x y‖ := by
  have hid : ‖ContinuousLinearMap.id ℝ F‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  exact (norm_smul_le (offDiag K x y) (ContinuousLinearMap.id ℝ F)).trans
    (mul_le_of_le_one_right (norm_nonneg _) hid)

private theorem norm_realKernel_le (h : HasStandardKernel T K C δ) (x y : V) (hxy : x ≠ y) :
    ‖realKernel F K x y‖ ≤ C * dist x y ^ (-(Module.finrank ℝ V : ℝ)) :=
  (norm_realKernel_le' x y).trans (h.norm_offDiag_le hxy)

private theorem norm_realKernel_sub_le (h : HasStandardKernel T K C δ) (x y y' : V)
    (hy : 2 * dist y y' < dist x y') :
    ‖realKernel F K x y - realKernel F K x y'‖ ≤
      C * (dist y y' ^ δ * dist x y' ^ (-(Module.finrank ℝ V + δ))) := by
  have hid : ‖ContinuousLinearMap.id ℝ F‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  rw [realKernel, realKernel, ← sub_smul]
  exact (norm_smul_le (offDiag K x y - offDiag K x y') (ContinuousLinearMap.id ℝ F)).trans
    ((mul_le_of_le_one_right (norm_nonneg _) hid).trans (h.norm_offDiag_sub_le hy))

private theorem ae_restrictScalars_apply_eq_integral (h : HasStandardKernel T K C δ)
    (f : Lp F 2 (volume : Measure V)) (s : Set V) (hs : IsCompact s)
    (hf : ∀ᵐ x, x ∉ s → f x = 0) :
    ∀ᵐ x, x ∉ s → T.restrictScalars ℝ f x = ∫ z, realKernel F K x z (f z) := by
  filter_upwards [h.ae_apply_eq_integral f s hs hf] with x hx hxs
  rw [ContinuousLinearMap.coe_restrictScalars', hx hxs, ← integral_offDiag_smul K hf hxs]
  simp [realKernel]

/-! ### Adjoints and the Calderón–Zygmund bounds -/

variable [CompleteSpace F]

/-- **Calderón–Zygmund operators are closed under adjoints.** The adjoint of a Calderón–Zygmund
operator with kernel `K` is a Calderón–Zygmund operator with the conjugate transposed kernel
`(x, y) ↦ conj (K y x)`, with the same constants. -/
theorem adjoint (h : HasStandardKernel T K C δ) :
    HasStandardKernel (ContinuousLinearMap.adjoint T) (fun x y ↦ conj (K y x)) C δ where
  exponent_pos := h.exponent_pos
  norm_le x y hxy := by simpa [dist_comm] using h.norm_le y x hxy.symm
  norm_sub_add_norm_sub_le x y y' hy := by
    simpa only [← map_sub, RCLike.norm_conj, add_comm] using h.norm_sub_add_norm_sub_le x y y' hy
  ae_apply_eq_integral g s hs hg := by
    have hk : ∀ r > 0, ∃ M, ∀ x y, r ≤ dist x y →
        ‖offDiag K x y • ContinuousLinearMap.id ℂ F‖ ≤ M := fun r hr ↦
      ⟨C * r ^ (-(Module.finrank ℝ V : ℝ)), fun x y hxy ↦ by
        have hxy' : x ≠ y := dist_pos.1 (hr.trans_le hxy)
        have hid : ‖ContinuousLinearMap.id ℂ F‖ ≤ 1 := ContinuousLinearMap.norm_id_le
        refine (norm_smul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) hid).trans
          ((h.norm_offDiag_le hxy').trans ?_))
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hr hxy (neg_nonpos.2 (Nat.cast_nonneg _))) C.2⟩
    have hrep : ∀ (f : Lp F 2 (volume : Measure V)) (s : Set V), IsCompact s →
        (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s →
          T f x = ∫ z, (offDiag K x z • ContinuousLinearMap.id ℂ F) (f z) := fun f s hs hf ↦ by
      filter_upwards [h.ae_apply_eq_integral f s hs hf] with x hx hxs
      rw [hx hxs, ← integral_offDiag_smul K hf hxs]
      simp
    filter_upwards [ContinuousLinearMap.ae_adjoint_apply_eq_integral T
      (h.stronglyMeasurable_offDiag.smul_const _) hk hrep g hs hg] with x hx hxs
    rw [hx hxs, ← integral_offDiag_smul (fun x y ↦ conj (K y x)) hg hxs]
    refine integral_congr_ae (.of_forall fun z ↦ ?_)
    by_cases hxz : x = z
    · simp [offDiag, hxz]
    · dsimp only
      rw [offDiag_of_ne hxz, offDiag_of_ne (Ne.symm hxz), map_smulₛₗ,
        ContinuousLinearMap.adjoint_id]
      rfl

/-- **Calderón–Zygmund operators are of weak type `(1, 1)`**: there is a constant `A` with
`t · |{x | ‖T f x‖ > t}| ≤ A ‖f‖₁` for every `f ∈ L²` and every `t`. A Calderón–Zygmund operator
need not be bounded on `L¹`, and this is the substitute at the endpoint. -/
theorem exists_mul_volume_lt_enorm_le (h : HasStandardKernel T K C δ) :
    ∃ A : ℝ≥0, ∀ (f : Lp F 2 (volume : Measure V)) (t : ℝ≥0∞),
      t * volume {x | t < ‖T f x‖ₑ} ≤ A * eLpNorm f 1 volume := by
  obtain ⟨A, hA⟩ := ContinuousLinearMap.exists_mul_volume_lt_enorm_le_of_norm_sub_le_mul_rpow
    (T.restrictScalars ℝ) h.stronglyMeasurable_realKernel h.exponent_pos h.norm_realKernel_le
    h.norm_realKernel_sub_le h.ae_restrictScalars_apply_eq_integral
  exact ⟨A, fun f t ↦ by
    rw [eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable f)]
    simpa using hA f t⟩

/-- **Calderón–Zygmund operators are bounded on `Lᵖ`** for `1 < p < ∞`: there is a constant `A`
with `‖T f‖_p ≤ A ‖f‖_p` for every `f ∈ L²`. The adjoint of `T` is a Calderón–Zygmund operator
(`TauCeti.HasStandardKernel.adjoint`), which gives the range `p > 2` by duality. -/
theorem exists_eLpNorm_le (h : HasStandardKernel T K C δ) {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ ∞) :
    ∃ A : ℝ≥0, ∀ f : Lp F 2 (volume : Measure V),
      eLpNorm (T f) p volume ≤ A * eLpNorm f p volume := by
  -- The Calderón–Zygmund theorem is stated for real Hilbert spaces.
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hadj : ContinuousLinearMap.adjoint (T.restrictScalars ℝ) =
      (ContinuousLinearMap.adjoint T).restrictScalars ℝ := by
    refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
    rw [L2.real_inner_eq_re_inner, L2.real_inner_eq_re_inner,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.adjoint_inner_left]
  have h' := h.adjoint
  exact ContinuousLinearMap.exists_eLpNorm_le_of_norm_sub_le_mul_rpow (T.restrictScalars ℝ)
    h.stronglyMeasurable_realKernel h'.stronglyMeasurable_realKernel h.exponent_pos
    h'.exponent_pos h.norm_realKernel_le h'.norm_realKernel_le h.norm_realKernel_sub_le
    h'.norm_realKernel_sub_le h.ae_restrictScalars_apply_eq_integral
    (hadj ▸ h'.ae_restrictScalars_apply_eq_integral) hp hp_top

end HasStandardKernel

/-- The identity is a Calderón–Zygmund operator, with the kernel `0`. -/
theorem hasStandardKernel_id (C : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    HasStandardKernel (ContinuousLinearMap.id ℂ (Lp F 2 (volume : Measure V))) 0 C δ where
  exponent_pos := hδ
  norm_le x y _ := by
    simp only [Pi.zero_apply, norm_zero]
    positivity
  norm_sub_add_norm_sub_le x y y' _ := by
    simp only [Pi.zero_apply, sub_zero, norm_zero, add_zero]
    positivity
  ae_apply_eq_integral f s _ hf := by
    filter_upwards [hf] with x hx hxs
    simp [hx hxs]

end TauCeti
