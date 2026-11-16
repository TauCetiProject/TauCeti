/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.EllipticRegularity
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Lp
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Microlocal elliptic regularity on the Sobolev scale

Let `P = ∑ i ∈ t, c i ∂^(m i)` be a linear differential operator with constant complex
coefficients `c i` and iterated directional derivatives `∂^(m i)` of orders `k i ≤ M`, with
principal symbol `σ_M(P)` (`TauCeti.constCoeffPrincipalSymbol`) and characteristic set `Char(P)`
(`TauCeti.constCoeffCharacteristicSet`). This file proves **microlocal elliptic regularity with
the exact gain of `M` Sobolev orders**: at a noncharacteristic covector, `T` is microlocally `H^s`
as soon as `P T` is microlocally `H^(s - M)`, that is,

`WF_s(T) ⊆ WF_(s - M)(P T) ∪ Char(P)`

(`Distribution.sobolevWaveFrontSet_subset_sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_union`).
Together with the order shift `WF_(s - M)(P T) ⊆ WF_s(T)` of differential operators
(`Distribution.sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_subset`), an elliptic `P`, whose
principal symbol vanishes nowhere off zero, satisfies `WF_(s - M)(P T) = WF_s(T)`. Projecting to
the base, `P T` is `H^(s - M)` near a point exactly when `T` is `H^s` there: this is local elliptic
regularity `P T ∈ H^(s - M)_loc ⇒ T ∈ H^s_loc`, for distributions of arbitrary order. For the
Laplacian it reads `WF_(s - 2)(Δ T) = WF_s(T)`.

This refines the corresponding statement for the wave front set,
`Distribution.waveFrontSet_subset_waveFrontSet_sum_smul_iteratedLineDerivOp_union`, which only
detects rapid decay.

## The argument

Write `L(T, ψ)(η) = T (ψ e_η)` for the localized Fourier transform, `⟨η⟩ ^ r` for the weight
`(1 + ‖η‖ ^ 2) ^ (r / 2)` and `p(η) = ∑ i ∈ t, c i ∏ₗ 2πi ⟪m i l, η⟫` for the full symbol of `P`.
Moving the derivatives of `P` onto the cutoff gives

`p(η) L(T, ψ)(η) = L(P T, ψ)(η) - ∑ i ∈ t, c i D_i(η)`,

where `D_i(η) = L(∂^(m i) T, ψ)(η) - (∏ₗ 2πi ⟪m i l, η⟫) L(T, ψ)(η)` only involves `L(T, ∂^β ψ)`
for derivatives of the cutoff, with one power of `η` fewer than the order `k i`. Fix an open
cone `Γ` around `ξ` on which `|p(η)| ≥ c (1 + ‖η‖) ^ M` for large `η`, and on which
`⟨η⟩ ^ (s - M) L(P T, ψ)` is square integrable for every cutoff `ψ` supported in a fixed
neighbourhood `U` of `x`. If `⟨η⟩ ^ r L(T, ψ)` is square integrable on `Γ` for every such `ψ`
and `r + 1 ≤ s`, then so is `⟨η⟩ ^ (r + 1 - k i) D_i`, hence `⟨η⟩ ^ (r + 1 - M) p L(T, ψ)`, and
dividing by `p` shows that `⟨η⟩ ^ (r + 1) L(T, ψ)` is square integrable on `Γ`. The induction
starts from the polynomial growth of the localized Fourier transform, with a degree uniform over
the cutoffs supported in a fixed compact set (`Distribution.exists_forall_norm_localFourier_le`),
and reaches the order `s` after finitely many steps, without shrinking `Γ` or `U`.

## Main results

* `Distribution.IsMicrolocallySobolevAt.of_sum_smul_iteratedLineDerivOp`: if `P T` is
  microlocally `H^(s - M)` at `(x, ξ)` and `σ_M(P)(ξ) ≠ 0`, then `T` is microlocally `H^s` there.
* `Distribution.sobolevWaveFrontSet_subset_sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_union`:
  `WF_s(T) ⊆ WF_(s - M)(P T) ∪ Char(P)`.
* `Distribution.sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero`,
  `Distribution.sobolevSingularSupport_sum_smul_iteratedLineDerivOp_of_forall_ne_zero`: an
  elliptic constant-coefficient operator of order `M` shifts the `H^s` wave front set and the
  `H^s` singular support by exactly `M`.
* `Distribution.IsLocallySobolevAt.of_sum_smul_iteratedLineDerivOp`: **local elliptic
  regularity**, if `P` is elliptic and `P T` is `H^(s - M)` near `x`, then `T` is `H^s` near `x`.
* `Distribution.sobolevWaveFrontSet_laplacianCLM`,
  `Distribution.sobolevSingularSupport_laplacianCLM`: `WF_(s - 2)(Δ T) = WF_s(T)` and
  `singsupp_(s - 2)(Δ T) = singsupp_s(T)`.

## References

* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1 (the `H^s` wave front set and microlocal elliptic regularity on the Sobolev scale).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.3.1 (the same argument for the wave front set).
-/

public section

noncomputable section

open Complex Filter MeasureTheory Module Real Set TopologicalSpace TestFunction LineDeriv
open scoped Distributions Topology RealInnerProductSpace ContDiff

namespace Distribution

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-! ### The regularity induction -/

/-- **The symbol of an iterated derivative.** If every cutoff supported in `U` makes
`⟨η⟩ ^ r L(T, ψ)` square integrable on `Γ`, then the localized Fourier transform of `∂^{m} T`, for
`q` directions `m`, is its symbol `∏ₗ 2πi ⟪m l, η⟫` times that of `T` up to an error `D` for which
`⟨η⟩ ^ (r + 1 - q) D` is square integrable on `Γ`: one order better than `∂^{m} T` itself. -/
private theorem memLp_localFourier_iteratedLineDerivOp_sub {r : ℝ} {T : 𝓓'(Ω, ℂ)} {U Γ : Set E}
    (hT : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
      MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (r / 2) • T.localFourier ψ η) 2 (volume.restrict Γ))
    {q : ℕ} (m : Fin q → E) {ψ : 𝓓(Ω, ℂ)} (hψ : tsupport ψ ⊆ U) :
    MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ ((r + 1 - q) / 2) • ((∂^{m} T).localFourier ψ η -
      (∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)) * T.localFourier ψ η)) 2 (volume.restrict Γ) := by
  induction q generalizing ψ with
  | zero => simp
  | succ q ih =>
    have h₁ := (ih (Fin.tail m) hψ).norm.const_mul (2 * π * ‖m 0‖)
    have h₂ := (memLp_one_add_norm_sq_rpow_smul_localFourier_iteratedLineDerivOp hT (Fin.tail m)
      ((tsupport_lineDerivOp_subset ψ (m 0)).trans hψ)).norm
    refine (h₁.add h₂).of_le
      (((Function.hasTemperateGrowth_one_add_norm_sq_rpow E _).1.continuous.smul
      (((∂^{m} T).continuous_localFourier ψ).sub
        ((by fun_prop : Continuous fun η : E ↦ ∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)).mul
          (T.continuous_localFourier ψ)))).aestronglyMeasurable) (.of_forall fun η ↦ ?_)
    have hw := one_add_norm_sq_rpow_mul_norm_two_mul_pi_mul_I_mul_inner_le (r + 1 - q) (m 0) η
    set a : ℂ := 2 * π * I * ⟪m 0, η⟫
    set D := (∂^{Fin.tail m} T).localFourier ψ η -
      (∏ l, (2 * π * I * ⟪Fin.tail m l, η⟫ : ℂ)) * T.localFourier ψ η
    set B := (∂^{Fin.tail m} T).localFourier (∂_{m 0} ψ) η
    have hid : (∂^{m} T).localFourier ψ η -
        (∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)) * T.localFourier ψ η = a * D - B := by
      rw [iteratedLineDerivOp_succ_left, localFourier_lineDerivOp, Fin.prod_univ_succ]
      simp only [a, D, B, Fin.tail]
      ring
    clear_value a
    have he : (r + 1 - ((q + 1 : ℕ) : ℝ)) / 2 = (r - q) / 2 := by push_cast; ring
    have he' : (r + 1 - q - 1) / 2 = (r - q) / 2 := by ring
    rw [he'] at hw
    have hW : 0 < 1 + ‖η‖ ^ 2 := by positivity
    rw [hid, he, Pi.add_apply, Real.norm_of_nonneg (by positivity)]
    simp only [norm_smul, Real.norm_eq_abs, Real.abs_rpow_of_nonneg hW.le, abs_of_pos hW]
    calc (1 + ‖η‖ ^ 2) ^ ((r - q) / 2) * ‖a * D - B‖
        ≤ (1 + ‖η‖ ^ 2) ^ ((r - q) / 2) * ‖a‖ * ‖D‖ + (1 + ‖η‖ ^ 2) ^ ((r - q) / 2) * ‖B‖ := by
          rw [mul_assoc, ← mul_add, ← norm_mul]
          gcongr
          exact norm_sub_le _ _
      _ ≤ 2 * π * ‖m 0‖ * (1 + ‖η‖ ^ 2) ^ ((r + 1 - q) / 2) * ‖D‖ +
            (1 + ‖η‖ ^ 2) ^ ((r - q) / 2) * ‖B‖ := by
          gcongr
      _ = 2 * π * ‖m 0‖ * ((1 + ‖η‖ ^ 2) ^ ((r + 1 - q) / 2) * ‖D‖) +
            (1 + ‖η‖ ^ 2) ^ ((r - q) / 2) * ‖B‖ := by ring

/-- **The symbol identity.** Moving the derivatives of `P` onto the cutoff writes
`p(η) L(T, ψ)(η)` as `L(P T, ψ)(η)` minus errors one order more regular than `L(∂^(m i) T, ψ)`.
Hence, if every cutoff supported in `U` makes `⟨η⟩ ^ (s - M) L(P T, ψ)` and `⟨η⟩ ^ r L(T, ψ)`
square integrable on `Γ`, and `r + 1 ≤ s`, then every such cutoff makes
`⟨η⟩ ^ (r + 1 - M) p(η) L(T, ψ)(η)` square integrable on `Γ`. -/
private theorem memLp_sum_mul_prod_mul_localFourier {ι : Type*} {t : Finset ι} {c : ι → ℂ}
    {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M) {T : 𝓓'(Ω, ℂ)}
    {U Γ : Set E} {s r : ℝ} (hrs : r + 1 ≤ s)
    (hP : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U → MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ ((s - M) / 2) •
      (∑ i ∈ t, c i • ∂^{m i} T).localFourier ψ η) 2 (volume.restrict Γ))
    (hT : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
      MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (r / 2) • T.localFourier ψ η) 2 (volume.restrict Γ))
    {ψ : 𝓓(Ω, ℂ)} (hψ : tsupport ψ ⊆ U) :
    MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ ((r + 1 - M) / 2) •
      ((∑ i ∈ t, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) * T.localFourier ψ η)) 2
      (volume.restrict Γ) := by
  refine ((hP ψ hψ).norm.add (memLp_finsetSum t fun i _ ↦
    (memLp_localFourier_iteratedLineDerivOp_sub hT (m i) hψ).norm.const_mul ‖c i‖)).of_le
    ((Function.hasTemperateGrowth_one_add_norm_sq_rpow E _).1.continuous.smul
      ((by fun_prop : Continuous fun η : E ↦ ∑ i ∈ t, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)).mul
        (T.continuous_localFourier ψ))).aestronglyMeasurable (.of_forall fun η ↦ ?_)
  have hid : (∑ i ∈ t, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) * T.localFourier ψ η =
      (∑ i ∈ t, c i • ∂^{m i} T).localFourier ψ η - ∑ i ∈ t, c i * ((∂^{m i} T).localFourier ψ η -
        (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) * T.localFourier ψ η) := by
    rw [localFourier_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [localFourier_smul]
    ring
  have hW : 0 < 1 + ‖η‖ ^ 2 := by positivity
  have h1 : 1 ≤ 1 + ‖η‖ ^ 2 := by nlinarith [norm_nonneg η]
  rw [hid, Pi.add_apply, Real.norm_of_nonneg (by positivity)]
  simp only [norm_smul, Real.norm_eq_abs, Real.abs_rpow_of_nonneg hW.le, abs_of_pos hW]
  refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)).trans ?_
  rw [mul_add]
  refine add_le_add ?_ ((mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_)
  · gcongr
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    rw [norm_mul, mul_left_comm]
    gcongr
    exact hk i hi

/-- **One step of the regularity induction.** Suppose that every cutoff supported in `U` makes
`⟨η⟩ ^ (s - M) L(P T, ψ)` square integrable on `Γ`, and that the full symbol of `P` is bounded
below by `c' (1 + ‖η‖) ^ M` on `Γ` outside a ball. If every such cutoff makes `⟨η⟩ ^ r L(T, ψ)`
square integrable on `Γ` and `r + 1 ≤ s`, then every such cutoff makes `⟨η⟩ ^ (r + 1) L(T, ψ)`
square integrable on `Γ`. -/
private theorem memLp_localFourier_add_one {ι : Type*} {t : Finset ι} {c : ι → ℂ} {k : ι → ℕ}
    {m : ∀ i, Fin (k i) → E} {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M) {T : 𝓓'(Ω, ℂ)} {U Γ : Set E}
    (hΓ : MeasurableSet Γ) {s r : ℝ} (hrs : r + 1 ≤ s)
    (hP : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U → MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ ((s - M) / 2) •
      (∑ i ∈ t, c i • ∂^{m i} T).localFourier ψ η) 2 (volume.restrict Γ))
    {R c' : ℝ} (hc' : 0 < c') (hp : ∀ η ∈ Γ, R ≤ ‖η‖ →
      c' * (1 + ‖η‖) ^ M ≤ ‖∑ i ∈ t, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖)
    (hT : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
      MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (r / 2) • T.localFourier ψ η) 2 (volume.restrict Γ))
    {ψ : 𝓓(Ω, ℂ)} (hψ : tsupport ψ ⊆ U) :
    MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ ((r + 1) / 2) • T.localFourier ψ η) 2 (volume.restrict Γ) := by
  set p : E → ℂ := fun η ↦ ∑ i ∈ t, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)
  -- Divide `⟨η⟩ ^ (r + 1 - M) p L(T, ψ)` by `p` at large frequencies; bounded frequencies cost a
  -- constant.
  refine (((hT ψ hψ).norm.const_mul ((1 + R ^ 2) ^ (1 / 2 : ℝ))).add
    ((memLp_sum_mul_prod_mul_localFourier hk hrs hP hT hψ).norm.const_mul c'⁻¹)).of_le
    ((Function.hasTemperateGrowth_one_add_norm_sq_rpow E _).1.continuous.smul
      (T.continuous_localFourier ψ)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hΓ] with η hη
  have hW : 0 < 1 + ‖η‖ ^ 2 := by positivity
  rw [Pi.add_apply, Real.norm_of_nonneg (by positivity)]
  simp only [norm_smul, norm_mul, Real.norm_eq_abs, Real.abs_rpow_of_nonneg hW.le, abs_of_pos hW]
  rcases lt_or_ge ‖η‖ R with hηR | hηR
  · -- At bounded frequencies `⟨η⟩ ≤ ⟨R⟩`.
    have hR : (1 + ‖η‖ ^ 2) ^ (1 / 2 : ℝ) ≤ (1 + R ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hW.le (by nlinarith [norm_nonneg η]) (by norm_num)
    calc (1 + ‖η‖ ^ 2) ^ ((r + 1) / 2) * ‖T.localFourier ψ η‖
        = (1 + ‖η‖ ^ 2) ^ (1 / 2 : ℝ) * ((1 + ‖η‖ ^ 2) ^ (r / 2) * ‖T.localFourier ψ η‖) := by
          rw [← mul_assoc, ← Real.rpow_add hW]
          ring_nf
      _ ≤ (1 + R ^ 2) ^ (1 / 2 : ℝ) * ((1 + ‖η‖ ^ 2) ^ (r / 2) * ‖T.localFourier ψ η‖) := by
          gcongr
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · -- At large frequencies `⟨η⟩ ^ M ≤ (1 + ‖η‖) ^ M ≤ |p(η)| / c'`.
    have hM : (1 + ‖η‖ ^ 2) ^ ((M : ℝ) / 2) ≤ c'⁻¹ * ‖p η‖ := by
      rw [le_inv_mul_iff₀ hc']
      exact (mul_le_mul_of_nonneg_left (one_add_norm_sq_rpow_le_one_add_norm_pow η M)
        hc'.le).trans (hp η hη hηR)
    calc (1 + ‖η‖ ^ 2) ^ ((r + 1) / 2) * ‖T.localFourier ψ η‖
        = (1 + ‖η‖ ^ 2) ^ ((r + 1 - M) / 2) * (1 + ‖η‖ ^ 2) ^ ((M : ℝ) / 2) *
            ‖T.localFourier ψ η‖ := by
          rw [← Real.rpow_add hW]
          ring_nf
      _ ≤ (1 + ‖η‖ ^ 2) ^ ((r + 1 - M) / 2) * (c'⁻¹ * ‖p η‖) * ‖T.localFourier ψ η‖ := by
          gcongr
      _ = c'⁻¹ * ((1 + ‖η‖ ^ 2) ^ ((r + 1 - M) / 2) * (‖p η‖ * ‖T.localFourier ψ η‖)) := by
          ring
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

/-! ### Microlocal elliptic regularity -/

/-- **Microlocal elliptic regularity on the Sobolev scale for constant-coefficient operators.**
Let `P = ∑ i ∈ t, c i ∂^(m i)` have orders `k i ≤ M`, and let `ξ` be noncharacteristic for `P`:
the principal symbol `constCoeffPrincipalSymbol t c m M` does not vanish at `ξ`. If `P T` is
microlocally `H^(s - M)` at `(x, ξ)`, then `T` is microlocally `H^s` there. -/
theorem IsMicrolocallySobolevAt.of_sum_smul_iteratedLineDerivOp {s : ℝ} {ι : Type*}
    {t : Finset ι} {c : ι → ℂ} {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ}
    (hk : ∀ i ∈ t, k i ≤ M) {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hP : (∑ i ∈ t, c i • ∂^{m i} T).IsMicrolocallySobolevAt (s - M) x ξ)
    (hξ : constCoeffPrincipalSymbol t c m M ξ ≠ 0) :
    T.IsMicrolocallySobolevAt s x ξ := by
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySobolevAt_iff.1 hP
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U, hU, Γ₁, hΓ₁, hξ₁, hcone₁, hPL⟩ := hP.exists_nhds_cone
  obtain ⟨Γ₂, hΓ₂, hξ₂, hcone₂, c₀, hc₀, hell⟩ := exists_cone_le_norm_constCoeffPrincipalSymbol hξ
  obtain ⟨R, c', hc', hp⟩ := exists_mul_one_add_norm_pow_le_norm_sum_mul_prod hk hc₀ hell
  -- A compact neighbourhood `K` of `x` on which `P T` is microlocally `H^(s - M)` along `Γ₁`.
  obtain ⟨K, hKx, hKsub, hKc⟩ := local_compact_nhds (inter_mem hU (Ω.isOpen.mem_nhds hx))
  -- `Reg r`: every cutoff supported in `K` has `⟨η⟩ ^ r L(T, ψ)` square integrable on `Γ₁ ∩ Γ₂`.
  let Reg : ℝ → Prop := fun r ↦ ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ K →
    MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (r / 2) • T.localFourier ψ η) 2 (volume.restrict (Γ₁ ∩ Γ₂))
  have hmono {r r' : ℝ} (hr : r' ≤ r) (h : Reg r) : Reg r' := fun ψ hψ ↦
    MemLp.one_add_norm_sq_rpow_smul_mono (h ψ hψ) (T.continuous_localFourier ψ).aestronglyMeasurable
      hr
  have hstep {r : ℝ} (hr : r + 1 ≤ s) (h : Reg r) : Reg (r + 1) := fun ψ hψ ↦
    memLp_localFourier_add_one hk (hΓ₁.inter hΓ₂).measurableSet hr
      (fun φ hφ ↦ (hPL φ (hφ.trans (hKsub.trans inter_subset_left))).mono_measure
        (Measure.restrict_mono inter_subset_left le_rfl))
      hc' (fun η hη ↦ hp η hη.2) h hψ
  -- The induction starts from the polynomial growth of the localized Fourier transforms.
  obtain ⟨k₀, hk₀⟩ := exists_forall_norm_localFourier_le T (K := ⟨K, hKc⟩)
    (hKsub.trans inter_subset_right)
  have hbase : Reg (-((k₀ : ℝ) + finrank ℝ E + 1)) := fun ψ hψ ↦ by
    obtain ⟨C, hC⟩ := hk₀ ψ hψ
    refine (memLp_two_one_add_norm_sq_rpow_smul_of_norm_le volume
      (T.continuous_localFourier ψ).aestronglyMeasurable (.of_forall hC) ?_).restrict _
    linarith [(finrank ℝ E).cast_nonneg (α := ℝ)]
  -- Each step gains one order, until the order `s` is reached.
  have hind (n : ℕ) : ∀ r, s - n ≤ r → Reg r → Reg s := by
    induction n with
    | zero => exact fun r hr h ↦ hmono (by simpa using hr) h
    | succ n ih =>
      intro r hr h
      refine ih (min r (s - 1) + 1) ?_
        (hstep (by linarith [min_le_right r (s - 1)]) (hmono (min_le_left _ _) h))
      push_cast at hr
      rcases le_total r (s - 1) with h' | h'
      · rw [min_eq_left h']
        linarith
      · rw [min_eq_right h']
        linarith [n.cast_nonneg (α := ℝ)]
  obtain ⟨n, hn⟩ := exists_nat_ge (s + ((k₀ : ℝ) + finrank ℝ E + 1))
  have hs := hind n _ (by linarith) hbase
  obtain ⟨φ, hφK, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤) hKx
    (hKsub.trans inter_subset_right) (1 : ℂ)
  exact isMicrolocallySobolevAt_iff.2 ⟨φ, by simp [hφx], Γ₁ ∩ Γ₂, hΓ₁.inter hΓ₂, ⟨hξ₁, hξ₂⟩,
    fun a ha η hη ↦ ⟨hcone₁ a ha η hη.1, hcone₂ a ha η hη.2⟩, hs φ hφK⟩

/-- **Microlocal elliptic regularity on the Sobolev scale**:
`WF_s(T) ⊆ WF_(s - M)(P T) ∪ Char(P)` for `P = ∑ i ∈ t, c i ∂^(m i)` with orders `k i ≤ M`, where
`Char(P) = constCoeffCharacteristicSet t c m M` is the set of `(x, ξ)` with `ξ ≠ 0` at which the
principal symbol vanishes. -/
theorem sobolevWaveFrontSet_subset_sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_union
    (s : ℝ) {ι : Type*} (t : Finset ι) (c : ι → ℂ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {M : ℕ}
    (hk : ∀ i ∈ t, k i ≤ M) (T : 𝓓'(Ω, ℂ)) :
    T.sobolevWaveFrontSet s ⊆ (∑ i ∈ t, c i • ∂^{m i} T).sobolevWaveFrontSet (s - M) ∪
      constCoeffCharacteristicSet t c m M := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hT⟩ := mem_sobolevWaveFrontSet_iff.1 hp
  by_contra h
  rw [mem_union, not_or, mem_sobolevWaveFrontSet_iff, mem_constCoeffCharacteristicSet_iff] at h
  exact hT (IsMicrolocallySobolevAt.of_sum_smul_iteratedLineDerivOp hk
    (by simpa [hx, hξ] using h.1) fun h0 ↦ h.2 ⟨hξ, h0⟩)

/-- **An elliptic constant-coefficient operator shifts the Sobolev wave front set by its order.**
If the principal symbol of `P = ∑ i ∈ t, c i ∂^(m i)` of order `M` vanishes at no `ξ ≠ 0`, then
`WF_(s - M)(P T) = WF_s(T)`. -/
theorem sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero (s : ℝ) {ι : Type*}
    (t : Finset ι) (c : ι → ℂ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {M : ℕ}
    (hk : ∀ i ∈ t, k i ≤ M) (hσ : ∀ ξ : E, ξ ≠ 0 → constCoeffPrincipalSymbol t c m M ξ ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ t, c i • ∂^{m i} T).sobolevWaveFrontSet (s - M) = T.sobolevWaveFrontSet s := by
  refine subset_antisymm (sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_subset s t c m hk T)
    fun p hp ↦ ?_
  refine (sobolevWaveFrontSet_subset_sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_union s t c
    m hk T hp).resolve_right ?_
  exact fun h ↦ hσ p.2 (mem_constCoeffCharacteristicSet_iff.1 h).1
    (mem_constCoeffCharacteristicSet_iff.1 h).2

/-- **Elliptic regularity on the Sobolev scale.** If the principal symbol of
`P = ∑ i ∈ t, c i ∂^(m i)` of order `M` vanishes at no `ξ ≠ 0`, then the `H^(s - M)` singular
support of `P T` is the `H^s` singular support of `T`. -/
theorem sobolevSingularSupport_sum_smul_iteratedLineDerivOp_of_forall_ne_zero (s : ℝ)
    {ι : Type*} (t : Finset ι) (c : ι → ℂ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {M : ℕ}
    (hk : ∀ i ∈ t, k i ≤ M) (hσ : ∀ ξ : E, ξ ≠ 0 → constCoeffPrincipalSymbol t c m M ξ ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ t, c i • ∂^{m i} T).sobolevSingularSupport (s - M) = T.sobolevSingularSupport s := by
  rw [← fst_image_sobolevWaveFrontSet, ← fst_image_sobolevWaveFrontSet,
    sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero s t c m hk hσ]

/-- **Local elliptic regularity**: `P T ∈ H^(s - M)_loc ⇒ T ∈ H^s_loc`. If the principal symbol
of `P = ∑ i ∈ t, c i ∂^(m i)` of order `M` vanishes at no `ξ ≠ 0` and `P T` is `H^(s - M)` near
`x`, then `T` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.of_sum_smul_iteratedLineDerivOp {s : ℝ} {ι : Type*} {t : Finset ι}
    {c : ι → ℂ} {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M)
    (hσ : ∀ ξ : E, ξ ≠ 0 → constCoeffPrincipalSymbol t c m M ξ ≠ 0) {T : 𝓓'(Ω, ℂ)} {x : E}
    (hP : (∑ i ∈ t, c i • ∂^{m i} T).IsLocallySobolevAt (s - M) x) :
    T.IsLocallySobolevAt s x :=
  (isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt hP.mem).2 fun ξ hξ ↦
    (hP.isMicrolocallySobolevAt ξ).of_sum_smul_iteratedLineDerivOp hk (hσ ξ hξ)

/-- **The Laplacian shifts the Sobolev wave front set by two.** The Laplacian
`Δ = LineDeriv.laplacianCLM ℝ E 𝓓'(Ω, ℂ)` satisfies `WF_(s - 2)(Δ T) = WF_s(T)`: its principal
symbol `‖ξ‖ ^ 2` vanishes only at `ξ = 0`. -/
theorem sobolevWaveFrontSet_laplacianCLM (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    (laplacianCLM ℝ E 𝓓'(Ω, ℂ) T).sobolevWaveFrontSet (s - 2) = T.sobolevWaveFrontSet s := by
  set b := stdOrthonormalBasis ℝ E
  have h := sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero s Finset.univ
    (fun _ ↦ 1) (k := fun _ ↦ 2) (fun i ↦ ![b i, b i]) (M := 2) (fun _ _ ↦ le_rfl)
    (fun ξ hξ ↦ ?_) T
  · simpa [laplacianCLM_eq_sum b, iteratedLineDerivOp_succ_left, iteratedLineDerivOp_one, Fin.tail]
      using h
  rw [constCoeffPrincipalSymbol_laplacian]
  exact_mod_cast (pow_pos (norm_pos_iff.2 hξ) 2).ne'

/-- **Elliptic regularity for the Laplacian on the Sobolev scale.** `Δ T` is `H^(s - 2)` near
exactly the points near which `T` is `H^s`: `singsupp_(s - 2)(Δ T) = singsupp_s(T)`. -/
theorem sobolevSingularSupport_laplacianCLM (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    (laplacianCLM ℝ E 𝓓'(Ω, ℂ) T).sobolevSingularSupport (s - 2) = T.sobolevSingularSupport s := by
  rw [← fst_image_sobolevWaveFrontSet, ← fst_image_sobolevWaveFrontSet,
    sobolevWaveFrontSet_laplacianCLM]

end Distribution
