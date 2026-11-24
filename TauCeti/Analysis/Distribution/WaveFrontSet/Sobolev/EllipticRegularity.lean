/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.EllipticRegularity
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.LineDeriv
import TauCeti.Analysis.Distribution.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Microlocal Sobolev elliptic regularity for constant-coefficient operators

Let `P = ∑ i ∈ t, c i ∂^(m i)` be a linear differential operator with complex constant
coefficients `c i` and iterated directional derivatives `∂^(m i)` of orders `k i ≤ M`, acting on
complex distributions `T` on an open subset `Ω` of a finite-dimensional real inner product space.
A differential operator of order `M` costs at most `M` orders of microlocal Sobolev regularity,
`WF_s(P T) ⊆ WF_(s + M)(T)`
(`Distribution.sobolevWaveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset`). This file
proves that at a noncharacteristic covector nothing more is lost:

`WF_(s + M)(T) ⊆ WF_s(P T) ∪ Char(P)`

(`Distribution.sobolevWaveFrontSet_subset_sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_union`),
for every real `s` and every distribution `T`, where `Char(P)` is the set
`TauCeti.constCoeffCharacteristicSet t c m M` of covectors `ξ ≠ 0` at which the principal symbol
vanishes. So `P T` is microlocally `H^s` at a noncharacteristic `(x, ξ)` exactly when `T` is
microlocally `H^(s + M)` there, and an elliptic operator shifts the `H^s` wave front set exactly
by its order: `WF_s(P T) = WF_(s + M)(T)`. For the Laplacian this is
`WF_s(Δ T) = WF_(s + 2)(T)` (`Distribution.sobolevWaveFrontSet_laplacianCLM`). Projecting to
the base gives local elliptic regularity `P T ∈ H^s_loc ⇒ T ∈ H^(s + M)_loc` on open subsets
of `E`, for distributions of arbitrary order. This is the `H^s` refinement of
`Distribution.waveFrontSet_subset_waveFrontSet_sum_smul_iteratedLineDerivOp_union`.

## The argument

Write `L(T, φ)(η) = T (φ e_η)` for the localized Fourier transform and
`p(η) = ∑ i ∈ t, c i ∏ₗ 2πi ⟪m i l, η⟫` for the full symbol of `P` in the frequency variable of
Mathlib's Fourier transform. Moving the derivatives onto the cutoff gives

`p(η) L(T, φ)(η) = L(P T, φ)(η) - ∑ i ∈ t, c i D_i(η)`,

where `D_i = L(∂^(m i) T, φ) - (∏ₗ 2πi ⟪m i l, η⟫) L(T, φ)` is one order more regular than
`∂^(m i) T`
(`Distribution.memLp_one_add_norm_sq_rpow_smul_localFourier_iteratedLineDerivOp_sub_prod_mul`).
Since the coefficients are constant, the same cutoff `φ` appears on both sides. Near a
noncharacteristic `ξ`, `|p(η)| ≥ c (1 + ‖η‖) ^ M` on an open cone `Γ` outside a ball
(`TauCeti.exists_mul_one_add_norm_pow_le_norm_sum_mul_prod`). Dividing by `p(η)` there shows: if
the weighted localized Fourier transforms of `T` are square integrable on `Γ` with weight
`⟨η⟩ ^ r`, uniformly over the cutoffs supported near `x`, then they are with weight
`⟨η⟩ ^ min (r + 1) (s + M)`. Every distribution is `H^r` near `x` for some `r`
(`Distribution.exists_forall_isLocallySobolevAt`), so finitely many steps reach `s + M`.

## Main results

* `Distribution.IsMicrolocallySobolevAt.of_sum_smul_iteratedLineDerivOp`: if `P T` is microlocally
  `H^s` at `(x, ξ)` and the principal symbol does not vanish at `ξ`, then `T` is microlocally
  `H^(s + M)` there.
* `Distribution.isMicrolocallySobolevAt_sum_smul_iteratedLineDerivOp_iff`: at a noncharacteristic
  `ξ`, `P T` is microlocally `H^s` exactly when `T` is microlocally `H^(s + M)`.
* `Distribution.sobolevWaveFrontSet_subset_sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_union`:
  `WF_(s + M)(T) ⊆ WF_s(P T) ∪ Char(P)`.
* `Distribution.sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero`: an elliptic
  operator satisfies `WF_s(P T) = WF_(s + M)(T)`.
* `Distribution.sobolevSingularSupport_sum_smul_iteratedLineDerivOp_of_forall_ne_zero`: an
  elliptic operator satisfies `singsupp_s(P T) = singsupp_(s + M)(T)`.
* `Distribution.IsLocallySobolevAt.of_sum_smul_iteratedLineDerivOp`: **local elliptic
  regularity**, if `P` is elliptic and `P T` is `H^s` near `x`, then `T` is `H^(s + M)` near `x`.
* `Distribution.isLocallySobolevAt_sum_smul_iteratedLineDerivOp_iff`: for elliptic `P`, `P T` is
  `H^s` near `x` exactly when `T` is `H^(s + M)` near `x`.
* `Distribution.sobolevWaveFrontSet_laplacianCLM`: `WF_s(Δ T) = WF_(s + 2)(T)`.

## References

* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1 (the `H^s` wave front set and microlocal elliptic regularity on the Sobolev scale).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.3.1.
-/

public section

noncomputable section

open Complex Filter LineDeriv MeasureTheory Real Set TopologicalSpace TestFunction
open scoped Distributions Topology RealInnerProductSpace ContDiff

namespace Distribution

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Division by the symbol at a high frequency.** Let `P = ∑ i ∈ t, c i ∂^(m i)` have orders at
most `M`, and let its full symbol `p(η) = ∑ i ∈ t, c i ∏ₗ 2πi ⟪m i l, η⟫` satisfy
`c' (1 + ‖η‖) ^ M ≤ |p(η)|` at the frequency `η`. Then for `u ≤ r + 1` and `u ≤ s + M`,
`⟨η⟩ ^ u |L(T, φ)(η)|` is at most `c'⁻¹` times `⟨η⟩ ^ s |L(P T, φ)(η)|` plus the sum of
`|c i| ⟨η⟩ ^ (r - k i + 1) |D_i(η)|`, where
`D_i = L(∂^(m i) T, φ) - (∏ₗ 2πi ⟪m i l, η⟫) L(T, φ)`. -/
private theorem one_add_norm_sq_rpow_mul_norm_localFourier_le {ι : Type*} {t : Finset ι}
    {c : ι → ℂ} {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M)
    (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) {η : E} {c' : ℝ} (hc' : 0 < c')
    (hp : c' * (1 + ‖η‖) ^ M ≤ ‖∑ i ∈ t, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖)
    {u r s : ℝ} (hu₁ : u ≤ r + 1) (hu₂ : u ≤ s + M) :
    (1 + ‖η‖ ^ 2) ^ (u / 2) * ‖T.localFourier φ η‖ ≤
      c'⁻¹ * ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖(∑ i ∈ t, c i • ∂^{m i} T).localFourier φ η‖ +
        ∑ i ∈ t, ‖c i‖ * ((1 + ‖η‖ ^ 2) ^ ((r - k i + 1) / 2) *
          ‖(∂^{m i} T).localFourier φ η -
            (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) * T.localFourier φ η‖)) := by
  set L := T.localFourier φ η
  set LP := (∑ i ∈ t, c i • ∂^{m i} T).localFourier φ η with hLP
  set wu := (1 + ‖η‖ ^ 2) ^ (u / 2)
  set ws := (1 + ‖η‖ ^ 2) ^ (s / 2)
  -- The symbol identity `p(η) L(T, φ) = L(P T, φ) - ∑ i, c i D_i`.
  have hid : (∑ i ∈ t, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) * L =
      LP - ∑ i ∈ t, c i * ((∂^{m i} T).localFourier φ η -
        (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) * L) := by
    rw [hLP, localFourier_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [localFourier_smul]
    ring
  have hell : c' * (1 + ‖η‖) ^ M * ‖L‖ ≤ ‖LP‖ + ∑ i ∈ t, ‖c i‖ *
      ‖(∂^{m i} T).localFourier φ η - (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) * L‖ := by
    calc c' * (1 + ‖η‖) ^ M * ‖L‖
        ≤ ‖∑ i ∈ t, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖ * ‖L‖ := by gcongr
      _ ≤ _ := by
          rw [← norm_mul, hid]
          exact (norm_sub_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans_eq
            (Finset.sum_congr rfl fun i _ ↦ norm_mul _ _)))
  -- The weight `⟨η⟩ ^ u` is at most `(1 + ‖η‖) ^ M` times the weights of `P T` and of `D i`.
  have hwP : wu ≤ ws * (1 + ‖η‖) ^ M := one_add_norm_sq_rpow_le_mul_one_add_norm_pow η hu₂
  have hwD (i : ι) (hi : i ∈ t) :
      wu ≤ (1 + ‖η‖ ^ 2) ^ ((r - k i + 1) / 2) * (1 + ‖η‖) ^ M :=
    one_add_norm_sq_rpow_le_mul_one_add_norm_pow η (by
      have : (k i : ℝ) ≤ M := by exact_mod_cast hk i hi
      linarith)
  rw [le_inv_mul_iff₀ hc']
  refine le_of_mul_le_mul_left ?_ (pow_pos (by positivity : (0 : ℝ) < 1 + ‖η‖) M)
  calc (1 + ‖η‖) ^ M * (c' * (wu * ‖L‖)) = wu * (c' * (1 + ‖η‖) ^ M * ‖L‖) := by ring
    _ ≤ wu * (‖LP‖ + ∑ i ∈ t, ‖c i‖ *
          ‖(∂^{m i} T).localFourier φ η - (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) * L‖) := by
        gcongr
    _ = wu * ‖LP‖ + ∑ i ∈ t, ‖c i‖ * (wu *
          ‖(∂^{m i} T).localFourier φ η - (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) * L‖) := by
        rw [mul_add, Finset.mul_sum]
        exact congr_arg _ (Finset.sum_congr rfl fun i _ ↦ by ring)
    _ ≤ ws * (1 + ‖η‖) ^ M * ‖LP‖ + ∑ i ∈ t, ‖c i‖ *
          ((1 + ‖η‖ ^ 2) ^ ((r - k i + 1) / 2) * (1 + ‖η‖) ^ M *
            ‖(∂^{m i} T).localFourier φ η - (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) * L‖) := by
        gcongr with i hi
        exact hwD i hi
    _ = (1 + ‖η‖) ^ M * (ws * ‖LP‖ + ∑ i ∈ t, ‖c i‖ * ((1 + ‖η‖ ^ 2) ^ ((r - k i + 1) / 2) *
          ‖(∂^{m i} T).localFourier φ η - (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) * L‖)) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **One step of the regularity induction.** Let `P = ∑ i ∈ t, c i ∂^(m i)` have orders at most
`M`, and let its full symbol be bounded below by `c' (1 + ‖η‖) ^ M` for `η ∈ Γ` with `R ≤ ‖η‖`.
If, for the cutoffs supported in `U`, the localized Fourier transforms of `T` are square integrable
on `Γ` with the weight `⟨η⟩ ^ r` and those of `P T` with the weight `⟨η⟩ ^ s`, then those of `T`
are with the weight `⟨η⟩ ^ min (r + 1) (s + M)`. -/
private theorem memLp_one_add_norm_sq_rpow_smul_localFourier_min {ι : Type*} {t : Finset ι}
    {c : ι → ℂ} {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M)
    {T : 𝓓'(Ω, ℂ)} {U Γ : Set E} (hΓ : MeasurableSet Γ) {R c' : ℝ} (hc' : 0 < c')
    (hp : ∀ η ∈ Γ, R ≤ ‖η‖ →
      c' * (1 + ‖η‖) ^ M ≤ ‖∑ i ∈ t, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖)
    {r s : ℝ} (hT : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
      MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (r / 2) • T.localFourier ψ η) 2 (volume.restrict Γ))
    (hPT : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
      MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • (∑ i ∈ t, c i • ∂^{m i} T).localFourier ψ η) 2
        (volume.restrict Γ))
    {φ : 𝓓(Ω, ℂ)} (hφ : tsupport φ ⊆ U) :
    MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (min (r + 1) (s + M) / 2) • T.localFourier φ η) 2
      (volume.restrict Γ) := by
  set u := min (r + 1) (s + M)
  have hu₁ : u ≤ r + 1 := min_le_left _ _
  set K : ℝ := (1 + R ^ 2) ^ ((1 : ℝ) / 2) with hK_def
  -- The dominating function `K ⟨η⟩ ^ r |L(T, φ)| + c'⁻¹ (⟨η⟩ ^ s |L(P T, φ)| + ∑ |c i| |D_i|)`,
  -- with the weight `⟨η⟩ ^ (r - k i + 1)` on the error `D_i` of `∂^(m i)`.
  have hG := ((hT φ hφ).norm.const_mul K).add (((hPT φ hφ).norm.add (memLp_finsetSum t fun i _ ↦
    (memLp_one_add_norm_sq_rpow_smul_localFourier_iteratedLineDerivOp_sub_prod_mul hT (m i)
      hφ).norm.const_mul ‖c i‖)).const_mul c'⁻¹)
  refine hG.of_le ((Function.hasTemperateGrowth_one_add_norm_sq_rpow E (u / 2)).1.continuous.smul
    (T.continuous_localFourier φ)).aestronglyMeasurable
    (ae_restrict_of_forall_mem hΓ fun η hη ↦ ?_)
  have hw (a : ℝ) : ‖(1 + ‖η‖ ^ 2) ^ (a / 2)‖ = (1 + ‖η‖ ^ 2) ^ (a / 2) :=
    Real.norm_of_nonneg (by positivity)
  simp only [Pi.add_apply, norm_smul, hw]
  have hP : 0 ≤ c'⁻¹ * ((1 + ‖η‖ ^ 2) ^ (s / 2) *
      ‖(∑ i ∈ t, c i • ∂^{m i} T).localFourier φ η‖ + ∑ i ∈ t, ‖c i‖ *
        ((1 + ‖η‖ ^ 2) ^ ((r - k i + 1) / 2) * ‖(∂^{m i} T).localFourier φ η -
          (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) * T.localFourier φ η‖)) :=
    mul_nonneg (inv_nonneg.2 hc'.le) (by positivity)
  rw [Real.norm_of_nonneg (add_nonneg (by positivity) hP)]
  rcases lt_or_ge ‖η‖ R with hηR | hηR
  · -- At low frequencies, `⟨η⟩ ^ u ≤ ⟨R⟩ ⟨η⟩ ^ r`.
    have hwu : (1 + ‖η‖ ^ 2) ^ (u / 2) ≤ K * (1 + ‖η‖ ^ 2) ^ (r / 2) := by
      calc (1 + ‖η‖ ^ 2) ^ (u / 2) ≤ (1 + ‖η‖ ^ 2) ^ (r / 2) * (1 + ‖η‖ ^ 2) ^ ((1 : ℝ) / 2) := by
            rw [← Real.rpow_add (by positivity), ← add_div]
            exact Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (by positivity))
              (by linarith)
        _ ≤ (1 + ‖η‖ ^ 2) ^ (r / 2) * K := by
            rw [hK_def]
            gcongr
        _ = K * (1 + ‖η‖ ^ 2) ^ (r / 2) := mul_comm _ _
    calc (1 + ‖η‖ ^ 2) ^ (u / 2) * ‖T.localFourier φ η‖
        ≤ K * (1 + ‖η‖ ^ 2) ^ (r / 2) * ‖T.localFourier φ η‖ := by gcongr
      _ = K * ((1 + ‖η‖ ^ 2) ^ (r / 2) * ‖T.localFourier φ η‖) := mul_assoc _ _ _
      _ ≤ _ := le_add_of_nonneg_right hP
  · -- At high frequencies, divide the symbol identity by `p(η)`.
    exact (one_add_norm_sq_rpow_mul_norm_localFourier_le hk T φ hc' (hp η hη hηR) hu₁
      (min_le_right _ _)).trans (le_add_of_nonneg_left (by positivity))

/-- **The regularity induction.** Under the hypotheses of the one-step lemma, starting from the
weight `⟨η⟩ ^ r`, `n` steps give square integrability with the weight
`⟨η⟩ ^ min (r + n) (s + M)`. -/
private theorem memLp_one_add_norm_sq_rpow_smul_localFourier_min_add {ι : Type*}
    {t : Finset ι} {c : ι → ℂ} {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ}
    (hk : ∀ i ∈ t, k i ≤ M) {T : 𝓓'(Ω, ℂ)} {U Γ : Set E} (hΓ : MeasurableSet Γ) {R c' : ℝ}
    (hc' : 0 < c')
    (hp : ∀ η ∈ Γ, R ≤ ‖η‖ →
      c' * (1 + ‖η‖) ^ M ≤ ‖∑ i ∈ t, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖)
    {r s : ℝ} (hT : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
      MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (r / 2) • T.localFourier ψ η) 2 (volume.restrict Γ))
    (hPT : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
      MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • (∑ i ∈ t, c i • ∂^{m i} T).localFourier ψ η) 2
        (volume.restrict Γ))
    (n : ℕ) {φ : 𝓓(Ω, ℂ)} (hφ : tsupport φ ⊆ U) :
    MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (min (r + n) (s + M) / 2) • T.localFourier φ η) 2
      (volume.restrict Γ) := by
  induction n generalizing φ with
  | zero =>
    simpa using memLp_one_add_norm_sq_rpow_smul_localFourier_of_le (hT φ hφ) (min_le_left _ _)
  | succ n ih =>
    refine memLp_one_add_norm_sq_rpow_smul_localFourier_of_le
      (memLp_one_add_norm_sq_rpow_smul_localFourier_min hk hΓ hc' hp (fun ψ hψ ↦ ih hψ) hPT hφ) ?_
    push_cast
    refine le_min ?_ (min_le_right _ _)
    rcases le_total (r + n) (s + M) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by linarith)
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (by linarith)

/-- **Microlocal Sobolev elliptic regularity for constant-coefficient operators.** Let
`P = ∑ i ∈ t, c i ∂^(m i)` have orders `k i ≤ M`, and let `ξ` be noncharacteristic for `P`: the
principal symbol `constCoeffPrincipalSymbol t c m M` does not vanish at `ξ`. If `P T` is
microlocally `H^s` at `(x, ξ)`, then `T` is microlocally `H^(s + M)` there. -/
theorem IsMicrolocallySobolevAt.of_sum_smul_iteratedLineDerivOp {ι : Type*} {t : Finset ι}
    {c : ι → ℂ} {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M)
    {T : 𝓓'(Ω, ℂ)} {s : ℝ} {x ξ : E}
    (hP : (∑ i ∈ t, c i • ∂^{m i} T).IsMicrolocallySobolevAt s x ξ)
    (hξ : constCoeffPrincipalSymbol t c m M ξ ≠ 0) :
    T.IsMicrolocallySobolevAt (s + M) x ξ := by
  have hx : x ∈ Ω := hP.mem
  obtain ⟨U₁, hU₁, Γ₁, hΓ₁, hξ₁, hcone₁, hL₁⟩ := hP.exists_nhds_cone
  obtain ⟨Γ₂, hΓ₂, hξ₂, hcone₂, c₀, hc₀, hell⟩ := exists_cone_le_norm_constCoeffPrincipalSymbol hξ
  -- The full symbol is elliptic at large frequencies in `Γ₂`.
  obtain ⟨R, c', hc', hp⟩ := exists_mul_one_add_norm_pow_le_norm_sum_mul_prod
    (b := fun i _ ↦ c i) hk hc₀ (U := univ) (Γ := Γ₂) (A := ∑ i ∈ t, ‖c i‖)
    (fun _ _ i hi ↦ Finset.single_le_sum (fun j _ ↦ norm_nonneg (c j)) hi)
    (fun _ _ η hη ↦ hell η hη)
  -- `T` is `H^r` near `x` for some `r`.
  obtain ⟨r, hr⟩ := T.exists_forall_isLocallySobolevAt isCompact_singleton
    (singleton_subset_iff.2 hx)
  obtain ⟨U₀, hU₀, hL₀⟩ := (hr x rfl).exists_nhds
  have hT (ψ : 𝓓(Ω, ℂ)) (hψ : tsupport ψ ⊆ U₀ ∩ U₁) :
      MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (r / 2) • T.localFourier ψ η) 2
        (volume.restrict (Γ₁ ∩ Γ₂)) :=
    (hL₀ ψ (hψ.trans inter_subset_left)).restrict _
  have hPT (ψ : 𝓓(Ω, ℂ)) (hψ : tsupport ψ ⊆ U₀ ∩ U₁) :
      MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • (∑ i ∈ t, c i • ∂^{m i} T).localFourier ψ η) 2
        (volume.restrict (Γ₁ ∩ Γ₂)) :=
    (hL₁ ψ (hψ.trans inter_subset_right)).mono_measure
      (Measure.restrict_mono inter_subset_left le_rfl)
  obtain ⟨ψ, hψ, hψx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (inter_mem hU₀ hU₁) (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  have hmin : min (r + ⌈s + M - r⌉₊) (s + M) = s + M :=
    min_eq_right (by linarith [Nat.le_ceil (s + M - r)])
  refine isMicrolocallySobolevAt_iff.2 ⟨ψ, by simp [hψx], Γ₁ ∩ Γ₂, hΓ₁.inter hΓ₂, ⟨hξ₁, hξ₂⟩,
    fun t ht η hη ↦ ⟨hcone₁ t ht η hη.1, hcone₂ t ht η hη.2⟩, ?_⟩
  simpa [hmin] using memLp_one_add_norm_sq_rpow_smul_localFourier_min_add hk
    (hΓ₁.inter hΓ₂).measurableSet hc' (fun η hη hR ↦ hp 0 (mem_univ _) η hη.2 hR) hT hPT
    ⌈s + M - r⌉₊ (hψ.trans inter_subset_left)

/-- At a noncharacteristic covector `(x, ξ)` of `P = ∑ i ∈ t, c i ∂^(m i)`, with orders
`k i ≤ M`, `P T` is microlocally `H^s` exactly when `T` is microlocally `H^(s + M)`. -/
theorem isMicrolocallySobolevAt_sum_smul_iteratedLineDerivOp_iff {ι : Type*} {t : Finset ι}
    {c : ι → ℂ} {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M)
    {T : 𝓓'(Ω, ℂ)} {s : ℝ} {x ξ : E} (hξ : constCoeffPrincipalSymbol t c m M ξ ≠ 0) :
    (∑ i ∈ t, c i • ∂^{m i} T).IsMicrolocallySobolevAt s x ξ ↔
      T.IsMicrolocallySobolevAt (s + M) x ξ := by
  refine ⟨fun h ↦ h.of_sum_smul_iteratedLineDerivOp hk hξ, fun h ↦ ?_⟩
  simpa using h.sum_smul_smulLeftCLM_iteratedLineDerivOp t c (g := fun _ _ ↦ 1)
    (fun _ ↦ contDiff_const) m hk

/-- **Microlocal Sobolev elliptic regularity for constant-coefficient operators**:
`WF_(s + M)(T) ⊆ WF_s(P T) ∪ Char(P)` for `P = ∑ i ∈ t, c i ∂^(m i)` with orders `k i ≤ M`, where
`Char(P) = constCoeffCharacteristicSet t c m M` is the set of `(x, ξ)` with `ξ ≠ 0` at which the
principal symbol vanishes. -/
theorem sobolevWaveFrontSet_subset_sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_union
    {ι : Type*} (s : ℝ) (t : Finset ι) (c : ι → ℂ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {M : ℕ}
    (hk : ∀ i ∈ t, k i ≤ M) (T : 𝓓'(Ω, ℂ)) :
    T.sobolevWaveFrontSet (s + M) ⊆ (∑ i ∈ t, c i • ∂^{m i} T).sobolevWaveFrontSet s ∪
      constCoeffCharacteristicSet t c m M := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hT⟩ := mem_sobolevWaveFrontSet_iff.1 hp
  by_contra h
  rw [mem_union, not_or, mem_sobolevWaveFrontSet_iff, mem_constCoeffCharacteristicSet_iff] at h
  exact hT (IsMicrolocallySobolevAt.of_sum_smul_iteratedLineDerivOp hk
    (by simpa [hx, hξ] using h.1) fun h0 ↦ h.2 ⟨hξ, h0⟩)

/-- **An elliptic constant-coefficient operator shifts the `H^s` wave front set by its order.** If
the principal symbol of `P = ∑ i ∈ t, c i ∂^(m i)` of order `M` vanishes at no `ξ ≠ 0`, then
`WF_s(P T) = WF_(s + M)(T)`. -/
theorem sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero {ι : Type*} (s : ℝ)
    (t : Finset ι) (c : ι → ℂ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {M : ℕ}
    (hk : ∀ i ∈ t, k i ≤ M) (hσ : ∀ ξ : E, ξ ≠ 0 → constCoeffPrincipalSymbol t c m M ξ ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ t, c i • ∂^{m i} T).sobolevWaveFrontSet s = T.sobolevWaveFrontSet (s + M) := by
  ext ⟨x, ξ⟩
  simp only [mem_sobolevWaveFrontSet_iff]
  refine and_congr_right fun _ ↦ ?_
  exact ⟨fun ⟨hξ, h⟩ ↦ ⟨hξ, fun h' ↦ h ((isMicrolocallySobolevAt_sum_smul_iteratedLineDerivOp_iff
    hk (hσ ξ hξ)).2 h')⟩, fun ⟨hξ, h⟩ ↦ ⟨hξ, fun h' ↦
      h ((isMicrolocallySobolevAt_sum_smul_iteratedLineDerivOp_iff hk (hσ ξ hξ)).1 h')⟩⟩

/-- **An elliptic constant-coefficient operator shifts the `H^s` singular support by its
order.** If the principal symbol of `P = ∑ i ∈ t, c i ∂^(m i)` of order `M` vanishes at no
`ξ ≠ 0`, then `P T` is `H^s` near exactly the points near which `T` is `H^(s + M)`. -/
theorem sobolevSingularSupport_sum_smul_iteratedLineDerivOp_of_forall_ne_zero {ι : Type*}
    (s : ℝ) (t : Finset ι) (c : ι → ℂ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {M : ℕ}
    (hk : ∀ i ∈ t, k i ≤ M) (hσ : ∀ ξ : E, ξ ≠ 0 → constCoeffPrincipalSymbol t c m M ξ ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ t, c i • ∂^{m i} T).sobolevSingularSupport s = T.sobolevSingularSupport (s + M) := by
  rw [← fst_image_sobolevWaveFrontSet, ← fst_image_sobolevWaveFrontSet,
    sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero s t c m hk hσ]

/-- **Local elliptic regularity for constant-coefficient operators**:
`P T ∈ H^s_loc ⇒ T ∈ H^(s + M)_loc`. If the principal symbol of `P = ∑ i ∈ t, c i ∂^(m i)` of
order `M` vanishes at no `ξ ≠ 0` and `P T` is `H^s` near `x`, then `T` is `H^(s + M)` near `x`. -/
theorem IsLocallySobolevAt.of_sum_smul_iteratedLineDerivOp {ι : Type*} {t : Finset ι}
    {c : ι → ℂ} {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M)
    (hσ : ∀ ξ : E, ξ ≠ 0 → constCoeffPrincipalSymbol t c m M ξ ≠ 0) {T : 𝓓'(Ω, ℂ)} {s : ℝ}
    {x : E} (hP : (∑ i ∈ t, c i • ∂^{m i} T).IsLocallySobolevAt s x) :
    T.IsLocallySobolevAt (s + M) x :=
  (isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt hP.mem).2 fun ξ hξ ↦
    (hP.isMicrolocallySobolevAt ξ).of_sum_smul_iteratedLineDerivOp hk (hσ ξ hξ)

/-- If the principal symbol of `P = ∑ i ∈ t, c i ∂^(m i)` of order `M` vanishes at no `ξ ≠ 0`,
then `P T` is `H^s` near `x` exactly when `T` is `H^(s + M)` near `x`. -/
theorem isLocallySobolevAt_sum_smul_iteratedLineDerivOp_iff {ι : Type*} {t : Finset ι}
    {c : ι → ℂ} {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M)
    (hσ : ∀ ξ : E, ξ ≠ 0 → constCoeffPrincipalSymbol t c m M ξ ≠ 0) {T : 𝓓'(Ω, ℂ)} {s : ℝ}
    {x : E} :
    (∑ i ∈ t, c i • ∂^{m i} T).IsLocallySobolevAt s x ↔ T.IsLocallySobolevAt (s + M) x := by
  refine ⟨fun h ↦ h.of_sum_smul_iteratedLineDerivOp hk hσ, fun h ↦ ?_⟩
  simpa using h.sum_smul_smulLeftCLM_iteratedLineDerivOp t c (g := fun _ _ ↦ 1)
    (fun _ ↦ contDiff_const) m hk

/-- **The Laplacian shifts the `H^s` wave front set by two.** The Laplacian
`Δ = LineDeriv.laplacianCLM ℝ E 𝓓'(Ω, ℂ)` satisfies `WF_s(Δ T) = WF_(s + 2)(T)`. -/
@[simp]
theorem sobolevWaveFrontSet_laplacianCLM (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    (laplacianCLM ℝ E 𝓓'(Ω, ℂ) T).sobolevWaveFrontSet s = T.sobolevWaveFrontSet (s + 2) := by
  set b := stdOrthonormalBasis ℝ E
  have h := sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero s Finset.univ
    (fun _ ↦ 1) (k := fun _ ↦ 2) (fun i ↦ ![b i, b i]) (M := 2) (fun _ _ ↦ le_rfl)
    (fun ξ hξ ↦ ?_) T
  · simpa [laplacianCLM_eq_sum_iteratedLineDerivOp b] using h
  rw [constCoeffPrincipalSymbol_laplacian]
  exact_mod_cast (pow_pos (norm_pos_iff.2 hξ) 2).ne'

end Distribution
