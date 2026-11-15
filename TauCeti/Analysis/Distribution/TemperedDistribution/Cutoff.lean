/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import TauCeti.Analysis.Distribution.ComplexPairing
import TauCeti.Analysis.Distribution.Regularization
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Distribution.TestFunction.Convergence

/-!
# Cut-off distributions as tempered distributions

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real normed space
`E`, and `φ` a complex test function on `Ω`. The product `φ T` is a compactly supported
distribution, and it extends to the tempered distribution

`Distribution.cutoffTempered T φ : ψ ↦ T (φ ψ)`

on all of `E`: the product of `φ` with a Schwartz function `ψ` is a test function on `Ω`, and
since `T` has finite order on the support of `φ`, the pairing `T (φ ψ)` is bounded by finitely
many Schwartz seminorms of `ψ`. This is the passage from distributions on open sets to the
Fourier analysis of tempered distributions, and in particular to Mathlib's Bessel-potential
spaces `H^s`: `φ T ∈ H^s` is a statement about `Distribution.cutoffTempered T φ`.

The extension is unique: a tempered distribution is determined by its values on real compactly
supported Schwartz functions (`TemperedDistribution.ext_real`), on which it must be `T (φ ψ)`. It
only depends on the cutoff near the support of `T`.

Pairing a cut-off distribution with a Fourier integral `φ ∫ g η • e_η dη` of test functions is
computed by `Distribution.complexPairing_eq_integral_of_continuous_iteratedFDeriv`, the complex
form of `Distribution.apply_eq_integral_of_continuous_iteratedFDeriv`: a distribution passes under
an integral of test functions over a compact parameter space.

## Main declarations

* `Distribution.cutoffTempered T φ`: the tempered distribution `φ T`.
* `Distribution.cutoffTempered_apply`: its value `T (φ ψ)` on a Schwartz function `ψ`.
* `Distribution.eq_cutoffTempered_of_forall`: uniqueness of the extension.
* `Distribution.cutoffTempered_congr`: independence of the cutoff near the support of `T`.
* `Distribution.complexPairing_eq_integral_of_continuous_iteratedFDeriv`: the complex-linear
  extension of `T` passes under a compact-parameter integral of test functions.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.3 (the order of a
  compactly supported distribution) and §7.1 (compactly supported distributions are tempered).
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology SchwartzMap ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}

/-! ### Compact-parameter integrals -/

section ParametricIntegral

variable [FiniteDimensional ℝ E] {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y] {μ : Measure Y} [IsFiniteMeasure μ]

/-- **The complex-linear extension passes under a compact-parameter integral.** Let `f y`, for `y`
in a compact space `Y`, be complex test functions supported in a fixed compact `K ⊆ Ω` whose
derivatives of every order are jointly continuous in `y` and the point. If the test function `ψ`
is the integral `ψ x = ∫ f y x ∂μ` against a finite measure `μ`, then

`T ψ = ∫ T (f y) ∂μ`. -/
theorem complexPairing_eq_integral_of_continuous_iteratedFDeriv (T : 𝓓'(Ω, ℂ))
    {K : Compacts E} (hKΩ : (K : Set E) ⊆ Ω) {f : Y → 𝓓(Ω, ℂ)} (hfK : ∀ y, tsupport (f y) ⊆ K)
    (hf : ∀ k : ℕ, Continuous fun p : Y × E ↦ iteratedFDeriv ℝ k (f p.1) p.2)
    {ψ : 𝓓(Ω, ℂ)} (hψ : ∀ x, ψ x = ∫ y, f y x ∂μ) :
    T.complexPairing ψ = ∫ y, T.complexPairing (f y) ∂μ := by
  -- The real and imaginary parts of the `f y` satisfy the same hypotheses.
  have hpart (L : ℂ →L[ℝ] ℝ) : T (postcompCLM (𝕜 := ℝ) L ψ) =
      ∫ y, T (postcompCLM (𝕜 := ℝ) L (f y)) ∂μ := by
    refine T.apply_eq_integral_of_continuous_iteratedFDeriv hKΩ
      (f := fun y ↦ postcompCLM (𝕜 := ℝ) L (f y)) (fun y ↦ ?_) (fun k ↦ ?_) (fun x ↦ ?_)
    · rw [postcompCLM_apply]
      exact (tsupport_comp_subset (map_zero L) _).trans (hfK y)
    · have h (p : Y × E) : iteratedFDeriv ℝ k (postcompCLM (𝕜 := ℝ) L (f p.1)) p.2 =
          L.compContinuousMultilinearMap (iteratedFDeriv ℝ k (f p.1) p.2) := by
        rw [postcompCLM_apply]
        exact L.iteratedFDeriv_comp_left (f p.1).contDiff.contDiffAt (mod_cast le_top)
      simp only [h]
      exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k ↦ E) ℂ ℝ
        L).continuous.comp (hf k)
    · have hc : Continuous fun y ↦ f y x := by
        have h0 := (hf 0).comp (continuous_id.prodMk (continuous_const (y := x)))
        simpa only [Function.comp_def, id_eq, iteratedFDeriv_zero_apply] using
          (continuous_eval_const (fun _ : Fin 0 ↦ (0 : E))).comp h0
      rw [postcompCLM_apply, Function.comp_apply, hψ, ← L.integral_comp_comm
        (integrableOn_univ.1 (hc.continuousOn.integrableOn_compact' isCompact_univ .univ))]
      rfl
  have hint (L : ℂ →L[ℝ] ℝ) : Integrable (fun y ↦ T (postcompCLM (𝕜 := ℝ) L (f y))) μ := by
    have hc : Continuous fun y ↦ postcompCLM (𝕜 := ℝ) L (f y) :=
      (postcompCLM (𝕜 := ℝ) L).continuous.comp
        (TestFunction.continuous_of_continuous_iteratedFDeriv K.isCompact hKΩ hfK fun k _ ↦ hf k)
    exact integrableOn_univ.1 ((T.continuous.comp hc).continuousOn.integrableOn_compact'
      isCompact_univ .univ)
  rw [complexPairing_apply, hpart, hpart, ← integral_const_mul,
    ← integral_add (hint _) ((hint _).const_mul I)]
  simp only [complexPairing_apply]

end ParametricIntegral

/-! ### The tempered distribution `φ T` -/

section Cutoff

/-- The product `φ ψ` of a test function on `Ω` with a Schwartz function, as a test function on
`Ω`. -/
private def mulSchwartz (φ : 𝓓(Ω, ℂ)) (ψ : 𝓢(E, ℂ)) : 𝓓(Ω, ℂ) :=
  ⟨fun x ↦ φ x * ψ x, φ.contDiff.mul (ψ.smooth ⊤), φ.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans φ.tsupport_subset⟩

private theorem mulSchwartz_apply (φ : 𝓓(Ω, ℂ)) (ψ : 𝓢(E, ℂ)) (x : E) :
    mulSchwartz φ ψ x = φ x * ψ x :=
  (rfl)

/-- Since `T` has finite order on the support of `φ`, the pairing `T (φ ψ)` is bounded by finitely
many Schwartz seminorms of `ψ`. -/
private theorem exists_norm_complexPairing_mulSchwartz_le (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ ψ : 𝓢(E, ℂ),
      ‖T.complexPairing (mulSchwartz φ ψ)‖ ≤ C * s.sup (schwartzSeminormFamily ℂ E ℂ) ψ := by
  let K : Compacts E := ⟨tsupport φ, φ.hasCompactSupport⟩
  obtain ⟨N, C, hC, hT⟩ := T.exists_norm_complexPairing_le (K := K) φ.tsupport_subset
  -- A bound `A` for the derivatives of `φ` of order at most `N`.
  choose c hc using fun j : ℕ ↦
    (φ.contDiff.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (φ.hasCompactSupport.iteratedFDeriv j)
  set A : ℝ := ∑ j ∈ Finset.range (N + 1), |c j|
  have hA (j : ℕ) (hj : j ≤ N) (x : E) : ‖iteratedFDeriv ℝ j φ x‖ ≤ A :=
    (hc j x).trans ((le_abs_self _).trans (Finset.single_le_sum (fun i _ ↦ abs_nonneg (c i))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))))
  set s : Finset (ℕ × ℕ) := (Finset.range (N + 1)).image fun j ↦ (0, j)
  refine ⟨s, C * (2 ^ N * A), by positivity, fun ψ ↦ ?_⟩
  set S := s.sup (schwartzSeminormFamily ℂ E ℂ) ψ
  have hψ (j : ℕ) (hj : j ≤ N) (x : E) : ‖iteratedFDeriv ℝ j ψ x‖ ≤ S :=
    (ψ.norm_iteratedFDeriv_le_seminorm ℂ j x).trans (Seminorm.le_finset_sup_apply
      (p := schwartzSeminormFamily ℂ E ℂ) (x := ψ) (Finset.mem_image_of_mem
        (fun j ↦ ((0 : ℕ), j)) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))))
  have hsupp : tsupport (mulSchwartz φ ψ) ⊆ K := by
    rw [show ⇑(mulSchwartz φ ψ) = fun x ↦ φ x * ψ x from funext (mulSchwartz_apply φ ψ)]
    exact tsupport_mul_subset_left
  refine (hT _ hsupp (2 ^ N * A * S) (by positivity) fun i hi x ↦ ?_).trans_eq (by ring)
  calc ‖iteratedFDeriv ℝ i (mulSchwartz φ ψ) x‖
      ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j φ x‖ *
          ‖iteratedFDeriv ℝ (i - j) ψ x‖ :=
        norm_iteratedFDeriv_mul_le φ.contDiff (ψ.smooth ⊤) x (mod_cast le_top)
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * A * S := by
        gcongr with j hj
        · exact hA j ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)).trans hi) x
        · exact hψ _ ((Nat.sub_le i j).trans hi) x
    _ = 2 ^ i * A * S := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose,
          Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ 2 ^ N * A * S := by gcongr; exact one_le_two

/-- **The tempered distribution `φ T`.** For a complex distribution `T` on `Ω` and a complex test
function `φ` on `Ω`, the compactly supported distribution `φ T`, extended to the tempered
distribution `ψ ↦ T (φ ψ)` on all of `E`. -/
def cutoffTempered (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) : 𝓢'(E, ℂ) :=
  ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _ <|
    SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ)
      (fun ψ ↦ T.complexPairing (mulSchwartz φ ψ))
      (fun ψ ψ' ↦ by
        rw [← map_add]
        congr 1
        ext x
        simp [mulSchwartz_apply, mul_add])
      (fun a ψ ↦ by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        ext x
        simp [mulSchwartz_apply, mul_left_comm])
      (exists_norm_complexPairing_mulSchwartz_le T φ)

/-- The value of `φ T` on a Schwartz function `ψ` is the pairing of `T` with any test function
equal to `φ ψ`. -/
theorem cutoffTempered_apply (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) {ψ : 𝓢(E, ℂ)} {χ : 𝓓(Ω, ℂ)}
    (hχ : ∀ x, χ x = φ x * ψ x) : T.cutoffTempered φ ψ = T.complexPairing χ := by
  have h : mulSchwartz φ ψ = χ := by
    ext x
    rw [mulSchwartz_apply, hχ]
  exact congrArg T.complexPairing h

/-- **Uniqueness of the extension.** A tempered distribution which takes the value `T (φ ψ)` on
every real compactly supported Schwartz function `ψ` is `φ T`. -/
theorem eq_cutoffTempered_of_forall [FiniteDimensional ℝ E] (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ))
    {S : 𝓢'(E, ℂ)}
    (hS : ∀ (ψ : 𝓢(E, ℝ)) (χ : 𝓓(Ω, ℂ)), HasCompactSupport ψ → (∀ x, χ x = φ x * ψ x) →
      S (ψ.postcompCLM Complex.ofRealCLM) = T.complexPairing χ) :
    S = T.cutoffTempered φ :=
  TemperedDistribution.ext_real fun ψ hψ ↦ by
    rw [hS ψ (mulSchwartz φ (ψ.postcompCLM Complex.ofRealCLM)) hψ fun x ↦ by
      simp [mulSchwartz_apply],
      cutoffTempered_apply T φ (χ := mulSchwartz φ (ψ.postcompCLM Complex.ofRealCLM)) fun _ ↦ (rfl)]

/-- **Cutoff independence.** The tempered distribution `φ T` only depends on the germ of `φ` along
the support of `T`. -/
theorem cutoffTempered_congr [FiniteDimensional ℝ E] (T : 𝓓'(Ω, ℂ)) {φ φ' : 𝓓(Ω, ℂ)}
    (h : (φ : E → ℂ) =ᶠ[𝓝ˢ (dsupport T)] φ') : T.cutoffTempered φ = T.cutoffTempered φ' := by
  ext ψ
  rw [cutoffTempered_apply T φ (χ := mulSchwartz φ ψ) fun _ ↦ (rfl),
    cutoffTempered_apply T φ' (χ := mulSchwartz φ' ψ) fun _ ↦ (rfl)]
  exact T.complexPairing_eq_of_eventuallyEq (h.mono fun x hx ↦ by
    simp only [mulSchwartz_apply, hx])

/-- The tempered distribution `φ T` is additive in `T`. -/
@[simp]
theorem cutoffTempered_add (T S : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    (T + S).cutoffTempered φ = T.cutoffTempered φ + S.cutoffTempered φ := by
  ext ψ
  simp only [add_apply, cutoffTempered_apply _ φ
    (χ := mulSchwartz φ ψ) fun _ ↦ (rfl), complexPairing_add]

/-- The tempered distribution `φ T` is complex-linear in `T`. -/
@[simp]
theorem cutoffTempered_smul (c : ℂ) (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    (c • T).cutoffTempered φ = c • T.cutoffTempered φ := by
  ext ψ
  simp only [smul_apply, cutoffTempered_apply _ φ
    (χ := mulSchwartz φ ψ) fun _ ↦ (rfl), complexPairing_smul, smul_eq_mul]

/-- The tempered distribution `φ T` is additive in the cutoff `φ`. -/
@[simp]
theorem cutoffTempered_add_cutoff (T : 𝓓'(Ω, ℂ)) (φ φ' : 𝓓(Ω, ℂ)) :
    T.cutoffTempered (φ + φ') = T.cutoffTempered φ + T.cutoffTempered φ' := by
  ext ψ
  rw [add_apply, cutoffTempered_apply T _ (χ := mulSchwartz φ ψ + mulSchwartz φ' ψ)
    fun x ↦ by simp [mulSchwartz_apply, add_mul], map_add,
    cutoffTempered_apply T φ (χ := mulSchwartz φ ψ) fun _ ↦ (rfl),
    cutoffTempered_apply T φ' (χ := mulSchwartz φ' ψ) fun _ ↦ (rfl)]

end Cutoff

end Distribution
