/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.TestFunction
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Test functions are Schwartz functions

A smooth function with compact support decays faster than every power together with all its
derivatives, so it is a Schwartz function (`HasCompactSupport.toSchwartzMap`). This file shows
that the inclusion is continuous for the natural topologies on the two sides: on smooth functions
supported in a fixed compact set `K`, the Schwartz seminorm `sup_x ‖x‖ ^ k ‖D^l f(x)‖` is at most
`R ^ k` times the sup norm of `D^l f` for any `R` with `K ⊆ closedBall 0 R`
(`ContDiffMapSupportedIn.toSchwartzMapCLM`), and by the universal property of the inductive limit
topology this gives a continuous linear map on all test functions
(`TestFunction.toSchwartzMapCLM`).

Restricting along this inclusion turns a tempered distribution into a distribution on any open
set, which is how tempered distributions, and in particular the Bessel-potential spaces `H^s`, are
compared with distributions on open sets.

## Main declarations

* `ContDiffMapSupportedIn.toSchwartzMapCLM`: smooth functions supported in a compact set as
  Schwartz functions, as a continuous linear map, with the seminorm bound
  `ContDiffMapSupportedIn.seminorm_toSchwartzMapCLM_le`.
* `TestFunction.toSchwartzMapCLM`: test functions on an open set as Schwartz functions, as a
  continuous linear map, with `TestFunction.coe_toSchwartzMapCLM`; it commutes with directional
  derivatives (`TestFunction.toSchwartzMapCLM_lineDerivOp`), also iterated
  (`TestFunction.toSchwartzMapCLM_iteratedLineDerivOp`), and with postcomposition by continuous
  linear maps (`TestFunction.toSchwartzMapCLM_postcompCLM`).
* `TestFunction.integral_bilinear_iteratedLineDerivOp_left_eq_neg_one_pow_smul_right`: iterated
  integration by parts `∫ L (∂^{m} u) φ = (-1) ^ k ∫ L u (∂^{m ∘ rev} φ)` for test functions,
  from the Schwartz-space identity.
* `SchwartzMap.toTestFunction`: a compactly supported Schwartz function as a test function, sent
  back to itself by `TestFunction.toSchwartzMapCLM` (`SchwartzMap.toSchwartzMapCLM_toTestFunction`).
* `TestFunction.smulSchwartzMap`: the product `ψ • u` of a real test function `ψ` and a Schwartz
  function `u`, as a test function. It depends continuously on `u`
  (`TestFunction.smulSchwartzMapCLM`): by the Leibniz rule, the `i`-th derivative of `ψ • u` is
  bounded by the first `i` derivatives of `u`, with constants given by the sup norms of the
  derivatives of `ψ`. So an operator which is continuous on Schwartz space, followed by a cutoff,
  lands continuously in the test functions on `Ω`.
* `TestFunction.fourierSchwartzCLM`: the Fourier transform of test functions, as a continuous
  linear map into the Schwartz functions; so `ψ ↦ 𝓕 ψ η` is continuous
  (`TestFunction.continuous_fourier_apply`), and the Fourier transforms of the test functions of a
  compact set decay rapidly, uniformly
  (`TestFunction.exists_forall_one_add_norm_pow_mul_norm_fourier_le`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.1 (the inclusion
  `C_c^∞ ⊆ 𝓢`, by which `𝓢'` is a space of distributions).
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped Distributions ContDiff SchwartzMap LineDeriv FourierTransform

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

namespace ContDiffMapSupportedIn

variable {K : Compacts E}

/-- On smooth functions supported in `K ⊆ closedBall 0 R`, the Schwartz seminorm of orders `k`
and `l` is at most `R ^ k` times the sup norm of the `l`-th derivative. -/
private theorem seminorm_toSchwartzMap_le {R : ℝ} (hR : 0 ≤ R)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (k l : ℕ) (f : 𝓓_{K}(E, F)) :
    SchwartzMap.seminorm 𝕜 k l (f.hasCompactSupport.toSchwartzMap f.contDiff) ≤
      R ^ k * N[𝕜]_{K, l} f := by
  refine SchwartzMap.seminorm_le_bound 𝕜 k l _ (by positivity) fun x ↦ ?_
  have hf : ⇑(f.hasCompactSupport.toSchwartzMap f.contDiff) = f :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  rw [hf]
  by_cases hx : x ∈ K
  · gcongr
    · exact hKR x hx
    · exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜
  · simpa [f.iteratedFDeriv_zero_on_compl hx] using
      mul_nonneg (pow_nonneg hR k) (apply_nonneg _ f)

/-- The inclusion `𝓓_{K}(E, F) → 𝓢(E, F)` as a linear map. -/
private def toSchwartzMapLM : 𝓓_{K}(E, F) →ₗ[𝕜] 𝓢(E, F) where
  toFun f := f.hasCompactSupport.toSchwartzMap f.contDiff
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

variable (𝕜) in
/-- A smooth function supported in a compact set `K` is a Schwartz function, and the inclusion
`𝓓_{K}(E, F) → 𝓢(E, F)` is a continuous linear map. -/
def toSchwartzMapCLM : 𝓓_{K}(E, F) →L[𝕜] 𝓢(E, F) where
  toLinearMap := toSchwartzMapLM
  cont := by
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
    have hKR (x : E) (hx : x ∈ K) : ‖x‖ ≤ max R 0 :=
      (mem_closedBall_zero_iff.1 (hR hx)).trans (le_max_left _ _)
    refine (schwartz_withSeminorms 𝕜 E F).continuous_of_continuous_comp _ fun i ↦ ?_
    set C : NNReal := (max R 0 ^ i.1).toNNReal
    refine Seminorm.continuous_of_le (q := C • N[𝕜]_{K, i.2}) ?_ fun f ↦ ?_
    · exact ((ContDiffMapSupportedIn.withSeminorms 𝕜 E F ⊤ K).continuous_seminorm i.2).const_smul C
    · exact (seminorm_toSchwartzMap_le (le_max_right R 0) hKR i.1 i.2 f).trans_eq (by
        rw [smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (by positivity)])

@[simp]
theorem coe_toSchwartzMapCLM (f : 𝓓_{K}(E, F)) : ⇑(toSchwartzMapCLM 𝕜 f) = f :=
  -- `HasCompactSupport.toSchwartzMap` keeps the underlying function.
  (rfl)

/-- **Quantitative inclusion of test functions in Schwartz space.** On smooth functions supported
in `K ⊆ closedBall 0 R`, the Schwartz seminorm of orders `k` and `l` is at most `R ^ k` times the
sup norm of the `l`-th derivative. -/
theorem seminorm_toSchwartzMapCLM_le {R : ℝ} (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (k l : ℕ)
    (f : 𝓓_{K}(E, F)) :
    SchwartzMap.seminorm 𝕜 k l (toSchwartzMapCLM 𝕜 f) ≤ R ^ k * N[𝕜]_{K, l} f :=
  -- `toSchwartzMapCLM 𝕜 f` is `HasCompactSupport.toSchwartzMap` applied to `f` by definition.
  seminorm_toSchwartzMap_le hR hKR k l f

end ContDiffMapSupportedIn

namespace TestFunction

variable {Ω : Opens E} [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F]

variable (𝕜) in
/-- **Test functions are Schwartz functions.** A smooth function with compact support in an open
set `Ω` is a Schwartz function, and the inclusion `𝓓(Ω, F) → 𝓢(E, F)` is a continuous linear map
for the inductive limit topology on test functions. -/
def toSchwartzMapCLM : 𝓓(Ω, F) →L[𝕜] 𝓢(E, F) :=
  TestFunction.limitCLM 𝕜 (fun φ ↦ φ.hasCompactSupport.toSchwartzMap φ.contDiff)
    (fun _ _ ↦ ContDiffMapSupportedIn.toSchwartzMapCLM 𝕜) fun _ _ _ ↦ (rfl)

@[simp]
theorem coe_toSchwartzMapCLM (φ : 𝓓(Ω, F)) : ⇑(toSchwartzMapCLM 𝕜 φ) = φ :=
  -- `HasCompactSupport.toSchwartzMap` keeps the underlying function.
  (rfl)

theorem toSchwartzMapCLM_apply (φ : 𝓓(Ω, F)) (x : E) : toSchwartzMapCLM 𝕜 φ x = φ x :=
  (rfl)

/-- A test function, read as a Schwartz function, still has compact support. -/
theorem hasCompactSupport_toSchwartzMapCLM (φ : 𝓓(Ω, F)) :
    HasCompactSupport (toSchwartzMapCLM 𝕜 φ) :=
  φ.hasCompactSupport

theorem toSchwartzMapCLM_injective : Function.Injective (toSchwartzMapCLM 𝕜 : 𝓓(Ω, F) → _) :=
  fun _ _ h ↦ TestFunction.ext fun x ↦ by
    simpa using congrArg (fun f : 𝓢(E, F) ↦ f x) h

/-- The inclusion of test functions in Schwartz space commutes with directional derivatives. -/
@[simp]
theorem toSchwartzMapCLM_lineDerivOp (v : E) (φ : 𝓓(Ω, F)) :
    toSchwartzMapCLM 𝕜 (∂_{v} φ) = ∂_{v} (toSchwartzMapCLM 𝕜 φ) := by
  ext x
  simp [lineDerivOp_eq_lineDerivCLM ℝ, SchwartzMap.lineDerivOp_apply]

/-- The inclusion of test functions in Schwartz space commutes with iterated directional
derivatives. -/
@[simp]
theorem toSchwartzMapCLM_iteratedLineDerivOp {k : ℕ} (m : Fin k → E) (φ : 𝓓(Ω, F)) :
    toSchwartzMapCLM 𝕜 (∂^{m} φ) = ∂^{m} (toSchwartzMapCLM 𝕜 φ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, LineDeriv.iteratedLineDerivOp_succ_left,
      toSchwartzMapCLM_lineDerivOp, ih]

/-- The inclusion of test functions in Schwartz space commutes with postcomposition by continuous
linear maps. -/
@[simp]
theorem toSchwartzMapCLM_postcompCLM {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedSpace 𝕜 G] [SMulCommClass ℝ 𝕜 G] [IsScalarTower ℝ 𝕜 G] (L : F →L[ℝ] G)
    (φ : 𝓓(Ω, F)) :
    toSchwartzMapCLM 𝕜 (postcompCLM L φ) = (toSchwartzMapCLM 𝕜 φ).postcompCLM L := by
  ext x
  simp

open MeasureTheory in
/-- **Iterated integration by parts for test functions.** For a continuous bilinear map `L`,
`∫ L (∂^{m} u) φ = (-1) ^ k ∫ L u (∂^{m ∘ rev} φ)`: the `k` derivatives move to `φ` in reverse
order, each with a minus sign. -/
theorem integral_bilinear_iteratedLineDerivOp_left_eq_neg_one_pow_smul_right [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure] {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : F →L[ℝ] G →L[ℝ] H) {k : ℕ} (m : Fin k → E) (u : 𝓓(Ω, F)) (φ : 𝓓(Ω, G)) :
    ∫ x, L ((∂^{m} u) x) (φ x) ∂μ = (-1 : ℝ) ^ k • ∫ x, L (u x) ((∂^{m ∘ Fin.rev} φ) x) ∂μ := by
  have h := SchwartzMap.integral_bilinear_iteratedLineDerivOp_left_eq_neg_one_pow_smul_right
    (μ := μ) L m (toSchwartzMapCLM ℝ u) (toSchwartzMapCLM ℝ φ)
  rw [← toSchwartzMapCLM_iteratedLineDerivOp, ← toSchwartzMapCLM_iteratedLineDerivOp] at h
  simpa only [toSchwartzMapCLM_apply] using h

/-- The test function `ψ • u` on `Ω`, the product of a real test function `ψ` on `Ω` and a Schwartz
function `u`. -/
def smulSchwartzMap (ψ : 𝓓(Ω, ℝ)) (u : 𝓢(E, F)) : 𝓓(Ω, F) where
  toFun x := ψ x • u x
  contDiff' := ψ.contDiff.smul (u.smooth ⊤)
  hasCompactSupport' := ψ.hasCompactSupport.smul_right
  tsupport_subset' := (tsupport_smul_subset_left _ _).trans ψ.tsupport_subset

@[simp]
theorem smulSchwartzMap_apply (ψ : 𝓓(Ω, ℝ)) (u : 𝓢(E, F)) (x : E) :
    ψ.smulSchwartzMap u x = ψ x • u x :=
  (rfl)

/-- The product `ψ • u` of a test function `ψ` and a Schwartz function `u`, as a smooth function
supported in the compact set `tsupport ψ`, depending continuously on `u`. -/
private def smulSchwartzMapSupportedInCLM (ψ : 𝓓(Ω, ℝ)) :
    𝓢(E, F) →L[ℝ] 𝓓_{⟨tsupport ψ, ψ.hasCompactSupport⟩}(E, F) :=
  letI P : 𝓢(E, F) →ₗ[ℝ] 𝓓_{⟨tsupport ψ, ψ.hasCompactSupport⟩}(E, F) :=
    { toFun u := ContDiffMapSupportedIn.of_support_subset (ψ.contDiff.smul (u.smooth ⊤))
        ((Function.support_smul_subset_left _ _).trans (subset_tsupport _))
      map_add' u v := ContDiffMapSupportedIn.ext fun x ↦ smul_add (ψ x) (u x) (v x)
      map_smul' c u := ContDiffMapSupportedIn.ext fun x ↦ smul_comm (ψ x) c (u x) }
  { toLinearMap := P
    cont := by
      -- Leibniz: the `i`-th derivative is controlled by the first `i` derivatives of `u`, with
      -- constants given by bounds for the derivatives of `ψ`.
      choose M hM using fun j : ℕ ↦
        (ψ.contDiff.continuous_iteratedFDeriv (m := j) (mod_cast le_top)).norm
          |>.bddAbove_range_of_hasCompactSupport (ψ.hasCompactSupport.iteratedFDeriv j).norm
      refine WithSeminorms.continuous_of_isBounded (schwartz_withSeminorms ℝ E F)
        (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ?_)
      refine ⟨{0} ×ˢ Finset.range (i + 1), ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * |M j|,
        fun u ↦ ((P u).seminorm_le_iff ℝ (mul_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity)
          (apply_nonneg _ _)) i).2 fun _ x _ ↦ ?_⟩
      refine (norm_iteratedFDeriv_smul_le ψ.contDiff (u.smooth ⊤) x (mod_cast le_top)).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj ↦ ?_
      have hj : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hψj : ‖iteratedFDeriv ℝ j ψ x‖ ≤ |M j| := (hM j ⟨x, rfl⟩).trans (le_abs_self _)
      have hmem : ((0, i - j) : ℕ × ℕ) ∈ ({0} ×ˢ Finset.range (i + 1)) := by
        simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, true_and]
        omega
      have huj : ‖iteratedFDeriv ℝ (i - j) u x‖ ≤
          (({0} ×ˢ Finset.range (i + 1)).sup (schwartzSeminormFamily ℝ E F)) u :=
        (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ u (i - j) x).trans
          (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ E F) hmem)
      calc (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j ψ x‖ * ‖iteratedFDeriv ℝ (i - j) u x‖
          ≤ (i.choose j : ℝ) * |M j| *
              (({0} ×ˢ Finset.range (i + 1)).sup (schwartzSeminormFamily ℝ E F)) u := by
            gcongr }

/-- **Cutting off Schwartz functions.** The product `ψ • u` of a real test function `ψ` on `Ω`
and a Schwartz function `u` (`TestFunction.smulSchwartzMap`), as a continuous linear map from
Schwartz functions to test functions on `Ω`. -/
def smulSchwartzMapCLM (ψ : 𝓓(Ω, ℝ)) : 𝓢(E, F) →L[ℝ] 𝓓(Ω, F) :=
  (ofSupportedInCLM ℝ ψ.tsupport_subset).comp (smulSchwartzMapSupportedInCLM ψ)

@[simp]
theorem smulSchwartzMapCLM_apply (ψ : 𝓓(Ω, ℝ)) (u : 𝓢(E, F)) (x : E) :
    smulSchwartzMapCLM ψ u x = ψ x • u x :=
  (rfl)

/-- The continuous linear map `smulSchwartzMapCLM ψ` is `TestFunction.smulSchwartzMap ψ`. -/
theorem smulSchwartzMapCLM_eq_smulSchwartzMap (ψ : 𝓓(Ω, ℝ)) (u : 𝓢(E, F)) :
    smulSchwartzMapCLM ψ u = ψ.smulSchwartzMap u :=
  TestFunction.ext fun x ↦ by simp

end TestFunction

namespace SchwartzMap

variable {Ω : Opens E}

/-- A compactly supported Schwartz function whose support lies in the open set `Ω` is a test
function on `Ω`. -/
def toTestFunction (f : 𝓢(E, F)) (hf : HasCompactSupport f) (hΩ : tsupport f ⊆ Ω) :
    𝓓(Ω, F) :=
  ⟨f, f.smooth ⊤, hf, hΩ⟩

@[simp]
theorem coe_toTestFunction (f : 𝓢(E, F)) (hf : HasCompactSupport f) (hΩ : tsupport f ⊆ Ω) :
    ⇑(f.toTestFunction hf hΩ) = f :=
  (rfl)

variable [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] in
@[simp]
theorem toSchwartzMapCLM_toTestFunction (f : 𝓢(E, F)) (hf : HasCompactSupport f)
    (hΩ : tsupport f ⊆ Ω) : TestFunction.toSchwartzMapCLM 𝕜 (f.toTestFunction hf hΩ) = f :=
  -- `TestFunction.toSchwartzMapCLM` is `TestFunction.limitCLM` of
  -- `HasCompactSupport.toSchwartzMap`, which unfolds to that map; it keeps the underlying
  -- function, and `SchwartzMap` has structure eta.
  (rfl)

end SchwartzMap

namespace TestFunction

section Fourier

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  {Ω : Opens E}

/-- The Fourier transform of test functions on `Ω`, as a continuous linear map into the Schwartz
functions. -/
def fourierSchwartzCLM : 𝓓(Ω, F) →L[ℂ] 𝓢(E, F) :=
  (FourierTransform.fourierCLM ℂ 𝓢(E, F)).comp (toSchwartzMapCLM ℂ)

@[simp]
theorem coe_fourierSchwartzCLM (ψ : 𝓓(Ω, F)) : ⇑(fourierSchwartzCLM ψ) = 𝓕 (ψ : E → F) := by
  simp [fourierSchwartzCLM, SchwartzMap.fourier_coe]

/-- The value `𝓕 ψ η` of the Fourier transform at a fixed frequency depends continuously on the
test function `ψ`. -/
theorem continuous_fourier_apply (η : E) : Continuous fun ψ : 𝓓(Ω, F) ↦ 𝓕 (ψ : E → F) η := by
  have h := (BoundedContinuousFunction.evalCLM ℂ η).continuous.comp
    ((SchwartzMap.toBoundedContinuousFunctionCLM ℂ E F).continuous.comp
      (fourierSchwartzCLM (Ω := Ω) (F := F)).continuous)
  simpa [Function.comp_def] using h

/-- The Fourier transforms of the test functions of a compact set decay rapidly, uniformly: for
every order `M`, `(1 + ‖η‖) ^ M ‖𝓕 ψ η‖` is bounded uniformly in `η` and in `ψ ∈ Q`. -/
theorem exists_forall_one_add_norm_pow_mul_norm_fourier_le {Q : Set 𝓓(Ω, F)}
    (hQ : IsCompact Q) (M : ℕ) :
    ∃ B, ∀ ψ ∈ Q, ∀ η, (1 + ‖η‖) ^ M * ‖𝓕 (ψ : E → F) η‖ ≤ B := by
  set p : Seminorm ℂ 𝓢(E, F) := ∑ i ∈ Finset.Iic (M, 0), SchwartzMap.seminorm ℂ i.1 i.2
  have hp : Continuous p := Seminorm.continuous_finsetSum fun i _ ↦
    (schwartz_withSeminorms ℂ E F).continuous_seminorm i
  obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn
    (hp.comp (fourierSchwartzCLM (Ω := Ω) (F := F)).continuous).continuousOn
  refine ⟨2 ^ M * C, fun ψ hψ η ↦ ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (M, 0)) le_rfl le_rfl
    (fourierSchwartzCLM ψ) η
  rw [norm_iteratedFDeriv_zero, coe_fourierSchwartzCLM] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  calc ((Finset.Iic (M, 0)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) (fourierSchwartzCLM ψ)
      ≤ p (fourierSchwartzCLM ψ) := Seminorm.finset_sup_le_sum _ _ _
    _ ≤ C := (Real.le_norm_self _).trans (hC ψ hψ)

end Fourier

end TestFunction
