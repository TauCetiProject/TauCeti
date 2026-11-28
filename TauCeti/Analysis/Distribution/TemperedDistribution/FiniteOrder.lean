/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Duality
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding.Schwartz
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

/-!
# Tempered distributions have finite weighted Sobolev order

A tempered distribution `u` is continuous on Schwartz space, so it is bounded by finitely many of
the seminorms `sup ‖x‖ ^ k ‖D^l φ(x)‖`. Multiplying by a negative power
`⟨x⟩ ^ (-2K) = (1 + ‖x‖ ^ 2) ^ (-K)` of the Japanese bracket absorbs the polynomial factors, and the
Sobolev embedding `H^t ⊆ C^l`, `t > l + n / 2`, bounds the remaining derivatives by `‖φ‖_{H^t}`.
So `⟨x⟩ ^ (-2K) u` is bounded on Schwartz functions in the `H^t` norm, and a functional bounded in
this way lies in `H^{-t}` (`TemperedDistribution.memSobolev_neg_of_norm_le`, from the duality of
`H^t` and `H^{-t}`). Hence every scalar
tempered distribution is `(1 + ‖x‖ ^ 2) ^ K` times an element of a Sobolev space, and its product
with a Schwartz function has finite Sobolev order.

This is the tempered counterpart of `Distribution.exists_memSobolev_cutoffTempered` for
distributions on open sets. It reduces statements about arbitrary tempered distributions to
statements on Sobolev spaces, for instance the regularizing property of smoothing pseudodifferential
operators (`TauCeti.Symbol.IsSmoothing.memSobolev_quantizeTempered`).

## Main declarations

* `SchwartzMap.exists_seminorm_smulLeftCLM_one_add_norm_sq_rpow_neg_le`: for `k ≤ 2K` and
  `t > l + n / 2`, the Schwartz seminorm `sup ‖x‖ ^ k ‖D^l (⟨x⟩ ^ (-2K) φ)‖` is at most
  `C ‖φ‖_{H^t}`.
* `TemperedDistribution.exists_memSobolev_smulLeftCLM_one_add_norm_sq_rpow_neg`: every scalar
  tempered distribution lies in some `H^s` after multiplication by some `(1 + ‖x‖ ^ 2) ^ (-K)`.
* `TemperedDistribution.exists_memSobolev_eq_smulLeftCLM_one_add_norm_sq_pow`: equivalently, every
  scalar tempered distribution is `(1 + ‖x‖ ^ 2) ^ K` times an element of some `H^s`.
* `TemperedDistribution.exists_memSobolev_smulLeftCLM`: `ψ u` has finite Sobolev order for every
  Schwartz function `ψ`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, 2nd ed., Springer,
  1990, §7.1 (tempered distributions are bounded by finitely many Schwartz seminorms).
* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3 (Sobolev spaces `H_s` and the duality of `H_s` and `H_{-s}`).
-/

public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap BesselPotentialSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace TemperedDistribution

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The weight `⟨x⟩ ^ (-2K) = (1 + ‖x‖ ^ 2) ^ (-K)` as a complex function. -/
private theorem weight_eq (K : ℕ) :
    (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-(K : ℝ)) : ℝ) : ℂ)) =
      fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-(2 * K : ℝ) / 2) : ℝ) : ℂ) := by
  ext x
  congr 3
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The weight `⟨x⟩ ^ (-2K) = (1 + ‖x‖ ^ 2) ^ (-K)` has temperate growth. -/
private theorem hasTemperateGrowth_weight (K : ℕ) :
    (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-(K : ℝ)) : ℝ) : ℂ)).HasTemperateGrowth := by
  rw [weight_eq K]
  fun_prop

end TemperedDistribution

namespace SchwartzMap

open TemperedDistribution in
/-- **Weighted Schwartz seminorms are controlled by Sobolev norms.** For `k ≤ 2K`, the seminorm
`sup ‖x‖ ^ k ‖D^l (⟨x⟩ ^ (-2K) φ)‖` is at most a constant times `‖φ‖_{H^t}` once
`t > l + n / 2`: the weight absorbs the polynomial factor, and the Sobolev embedding bounds the
derivatives of `φ` of order at most `l`. -/
theorem exists_seminorm_smulLeftCLM_one_add_norm_sq_rpow_neg_le (K : ℕ) {k l : ℕ}
    (hk : k ≤ 2 * K) {t : ℝ} (ht : Module.finrank ℝ E < 2 * (t - l)) :
    ∃ C, ∀ φ : 𝓢(E, ℂ), SchwartzMap.seminorm ℂ k l
      (SchwartzMap.smulLeftCLM ℂ (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-(K : ℝ)) : ℝ) : ℂ)) φ) ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM t 2 φ‖ := by
  set w : E → ℂ := fun x ↦ (((1 + ‖x‖ ^ 2) ^ (-(K : ℝ)) : ℝ) : ℂ)
  have hw : w.HasTemperateGrowth := hasTemperateGrowth_weight K
  -- The weight absorbs `‖x‖ ^ k` together with each of its derivatives.
  have hks : (k : ℝ) + -(2 * K : ℝ) ≤ 0 := by
    have : (k : ℝ) ≤ 2 * K := by exact_mod_cast hk
    linarith
  have hxw (i : ℕ) : ∃ C, ∀ x : E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ i w x‖ ≤ C := by
    simp only [w, weight_eq K]
    exact TauCeti.exists_norm_pow_mul_norm_iteratedFDeriv_ofReal_one_add_norm_sq_rpow_half_le hks i
  choose Cw hCw using hxw
  obtain ⟨Cg, hCg0, hD⟩ :=
    exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpaceCLM (F := ℂ) (k := l) ht
  refine ⟨(∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * |Cw i|) * Cg, fun φ ↦ ?_⟩
  have hcoe : ⇑(SchwartzMap.smulLeftCLM ℂ w φ) = fun x ↦ w x * φ x :=
    funext fun x ↦ SchwartzMap.smulLeftCLM_apply_apply hw φ x
  refine SchwartzMap.seminorm_le_bound ℂ k l _ (by positivity) fun x ↦ ?_
  rw [hcoe]
  refine (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le (N := l) (hw.1.of_le
    (mod_cast le_top)) (φ.smooth l) x le_rfl) (by positivity)).trans ?_
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hil : l - i ≤ l := Nat.sub_le l i
  calc ‖x‖ ^ k * ((l.choose i : ℝ) * ‖iteratedFDeriv ℝ i w x‖ * ‖iteratedFDeriv ℝ (l - i) φ x‖)
      = (l.choose i : ℝ) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ i w x‖) *
          ‖iteratedFDeriv ℝ (l - i) φ x‖ := by ring
    _ ≤ (l.choose i : ℝ) * |Cw i| * (Cg * ‖SchwartzMap.toBesselPotentialSpaceCLM t 2 φ‖) := by
        gcongr
        · exact (hCw i x).trans (le_abs_self _)
        · exact hD φ _ hil x
    _ = _ := by ring

end SchwartzMap

namespace TemperedDistribution

/-- **Tempered distributions have finite weighted Sobolev order.** Every scalar tempered
distribution `u` becomes an element of a Sobolev space `H^s` after multiplication by a negative
power `⟨x⟩ ^ (-2K) = (1 + ‖x‖ ^ 2) ^ (-K)` of the Japanese bracket. Equivalently,
`u = (1 + ‖x‖ ^ 2) ^ K v` with `v ∈ H^s`. -/
theorem exists_memSobolev_smulLeftCLM_one_add_norm_sq_rpow_neg (u : 𝓢'(E, ℂ)) :
    ∃ (K : ℕ) (s : ℝ), (smulLeftCLM ℂ (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-(K : ℝ)) : ℝ) : ℂ))
      u).MemSobolev s 2 := by
  -- `u` is bounded by finitely many Schwartz seminorms.
  have hq : Continuous ((normSeminorm ℂ ℂ).comp (u : 𝓢(E, ℂ) →L[ℂ] ℂ).toLinearMap) :=
    continuous_norm.comp (u : 𝓢(E, ℂ) →L[ℂ] ℂ).continuous
  obtain ⟨S, c, -, hc⟩ := Seminorm.bound_sum_of_continuous (schwartz_withSeminorms ℂ E ℂ) _ hq
  have hc' (φ : 𝓢(E, ℂ)) : ‖u φ‖ ≤ c * ∑ i ∈ S, SchwartzMap.seminorm ℂ i.1 i.2 φ :=
    (hc φ).trans_eq (by simp [schwartzSeminormFamily, NNReal.smul_def])
  set N := S.sup fun i ↦ i.1 + i.2
  have hN (i : ℕ × ℕ) (hi : i ∈ S) : i.1 ≤ N ∧ i.2 ≤ N := by
    have := Finset.le_sup (f := fun i : ℕ × ℕ ↦ i.1 + i.2) hi
    constructor <;> omega
  set t : ℝ := N + Module.finrank ℝ E / 2 + 1
  have ht (i : ℕ × ℕ) (hi : i ∈ S) : Module.finrank ℝ E < 2 * (t - i.2) := by
    have : (i.2 : ℝ) ≤ N := by exact_mod_cast (hN i hi).2
    simp only [t]
    linarith
  have hC (i : ℕ × ℕ) : ∃ C, i ∈ S → ∀ φ : 𝓢(E, ℂ), SchwartzMap.seminorm ℂ i.1 i.2
      (SchwartzMap.smulLeftCLM ℂ (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-(N : ℝ)) : ℝ) : ℂ)) φ) ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM t 2 φ‖ := by
    by_cases hi : i ∈ S
    · obtain ⟨C, hC⟩ := SchwartzMap.exists_seminorm_smulLeftCLM_one_add_norm_sq_rpow_neg_le N
        (k := i.1) (l := i.2) (by have := (hN i hi).1; omega) (ht i hi)
      exact ⟨C, fun _ ↦ hC⟩
    · exact ⟨0, fun h ↦ absurd h hi⟩
  choose C hC using hC
  refine ⟨N, -t, memSobolev_neg_of_norm_le (C := c * ∑ i ∈ S, C i) fun φ ↦ ?_⟩
  rw [smulLeftCLM_apply_apply]
  refine (hc' _).trans ?_
  rw [mul_assoc, Finset.sum_mul]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi ↦ hC i hi φ) c.property

/-- **Structure of tempered distributions.** Every scalar tempered distribution `u` is
`(1 + ‖x‖ ^ 2) ^ K` times a tempered distribution of finite Sobolev order. -/
theorem exists_memSobolev_eq_smulLeftCLM_one_add_norm_sq_pow (u : 𝓢'(E, ℂ)) :
    ∃ (K : ℕ) (s : ℝ) (v : 𝓢'(E, ℂ)), v.MemSobolev s 2 ∧
      u = smulLeftCLM ℂ (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ K : ℝ) : ℂ)) v := by
  obtain ⟨K, s, hS⟩ := exists_memSobolev_smulLeftCLM_one_add_norm_sq_rpow_neg u
  refine ⟨K, s, _, hS, ?_⟩
  have hwp : (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-(K : ℝ)) : ℝ) : ℂ)) *
      (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ K : ℝ) : ℂ)) = fun _ ↦ 1 := by
    ext x
    have h1 : 0 < 1 + ‖x‖ ^ 2 := by positivity
    rw [Pi.mul_apply, ← Complex.ofReal_mul, Real.rpow_neg h1.le, Real.rpow_natCast,
      inv_mul_cancel₀ (pow_ne_zero _ h1.ne'), Complex.ofReal_one]
  rw [smulLeftCLM_smulLeftCLM_apply (hasTemperateGrowth_weight K) (by fun_prop), hwp,
    smulLeftCLM_const, one_smul]

/-- **Local finite Sobolev order.** For every scalar tempered distribution `u` and Schwartz function
`ψ`, the product `ψ u` lies in some Sobolev space `H^s`. -/
theorem exists_memSobolev_smulLeftCLM (u : 𝓢'(E, ℂ)) (ψ : 𝓢(E, ℂ)) :
    ∃ s : ℝ, (smulLeftCLM ℂ (ψ : E → ℂ) u).MemSobolev s 2 := by
  obtain ⟨K, s, v, hv, rfl⟩ := exists_memSobolev_eq_smulLeftCLM_one_add_norm_sq_pow u
  have hp : (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ K : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  refine ⟨s, ?_⟩
  rw [smulLeftCLM_smulLeftCLM_apply hp ψ.hasTemperateGrowth]
  exact hv.smulLeftCLM_mul hp ψ

end TemperedDistribution
