/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import TauCeti.Analysis.Sobolev.Wkp.Density
public import TauCeti.Analysis.Sobolev.Wkp.ZeroAtInfty
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.Distribution.TestFunction.ZeroAtInfty
import TauCeti.Analysis.FunctionalSpaces.SobolevInequality

/-!
# The critical Sobolev embedding `W^{n,1}(ℝⁿ) ⊆ C₀(ℝⁿ)`

Let `E` be a finite-dimensional real inner product space of dimension `n`, with its Lebesgue
measure. This file proves that for every order `k ≥ n` each function in the whole-space
weak-derivative Sobolev space `W^{k,1}(E)` agrees almost everywhere with a unique continuous
function vanishing at infinity, and that

`sup_x |u(x)| ≤ ‖u‖_{W^{k,1}}`.

The bundled map is `TauCeti.Wkp.toZeroAtInftyOne`, a continuous linear map
`W^{k,1}(E) →L[ℝ] C₀(E)` of norm at most `1`.

This is the critical case `kp = n` of the embedding of `W^{k,p}` into the continuous functions,
which fails for `p > 1`. For `p = 1` it holds because of the pointwise bound `|φ(x)| ≤ ∫ ‖Dⁿφ‖`
for test functions (`HasCompactSupport.eNorm_le_lintegral_iteratedFDeriv`).

## The argument

Test functions are dense in `W^{k,1}(E)` (`TauCeti.Wkp.denseRange_ofTestFunctionₗ_top`). For a
test function `φ`, the pointwise bound together with
`TauCeti.Wkp.lpNorm_iteratedFDeriv_le_of_contDiffOn` gives `sup |φ| ≤ ‖φ‖_{W^{k,1}}`. A sequence of
test functions converging to `u` in `W^{k,1}` is therefore uniformly Cauchy, and converges in the
complete space `C₀(E)` to a function `g`. Along a subsequence the test functions also converge to
`u` almost everywhere, so `g` represents `u`. Two continuous functions that agree almost everywhere
are equal, so the representative is unique and depends linearly on `u`. This last step does not
depend on `k`, `p` or the dimension, and is `TauCeti.Wkp.toZeroAtInftyOfExists`.

## Main declarations

* `TauCeti.Wkp.toZeroAtInftyOne`: the Sobolev embedding `W^{k,1}(E) →L[ℝ] C₀(E)` for
  `dim E ≤ k`.
* `TauCeti.Wkp.value_ae_eq_toZeroAtInftyOne`, `TauCeti.Wkp.toZeroAtInftyOne_eq_iff`: the embedding
  sends a Sobolev function to its unique continuous representative.
* `TauCeti.Wkp.coe_toZeroAtInftyOne_ofTestFunctionₗ`: the embedding sends a test function to
  itself.
* `TauCeti.Wkp.norm_toZeroAtInftyOne_le`: the bound `sup_x |u(x)| ≤ ‖u‖_{W^{k,1}}`.
* `TauCeti.Wkp.toZeroAtInftyOne_injective`: the continuous representative determines the Sobolev
  function.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.12, Part I, Case A, for
  `p = 1` and `m = n`.
-/

public section

noncomputable section

open MeasureTheory Filter Module Topology TopologicalSpace
open scoped ZeroAtInfty Distributions ENNReal

namespace TauCeti

namespace Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {k : ℕ}

/-- **The critical Sobolev inequality for test functions.** For `dim E ≤ k`, the values of a test
function are bounded by its `W^{k,1}` norm. -/
private theorem norm_apply_le_norm_ofTestFunctionₗ (hk : finrank ℝ E ≤ k)
    (φ : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    ‖φ x‖ ≤ ‖ofTestFunctionₗ (mu := (volume : Measure E)) (p := 1) k φ‖ := by
  have hvolume : (volume : Measure E).restrict ((⊤ : Opens E) : Set E) = volume := by simp
  have hvalue : (value k (ofTestFunctionₗ (mu := (volume : Measure E)) (p := 1) k φ) : E → ℝ)
      =ᵐ[(volume : Measure E).restrict (⊤ : Opens E)] φ :=
    ae_restrict_of_ae (value_ofTestFunctionₗ_top_ae k φ)
  have hle := lpNorm_iteratedFDeriv_le_of_contDiffOn k _
    (φ.contDiff.of_le (by exact_mod_cast le_top)).contDiffOn hvalue _ hk
  have hmem : MemLp (iteratedFDeriv ℝ (finrank ℝ E) (φ : E → ℝ)) 1 volume :=
    (φ.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).memLp_of_hasCompactSupport
      (φ.hasCompactSupport.iteratedFDeriv _)
  rw [hvolume] at hle
  rw [← ENNReal.ofReal_le_ofReal_iff (norm_nonneg _), ofReal_norm]
  calc ‖φ x‖ₑ ≤ ∫⁻ y, ‖iteratedFDeriv ℝ (finrank ℝ E) (φ : E → ℝ) y‖ₑ :=
        HasCompactSupport.eNorm_le_lintegral_iteratedFDeriv
          (φ.contDiff.of_le (by exact_mod_cast le_top)) φ.hasCompactSupport x
    _ = ENNReal.ofReal (lpNorm (iteratedFDeriv ℝ (finrank ℝ E) (φ : E → ℝ)) 1 volume) := by
        rw [ofReal_lpNorm hmem, eLpNorm_one_eq_lintegral_eNorm hmem.aestronglyMeasurable]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hle

/-- For `dim E ≤ k`, every function in `W^{k,1}(E)` agrees almost everywhere with a continuous
function vanishing at infinity, whose supremum is at most the `W^{k,1}` norm. The bundled form is
`TauCeti.Wkp.toZeroAtInftyOne`. -/
private theorem exists_zeroAtInftyContinuousMap_ae_eq_and_norm_le (hk : finrank ℝ E ≤ k)
    (u : Wkp (volume : Measure E) ⊤ 1 k) :
    ∃ g : C₀(E, ℝ), value k u =ᵐ[volume] g ∧ ‖g‖ ≤ ‖u‖ := by
  let D := ofTestFunctionₗ (mu := (volume : Measure E)) (Omega := ⊤) (p := 1) k
  -- Test functions `φ j` converging to `u` in `W^{k,1}`.
  obtain ⟨w, hwD, hw⟩ := mem_closure_iff_seq_limit.1
    ((denseRange_ofTestFunctionₗ_top (mu := (volume : Measure E)) ENNReal.one_ne_top k) u)
  choose φ hφ using hwD
  let G := TestFunction.toZeroAtInftyCLM ℝ (Ω := (⊤ : Opens E)) (F := ℝ) (n := ⊤)
  have hG (ψ : 𝓓((⊤ : Opens E), ℝ)) : value k (D ψ) =ᵐ[volume] G ψ := by
    simpa only [G, TestFunction.coe_toZeroAtInftyCLM] using value_ofTestFunctionₗ_top_ae k ψ
  have hDφ : Tendsto (fun j => D (φ j)) atTop (𝓝 u) := by simpa only [D, hφ] using hw
  have hnorm (ψ : 𝓓((⊤ : Opens E), ℝ)) : ‖G ψ‖ ≤ ‖D ψ‖ := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
      BoundedContinuousFunction.norm_le (norm_nonneg _)]
    simpa [G] using norm_apply_le_norm_ofTestFunctionₗ hk ψ
  -- Their continuous versions form a Cauchy sequence in `C₀`, with a limit `g`.
  have hcauchy : CauchySeq fun j => G (φ j) := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hDφ.cauchySeq ε hε
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm, ← map_sub]
    refine (hnorm _).trans_lt ?_
    rw [map_sub, ← dist_eq_norm]
    exact hN i hi j hj
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨g, value_ae_eq_of_tendsto hDφ (fun j => hG (φ j)) hg,
    le_of_tendsto_of_tendsto' hg.norm hDφ.norm fun j => hnorm (φ j)⟩

/-- **The critical Sobolev embedding `W^{k,1}(ℝⁿ) →L[ℝ] C₀(ℝⁿ)`** for `dim E ≤ k`: the bounded
linear map sending a function in the whole-space weak-derivative Sobolev space `W^{k,1}` to its
unique representative that is continuous and vanishes at infinity. Its boundedness is the estimate
`sup_x |u(x)| ≤ ‖u‖_{W^{k,1}}` (`TauCeti.Wkp.norm_toZeroAtInftyOne_le`). -/
def toZeroAtInftyOne (hk : finrank ℝ E ≤ k) : Wkp (volume : Measure E) ⊤ 1 k →L[ℝ] C₀(E, ℝ) :=
  toZeroAtInftyOfExists fun u => (exists_zeroAtInftyContinuousMap_ae_eq_and_norm_le hk u).imp
    fun _ hg => hg.1

/-- The Sobolev embedding sends a Sobolev function to a representative of its value. -/
theorem value_ae_eq_toZeroAtInftyOne (hk : finrank ℝ E ≤ k)
    (u : Wkp (volume : Measure E) ⊤ 1 k) :
    value k u =ᵐ[volume] toZeroAtInftyOne hk u :=
  value_ae_eq_toZeroAtInftyOfExists _ u

/-- The Sobolev embedding of `u` is the only function in `C₀` representing the value of `u`. -/
theorem toZeroAtInftyOne_eq_iff (hk : finrank ℝ E ≤ k) (u : Wkp (volume : Measure E) ⊤ 1 k)
    (g : C₀(E, ℝ)) :
    toZeroAtInftyOne hk u = g ↔ value k u =ᵐ[volume] g :=
  toZeroAtInftyOfExists_eq_iff _ u g

/-- The Sobolev embedding sends a test function to itself. -/
@[simp]
theorem coe_toZeroAtInftyOne_ofTestFunctionₗ (hk : finrank ℝ E ≤ k) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    ⇑(toZeroAtInftyOne hk (ofTestFunctionₗ k φ)) = φ := by
  rw [(toZeroAtInftyOne_eq_iff hk _ (TestFunction.toZeroAtInftyCLM ℝ φ)).2,
    TestFunction.coe_toZeroAtInftyCLM]
  simpa only [TestFunction.coe_toZeroAtInftyCLM] using value_ofTestFunctionₗ_top_ae k φ

/-- **The critical Sobolev inequality** `sup_x |u(x)| ≤ ‖u‖_{W^{k,1}}` for `dim E ≤ k`. -/
theorem norm_toZeroAtInftyOne_le (hk : finrank ℝ E ≤ k) (u : Wkp (volume : Measure E) ⊤ 1 k) :
    ‖toZeroAtInftyOne hk u‖ ≤ ‖u‖ := by
  obtain ⟨g, hg, hgu⟩ := exists_zeroAtInftyContinuousMap_ae_eq_and_norm_le hk u
  rwa [(toZeroAtInftyOne_eq_iff hk u g).2 hg]

/-- The Sobolev embedding has operator norm at most `1`. -/
theorem opNorm_toZeroAtInftyOne_le (hk : finrank ℝ E ≤ k) :
    ‖toZeroAtInftyOne (E := E) hk‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    rw [one_mul]
    exact norm_toZeroAtInftyOne_le hk u

/-- The Sobolev embedding is injective: the continuous representative determines the Sobolev
function. -/
theorem toZeroAtInftyOne_injective (hk : finrank ℝ E ≤ k) :
    Function.Injective (toZeroAtInftyOne (E := E) hk) :=
  toZeroAtInftyOfExists_injective _

end Wkp

end TauCeti
