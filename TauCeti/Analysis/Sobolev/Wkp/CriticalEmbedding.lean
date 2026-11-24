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
import TauCeti.Analysis.Sobolev.WeakDeriv.Classical
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv

/-!
# The critical Sobolev embeddings `W^{n,1}(ℝⁿ) ⊆ C₀(ℝⁿ)` and `W^{n+j,1}(ℝⁿ) ⊆ Cʲ(ℝⁿ)`

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

More generally, for `k ≥ n + j` the continuous representative of `u ∈ W^{k,1}(E)` is `Cʲ`, and each
of its derivatives of order `i ≤ j` vanishes at infinity and is bounded by a constant multiple of
`‖u‖_{W^{k,1}}`. Hence `u` lies in `W^{j,∞}(E)`, and `TauCeti.Wkp.toWkpTopOne` is the resulting
continuous linear map `W^{k,1}(E) →L[ℝ] W^{j,∞}(E)`. These are the integer endpoint embeddings
`W^{n+j,1} → Cʲ` and `W^{n+j,1} → W^{j,∞}` at the critical exponent `p = 1`, the Euclidean input
for the corresponding embeddings of Sobolev sections over compact manifolds.

## The argument

Test functions are dense in `W^{k,1}(E)` (`TauCeti.Wkp.denseRange_ofTestFunctionₗ_top`). For a
test function `φ`, the pointwise bound together with
`TauCeti.Wkp.lpNorm_iteratedFDeriv_le_of_contDiffOn` gives `sup |φ| ≤ ‖φ‖_{W^{k,1}}`. A sequence of
test functions converging to `u` in `W^{k,1}` is therefore uniformly Cauchy, and converges in the
complete space `C₀(E)` to a function `g`. Along a subsequence the test functions also converge to
`u` almost everywhere, so `g` represents `u`. Two continuous functions that agree almost everywhere
are equal, so the representative is unique and depends linearly on `u`. This last step does not
depend on `k`, `p` or the dimension, and is `TauCeti.Wkp.toZeroAtInftyOfExists`.

For the derivatives, induct on `j`. The weak derivatives `∂ₗu` of `u ∈ W^{n+j+1,1}(E)` along an
orthonormal basis lie in `W^{n+j,1}(E)` (`TauCeti.Wkp.lineDerivL`), so by induction their continuous
representatives `Gₗ` are `Cʲ`, with bounded derivatives vanishing at infinity. Assembled into a
field of linear maps, they form a continuous weak derivative of the continuous representative of
`u`, which is therefore its classical derivative (`TauCeti.HasWeakFDerivOn.contDiffOn_succ`). The
`(i + 1)`-th derivative of the representative is then controlled by the `i`-th derivatives of the
`Gₗ`. The induction follows that of
`TauCeti.Wkp.exists_contDiffOn_holderOnWith_iteratedFDeriv_of_forall_holderSpaceL`.

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
* `TauCeti.Wkp.contDiff_toZeroAtInftyOne`: for `dim E + j ≤ k`, the continuous representative
  of a function in `W^{k,1}(E)` is `Cʲ`.
* `TauCeti.Wkp.exists_norm_iteratedFDeriv_toZeroAtInftyOne_le`,
  `TauCeti.Wkp.tendsto_iteratedFDeriv_toZeroAtInftyOne`: for `dim E + i ≤ k`, its `i`-th derivative
  is bounded by a constant multiple of `‖u‖_{W^{k,1}}` and tends to zero at infinity.
* `TauCeti.Wkp.toWkpTopOne`: the Sobolev embedding `W^{k,1}(E) →L[ℝ] W^{j,∞}(E)` for
  `dim E + j ≤ k`, characterized by `TauCeti.Wkp.value_toWkpTopOne_ae_eq` and
  `TauCeti.Wkp.toWkpTopOne_eq_iff`.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.12, Part I, Case A, for
  `p = 1` and `m = n`, and the embeddings `W^{j+m,1} → C^j_B` and `W^{j+m,1} → W^{j,∞}` of the
  same case.
-/

public section

noncomputable section

open MeasureTheory Filter Module Topology TopologicalSpace
open scoped ZeroAtInfty Distributions ENNReal NNReal

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

/-! ### Derivatives: `W^{n+j,1}(ℝⁿ) ⊆ Cʲ` -/

/-- The continuous representative, as its own zeroth derivative, is bounded by the `W^{k,1}` norm
and tends to zero at infinity. -/
private theorem iteratedFDeriv_zero_toZeroAtInftyOne (hk : finrank ℝ E ≤ k)
    (u : Wkp (volume : Measure E) ⊤ 1 k) :
    (∀ x, ‖iteratedFDeriv ℝ 0 ⇑(toZeroAtInftyOne hk u) x‖ ≤ ‖u‖) ∧
      Tendsto (iteratedFDeriv ℝ 0 ⇑(toZeroAtInftyOne hk u)) (cocompact E) (𝓝 0) := by
  refine ⟨fun x => ?_, tendsto_zero_iff_norm_tendsto_zero.2 ?_⟩
  · rw [norm_iteratedFDeriv_zero]
    exact ((toZeroAtInftyOne hk u).toBCF.norm_coe_le_norm x).trans
      (ZeroAtInftyContinuousMap.norm_toBCF_eq_norm.trans_le (norm_toZeroAtInftyOne_le hk u))
  · simpa only [norm_iteratedFDeriv_zero] using
      tendsto_zero_iff_norm_tendsto_zero.1 (zero_at_infty (toZeroAtInftyOne hk u))

/-- The inductive step of the `Cʲ` embedding: if each `u ∈ W^{dim E + j,1}(E)` agrees almost
everywhere with a `Cʲ` function whose derivatives of order at most `j` are bounded by `K ‖u‖` and
tend to zero at infinity, the same holds one order higher. The derivatives of `u` along an
orthonormal basis have such representatives, and these are the derivatives of the continuous
representative of `u`. -/
private theorem exists_contDiff_ae_eq_and_iteratedFDeriv_succ {j : ℕ}
    (hK : ∃ K : ℝ≥0, ∀ u : Wkp (volume : Measure E) ⊤ 1 (finrank ℝ E + j),
        ∃ g : E → ℝ, ContDiff ℝ j g ∧ (value (finrank ℝ E + j) u : E → ℝ) =ᵐ[volume] g ∧
          ∀ i ≤ j, (∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ K * ‖u‖) ∧
            Tendsto (iteratedFDeriv ℝ i g) (cocompact E) (𝓝 0)) :
    ∃ K : ℝ≥0, ∀ u : Wkp (volume : Measure E) ⊤ 1 (finrank ℝ E + (j + 1)),
      ∃ g : E → ℝ, ContDiff ℝ (j + 1 : ℕ) g ∧
        (value (finrank ℝ E + (j + 1)) u : E → ℝ) =ᵐ[volume] g ∧
          ∀ i ≤ j + 1, (∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ K * ‖u‖) ∧
            Tendsto (iteratedFDeriv ℝ i g) (cocompact E) (𝓝 0) := by
  obtain ⟨K, hK⟩ := hK
  let b := stdOrthonormalBasis ℝ E
  -- The weak derivative along `b l`.
  let D : Fin (finrank ℝ E) → Wkp (volume : Measure E) ⊤ 1 (finrank ℝ E + j + 1) →L[ℝ]
      Wkp (volume : Measure E) ⊤ 1 (finrank ℝ E + j) :=
    fun l => lineDerivL (b l) (finrank ℝ E + j)
  let c : ℝ≥0 := ∑ l, K * ‖D l‖₊
  refine ⟨max 1 c, fun u => ?_⟩
  -- The continuous representative `g` of `u`.
  let T := toZeroAtInftyOne (E := E) (k := finrank ℝ E + (j + 1)) (by omega)
  have hgc : Continuous (T u) := (T u).continuous
  -- Representatives `G l` of the derivatives of `u` along `b`, with the bounds of order `j`.
  choose G hG hdG hGb using fun l => hK (D l u)
  have hdG' : ∀ l, HasWeakLineDerivOn volume ⊤ (T u) (G l) (b l) := fun l =>
    ((hasWeakLineDerivOn_lineDerivL (b l) (finrank ℝ E + j) u).congr_ae
      (ae_restrict_of_ae (value_ae_eq_toZeroAtInftyOne _ u))).congr_ae_deriv
        (ae_restrict_of_ae (hdG l))
  -- The derivatives of `g` of positive order are controlled by those of the `G l`.
  have hit : ∀ i ≤ j, ∀ x, ‖iteratedFDeriv ℝ (i + 1) (T u) x‖ ≤
      ∑ l, ‖iteratedFDeriv ℝ i (G l) x‖ := fun i hi x =>
    norm_iteratedFDeriv_succ_le_sum_of_forall_hasWeakLineDerivOn hgc.continuousOn
      (fun l => (hG l).contDiffOn) hdG' (by exact_mod_cast hi) (by simp)
  refine ⟨T u, ?_, value_ae_eq_toZeroAtInftyOne _ u, fun i hi => ?_⟩
  · have h := contDiffOn_succ_of_forall_hasWeakLineDerivOn hgc.continuousOn
      (n := (j : ℕ∞)) (fun l => (hG l).contDiffOn) hdG'
    rw [Opens.coe_top, contDiffOn_univ] at h
    exact_mod_cast h
  rcases i with _ | i
  · refine ⟨fun x => ((iteratedFDeriv_zero_toZeroAtInftyOne _ u).1 x).trans
      (le_mul_of_one_le_left (norm_nonneg u) ?_), (iteratedFDeriv_zero_toZeroAtInftyOne _ u).2⟩
    exact_mod_cast le_max_left 1 c
  have hi : i ≤ j := Nat.le_of_succ_le_succ hi
  refine ⟨fun x => ?_, squeeze_zero_norm (hit i hi) ?_⟩
  · calc ‖iteratedFDeriv ℝ (i + 1) (T u) x‖
        ≤ ∑ l, K * ‖D l‖ * ‖u‖ := (hit i hi x).trans (Finset.sum_le_sum fun l _ =>
          ((hGb l i hi).1 x).trans (by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left ((D l).le_opNorm u) K.coe_nonneg))
      _ = c * ‖u‖ := by simp only [c, NNReal.coe_sum, NNReal.coe_mul, coe_nnNorm, Finset.sum_mul]
      _ ≤ max 1 c * ‖u‖ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast le_max_right _ _) (norm_nonneg u)
  · simpa only [Function.comp_def, norm_zero, Finset.sum_const_zero] using
      tendsto_finsetSum _ fun l _ => tendsto_norm_zero.comp ((hGb l i hi).2)

/-- The induction behind the `Cʲ` embedding, at the orders `dim E + j`: each
`u ∈ W^{dim E + j,1}(E)` agrees almost everywhere with a `Cʲ` function whose derivatives of order
at most `j` are bounded by `K ‖u‖` and tend to zero at infinity. -/
private theorem exists_contDiff_ae_eq_and_iteratedFDeriv :
    ∀ j : ℕ, ∃ K : ℝ≥0, ∀ u : Wkp (volume : Measure E) ⊤ 1 (finrank ℝ E + j),
      ∃ g : E → ℝ, ContDiff ℝ j g ∧ (value (finrank ℝ E + j) u : E → ℝ) =ᵐ[volume] g ∧
        ∀ i ≤ j, (∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ K * ‖u‖) ∧
          Tendsto (iteratedFDeriv ℝ i g) (cocompact E) (𝓝 0)
  | 0 => by
    let T := toZeroAtInftyOne (E := E) (k := finrank ℝ E + 0) le_rfl
    refine ⟨1, fun u => ⟨T u, ?_, value_ae_eq_toZeroAtInftyOne _ u, fun i hi => ?_⟩⟩
    · rw [Nat.cast_zero, contDiff_zero]
      exact (T u).continuous
    · obtain rfl := Nat.le_zero.1 hi
      simpa only [NNReal.coe_one, one_mul] using iteratedFDeriv_zero_toZeroAtInftyOne _ u
  | j + 1 => exists_contDiff_ae_eq_and_iteratedFDeriv_succ
    (exists_contDiff_ae_eq_and_iteratedFDeriv j)

/-- The derivatives of the continuous representative: for `dim E + j ≤ k`, the continuous
representative of `u ∈ W^{k,1}(E)` is `Cʲ`, and its derivatives of order at most `j` are bounded
by `K ‖u‖` and tend to zero at infinity. -/
private theorem exists_contDiff_toZeroAtInftyOne (hk : finrank ℝ E ≤ k) {j : ℕ}
    (hj : finrank ℝ E + j ≤ k) :
    ∃ K : ℝ≥0, ∀ u : Wkp (volume : Measure E) ⊤ 1 k, ContDiff ℝ j ⇑(toZeroAtInftyOne hk u) ∧
      ∀ i ≤ j, (∀ x, ‖iteratedFDeriv ℝ i ⇑(toZeroAtInftyOne hk u) x‖ ≤ K * ‖u‖) ∧
        Tendsto (iteratedFDeriv ℝ i ⇑(toZeroAtInftyOne hk u)) (cocompact E) (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_contDiff_ae_eq_and_iteratedFDeriv (E := E) j
  refine ⟨K, fun u => ?_⟩
  -- Truncate `u` to the order `dim E + j`; the representatives of the two agree.
  obtain ⟨g, hg, hug, hgb⟩ := hK (toOrderL hj u)
  have hgu : ⇑(toZeroAtInftyOne hk u) = g := (Continuous.ae_eq_iff_eq volume
    (toZeroAtInftyOne hk u).continuous hg.continuous).1
      ((value_ae_eq_toZeroAtInftyOne hk u).symm.trans (by rwa [value_toOrderL] at hug))
  rw [hgu]
  refine ⟨hg, fun i hi => ⟨fun x => ((hgb i hi).1 x).trans ?_, (hgb i hi).2⟩⟩
  exact mul_le_mul_of_nonneg_left (norm_toOrderL_le hj u) K.coe_nonneg

/-- **The critical Sobolev embedding into `Cʲ`.** For `dim E + j ≤ k`, the continuous
representative of a function in `W^{k,1}(E)` is `Cʲ`. -/
theorem contDiff_toZeroAtInftyOne (hk : finrank ℝ E ≤ k) {j : ℕ} (hj : finrank ℝ E + j ≤ k)
    (u : Wkp (volume : Measure E) ⊤ 1 k) : ContDiff ℝ j ⇑(toZeroAtInftyOne hk u) :=
  ((exists_contDiff_toZeroAtInftyOne hk hj).choose_spec u).1

/-- For `dim E + i ≤ k`, the `i`-th derivative of the continuous representative of a function in
`W^{k,1}(E)` is bounded by a constant multiple of its `W^{k,1}` norm. -/
theorem exists_norm_iteratedFDeriv_toZeroAtInftyOne_le (hk : finrank ℝ E ≤ k) {i : ℕ}
    (hi : finrank ℝ E + i ≤ k) :
    ∃ C : ℝ≥0, ∀ (u : Wkp (volume : Measure E) ⊤ 1 k) (x : E),
      ‖iteratedFDeriv ℝ i ⇑(toZeroAtInftyOne hk u) x‖ ≤ C * ‖u‖ :=
  (exists_contDiff_toZeroAtInftyOne hk hi).imp fun _ hK u => ((hK u).2 i le_rfl).1

/-- For `dim E + i ≤ k`, the `i`-th derivative of the continuous representative of a function in
`W^{k,1}(E)` tends to zero at infinity. -/
theorem tendsto_iteratedFDeriv_toZeroAtInftyOne (hk : finrank ℝ E ≤ k) {i : ℕ}
    (hi : finrank ℝ E + i ≤ k) (u : Wkp (volume : Measure E) ⊤ 1 k) :
    Tendsto (iteratedFDeriv ℝ i ⇑(toZeroAtInftyOne hk u)) (cocompact E) (𝓝 0) :=
  (((exists_contDiff_toZeroAtInftyOne hk hi).choose_spec u).2 i le_rfl).2

/-! ### The embedding `W^{n+j,1}(ℝⁿ) → W^{j,∞}(ℝⁿ)` -/

/-- For `dim E + j ≤ k`, the continuous representative of `u ∈ W^{k,1}(E)` is `Cʲ` with bounded
derivatives, so it represents an element of `W^{j,∞}(E)` of norm at most `C ‖u‖`. -/
private theorem exists_wkp_top_value_ae_eq {j : ℕ} (hj : finrank ℝ E + j ≤ k) :
    ∃ C : ℝ≥0, ∀ u : Wkp (volume : Measure E) ⊤ 1 k, ∃ w : Wkp (volume : Measure E) ⊤ ∞ j,
      value j w =ᵐ[volume] value k u ∧ ‖w‖ ≤ C * ‖u‖ := by
  have hk : finrank ℝ E ≤ k := (Nat.le_add_right _ _).trans hj
  obtain ⟨K, hK⟩ := exists_contDiff_toZeroAtInftyOne hk hj
  refine ⟨(j + 1) * K, fun u => ?_⟩
  obtain ⟨hg, hgb⟩ := hK u
  have hmeas : ∀ i ≤ j, AEStronglyMeasurable (iteratedFDeriv ℝ i ⇑(toZeroAtInftyOne hk u))
      ((volume : Measure E).restrict (⊤ : Opens E)) := fun i hi =>
    (hg.continuous_iteratedFDeriv (by exact_mod_cast hi)).aestronglyMeasurable
  have hbound : ∀ i ≤ j, eLpNorm (iteratedFDeriv ℝ i ⇑(toZeroAtInftyOne hk u)) ∞
      ((volume : Measure E).restrict (⊤ : Opens E)) ≤ ENNReal.ofReal (K * ‖u‖) := fun i hi =>
    (eLpNorm_exponent_top (hmeas i hi)).trans_le
      (eLpNormEssSup_le_of_ae_bound (ae_of_all _ (hgb i hi).1))
  obtain ⟨w, hw⟩ := exists_value_ae_eq_of_contDiffOn (mu := volume) (Omega := ⊤) (p := ∞) j
    hg.contDiffOn fun i hi => memLp_top_of_bound (hmeas i hi) _ (ae_of_all _ (hgb i hi).1)
  refine ⟨w, ?_, (norm_le_sum_lpNorm_iteratedFDeriv_of_contDiffOn j w hg.contDiffOn hw).trans ?_⟩
  · have hw' : value j w =ᵐ[volume] toZeroAtInftyOne hk u := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using hw
    exact hw'.trans (value_ae_eq_toZeroAtInftyOne hk u).symm
  · calc ∑ i ∈ Finset.range (j + 1), lpNorm (iteratedFDeriv ℝ i ⇑(toZeroAtInftyOne hk u)) ∞
          ((volume : Measure E).restrict (⊤ : Opens E))
        ≤ ∑ _i ∈ Finset.range (j + 1), K * ‖u‖ := Finset.sum_le_sum fun i hi =>
          ENNReal.toReal_le_of_le_ofReal (by positivity)
            (hbound i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))
      _ = ↑((j + 1) * K) * ‖u‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- A map `W^{k,1}(E) → W^{j,∞}(E)` preserving values is linear. -/
private def toWkpTopOneₗ {j : ℕ}
    (w : Wkp (volume : Measure E) ⊤ 1 k → Wkp (volume : Measure E) ⊤ ∞ j)
    (hw : ∀ u, value j (w u) =ᵐ[volume] value k u) :
    Wkp (volume : Measure E) ⊤ 1 k →ₗ[ℝ] Wkp (volume : Measure E) ⊤ ∞ j where
  toFun := w
  map_add' u v := by
    refine ext j (Lp.ext ?_)
    filter_upwards [ae_restrict_of_ae (hw (u + v)), ae_restrict_of_ae (hw u),
      ae_restrict_of_ae (hw v), Lp.coeFn_add (value k u) (value k v),
      Lp.coeFn_add (value j (w u)) (value j (w v))] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, value_add, value_add, h₄, h₅, Pi.add_apply, Pi.add_apply, h₂, h₃]
  map_smul' c u := by
    refine ext j (Lp.ext ?_)
    filter_upwards [ae_restrict_of_ae (hw (c • u)), ae_restrict_of_ae (hw u),
      Lp.coeFn_smul c (value k u), Lp.coeFn_smul c (value j (w u))] with x h₁ h₂ h₃ h₄
    rw [h₁, RingHom.id_apply, value_smul, value_smul, h₃, h₄, Pi.smul_apply, Pi.smul_apply, h₂]

/-- **The critical Sobolev embedding `W^{k,1}(ℝⁿ) →L[ℝ] W^{j,∞}(ℝⁿ)`** for `dim E + j ≤ k`: the
bounded linear map sending a function in `W^{k,1}(E)` to the element of `W^{j,∞}(E)` with the same
value (`TauCeti.Wkp.value_toWkpTopOne_ae_eq`). Its value is therefore also represented by the `Cʲ`
function `TauCeti.Wkp.toZeroAtInftyOne` (`TauCeti.Wkp.value_ae_eq_toZeroAtInftyOne`). -/
def toWkpTopOne {j : ℕ} (hj : finrank ℝ E + j ≤ k) :
    Wkp (volume : Measure E) ⊤ 1 k →L[ℝ] Wkp (volume : Measure E) ⊤ ∞ j :=
  have H := exists_wkp_top_value_ae_eq hj
  (toWkpTopOneₗ (fun u => (H.choose_spec u).choose) fun u => (H.choose_spec u).choose_spec.1)
    |>.mkContinuousOfExistsBound ⟨H.choose, fun u => (H.choose_spec u).choose_spec.2⟩

/-- The embedding into `W^{j,∞}` preserves the value of a Sobolev function. -/
theorem value_toWkpTopOne_ae_eq {j : ℕ} (hj : finrank ℝ E + j ≤ k)
    (u : Wkp (volume : Measure E) ⊤ 1 k) : value j (toWkpTopOne hj u) =ᵐ[volume] value k u :=
  ((exists_wkp_top_value_ae_eq hj).choose_spec u).choose_spec.1

/-- The image of `u` under the embedding into `W^{j,∞}` is the only element of `W^{j,∞}(E)` whose
value agrees with that of `u`. -/
theorem toWkpTopOne_eq_iff {j : ℕ} (hj : finrank ℝ E + j ≤ k) (u : Wkp (volume : Measure E) ⊤ 1 k)
    (w : Wkp (volume : Measure E) ⊤ ∞ j) :
    toWkpTopOne hj u = w ↔ value j w =ᵐ[volume] value k u :=
  ⟨fun h => h ▸ value_toWkpTopOne_ae_eq hj u,
    fun h => ext j (Lp.ext (ae_restrict_of_ae ((value_toWkpTopOne_ae_eq hj u).trans h.symm)))⟩

/-- The embedding into `W^{j,∞}` is injective. -/
theorem toWkpTopOne_injective {j : ℕ} (hj : finrank ℝ E + j ≤ k) :
    Function.Injective (toWkpTopOne (E := E) hj) := fun u v huv =>
  ext k (Lp.ext (ae_restrict_of_ae
    ((value_toWkpTopOne_ae_eq hj u).symm.trans (huv ▸ value_toWkpTopOne_ae_eq hj v))))

end Wkp

end TauCeti
