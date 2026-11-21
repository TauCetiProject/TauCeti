/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Transpose
public import TauCeti.Analysis.Pseudodifferential.Sobolev
public import TauCeti.Analysis.Pseudodifferential.Symbol.LineSpatialDeriv
public import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier
import TauCeti.Analysis.Pseudodifferential.Recovery
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz

/-!
# Pseudodifferential operators on tempered distributions

Let `a` be a scalar symbol of order `m` on `ℝⁿ` whose estimates hold uniformly in the position
(`TauCeti.Symbol.IsUniform`). Its quantization `Op(a)` is a continuous operator on Schwartz space
(`TauCeti.Symbol.quantizeUniformCLM`), and so is its transpose `Op(a)ᵗ` for the bilinear pairing
`⟨φ, u⟩ = ∫ φ u`: `∫ φ · Op(a) u = ∫ Op(a)ᵗ φ · u` for all Schwartz functions `u` and `φ`
(`TauCeti.Symbol.transposeUniformCLM`, `TauCeti.Symbol.integral_mul_quantizeUniformCLM`). The
transpose is obtained from the formal adjoint `Op_R(ā)`
(`TauCeti.Symbol.integral_inner_quantizeUniformCLM`) by conjugating its input and output, and it
is the only operator with this property (`TauCeti.Symbol.eq_transposeUniformCLM`).

Duality then extends `Op(a)` to tempered distributions with values in any topological vector
space `F`: `Op(a) T = T ∘ Op(a)ᵗ` (`TauCeti.Symbol.quantizeTempered`), a continuous operator on
`𝓢'(ℝⁿ, F)` for the topology of pointwise convergence. On the tempered distribution of a Schwartz
function `u` it gives the tempered distribution of `Op(a) u`
(`TauCeti.Symbol.quantizeTempered_toTemperedDistributionCLM`), and every Sobolev realization
`H^s → H^r` of `Op(a)`, such as `TauCeti.Symbol.quantizeSobolev` for a symbol with compact spatial
support, is the restriction of this one operator to `H^s`
(`TauCeti.Symbol.toDistr_eq_quantizeTempered`, `TauCeti.Symbol.toDistr_quantizeSobolev`).
Pseudodifferential operators thus act on arbitrary tempered distributions, as needed for
distributional regularity and for wave front sets, compatibly with all their Sobolev mappings.

The rules of the calculus on Schwartz space carry over to distributions, since an identity between
transposes is detected by testing against Schwartz functions:

* a constant symbol `T` acts as multiplication by `T 1`, so the symbol `1` is the identity
  (`TauCeti.Symbol.quantizeTempered_const`);
* `∂_j (Op(a) T) = Op(a) (∂_j T) + Op(∂_{x_j} a) T`
  (`TauCeti.Symbol.lineDerivOp_quantizeTempered`), with distributional derivatives;
* `Op(a) (∂_v T) = i Op(a ⟪ξ, v⟫) T` (`TauCeti.Symbol.quantizeTempered_lineDerivOp`);
* `x_j Op(a) T = Op(a) (x_j T) + i Op(∂_{ξ_j} a) T` (`TauCeti.Symbol.smulLeftCLM_quantizeTempered`);
* for `b` with compact spatial support, `Op(a # b) = Op(a) ∘ Op(b)` on tempered distributions
  (`TauCeti.Symbol.quantizeTempered_sharp`), from the same identity on Schwartz space
  (`TauCeti.Symbol.quantizeUniformCLM_sharp`);
* for a Fourier multiplier `g(D)` in the frequency `ζ = ξ / 2π`, `Op(a) ∘ g(D) = Op(g(ξ / 2π) a)`
  (`TauCeti.Symbol.IsUniform.quantizeTempered_fourierMultiplierCLM`); with the Bessel potential
  `J^m` this reduces a symbol of order `m` to one of order `0`,
  `Op(a) = Op(a ⟨ξ / 2π⟩ ^ (-m)) ∘ J^m`
  (`TauCeti.Symbol.IsUniform.quantizeTempered_eq_comp_besselPotential`);
* `∂_v (Op(a) T) = Op(a) (∂_v T) + Op(∂_{x, v} a) T` in every direction `v`
  (`TauCeti.Symbol.lineDerivOp_quantizeTempered_eq_add`), and `Op(a)` is additive in the symbol
  (`TauCeti.Symbol.quantizeTempered_zero`, `TauCeti.Symbol.quantizeTempered_add`,
  `TauCeti.Symbol.quantizeTempered_sum`).

In particular, for a symbol of order `m` with compact spatial support, `Op(a)` maps tempered
distributions of Sobolev order `s` to tempered distributions of Sobolev order `s - m`
(`TauCeti.Symbol.memSobolev_quantizeTempered`).

The full symbol is recovered exactly from the operator on tempered distributions by testing on
exponentials. The exponential `e_ξ(y) = exp(i ⟪y, ξ⟫)` is not a Schwartz function, but it has
temperate growth, hence is a tempered distribution, and

`Op(a) e_ξ = (x ↦ exp(i ⟪x, ξ⟫) a(x, ξ))`

as tempered distributions
(`TauCeti.Symbol.quantizeTempered_toTemperedDistribution_exp_inner_mul_I`, with the tested form
`TauCeti.Symbol.quantizeTempered_toTemperedDistribution_exp_inner_mul_I_apply`), that is,
`a(x, ξ) = exp(-i ⟪x, ξ⟫) (Op(a) e_ξ)(x)`. The function on the right has temperate growth since
the position slices of a uniform symbol have bounded derivatives
(`TauCeti.Symbol.IsUniform.hasTemperateGrowth_coefficient_slice`). The proof tests the transpose
identity on the cut-off exponentials `y ↦ exp(i ⟪y, ξ⟫) ψ(ε y)`, with `ψ(0) = 1`, and lets `ε → 0`:
on one side they tend to `e_ξ` as tempered distributions
(`SchwartzMap.tendsto_integral_mul_cutoffExponential`), on the other their quantizations tend to
`exp(i ⟪x, ξ⟫) a(x, ξ)` boundedly in `x`
(`TauCeti.Symbol.IsUniform.tendsto_integral_smul_quantizeSchwartzValue_cutoffExponential`).

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* R. Melrose, *Pseudodifferential operators on Euclidean space*, Chapter 2, MIT 18.199 (2008),
  §2.8, (2.75)–(2.77), for the recovery of the full symbol from exponentials.
-/

public section

noncomputable section

open MeasureTheory Complex
open scoped SchwartzMap BesselPotentialSpace RealInnerProductSpace LineDeriv

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ}

/-! ### Quantization of tempered distributions -/

section Tempered

variable (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

/-- **Pseudodifferential operators on tempered distributions.** For a scalar symbol `a` whose
estimates are uniform in the position, the quantization `Op(a)` acts on tempered distributions with
values in `F` by duality, `Op(a) T = T ∘ Op(a)ᵗ` (`TauCeti.Symbol.transposeUniformCLM`), a
continuous operator on `𝓢'(ℝⁿ, F)`. It extends the quantization of Schwartz functions
(`TauCeti.Symbol.quantizeTempered_toTemperedDistributionCLM`) and of Sobolev spaces
(`TauCeti.Symbol.toDistr_eq_quantizeTempered`). -/
def quantizeTempered (a : Symbol n ℂ ℂ m) (ha : a.IsUniform) :
    𝓢'(CoordinateSpace n, F) →L[ℂ] 𝓢'(CoordinateSpace n, F) :=
  PointwiseConvergenceCLM.precomp F (transposeUniformCLM a ha)

variable {F}

/-- `(Op(a) T) φ = T (Op(a)ᵗ φ)`. -/
@[simp]
theorem quantizeTempered_apply_apply (a : Symbol n ℂ ℂ m) (ha : a.IsUniform)
    (T : 𝓢'(CoordinateSpace n, F)) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    quantizeTempered F a ha T φ = T (transposeUniformCLM a ha φ) :=
  (rfl)

/-- On the tempered distribution of a Schwartz function `u`, `Op(a)` gives the tempered
distribution of `Op(a) u`. -/
@[simp]
theorem quantizeTempered_toTemperedDistributionCLM (a : Symbol n ℂ ℂ m) (ha : a.IsUniform)
    (u : 𝓢(CoordinateSpace n, ℂ)) :
    quantizeTempered ℂ a ha (SchwartzMap.toTemperedDistributionCLM _ ℂ volume u) =
      SchwartzMap.toTemperedDistributionCLM _ ℂ volume (quantizeUniformCLM a ha u) := by
  ext φ
  simp only [quantizeTempered_apply_apply, SchwartzMap.toTemperedDistributionCLM_apply_apply,
    smul_eq_mul]
  exact (integral_mul_quantizeUniformCLM a ha u φ).symm

/-- `Op(a)` on tempered distributions is additive in the symbol. -/
theorem quantizeTempered_add {a b : Symbol n ℂ ℂ m} (ha : a.IsUniform) (hb : b.IsUniform) :
    quantizeTempered F (a + b) (ha.add hb) = quantizeTempered F a ha + quantizeTempered F b hb := by
  ext T φ
  simp [transposeUniformCLM_add ha hb]

/-- `Op(a)` on tempered distributions is homogeneous in the symbol. -/
theorem quantizeTempered_smul {a : Symbol n ℂ ℂ m} (ha : a.IsUniform) (c : ℂ) :
    quantizeTempered F (c • a) (ha.smul c) = c • quantizeTempered F a ha := by
  ext T φ
  simp [transposeUniformCLM_smul ha c]

/-- `Op(a)` on tempered distributions does not depend on the order at which `a` is considered. -/
theorem quantizeTempered_inclusion {a : Symbol n ℂ ℂ m} (ha : a.IsUniform) (h : m ≤ m') :
    quantizeTempered F (inclusion h a) (ha.inclusion h) = quantizeTempered F a ha := by
  ext T φ
  simp [transposeUniformCLM_inclusion ha h]

/-- `Op(a)` on tempered distributions depends only on the coefficient of `a`. -/
theorem quantizeTempered_congr {a : Symbol n ℂ ℂ m} {b : Symbol n ℂ ℂ m'} (ha : a.IsUniform)
    (hb : b.IsUniform) (h : a.coefficient = b.coefficient) :
    quantizeTempered F a ha = quantizeTempered F b hb := by
  ext T φ
  simp [transposeUniformCLM_congr ha hb h]

/-- `Op(0) = 0` on tempered distributions. -/
@[simp]
theorem quantizeTempered_zero : quantizeTempered F (0 : Symbol n ℂ ℂ m) isUniform_zero = 0 := by
  have h := quantizeTempered_smul (F := F) (isUniform_zero (n := n) (m := m) (V := ℂ) (W := ℂ)) 0
  exact (quantizeTempered_congr _ _ (by simp)).trans (h.trans (zero_smul _ _))

/-- A constant symbol `T` acts on tempered distributions as multiplication by `T 1`; in particular
the symbol `1` acts as the identity. -/
theorem quantizeTempered_const (T : ℂ →L[ℂ] ℂ) :
    quantizeTempered F (n := n) (const T) (isUniform_const T) =
      T 1 • ContinuousLinearMap.id ℂ _ := by
  ext S φ
  simp [transposeUniformCLM_const]

/-- **Commutator with a derivative.** `∂_j (Op(a) T) = Op(a) (∂_j T) + Op(∂_{x_j} a) T` for
every tempered distribution `T`. -/
theorem lineDerivOp_quantizeTempered (a : Symbol n ℂ ℂ m) (ha : a.IsUniform) (j : Fin n)
    (T : 𝓢'(CoordinateSpace n, F)) :
    ∂_{EuclideanSpace.single j (1 : ℝ)} (quantizeTempered F a ha T) =
      quantizeTempered F a ha (∂_{EuclideanSpace.single j (1 : ℝ)} T) +
        quantizeTempered F (spatialDeriv j a) (ha.spatialDeriv j) T := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply, quantizeTempered_apply_apply, map_neg,
    transposeUniformCLM_lineDerivOp, neg_sub, map_sub, add_apply]
  abel

/-- **Composition with a derivative on the right.** `Op(a) (∂_v T) = i Op(a ⟪ξ, v⟫) T` for every
tempered distribution `T`. -/
theorem quantizeTempered_lineDerivOp (a : Symbol n ℂ ℂ m) (ha : a.IsUniform)
    (v : CoordinateSpace n) (T : 𝓢'(CoordinateSpace n, F)) :
    quantizeTempered F a ha (∂_{v} T) =
      I • quantizeTempered F (a.comp (ofInner v)) (ha.comp (isUniform_ofInner v)) T := by
  ext φ
  simp [transposeUniformCLM_comp_ofInner ha, smul_smul]

/-- **Commutator with a coordinate function.** `x_j Op(a) T = Op(a) (x_j T) + i Op(∂_{ξ_j} a) T`
for every tempered distribution `T`. -/
theorem smulLeftCLM_quantizeTempered (a : Symbol n ℂ ℂ m) (ha : a.IsUniform) (j : Fin n)
    (T : 𝓢'(CoordinateSpace n, F)) :
    TemperedDistribution.smulLeftCLM F (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ))
        (quantizeTempered F a ha T) =
      quantizeTempered F a ha
          (TemperedDistribution.smulLeftCLM F (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)) T) +
        I • quantizeTempered F (frequencyDeriv j a) (ha.frequencyDeriv j) T := by
  ext φ
  simp only [TemperedDistribution.smulLeftCLM_apply_apply, quantizeTempered_apply_apply,
    transposeUniformCLM_smulLeftCLM, map_add, map_smul, add_apply, smul_apply]

/-- **Composition of quantizations on tempered distributions.** For a symbol `b` with compact
spatial support, `Op(a # b) = Op(a) ∘ Op(b)` on `𝓢'(ℝⁿ, F)`. -/
theorem quantizeTempered_sharp {a : Symbol n ℂ ℂ m'} {b : Symbol n ℂ ℂ m} (ha : a.IsUniform)
    (hb : b.HasCompactSpatialSupport) :
    quantizeTempered F (a.sharp b hb) (ha.sharp hb) =
      quantizeTempered F a ha ∘L quantizeTempered F b hb.isUniform := by
  ext T φ
  simp only [quantizeTempered_apply_apply, transposeUniformCLM_sharp ha hb,
    ContinuousLinearMap.comp_apply]

end Tempered

/-! ### Composition with Fourier multipliers -/

section Multiplier

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Composition with a Fourier multiplier on the right.** For Mathlib's Fourier multiplier
`g(D)` in the frequency `ζ`, `Op(a) ∘ g(D) = Op(b)` on tempered distributions, where
`b(x, ξ) = g(ξ / 2π) a(x, ξ)` in the angular frequency `ξ`. -/
theorem IsUniform.quantizeTempered_fourierMultiplierCLM {a : Symbol n ℂ ℂ m}
    (ha : a.IsUniform) {b : Symbol n ℂ ℂ m'} (hb : b.IsUniform) {g : CoordinateSpace n → ℂ}
    (hg : g.HasTemperateGrowth)
    (hab : ∀ x ξ, b.coefficient (x, ξ) = g ((2 * Real.pi)⁻¹ • ξ) • a.coefficient (x, ξ))
    (T : 𝓢'(CoordinateSpace n, F)) :
    quantizeTempered F a ha (TemperedDistribution.fourierMultiplierCLM F g T) =
      quantizeTempered F b hb T := by
  -- On Schwartz space, `g(-D) ∘ Op(a)ᵗ = Op(b)ᵗ`.
  have hS : SchwartzMap.fourierMultiplierCLM ℂ (fun ξ ↦ g (-ξ)) ∘L transposeUniformCLM a ha =
      transposeUniformCLM b hb := by
    refine eq_transposeUniformCLM fun u φ ↦ ?_
    have h := congrArg (fun T : 𝓢'(CoordinateSpace n, ℂ) ↦ T (transposeUniformCLM a ha φ))
      (TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq hg u)
    simp only [TemperedDistribution.fourierMultiplierCLM_apply_apply_transpose,
      SchwartzMap.toTemperedDistributionCLM_apply_apply, smul_eq_mul] at h
    rw [ContinuousLinearMap.comp_apply, h, ← integral_mul_quantizeUniformCLM]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    dsimp only
    rw [quantizeUniformCLM_apply, quantizeUniformCLM_apply,
      quantizeSchwartzValue_fourierMultiplierCLM hg]
    congr 2
    ext p : 1
    exact hab p.1 p.2
  ext φ
  rw [quantizeTempered_apply_apply, quantizeTempered_apply_apply,
    TemperedDistribution.fourierMultiplierCLM_apply_apply_transpose, ← hS,
    ContinuousLinearMap.comp_apply]

/-- `Op(a)` on tempered distributions is additive in the symbol, for finite sums. -/
theorem quantizeTempered_sum {ι : Type*} {a : ι → Symbol n ℂ ℂ m} (ha : ∀ i, (a i).IsUniform)
    (s : Finset ι) :
    quantizeTempered F (∑ i ∈ s, a i) (IsUniform.sum fun i _ ↦ ha i) =
      ∑ i ∈ s, quantizeTempered F (a i) (ha i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact (quantizeTempered_congr _ (isUniform_zero (m := m)) (by simp)).trans
      (by rw [quantizeTempered_zero, Finset.sum_empty])
  | insert i s hi ih =>
    conv_rhs => rw [Finset.sum_insert hi, ← ih, ← quantizeTempered_add]
    exact quantizeTempered_congr _ _ (by rw [Finset.sum_insert hi])

/-- **Reduction to order zero.** For a uniform symbol `a` of order `m`,
`Op(a) = Op(a ⟨ξ / 2π⟩ ^ (-m)) ∘ J^m` on tempered distributions, where `J^m` is the Bessel
potential of order `m` and the first factor is a uniform symbol of order `0`. -/
theorem IsUniform.quantizeTempered_eq_comp_besselPotential {a : Symbol n ℂ ℂ m}
    (ha : a.IsUniform) (T : 𝓢'(CoordinateSpace n, F)) :
    quantizeTempered F a ha T = quantizeTempered F
      (Symbol.inclusion (add_neg_cancel m).le (a.comp (Symbol.besselPotential (-m))))
      ((ha.comp (isUniform_besselPotential _)).inclusion _)
      (TemperedDistribution.besselPotential (CoordinateSpace n) F m T) := by
  have hg : (fun ζ : CoordinateSpace n ↦
      (((1 + ‖ζ‖ ^ 2) ^ (m / 2) : ℝ) : ℂ)).HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth.comp
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow _ (m / 2))
  have hab (x ξ : CoordinateSpace n) :
      a.coefficient (x, ξ) = (((1 + ‖(2 * Real.pi)⁻¹ • ξ‖ ^ 2) ^ (m / 2) : ℝ) : ℂ) •
        (Symbol.inclusion (add_neg_cancel m).le
          (a.comp (Symbol.besselPotential (-m)))).coefficient (x, ξ) := by
    have h := congrFun (coefficient_comp_besselPotential_comp_besselPotential a (-m) m) (x, ξ)
    rw [neg_add_cancel, coefficient_comp_besselPotential_zero] at h
    rw [← h, coefficient_comp, coefficient_besselPotential, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_id, coefficient_inclusion]
  rw [TemperedDistribution.besselPotential]
  exact (IsUniform.quantizeTempered_fourierMultiplierCLM (F := F)
    ((ha.comp (isUniform_besselPotential _)).inclusion _) ha hg hab T).symm

/-- **Commutator with a directional derivative.** `∂_v (Op(a) T) = Op(a) (∂_v T) + Op(∂_{x, v} a) T`
for every tempered distribution `T` and every direction `v`. -/
theorem lineDerivOp_quantizeTempered_eq_add {a : Symbol n ℂ ℂ m} (ha : a.IsUniform)
    (v : CoordinateSpace n) (T : 𝓢'(CoordinateSpace n, F)) :
    ∂_{v} (quantizeTempered F a ha T) =
      quantizeTempered F a ha (∂_{v} T) +
        quantizeTempered F (lineSpatialDeriv v a) (ha.lineSpatialDeriv v) T := by
  have hv : v = ∑ j, v j • EuclideanSpace.single j (1 : ℝ) := by
    ext i
    simp [Pi.single_apply]
  have hd (S : 𝓢'(CoordinateSpace n, F)) :
      ∂_{v} S = ∑ j, v j • ∂_{EuclideanSpace.single j (1 : ℝ)} S := by
    conv_lhs => rw [hv]
    simp only [LineDeriv.lineDerivOp_left_sum, LineDeriv.lineDerivOp_left_smul]
  have hq : quantizeTempered F (lineSpatialDeriv v a) (ha.lineSpatialDeriv v) =
      ∑ j, ((v j : ℝ) : ℂ) • quantizeTempered F (spatialDeriv j a) (ha.spatialDeriv j) := by
    rw [← Finset.sum_congr rfl fun j _ ↦ quantizeTempered_smul (ha.spatialDeriv j) _,
      ← quantizeTempered_sum (fun j ↦ (ha.spatialDeriv j).smul _) Finset.univ]
    exact quantizeTempered_congr _ _ (by rw [lineSpatialDeriv_apply])
  rw [hd, hd, hq, map_sum]
  simp only [ContinuousLinearMap.map_smul_of_tower, lineDerivOp_quantizeTempered, smul_add,
    Finset.sum_add_distrib, sum_apply, smul_apply, Complex.coe_smul]

end Multiplier

/-! ### Comparison with the Sobolev mappings -/

section Sobolev

/-- **Sobolev realizations are restrictions of the tempered one.** Any bounded operator
`T : H^s(ℝⁿ) → H^r(ℝⁿ)` that agrees with `Op(a)` on Schwartz functions is the restriction of
`Op(a) : 𝓢'(ℝⁿ, ℂ) → 𝓢'(ℝⁿ, ℂ)` to `H^s`: `T f = Op(a) f` as tempered distributions. This
applies to `TauCeti.Symbol.quantizeSobolev` (`TauCeti.Symbol.toDistr_quantizeSobolev`) and to the
Sobolev mappings of uniform symbols. -/
theorem toDistr_eq_quantizeTempered {a : Symbol n ℂ ℂ m} (ha : a.IsUniform) {s r : ℝ}
    {T : H^{s}(CoordinateSpace n) →L[ℂ] H^{r}(CoordinateSpace n)}
    (hT : ∀ u φ : 𝓢(CoordinateSpace n, ℂ),
      (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
        ∫ x, φ x • quantizeSchwartzValue a.coefficient u x)
    (f : H^{s}(CoordinateSpace n)) :
    (T f).toDistr = quantizeTempered ℂ a ha f.toDistr := by
  have key : BesselPotentialSpace.toDistrCLM _ ℂ r 2 ∘L T =
      quantizeTempered ℂ a ha ∘L BesselPotentialSpace.toDistrCLM _ ℂ s 2 := by
    refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
    ext φ
    simp only [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistrCLM_apply, hT,
      quantizeTempered_apply_apply, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
      SchwartzMap.coe_apply, smul_eq_mul, ← integral_mul_quantizeUniformCLM,
      quantizeUniformCLM_apply]
  simpa using congr($key f)

/-- For a symbol with compact spatial support, `Op(a) : H^s → H^{s - m}`
(`TauCeti.Symbol.quantizeSobolev`) is the restriction of `Op(a)` on tempered distributions. -/
theorem toDistr_quantizeSobolev {a : Symbol n ℂ ℂ m} (ha : a.HasCompactSpatialSupport) (s : ℝ)
    (f : H^{s}(CoordinateSpace n)) :
    (a.quantizeSobolev ha s f).toDistr = quantizeTempered ℂ a ha.isUniform f.toDistr :=
  toDistr_eq_quantizeTempered ha.isUniform
    (toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply ha s) f

/-- **Sobolev mapping on tempered distributions.** For a symbol `a` of order `m` with compact
spatial support, `Op(a)` maps every tempered distribution of Sobolev order `s` to one of Sobolev
order `s - m`. -/
theorem memSobolev_quantizeTempered {a : Symbol n ℂ ℂ m} (ha : a.HasCompactSpatialSupport)
    {s : ℝ} {T : 𝓢'(CoordinateSpace n, ℂ)} (hT : T.MemSobolev s 2) :
    (quantizeTempered ℂ a ha.isUniform T).MemSobolev (s - m) 2 := by
  rw [← hT.toBesselPotentialSpace_toDistr, ← toDistr_quantizeSobolev ha s]
  exact BesselPotentialSpace.memSobolev_toDistr _

end Sobolev

/-! ### Recovery of the symbol from exponentials -/

section Exponential

open scoped Topology

/-- **Recovery of the symbol from exponentials, on tempered distributions.** For a scalar symbol
`a` with estimates uniform in the position, `Op(a)` sends the exponential
`e_ξ(y) = exp(i ⟪y, ξ⟫)`, as a tempered distribution, to the function
`x ↦ exp(i ⟪x, ξ⟫) a(x, ξ)`: for every Schwartz function `φ`,

`(Op(a) e_ξ) φ = ∫ φ(x) exp(i ⟪x, ξ⟫) a(x, ξ) dx`.

Thus `a(x, ξ) = exp(-i ⟪x, ξ⟫) (Op(a) e_ξ)(x)` holds exactly, for the action of `Op(a)` on
tempered distributions by duality; see
`TauCeti.Symbol.quantizeTempered_toTemperedDistribution_exp_inner_mul_I` for the identity of
tempered distributions. -/
theorem quantizeTempered_toTemperedDistribution_exp_inner_mul_I_apply (a : Symbol n ℂ ℂ m)
    (ha : a.IsUniform) (ξ : CoordinateSpace n) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    quantizeTempered ℂ a ha (Function.HasTemperateGrowth.toTemperedDistribution volume
        (Function.hasTemperateGrowth_exp_inner_mul_I ξ)) φ =
      ∫ x, φ x * (Complex.exp (⟪x, ξ⟫ * I) * a.coefficient (x, ξ) 1) := by
  -- A Schwartz function `ψ` with `ψ 0 = 1`, the cutoff of the exponentials.
  obtain ⟨ψ, -, -, hψ⟩ := (isCompact_singleton (x := (0 : CoordinateSpace n)))
    |>.exists_schwartzMap_cutoff isOpen_univ (Set.subset_univ _)
  replace hψ : ψ 0 = 1 := hψ.self_of_nhdsSet 0 rfl
  -- Pair the transpose identity `∫ φ Op(a) u = ∫ Op(a)ᵗ φ u` on the cut-off exponentials
  -- `u = (y ↦ exp(i ⟪y, ξ⟫) ψ(ε y))`, and let `ε → 0` on both sides.
  set t := transposeUniformCLM a ha φ
  have hleft := ha.tendsto_integral_smul_quantizeSchwartzValue_cutoffExponential ξ hψ 1
    φ.integrable
  have hright := ψ.tendsto_integral_mul_cutoffExponential t.integrable ξ
  have hlim := tendsto_nhds_unique hright (hleft.congr fun ε ↦ by
    simpa only [smul_eq_mul, quantizeUniformCLM_apply] using
      integral_mul_quantizeUniformCLM a ha (ψ.cutoffExponential ε ξ 1) φ)
  simpa only [quantizeTempered_apply_apply, hψ, one_mul, smul_eq_mul,
    Function.HasTemperateGrowth.toTemperedDistribution_apply] using hlim

/-- **Recovery of the symbol from exponentials, on tempered distributions.** For a scalar symbol
`a` with estimates uniform in the position, `Op(a)` sends the tempered distribution of the
exponential `e_ξ(y) = exp(i ⟪y, ξ⟫)` to that of the function `x ↦ exp(i ⟪x, ξ⟫) a(x, ξ)`. -/
theorem quantizeTempered_toTemperedDistribution_exp_inner_mul_I (a : Symbol n ℂ ℂ m)
    (ha : a.IsUniform) (ξ : CoordinateSpace n) :
    quantizeTempered ℂ a ha (Function.HasTemperateGrowth.toTemperedDistribution volume
        (Function.hasTemperateGrowth_exp_inner_mul_I ξ)) =
      Function.HasTemperateGrowth.toTemperedDistribution volume
        ((Function.hasTemperateGrowth_exp_inner_mul_I ξ).mul
          (((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).restrictScalars ℝ).hasTemperateGrowth.comp
            (ha.hasTemperateGrowth_coefficient_slice ξ))) := by
  ext φ
  rw [quantizeTempered_toTemperedDistribution_exp_inner_mul_I_apply]
  simp only [Function.HasTemperateGrowth.toTemperedDistribution_apply, smul_eq_mul,
    ContinuousLinearMap.coe_restrictScalars', Pi.mul_apply, Function.comp_apply,
    ContinuousLinearMap.apply_apply]

end Exponential

end Symbol

end TauCeti
