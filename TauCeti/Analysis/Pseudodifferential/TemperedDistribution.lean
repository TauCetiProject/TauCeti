/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Transpose
public import TauCeti.Analysis.Pseudodifferential.Sobolev
public import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
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
* the symbol `φ(x)` acts as multiplication by `φ`
  (`TauCeti.Symbol.quantizeTempered_ofSpatial_smul_id`).

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

A spatial cutoff `ψ` equal to `1` wherever the symbol `r` does not vanish identically leaves
`Op(r) T` unchanged: `ψ Op(r) T = Op(r) T`
(`TauCeti.Symbol.smulLeftCLM_quantizeTempered_of_eq_one`).

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

/-- **Multiplication operators.** For a Schwartz function `φ` such that the symbol `φ(x) id` of
order `0` is uniform, for instance a compactly supported `φ`
(`TauCeti.Symbol.hasCompactSpatialSupport_ofSpatial_smul_id`), this symbol quantizes to
multiplication by `φ` on tempered distributions. -/
theorem quantizeTempered_ofSpatial_smul_id (φ : 𝓢(CoordinateSpace n, ℂ))
    (h : (ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ ℂ)
      ((φ.smooth ⊤).smul contDiff_const)).IsUniform) :
    quantizeTempered F (ofSpatial _ _) h = TemperedDistribution.smulLeftCLM F φ := by
  have key : transposeUniformCLM (ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ ℂ)
      ((φ.smooth ⊤).smul contDiff_const)) h = SchwartzMap.smulLeftCLM ℂ φ := by
    refine (eq_transposeUniformCLM fun u ψ ↦ integral_congr_ae (.of_forall fun x ↦ ?_)).symm
    dsimp only
    rw [quantizeUniformCLM_ofSpatial_apply _ h u x,
      SchwartzMap.smulLeftCLM_apply_apply φ.hasTemperateGrowth]
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  ext T ψ
  simp only [quantizeTempered_apply_apply, TemperedDistribution.smulLeftCLM_apply_apply, key]

end Tempered

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

/-! ### Spatial cutoffs -/

section Cutoff

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F] {r : Symbol n ℂ ℂ m}

/-- **Spatial cutoffs.** If `ψ`, of temperate growth, is `1` at every position at which the symbol
`r` does not vanish identically, then `ψ Op(r) T = Op(r) T` for every tempered distribution `T`. -/
theorem smulLeftCLM_quantizeTempered_of_eq_one (hr : r.IsUniform)
    {ψ : CoordinateSpace n → ℂ} (hψg : ψ.HasTemperateGrowth)
    (hψ : ∀ x ξ, r.coefficient (x, ξ) ≠ 0 → ψ x = 1) (T : 𝓢'(CoordinateSpace n, F)) :
    TemperedDistribution.smulLeftCLM F ψ (quantizeTempered F r hr T) =
      quantizeTempered F r hr T := by
  -- `ψ Op(r) u = Op(r) u` pointwise, so `Op(r)ᵗ (ψ φ) = Op(r)ᵗ φ`.
  have hpt (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
      ψ x * quantizeUniformCLM r hr u x = quantizeUniformCLM r hr u x := by
    by_cases hx : ∀ ξ, r.coefficient (x, ξ) = 0
    · rw [quantizeUniformCLM_apply, quantizeSchwartzValue_congr_left (b := 0) hx u,
        quantizeSchwartzValue_zero_left, mul_zero]
    · obtain ⟨ξ, hξ⟩ := not_forall.1 hx
      rw [hψ x ξ hξ, one_mul]
  have key : transposeUniformCLM r hr ∘L SchwartzMap.smulLeftCLM ℂ ψ =
      transposeUniformCLM r hr := by
    refine eq_transposeUniformCLM fun u φ ↦ ?_
    rw [ContinuousLinearMap.coe_comp, Function.comp_apply, ← integral_mul_quantizeUniformCLM]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [SchwartzMap.smulLeftCLM_apply_apply hψg, smul_eq_mul]
    rw [mul_comm (ψ x), mul_assoc, hpt]
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, quantizeTempered_apply_apply,
    quantizeTempered_apply_apply, ← ContinuousLinearMap.comp_apply, key]

end Cutoff

end Symbol

end TauCeti
