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
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Pseudodifferential.Recovery
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Sobolev.BesselPotential.TemperedOrder

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
  (`TauCeti.Symbol.quantizeTempered_ofSpatial_smul_id`), and for `a` with compact spatial
  support `Op(f a) T = f Op(a) T` for smooth real `f` of temperate growth
  (`TauCeti.Symbol.quantizeTempered_ofSpatial_smul_id_comp`), so that
  `Op(a) (x_j T) = Op(x_j a) T - i Op(∂_{ξ_j} a) T`
  (`TauCeti.Symbol.quantizeTempered_smulLeftCLM_coord`).

In particular, for a symbol of order `m` with compact spatial support, `Op(a)` maps tempered
distributions of Sobolev order `s` to tempered distributions of Sobolev order `s - m`
(`TauCeti.Symbol.memSobolev_quantizeTempered`). A smoothing symbol with compact spatial support maps
*every* tempered distribution into every `H^s`
(`TauCeti.Symbol.IsSmoothing.memSobolev_quantizeTempered`): a tempered distribution is a polynomial
weight `(1 + ‖x‖ ^ 2) ^ N` times an element of some `H^t`
(`TemperedDistribution.exists_memSobolev_and_eq_smulLeftCLM_pow`), and the last identity moves the
weight into the symbol. This is what extends local elliptic regularity from Sobolev spaces to
arbitrary tempered distributions
(`TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM_of_memSobolev_quantizeTempered`).

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
open scoped SchwartzMap BesselPotentialSpace RealInnerProductSpace LineDeriv ContDiff

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

/-- **Multiplication by a function of the position.** For a symbol `a` with compact spatial support
and a smooth real function `f` of the position with temperate growth, quantizing the symbol
`f(x) a(x, ξ)` multiplies `Op(a) T` by `f`, for every tempered distribution `T`. -/
theorem quantizeTempered_ofSpatial_smul_id_comp {a : Symbol n ℂ ℂ m}
    (ha : a.HasCompactSpatialSupport) {f : CoordinateSpace n → ℝ}
    (hf : ContDiff ℝ ∞ fun x ↦ f x • ContinuousLinearMap.id ℂ ℂ)
    (hft : (fun x ↦ (f x : ℂ)).HasTemperateGrowth) (T : 𝓢'(CoordinateSpace n, F)) :
    quantizeTempered F ((ofSpatial (fun x ↦ f x • ContinuousLinearMap.id ℂ ℂ) hf).comp a)
        (ha.comp_left _).isUniform T =
      TemperedDistribution.smulLeftCLM F (fun x ↦ (f x : ℂ))
        (quantizeTempered F a ha.isUniform T) := by
  -- The transpose of `Op(f a)` is the transpose of `Op(a)` after multiplication by `f`.
  have key : transposeUniformCLM ((ofSpatial _ hf).comp a) (ha.comp_left _).isUniform =
      transposeUniformCLM a ha.isUniform ∘L SchwartzMap.smulLeftCLM ℂ (fun x ↦ (f x : ℂ)) := by
    refine (eq_transposeUniformCLM fun u φ ↦ ?_).symm
    rw [ContinuousLinearMap.comp_apply, ← integral_mul_quantizeUniformCLM]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [quantizeUniformCLM_apply, quantizeSchwartzValue_ofSpatial_smul_id_comp,
      SchwartzMap.smulLeftCLM_apply_apply hft, smul_eq_mul]
    ring
  ext φ
  simp only [quantizeTempered_apply_apply, TemperedDistribution.smulLeftCLM_apply_apply, key,
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

/-- **Commutator with a coordinate function, solved for the input.** For a symbol `a` with compact
spatial support, `Op(a) (x_j T) = Op(x_j a) T - i Op(∂_{ξ_j} a) T` for every tempered distribution
`T`. -/
theorem quantizeTempered_smulLeftCLM_coord {a : Symbol n ℂ ℂ m} (ha : a.HasCompactSpatialSupport)
    (j : Fin n) (T : 𝓢'(CoordinateSpace n, F)) :
    quantizeTempered F a ha.isUniform
        (TemperedDistribution.smulLeftCLM F (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)) T) =
      quantizeTempered F ((coordSubSymbol 0 j).comp a) (ha.comp_left _).isUniform T -
        I • quantizeTempered F (frequencyDeriv j a) (ha.isUniform.frequencyDeriv j) T := by
  have hft : (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)).HasTemperateGrowth :=
    (ofRealCLM.comp (EuclideanSpace.proj j)).hasTemperateGrowth
  have h : quantizeTempered F ((coordSubSymbol 0 j).comp a) (ha.comp_left _).isUniform T =
      TemperedDistribution.smulLeftCLM F (fun y : CoordinateSpace n ↦ (((y - 0) j : ℝ) : ℂ))
        (quantizeTempered F a ha.isUniform T) := by
    rw [coordSubSymbol_eq_ofSpatial]
    exact quantizeTempered_ofSpatial_smul_id_comp ha _ (by simpa using hft) T
  simp only [sub_zero] at h
  rw [h, smulLeftCLM_quantizeTempered]
  abel

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

/-! ### Smoothing operators on tempered distributions -/

section Smoothing

/-- **Smoothing operators regularize all tempered distributions.** Let `r` be a smoothing symbol
with compact spatial support. Then `Op(r) T` lies in every Bessel-potential space `H^s`, for every
tempered distribution `T`, and not only for `T` in some `H^t`
(`TauCeti.Symbol.IsSmoothing.memSobolev_toDistr_quantizeSobolev`). -/
theorem IsSmoothing.memSobolev_quantizeTempered {r : Symbol n ℂ ℂ m} (hr : r.IsSmoothing)
    (hc : r.HasCompactSpatialSupport) (T : 𝓢'(CoordinateSpace n, ℂ)) (s : ℝ) :
    (quantizeTempered ℂ r hc.isUniform T).MemSobolev s 2 := by
  -- Write `T = (1 + ‖x‖ ^ 2) ^ N S` with `S ∈ H^t`
  -- (`TemperedDistribution.exists_memSobolev_and_eq_smulLeftCLM_pow`). The commutator identity
  -- `Op(r) (x_j U) = Op(x_j r) U - i Op(∂_{ξ_j} r) U` trades each factor `x_j` of the weight for
  -- other smoothing symbols with compact spatial support, which map `S` into every `H^s`.
  -- `P U`: every smoothing symbol with compact spatial support maps `U` into every `H^s`.
  let P : 𝓢'(CoordinateSpace n, ℂ) → Prop := fun U ↦ ∀ (m : ℝ) (r : Symbol n ℂ ℂ m),
    r.IsSmoothing → ∀ (hc : r.HasCompactSpatialSupport) (s : ℝ),
      (quantizeTempered ℂ r hc.isUniform U).MemSobolev s 2
  have hSob {t : ℝ} {U : 𝓢'(CoordinateSpace n, ℂ)} (hU : U.MemSobolev t 2) : P U := by
    intro m r hr hc s
    rw [← hU.toBesselPotentialSpace_toDistr, ← toDistr_quantizeSobolev hc t]
    exact hr.memSobolev_toDistr_quantizeSobolev hc t s _
  have hzero : P 0 := fun m r _ hc s ↦ by
    rw [map_zero]
    exact TemperedDistribution.memSobolev_fun_zero _ _ s 2
  have hadd {U V : 𝓢'(CoordinateSpace n, ℂ)} (hU : P U) (hV : P V) : P (U + V) :=
    fun m r hr hc s ↦ by
      rw [map_add]
      exact (hU m r hr hc s).add (hV m r hr hc s)
  have hcoord (j : Fin n) {U : 𝓢'(CoordinateSpace n, ℂ)} (hU : P U) :
      P (TemperedDistribution.smulLeftCLM ℂ (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)) U) :=
    fun m r hr hc s ↦ by
      rw [quantizeTempered_smulLeftCLM_coord hc j]
      exact (hU _ _ (hr.comp_left _) (hc.comp_left _) s).sub
        ((hU _ _ (hr.frequencyDeriv j) (hc.frequencyDeriv j) s).smul I)
  -- Multiplication by `1 + ‖x‖ ^ 2 = 1 + ∑ⱼ xⱼ xⱼ` preserves `P`.
  have hweight {U : 𝓢'(CoordinateSpace n, ℂ)} (hU : P U) :
      P (TemperedDistribution.smulLeftCLM ℂ
        (fun x : CoordinateSpace n ↦ ((1 + ‖x‖ ^ 2 : ℝ) : ℂ)) U) := by
    rw [TemperedDistribution.smulLeftCLM_one_add_norm_sq_apply]
    exact hadd hU (Finset.sum_induction _ P (fun _ _ ↦ hadd) hzero fun j _ ↦
      hcoord j (hcoord j hU))
  have hpow (N : ℕ) {U : 𝓢'(CoordinateSpace n, ℂ)} (hU : P U) :
      P (TemperedDistribution.smulLeftCLM ℂ
        (fun x : CoordinateSpace n ↦ ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) ^ N) U) := by
    induction N with
    | zero => simpa using hU
    | succ N ih =>
      have hfun : (fun x : CoordinateSpace n ↦ ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) ^ (N + 1)) =
          (fun x ↦ ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) ^ N) * fun x ↦ ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) := by
        funext x
        simp [pow_succ]
      rw [hfun, ← TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
      exact hweight ih
  obtain ⟨N, t, S, hS, rfl⟩ := TemperedDistribution.exists_memSobolev_and_eq_smulLeftCLM_pow T
  exact hpow N (hSob hS) m r hr hc s

end Smoothing

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
