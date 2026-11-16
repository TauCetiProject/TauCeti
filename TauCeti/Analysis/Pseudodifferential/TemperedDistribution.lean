/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Basic
public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
public import TauCeti.Analysis.Pseudodifferential.Sobolev
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
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
  (`TauCeti.Symbol.quantizeUniformCLM_sharp`).

In particular, for a symbol of order `m` with compact spatial support, `Op(a)` maps tempered
distributions of Sobolev order `s` to tempered distributions of Sobolev order `s - m`
(`TauCeti.Symbol.memSobolev_quantizeTempered`).

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open MeasureTheory Complex ComplexConjugate
open ContinuousLinearMap (adjointRealCLM)
open scoped SchwartzMap BesselPotentialSpace RealInnerProductSpace LineDeriv

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ}

/-! ### The transpose on Schwartz space -/

section Transpose

/-- Conjugation of the values, as a real-linear map on Schwartz space. -/
private def conjSchwartz : 𝓢(CoordinateSpace n, ℂ) →L[ℝ] 𝓢(CoordinateSpace n, ℂ) :=
  SchwartzMap.postcompCLM conjCLE.toContinuousLinearMap

private theorem conjSchwartz_apply (φ : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
    conjSchwartz φ x = conj (φ x) :=
  (rfl)

private theorem conjSchwartz_smul (c : ℂ) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    conjSchwartz (c • φ) = conj c • conjSchwartz φ := by
  ext x
  simp [conjSchwartz_apply]

/-- The product of two Schwartz functions is integrable. -/
private theorem integrable_mul (φ u : 𝓢(CoordinateSpace n, ℂ)) :
    Integrable fun x ↦ φ x * u x :=
  (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) φ u).integrable

variable (a : Symbol n ℂ ℂ m) (ha : a.IsUniform)

/-- **The transpose of a uniform quantization.** For a scalar symbol `a` whose estimates are
uniform in the position, the transpose `Op(a)ᵗ` of its quantization for the bilinear pairing
`⟨φ, u⟩ = ∫ φ u`, a continuous operator on Schwartz space with
`∫ φ · Op(a) u = ∫ Op(a)ᵗ φ · u` (`TauCeti.Symbol.integral_mul_quantizeUniformCLM`). It is the
formal adjoint `Op_R(ā)` with conjugated input and output, `Op(a)ᵗ φ = conj (Op_R(ā) (conj φ))`
(`TauCeti.Symbol.transposeUniformCLM_apply`). -/
def transposeUniformCLM : 𝓢(CoordinateSpace n, ℂ) →L[ℂ] 𝓢(CoordinateSpace n, ℂ) where
  toFun φ := conjSchwartz
    (quantizeRightUniformCLM (a.map adjointRealCLM) (ha.map _) (conjSchwartz φ))
  map_add' φ ψ := by simp
  map_smul' c φ := by
    rw [conjSchwartz_smul, map_smul, conjSchwartz_smul, conj_conj, RingHom.id_apply]
  cont := conjSchwartz.continuous.comp
    ((quantizeRightUniformCLM _ (ha.map _)).continuous.comp conjSchwartz.continuous)

/-- `Op(a)ᵗ φ = conj (Op_R(ā) (conj φ))`, where `ā` is the pointwise adjoint of the symbol. -/
theorem transposeUniformCLM_apply (φ : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
    transposeUniformCLM a ha φ x = conj (quantizeRightUniformCLM (a.map adjointRealCLM)
      (ha.map _) (SchwartzMap.postcompCLM conjCLE.toContinuousLinearMap φ) x) :=
  (rfl)

/-- **The transpose identity.** `∫ φ · Op(a) u = ∫ Op(a)ᵗ φ · u` for all Schwartz functions `u`
and `φ`. -/
theorem integral_mul_quantizeUniformCLM (u φ : 𝓢(CoordinateSpace n, ℂ)) :
    ∫ x, φ x * quantizeUniformCLM a ha u x = ∫ x, transposeUniformCLM a ha φ x * u x := by
  -- Conjugate the adjoint identity `∫ ⟪Op(a) u, conj φ⟫ = ∫ ⟪u, Op_R(ā) (conj φ)⟫`.
  have h := integral_inner_quantizeUniformCLM a ha u (conjSchwartz φ)
  simp only [conjSchwartz_apply, RCLike.inner_apply] at h
  calc ∫ x, φ x * quantizeUniformCLM a ha u x
      = conj (∫ x, conj (φ x) * conj (quantizeUniformCLM a ha u x)) := by
        rw [← integral_conj]
        simp
    _ = conj (∫ x, quantizeRightUniformCLM (a.map adjointRealCLM)
          (ha.map _) (conjSchwartz φ) x * conj (u x)) := by
        rw [h]
    _ = ∫ x, transposeUniformCLM a ha φ x * u x := by
        rw [← integral_conj]
        simp [transposeUniformCLM_apply, conjSchwartz]

variable {a ha} in
/-- **Uniqueness of the transpose.** An operator `B` on Schwartz space with
`∫ φ · Op(a) u = ∫ B φ · u` for all Schwartz functions `u` and `φ` is the transpose of `Op(a)`. -/
theorem eq_transposeUniformCLM {B : 𝓢(CoordinateSpace n, ℂ) →L[ℂ] 𝓢(CoordinateSpace n, ℂ)}
    (hB : ∀ u φ : 𝓢(CoordinateSpace n, ℂ),
      ∫ x, φ x * quantizeUniformCLM a ha u x = ∫ x, B φ x * u x) :
    B = transposeUniformCLM a ha :=
  ContinuousLinearMap.ext fun φ ↦ eq_of_forall_integral_mul_eq (μ := volume) fun u ↦ by
    rw [← hB, integral_mul_quantizeUniformCLM]

end Transpose

/-! ### The calculus of transposes -/

section TransposeCalculus

/-- The transpose is additive in the symbol. -/
theorem transposeUniformCLM_add {a b : Symbol n ℂ ℂ m} (ha : a.IsUniform) (hb : b.IsUniform) :
    transposeUniformCLM (a + b) (ha.add hb) =
      transposeUniformCLM a ha + transposeUniformCLM b hb :=
  (eq_transposeUniformCLM fun u φ ↦ by
    simp only [quantizeUniformCLM_add ha hb, add_apply, mul_add, add_mul]
    rw [integral_add (integrable_mul _ _) (integrable_mul _ _),
      integral_add (integrable_mul _ _) (integrable_mul _ _),
      integral_mul_quantizeUniformCLM, integral_mul_quantizeUniformCLM]).symm

/-- The transpose is homogeneous in the symbol. -/
theorem transposeUniformCLM_smul {a : Symbol n ℂ ℂ m} (ha : a.IsUniform) (c : ℂ) :
    transposeUniformCLM (c • a) (ha.smul c) = c • transposeUniformCLM a ha :=
  (eq_transposeUniformCLM fun u φ ↦ by
    simp only [quantizeUniformCLM_smul ha c, smul_apply,
      smul_eq_mul, mul_left_comm (φ _), mul_assoc, integral_const_mul,
      integral_mul_quantizeUniformCLM]).symm

/-- The transpose does not depend on the order at which a symbol is considered. -/
theorem transposeUniformCLM_inclusion {a : Symbol n ℂ ℂ m} (ha : a.IsUniform) (h : m ≤ m') :
    transposeUniformCLM (inclusion h a) (ha.inclusion h) = transposeUniformCLM a ha :=
  (eq_transposeUniformCLM fun u φ ↦ by
    rw [quantizeUniformCLM_inclusion, integral_mul_quantizeUniformCLM]).symm

/-- The transpose of `Op(a)` depends only on the coefficient of `a`. -/
theorem transposeUniformCLM_congr {a : Symbol n ℂ ℂ m} {b : Symbol n ℂ ℂ m'} (ha : a.IsUniform)
    (hb : b.IsUniform) (h : a.coefficient = b.coefficient) :
    transposeUniformCLM a ha = transposeUniformCLM b hb :=
  eq_transposeUniformCLM fun u φ ↦ by
    rw [← quantizeUniformCLM_congr ha hb h, integral_mul_quantizeUniformCLM]

/-- A constant symbol `T` is its own transpose: `Op(T)ᵗ` is multiplication by `T 1`. -/
theorem transposeUniformCLM_const (T : ℂ →L[ℂ] ℂ) :
    transposeUniformCLM (n := n) (const T) (isUniform_const T) = T 1 • ContinuousLinearMap.id ℂ _ :=
  (eq_transposeUniformCLM fun u φ ↦ by
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    rw [quantizeUniformCLM_const]
    simp only [SchwartzMap.postcompCLM_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [← mul_one (u x), ← smul_eq_mul (u x), T.map_smul, smul_eq_mul]
    ring).symm

/-- **The transpose of a commutator with a derivative.** Transposing
`∂_j (Op(a) u) = Op(a) (∂_j u) + Op(∂_{x_j} a) u` gives
`Op(a)ᵗ (∂_j φ) = ∂_j (Op(a)ᵗ φ) - Op(∂_{x_j} a)ᵗ φ`. -/
theorem transposeUniformCLM_lineDerivOp {a : Symbol n ℂ ℂ m} (ha : a.IsUniform) (j : Fin n)
    (φ : 𝓢(CoordinateSpace n, ℂ)) :
    transposeUniformCLM a ha (∂_{EuclideanSpace.single j (1 : ℝ)} φ) =
      ∂_{EuclideanSpace.single j (1 : ℝ)} (transposeUniformCLM a ha φ) -
        transposeUniformCLM (spatialDeriv j a) (ha.spatialDeriv j) φ := by
  refine eq_of_forall_integral_mul_eq (μ := volume) fun u ↦ ?_
  set e := EuclideanSpace.single j (1 : ℝ)
  -- Integrate by parts on both sides and use the commutator formula on Schwartz space.
  calc ∫ x, transposeUniformCLM a ha (∂_{e} φ) x * u x
      = -∫ x, φ x * ∂_{e} (quantizeUniformCLM a ha u) x := by
        rw [← integral_mul_quantizeUniformCLM,
          SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left, neg_neg]
    _ = -((∫ x, transposeUniformCLM a ha φ x * ∂_{e} u x) +
          ∫ x, transposeUniformCLM (spatialDeriv j a) (ha.spatialDeriv j) φ x * u x) := by
        rw [lineDerivOp_quantizeUniformCLM]
        simp only [add_apply, mul_add]
        rw [integral_add (integrable_mul _ _) (integrable_mul _ _),
          integral_mul_quantizeUniformCLM, integral_mul_quantizeUniformCLM]
    _ = ∫ x, (∂_{e} (transposeUniformCLM a ha φ) -
          transposeUniformCLM (spatialDeriv j a) (ha.spatialDeriv j) φ) x * u x := by
        simp only [sub_apply, sub_mul]
        rw [integral_sub (integrable_mul _ _) (integrable_mul _ _),
          SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left]
        ring

/-- **The transpose of a derivative on the right.** Transposing `Op(a) (∂_v u) = i Op(a ⟪ξ, v⟫) u`
gives `Op(a ⟪ξ, v⟫)ᵗ φ = i ∂_v (Op(a)ᵗ φ)`. -/
theorem transposeUniformCLM_comp_ofInner {a : Symbol n ℂ ℂ m} (ha : a.IsUniform)
    (v : CoordinateSpace n) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    transposeUniformCLM (a.comp (ofInner v)) (ha.comp (isUniform_ofInner v)) φ =
      I • ∂_{v} (transposeUniformCLM a ha φ) := by
  refine eq_of_forall_integral_mul_eq (μ := volume) fun u ↦ ?_
  have h := congrArg (fun w : 𝓢(CoordinateSpace n, ℂ) ↦ ∫ x, φ x * w x)
    (quantizeUniformCLM_lineDerivOp a ha v u)
  simp only [smul_apply, smul_eq_mul, mul_left_comm (φ _), integral_const_mul,
    integral_mul_quantizeUniformCLM, SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left] at h
  simp only [smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  linear_combination I * h +
    (∫ x, transposeUniformCLM (a.comp (ofInner v)) (ha.comp (isUniform_ofInner v)) φ x * u x) *
      I_sq

/-- **The transpose of a commutator with a coordinate function.** Transposing
`x_j Op(a) u = Op(a) (x_j u) + i Op(∂_{ξ_j} a) u` gives
`Op(a)ᵗ (x_j φ) = x_j Op(a)ᵗ φ + i Op(∂_{ξ_j} a)ᵗ φ`. -/
theorem transposeUniformCLM_smulLeftCLM {a : Symbol n ℂ ℂ m} (ha : a.IsUniform) (j : Fin n)
    (φ : 𝓢(CoordinateSpace n, ℂ)) :
    transposeUniformCLM a ha
        (SchwartzMap.smulLeftCLM ℂ (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)) φ) =
      SchwartzMap.smulLeftCLM ℂ (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ))
          (transposeUniformCLM a ha φ) +
        I • transposeUniformCLM (frequencyDeriv j a) (ha.frequencyDeriv j) φ := by
  have hg : (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)).HasTemperateGrowth :=
    (ofRealCLM.comp (EuclideanSpace.proj j)).hasTemperateGrowth
  have hg' : (fun y : CoordinateSpace n ↦ y j).HasTemperateGrowth :=
    (EuclideanSpace.proj j).hasTemperateGrowth
  refine eq_of_forall_integral_mul_eq (μ := volume) fun u ↦ ?_
  -- The commutator formula on Schwartz space, at each point `y`.
  have hcomm (y : CoordinateSpace n) : (y j : ℂ) * quantizeUniformCLM a ha u y =
      quantizeUniformCLM a ha (SchwartzMap.smulLeftCLM ℂ (fun y : CoordinateSpace n ↦ y j) u) y +
        I * quantizeUniformCLM (frequencyDeriv j a) (ha.frequencyDeriv j) u y := by
    have := congrArg (· y) (smulLeftCLM_quantizeUniformCLM a ha j u)
    simpa [SchwartzMap.smulLeftCLM_apply_apply hg', Complex.real_smul] using this
  calc ∫ y, transposeUniformCLM a ha
        (SchwartzMap.smulLeftCLM ℂ (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)) φ) y * u y
      = ∫ y, φ y * quantizeUniformCLM a ha
          (SchwartzMap.smulLeftCLM ℂ (fun y : CoordinateSpace n ↦ y j) u) y +
          I * (φ y * quantizeUniformCLM (frequencyDeriv j a) (ha.frequencyDeriv j) u y) := by
        rw [← integral_mul_quantizeUniformCLM]
        refine integral_congr_ae (.of_forall fun y ↦ ?_)
        simp only [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
        rw [mul_comm (y j : ℂ), mul_assoc, hcomm]
        ring
    _ = ∫ y, (SchwartzMap.smulLeftCLM ℂ (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ))
          (transposeUniformCLM a ha φ) +
          I • transposeUniformCLM (frequencyDeriv j a) (ha.frequencyDeriv j) φ) y * u y := by
        rw [integral_add (integrable_mul _ _) ((integrable_mul _ _).const_mul _),
          integral_const_mul, integral_mul_quantizeUniformCLM, integral_mul_quantizeUniformCLM,
          ← integral_const_mul,
          ← integral_add (integrable_mul _ _) ((integrable_mul _ _).const_mul _)]
        refine integral_congr_ae (.of_forall fun y ↦ ?_)
        simp only [add_apply, smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
          SchwartzMap.smulLeftCLM_apply_apply hg', smul_eq_mul, Complex.real_smul]
        ring

/-- **Composition of uniform quantizations.** For a symbol `b` with compact spatial support,
`Op(a # b) = Op(a) ∘ Op(b)` on Schwartz space. -/
theorem quantizeUniformCLM_sharp {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] [NormedAddCommGroup U]
    [NormedSpace ℂ U] [CompleteSpace U] {a : Symbol n W U m'} {b : Symbol n V W m}
    (ha : a.IsUniform) (hb : b.HasCompactSpatialSupport) :
    quantizeUniformCLM (a.sharp b hb) (ha.sharp hb) =
      quantizeUniformCLM a ha ∘L quantizeUniformCLM b hb.isUniform := by
  ext u x
  rw [quantizeUniformCLM_apply, quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue hb,
    ContinuousLinearMap.comp_apply, quantizeUniformCLM_apply]
  congr 1
  ext y
  simp

/-- **The transpose of a composition.** For a symbol `b` with compact spatial support,
`Op(a # b)ᵗ = Op(b)ᵗ ∘ Op(a)ᵗ`. -/
theorem transposeUniformCLM_sharp {a : Symbol n ℂ ℂ m'} {b : Symbol n ℂ ℂ m} (ha : a.IsUniform)
    (hb : b.HasCompactSpatialSupport) :
    transposeUniformCLM (a.sharp b hb) (ha.sharp hb) =
      transposeUniformCLM b hb.isUniform ∘L transposeUniformCLM a ha :=
  (eq_transposeUniformCLM fun u φ ↦ by
    rw [quantizeUniformCLM_sharp, ContinuousLinearMap.comp_apply, integral_mul_quantizeUniformCLM,
      integral_mul_quantizeUniformCLM, ContinuousLinearMap.comp_apply]).symm

end TransposeCalculus

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
  simp [transposeUniformCLM_lineDerivOp, map_sub]
  abel

/-- **Composition with a derivative on the right.** `Op(a) (∂_v T) = i Op(a ⟪ξ, v⟫) T` for every
tempered distribution `T`. -/
theorem quantizeTempered_lineDerivOp (a : Symbol n ℂ ℂ m) (ha : a.IsUniform)
    (v : CoordinateSpace n) (T : 𝓢'(CoordinateSpace n, F)) :
    quantizeTempered F a ha (∂_{v} T) =
      I • quantizeTempered F (a.comp (ofInner v)) (ha.comp (isUniform_ofInner v)) T := by
  ext φ
  rw [quantizeTempered_apply_apply, TemperedDistribution.lineDerivOp_apply_apply, smul_apply,
    quantizeTempered_apply_apply, transposeUniformCLM_comp_ofInner, ← map_smul, smul_smul, I_mul_I,
    neg_one_smul]

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
  rw [quantizeTempered_apply_apply, transposeUniformCLM_sharp]
  rfl

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

end Symbol

end TauCeti
