/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Basic
public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
public import TauCeti.Analysis.Distribution.SchwartzSpace.Basic

/-!
# The transpose of a quantization

Let `a` be a scalar symbol of order `m` on `ℝⁿ` whose estimates hold uniformly in the position
(`TauCeti.Symbol.IsUniform`). Its quantization `Op(a)` is a continuous operator on Schwartz space
(`TauCeti.Symbol.quantizeUniformCLM`), and so is its transpose `Op(a)ᵗ` for the bilinear pairing
`⟨φ, u⟩ = ∫ φ u`: `∫ φ · Op(a) u = ∫ Op(a)ᵗ φ · u` for all Schwartz functions `u` and `φ`
(`TauCeti.Symbol.transposeUniformCLM`, `TauCeti.Symbol.integral_mul_quantizeUniformCLM`). The
transpose is obtained from the formal adjoint `Op_R(ā)`
(`TauCeti.Symbol.integral_inner_quantizeUniformCLM`) by conjugating its input and output, and it
is the only operator with this property (`TauCeti.Symbol.eq_transposeUniformCLM`). It is the
bilinear analogue of the formal adjoint, and extends `Op(a)` to tempered distributions by duality
(`TauCeti.Analysis.Pseudodifferential.TemperedDistribution`).

Since an identity between transposes is detected by testing against Schwartz functions, the rules
of the calculus on Schwartz space transpose:

* the transpose is linear in the symbol (`TauCeti.Symbol.transposeUniformCLM_add`,
  `TauCeti.Symbol.transposeUniformCLM_smul`) and depends only on its coefficient
  (`TauCeti.Symbol.transposeUniformCLM_congr`); a constant symbol `T` is its own transpose
  (`TauCeti.Symbol.transposeUniformCLM_const`);
* `Op(a)ᵗ (∂_j φ) = ∂_j (Op(a)ᵗ φ) - Op(∂_{x_j} a)ᵗ φ`
  (`TauCeti.Symbol.transposeUniformCLM_lineDerivOp`);
* `Op(a ⟪ξ, v⟫)ᵗ φ = i ∂_v (Op(a)ᵗ φ)` (`TauCeti.Symbol.transposeUniformCLM_comp_ofInner`);
* `Op(a)ᵗ (x_j φ) = x_j Op(a)ᵗ φ + i Op(∂_{ξ_j} a)ᵗ φ`
  (`TauCeti.Symbol.transposeUniformCLM_smulLeftCLM`);
* for `b` with compact spatial support, `Op(a # b)ᵗ = Op(b)ᵗ ∘ Op(a)ᵗ`
  (`TauCeti.Symbol.transposeUniformCLM_sharp`).

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open MeasureTheory Complex ComplexConjugate
open ContinuousLinearMap (adjointRealCLM)
open scoped SchwartzMap LineDeriv

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ}

/-! ### The transpose on Schwartz space -/

section Transpose

variable (a : Symbol n ℂ ℂ m) (ha : a.IsUniform)

/-- **The transpose of a uniform quantization.** For a scalar symbol `a` whose estimates are
uniform in the position, the transpose `Op(a)ᵗ` of its quantization for the bilinear pairing
`⟨φ, u⟩ = ∫ φ u`, a continuous operator on Schwartz space with
`∫ φ · Op(a) u = ∫ Op(a)ᵗ φ · u` (`TauCeti.Symbol.integral_mul_quantizeUniformCLM`). It is the
formal adjoint `Op_R(ā)` with conjugated input and output, `Op(a)ᵗ φ = conj (Op_R(ā) (conj φ))`
(`TauCeti.Symbol.transposeUniformCLM_apply`). -/
def transposeUniformCLM : 𝓢(CoordinateSpace n, ℂ) →L[ℂ] 𝓢(CoordinateSpace n, ℂ) where
  toFun φ := SchwartzMap.conjCLM
    (quantizeRightUniformCLM (a.map adjointRealCLM) (ha.map _) (SchwartzMap.conjCLM φ))
  map_add' φ ψ := by simp
  map_smul' c φ := by
    rw [SchwartzMap.conjCLM_smul, map_smul, SchwartzMap.conjCLM_smul, conj_conj,
      RingHom.id_apply]
  cont := SchwartzMap.conjCLM.continuous.comp
    ((quantizeRightUniformCLM _ (ha.map _)).continuous.comp SchwartzMap.conjCLM.continuous)

/-- `Op(a)ᵗ φ = conj (Op_R(ā) (conj φ))`, where `ā` is the pointwise adjoint of the symbol. -/
theorem transposeUniformCLM_apply (φ : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
    transposeUniformCLM a ha φ x = conj (quantizeRightUniformCLM (a.map adjointRealCLM)
      (ha.map _) (SchwartzMap.conjCLM φ) x) :=
  SchwartzMap.conjCLM_apply _ _

/-- **The transpose identity.** `∫ φ · Op(a) u = ∫ Op(a)ᵗ φ · u` for all Schwartz functions `u`
and `φ`. -/
theorem integral_mul_quantizeUniformCLM (u φ : 𝓢(CoordinateSpace n, ℂ)) :
    ∫ x, φ x * quantizeUniformCLM a ha u x = ∫ x, transposeUniformCLM a ha φ x * u x := by
  -- Conjugate the adjoint identity `∫ ⟪Op(a) u, conj φ⟫ = ∫ ⟪u, Op_R(ā) (conj φ)⟫`.
  have h := integral_inner_quantizeUniformCLM a ha u (SchwartzMap.conjCLM φ)
  simp only [SchwartzMap.conjCLM_apply, RCLike.inner_apply] at h
  calc ∫ x, φ x * quantizeUniformCLM a ha u x
      = conj (∫ x, conj (φ x) * conj (quantizeUniformCLM a ha u x)) := by
        rw [← integral_conj]
        simp
    _ = conj (∫ x, quantizeRightUniformCLM (a.map adjointRealCLM)
          (ha.map _) (SchwartzMap.conjCLM φ) x * conj (u x)) := by
        rw [h]
    _ = ∫ x, transposeUniformCLM a ha φ x * u x := by
        rw [← integral_conj]
        simp [transposeUniformCLM_apply]

variable {a ha} in
/-- **Uniqueness of the transpose.** An operator `B` on Schwartz space with
`∫ φ · Op(a) u = ∫ B φ · u` for all Schwartz functions `u` and `φ` is the transpose of `Op(a)`. -/
theorem eq_transposeUniformCLM {B : 𝓢(CoordinateSpace n, ℂ) →L[ℂ] 𝓢(CoordinateSpace n, ℂ)}
    (hB : ∀ u φ : 𝓢(CoordinateSpace n, ℂ),
      ∫ x, φ x * quantizeUniformCLM a ha u x = ∫ x, B φ x * u x) :
    B = transposeUniformCLM a ha :=
  ContinuousLinearMap.ext fun φ ↦ SchwartzMap.eq_of_forall_integral_mul_eq (μ := volume) fun u ↦ by
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
    rw [integral_add (SchwartzMap.integrable_mul _ _) (SchwartzMap.integrable_mul _ _),
      integral_add (SchwartzMap.integrable_mul _ _) (SchwartzMap.integrable_mul _ _),
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
    have hT : T (u x) = u x * T 1 := by simpa using T.map_smul (u x) 1
    rw [hT]
    ring).symm

/-- **The transpose of a commutator with a derivative.** Transposing
`∂_j (Op(a) u) = Op(a) (∂_j u) + Op(∂_{x_j} a) u` gives
`Op(a)ᵗ (∂_j φ) = ∂_j (Op(a)ᵗ φ) - Op(∂_{x_j} a)ᵗ φ`. -/
theorem transposeUniformCLM_lineDerivOp {a : Symbol n ℂ ℂ m} (ha : a.IsUniform) (j : Fin n)
    (φ : 𝓢(CoordinateSpace n, ℂ)) :
    transposeUniformCLM a ha (∂_{EuclideanSpace.single j (1 : ℝ)} φ) =
      ∂_{EuclideanSpace.single j (1 : ℝ)} (transposeUniformCLM a ha φ) -
        transposeUniformCLM (spatialDeriv j a) (ha.spatialDeriv j) φ := by
  refine SchwartzMap.eq_of_forall_integral_mul_eq (μ := volume) fun u ↦ ?_
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
        rw [integral_add (SchwartzMap.integrable_mul _ _) (SchwartzMap.integrable_mul _ _),
          integral_mul_quantizeUniformCLM, integral_mul_quantizeUniformCLM]
    _ = ∫ x, (∂_{e} (transposeUniformCLM a ha φ) -
          transposeUniformCLM (spatialDeriv j a) (ha.spatialDeriv j) φ) x * u x := by
        simp only [sub_apply, sub_mul]
        rw [integral_sub (SchwartzMap.integrable_mul _ _) (SchwartzMap.integrable_mul _ _),
          SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left]
        ring

/-- **The transpose of a derivative on the right.** Transposing `Op(a) (∂_v u) = i Op(a ⟪ξ, v⟫) u`
gives `Op(a ⟪ξ, v⟫)ᵗ φ = i ∂_v (Op(a)ᵗ φ)`. -/
theorem transposeUniformCLM_comp_ofInner {a : Symbol n ℂ ℂ m} (ha : a.IsUniform)
    (v : CoordinateSpace n) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    transposeUniformCLM (a.comp (ofInner v)) (ha.comp (isUniform_ofInner v)) φ =
      I • ∂_{v} (transposeUniformCLM a ha φ) := by
  refine SchwartzMap.eq_of_forall_integral_mul_eq (μ := volume) fun u ↦ ?_
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
  refine SchwartzMap.eq_of_forall_integral_mul_eq (μ := volume) fun u ↦ ?_
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
        rw [integral_add (SchwartzMap.integrable_mul _ _)
            ((SchwartzMap.integrable_mul _ _).const_mul _),
          integral_const_mul, integral_mul_quantizeUniformCLM, integral_mul_quantizeUniformCLM,
          ← integral_const_mul, ← integral_add (SchwartzMap.integrable_mul _ _)
            ((SchwartzMap.integrable_mul _ _).const_mul _)]
        refine integral_congr_ae (.of_forall fun y ↦ ?_)
        simp only [add_apply, smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
          SchwartzMap.smulLeftCLM_apply_apply hg', smul_eq_mul, Complex.real_smul]
        ring

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

end Symbol

end TauCeti
