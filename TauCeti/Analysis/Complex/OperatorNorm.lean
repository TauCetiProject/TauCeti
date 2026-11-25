/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.OperatorNorm
public import Mathlib.Analysis.Normed.Operator.Mul
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Bounds for real-linear maps out of the complex line

The values on `1` and `I` determine a continuous real-linear map on every complex vector
(`ContinuousLinearMap.apply_eq_re_smul_one_add_im_smul_I`).
A real-linear map is the sum of its values at `1` and `I` weighted by the real and imaginary
parts (`ContinuousLinearMap.eq_reCLM_smulRight_add_imCLM_smulRight`, and for families
`ContinuousLinearMap.fun_eq_smulRightL_reCLM_add_smulRightL_imCLM`). A complex antilinear one is
determined by its value at `1`
(`ContinuousLinearMap.eq_reCLM_smulRight_sub_imCLM_smulRight_of_antilinear`), the image of its
value at `1` under `ContinuousLinearMap.antilinearOfOneL`
(`ContinuousLinearMap.antilinearOfOneL_apply_one`).
For a real bilinear map `B` on `ℂ` with `B 1 I = B I 1`, the trace `B a a + B (I a) (I a)` over the
orthogonal pair `a, I a` is `‖a‖²` times the trace over `1, I`
(`ContinuousLinearMap.apply_add_apply_I_mul_eq_norm_sq_smul`).

Multiplication by `c : ℂ` is a similarity of ratio `‖c‖`, so precomposing a real-linear map with
it multiplies the operator norm by `‖c‖`
(`ContinuousLinearMap.norm_comp_restrictScalars_smulRight_one`).

The norm bounds in terms of the values on `1` and `I` hold over any `RCLike` field and live in
`TauCeti.Analysis.RCLike.OperatorNorm`.
-/

public section

namespace ContinuousLinearMap

/-- A continuous real-linear map out of the complex plane is evaluated in the real basis
`(1,I)`. -/
theorem apply_eq_re_smul_one_add_im_smul_I {F : Type*} [TopologicalSpace F] [AddCommMonoid F]
    [Module ℝ F] (L : ℂ →L[ℝ] F) (z : ℂ) : L z = z.re • L 1 + z.im • L Complex.I :=
  L.toLinearMap.apply_eq_re_smul_one_add_im_smul_I z

/-- A real-linear map out of `ℂ` is determined by its values at `1` and `I`:
`L = re ⬝ L 1 + im ⬝ L I`. -/
theorem eq_reCLM_smulRight_add_imCLM_smulRight {V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] (L : ℂ →L[ℝ] V) :
    L = Complex.reCLM.smulRight (L 1) + Complex.imCLM.smulRight (L Complex.I) := by
  ext z
  simp [L.apply_eq_re_smul_one_add_im_smul_I z]

/-- A complex antilinear real-linear map out of `ℂ` is determined by its value at `1`:
`L = re ⬝ L 1 - im ⬝ (I • L 1)`, that is, `L w = conj w • L 1`. -/
theorem eq_reCLM_smulRight_sub_imCLM_smulRight_of_antilinear {V : Type*}
    [SeminormedAddCommGroup V] [NormedSpace ℝ V] [Module ℂ V] (L : ℂ →L[ℝ] V)
    (hL : ∀ v, L (Complex.I • v) = -(Complex.I • L v)) :
    L = Complex.reCLM.smulRight (L 1) - Complex.imCLM.smulRight (Complex.I • L 1) := by
  have hI : L Complex.I = -(Complex.I • L 1) := by simpa using hL 1
  conv_lhs => rw [L.eq_reCLM_smulRight_add_imCLM_smulRight, hI]
  ext z
  simp [sub_eq_add_neg]

/-- The complex antilinear real-linear map out of `ℂ` with value `v` at `1`, `w ↦ conj w • v`,
written `re ⬝ v - im ⬝ (I • v)`, as a continuous linear map in `v`. -/
noncomputable def antilinearOfOneL (V : Type*) [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] : V →L[ℝ] ℂ →L[ℝ] V :=
  StrongDual.smulRightL ℝ ℂ V Complex.reCLM -
    (StrongDual.smulRightL ℝ ℂ V Complex.imCLM).comp (lsmul ℝ ℂ Complex.I)

@[simp]
theorem antilinearOfOneL_apply {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] (v : V) :
    antilinearOfOneL V v = Complex.reCLM.smulRight v - Complex.imCLM.smulRight (Complex.I • v) :=
  (rfl)

/-- `antilinearOfOneL V v` has value `v` at `1`. -/
theorem antilinearOfOneL_apply_apply_one {V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] (v : V) :
    antilinearOfOneL V v 1 = v := by
  simp [antilinearOfOneL_apply]

/-- `antilinearOfOneL V v` is complex antilinear: `w ↦ conj w • v` anticommutes with `i`. -/
theorem antilinearOfOneL_apply_I_smul {V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] (v : V) (w : ℂ) :
    antilinearOfOneL V v (Complex.I • w) = -(Complex.I • antilinearOfOneL V v w) := by
  -- `antilinearOfOneL V v w = conj w • v`, and `conj (i w) = -i conj w`.
  have key (w : ℂ) : antilinearOfOneL V v w = (starRingEnd ℂ w) • v := by
    simp only [antilinearOfOneL_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul,
      ← sub_smul]
    congr 1
    apply Complex.ext <;> simp
  rw [key, key, smul_smul, smul_eq_mul, map_mul, Complex.conj_I, neg_mul, neg_smul]

/-- A complex antilinear real-linear map out of `ℂ` is the antilinear map with its value at `1`. -/
theorem antilinearOfOneL_apply_one {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] (L : ℂ →L[ℝ] V)
    (hL : ∀ v, L (Complex.I • v) = -(Complex.I • L v)) : antilinearOfOneL V (L 1) = L := by
  rw [antilinearOfOneL_apply, ← L.eq_reCLM_smulRight_sub_imCLM_smulRight_of_antilinear hL]

/-- A family of real-linear maps out of `ℂ` splits through its values at `1` and `I`, written
with the continuous linear maps `smulRightL` so that it can be postcomposed in families. -/
theorem fun_eq_smulRightL_reCLM_add_smulRightL_imCLM {X V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] (D : X → ℂ →L[ℝ] V) :
    D = (fun x => smulRightL ℝ ℝ ℝ ℂ V Complex.reCLM (D x 1)) +
      fun x => smulRightL ℝ ℝ ℝ ℂ V Complex.imCLM (D x Complex.I) := by
  funext x
  conv_lhs => rw [(D x).eq_reCLM_smulRight_add_imCLM_smulRight]
  ext z
  simp

/-- For a real bilinear map `B` on `ℂ` with `B 1 I = B I 1`, the trace over the orthogonal pair
`a, I a` is `‖a‖²` times the trace over `1, I`. -/
theorem apply_add_apply_I_mul_eq_norm_sq_smul {V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] (B : ℂ →L[ℝ] ℂ →L[ℝ] V) (hB : B 1 Complex.I = B Complex.I 1) (a : ℂ) :
    B a a + B (Complex.I * a) (Complex.I * a) = ‖a‖ ^ 2 • (B 1 1 + B Complex.I Complex.I) := by
  obtain ⟨p, q, rfl⟩ : ∃ p q : ℝ, a = p • (1 : ℂ) + q • Complex.I :=
    ⟨a.re, a.im, by simp⟩
  have hIa : Complex.I * (p • (1 : ℂ) + q • Complex.I) = (-q) • (1 : ℂ) + p • Complex.I := by
    simp [Complex.ext_iff]
  have hn : ‖p • (1 : ℂ) + q • Complex.I‖ ^ 2 = p ^ 2 + q ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [sq]
  rw [hIa, hn]
  simp only [map_add, map_smul, add_apply, smul_apply, hB]
  module

/-- Precomposing a real-linear map out of the complex plane with multiplication by `c`, a
similarity of ratio `‖c‖`, multiplies its operator norm by `‖c‖`. -/
theorem norm_comp_restrictScalars_smulRight_one {V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] (L : ℂ →L[ℝ] V) (c : ℂ) :
    ‖L.comp ((smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ)‖ = ‖L‖ * ‖c‖ := by
  have hnorm (a : ℂ) : ‖(smulRight (1 : ℂ →L[ℂ] ℂ) a).restrictScalars ℝ‖ = ‖a‖ := by
    rw [norm_restrictScalars, norm_smulRight_apply, norm_one, one_mul]
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  refine le_antisymm ((L.opNorm_comp_le _).trans_eq (by rw [hnorm])) ?_
  -- Multiplying back by `c⁻¹` recovers `L`, which gives the reverse inequality.
  have hL : L = (L.comp ((smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ)).comp
      ((smulRight (1 : ℂ →L[ℂ] ℂ) c⁻¹).restrictScalars ℝ) := by
    ext w
    simp [hc]
  rw [← le_div_iff₀ (norm_pos_iff.2 hc), div_eq_mul_inv, ← norm_inv, ← hnorm c⁻¹]
  calc ‖L‖ = ‖(L.comp ((smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ)).comp
        ((smulRight (1 : ℂ →L[ℂ] ℂ) c⁻¹).restrictScalars ℝ)‖ := congrArg norm hL
    _ ≤ _ := opNorm_comp_le _ _

end ContinuousLinearMap

end
