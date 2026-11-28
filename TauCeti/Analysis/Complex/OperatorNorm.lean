/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.OperatorNorm
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Bounds for real-linear maps out of the complex line

The values on `1` and `I` determine a continuous real-linear map on every complex vector
(`ContinuousLinearMap.apply_eq_re_smul_one_add_im_smul_I`), so one vanishing at `1` and nonzero
somewhere is nonzero at `I` (`ContinuousLinearMap.apply_I_ne_zero_of_apply_one_eq_zero`).
A real-linear map is the sum of its values at `1` and `I` weighted by the real and imaginary
parts (`ContinuousLinearMap.eq_reCLM_smulRight_add_imCLM_smulRight`, and for families
`ContinuousLinearMap.fun_eq_smulRightL_reCLM_add_smulRightL_imCLM`). A complex antilinear one is
determined by its value at `1`: it is `w ↦ conj w • L 1`, the image of `L 1` under
`ContinuousLinearMap.antilinearOfOneL`
(`ContinuousLinearMap.antilinearOfOneL_apply_eq_of_antilinear`).
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

/-- A continuous real-linear map out of `ℂ` vanishing at `1` and nonzero somewhere is nonzero at
`I`. -/
theorem apply_I_ne_zero_of_apply_one_eq_zero {F : Type*} [TopologicalSpace F] [AddCommMonoid F]
    [Module ℝ F] {L : ℂ →L[ℝ] F} (h1 : L 1 = 0) {v : ℂ} (hv : L v ≠ 0) : L Complex.I ≠ 0 :=
  fun hI ↦ hv (by rw [L.apply_eq_re_smul_one_add_im_smul_I, h1, hI, smul_zero, smul_zero, add_zero])

/-- A real-linear map out of `ℂ` is determined by its values at `1` and `I`:
`L = re ⬝ L 1 + im ⬝ L I`. -/
theorem eq_reCLM_smulRight_add_imCLM_smulRight {V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] (L : ℂ →L[ℝ] V) :
    L = Complex.reCLM.smulRight (L 1) + Complex.imCLM.smulRight (L Complex.I) := by
  ext z
  simp [L.apply_eq_re_smul_one_add_im_smul_I z]

/-- The complex antilinear real-linear map out of `ℂ` with value `v` at `1`, `w ↦ conj w • v`, as
a continuous linear map in `v`: `ContinuousLinearMap.smulRightL` applied to complex conjugation. -/
noncomputable def antilinearOfOneL (V : Type*) [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] : V →L[ℝ] ℂ →L[ℝ] V :=
  smulRightL ℝ ℝ ℂ ℂ V (Complex.conjCLE : ℂ →L[ℝ] ℂ)

/-- **The antilinear map with value `v` at `1`** is `w ↦ conj w • v`. -/
@[simp]
theorem antilinearOfOneL_apply_apply {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] (v : V) (w : ℂ) :
    antilinearOfOneL V v w = (starRingEnd ℂ w) • v := by
  simp [antilinearOfOneL]

/-- `antilinearOfOneL V v` has value `v` at `1`. -/
theorem antilinearOfOneL_apply_apply_one {V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] (v : V) :
    antilinearOfOneL V v 1 = v := by
  simp

/-- `antilinearOfOneL V` is injective: `antilinearOfOneL V v` has value `v` at `1`. -/
theorem antilinearOfOneL_injective {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] : Function.Injective (antilinearOfOneL V) :=
  fun u v h ↦ by
    simpa only [antilinearOfOneL_apply_apply_one] using congrArg (fun L : ℂ →L[ℝ] V ↦ L 1) h

/-- `antilinearOfOneL V v` is complex antilinear: `w ↦ conj w • v` anticommutes with `i`, since
`conj (i w) = -i conj w`. -/
theorem antilinearOfOneL_apply_I_smul {V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] (v : V) (w : ℂ) :
    antilinearOfOneL V v (Complex.I • w) = -(Complex.I • antilinearOfOneL V v w) := by
  simp [smul_smul]

/-- **Antilinear maps are determined by their value at `1`.** A complex antilinear real-linear map
out of `ℂ` is the antilinear map with its value at `1`: `L w = conj w • L 1`. -/
theorem antilinearOfOneL_apply_eq_of_antilinear {V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] (L : ℂ →L[ℝ] V)
    (hL : ∀ v, L (Complex.I • v) = -(Complex.I • L v)) : antilinearOfOneL V (L 1) = L := by
  -- `L w = re w • L 1 + im w • L i` and `L i = -(i • L 1)`.
  have hI : L Complex.I = -(Complex.I • L 1) := by simpa using hL 1
  ext w
  -- `conj w = re w - im w * i`, with real scalars acting through `ℂ`.
  have hw : starRingEnd ℂ w = (w.re : ℂ) - w.im * Complex.I := by
    apply Complex.ext <;> simp
  rw [antilinearOfOneL_apply_apply, L.apply_eq_re_smul_one_add_im_smul_I w, hI, hw]
  module

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
