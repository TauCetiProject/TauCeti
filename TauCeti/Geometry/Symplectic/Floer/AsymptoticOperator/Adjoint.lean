/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The formal adjoint of the stationary cylinder operator

Let `(V, ω)` be a finite-dimensional symplectic vector space, `J_t` a continuous family of
`ω`-invariant complex structures with associated forms `g_t = ω(·, J_t ·)`, and `S_t` a continuous
family of infinitesimally symplectic maps, the linearized Hamiltonian vector field along an orbit.
The linearized Floer operator at the stationary cylinder over the orbit is
`D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ) = ∂s ξ + A ξ`
(`TauCeti.Floer.stationaryCylinderOperator`), where `A` is the asymptotic operator, symmetric for
the `L²` pairing `∫₀¹ g_t` on loops. Its formal adjoint for the pairing `∫∫ g_t` is therefore

`D† η = -∂s η + J_t (∂t η - S_t η) = -∂s η + A η`

(`TauCeti.Floer.stationaryCylinderAdjoint`). This file proves the corresponding Green formula and
uses it to show that `D` has no classical cokernel on decaying maps.

* **Weights.** Replacing `S_t` by `S_t - δ J_t` shifts `D†` by `-δ`
  (`Floer.stationaryCylinderAdjoint_sub_smul`), while conjugating by the weight `e^{δ s}` shifts
  it by `+δ`, the opposite sign to `D` (`Floer.stationaryCylinderAdjoint_exp_smul`).
* **Green's formula.** For maps `ξ` and `η` which are `C¹` near a rectangle
  `[a₁, b₁] × [a₂, b₂]`, `∫∫ g(D ξ, η) = ∫∫ g(ξ, D† η)` plus the boundary terms `∫ g_t(ξ, η)`
  over the two vertical sides and `∫ ω(ξ, η)` over the two horizontal sides
  (`Floer.setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_add`). Pointwise,
  `g(D ξ, η) - g(ξ, D† η)` is `∂s g_t(ξ, η) + ∂t ω(ξ, η)`: the complex structure cancels from the
  `t`-derivative terms, and the zeroth-order terms cancel because `S_t` is infinitesimally
  symplectic. When `ξ` and `η` take equal values on the slices `t = 0` and `t = 1` the horizontal
  terms cancel, so on a finite cylinder `[a, b] × [0, 1]` with `ξ` or `η` vanishing at each point
  of the two boundary slices the identity is `∫∫ g(D ξ, η) = ∫∫ g(ξ, D† η)`
  (`Floer.setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_of_periodic`), and for a
  compactly supported `ξ` or `η` it holds over the whole plane
  (`Floer.integral_associatedBilinForm_stationaryCylinderOperator_eq_of_hasCompactSupport` and
  `Floer.integral_associatedBilinForm_stationaryCylinderOperator_eq_of_hasCompactSupport_right`).
* **`C¹` weak solutions of the adjoint equation.** A map `η` which is `C¹` on an open set `U` and
  satisfies `∫∫ g(D ξ, η) = 0` for every smooth `ξ` compactly supported in `U` solves
  `D† η = 0` on `U` (`Floer.eqOn_stationaryCylinderAdjoint_zero_of_forall_integral_eq_zero`).
  This is the fundamental lemma of the calculus of variations
  (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) applied to the Green formula.
* **Reflection.** `D† η (s, t) = D (η ∘ ρ) (-s, t)` for the reflection `ρ (s, t) = (-s, t)`
  (`Floer.stationaryCylinderAdjoint_eq_stationaryCylinderOperator_comp`). So decaying solutions of
  `D† η = 0` are reflections of decaying solutions of `D ξ = 0`, and these vanish by
  `Floer.eq_zero_of_stationaryCylinderOperator_eq_zero`: for `ω`-compatible `J_t`, a `C²` map of
  period one in `t` with `D† η = 0` on `ℝ × (0, 1)` which tends to zero with `∂t η` as
  `|s| → ∞` is zero (`Floer.eq_zero_of_stationaryCylinderAdjoint_eq_zero`).
* **No classical cokernel.** Consequently, for `ω`-compatible `J_t`, a `C²` map `η` of period one
  in `t`, decaying with `∂t η`, which is `L²`-orthogonal on the cylinder `ℝ × [0, 1]` to `D ξ` for
  every smooth `ξ` of period one in `t` vanishing for large `|s|`, is zero
  (`Floer.eq_zero_of_forall_integral_associatedBilinForm_stationaryCylinderOperator_eq_zero`).
  The test maps supported in `ℝ × (0, 1)` suffice: their periodizations are cylinder test maps.
  As for the injectivity of `D`, no nondegeneracy of the orbit is needed.

The injectivity of `D` on decaying maps, the `L²` estimate of
`TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator.Estimate` at a nondegenerate orbit and the
vanishing of the classical cokernel proved here are the ingredients of the invertibility of
`∂s + A` on the cylinder. That invertibility itself, which needs the regularity of weak cokernel
elements in `L²` and the Sobolev realization of `D`, is not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.1, on the formal adjoint of a real Cauchy–Riemann
  operator.
-/

public section

open Function Filter Set MeasureTheory Topology

namespace TauCeti

namespace Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {J : ℝ → AlmostComplexStructure V} {S : ℝ → V →L[ℝ] V} {ξ η : ℝ × ℝ → V} {z : ℝ × ℝ}

/-- The formal adjoint `D† η = -∂s η + J_t (∂t η - S_t η)` of the stationary cylinder operator
`D = ∂s + J_t (∂t - S_t)` for the `L²` pairing `∫∫ ω(·, J_t ·)`, with `s` the first and `t` the
second coordinate. On each slice `s = const` it is `-∂s + A` for the asymptotic operator `A`. -/
noncomputable def stationaryCylinderAdjoint (J : ℝ → AlmostComplexStructure V)
    (S : ℝ → V →L[ℝ] V) (η : ℝ × ℝ → V) (z : ℝ × ℝ) : V :=
  -fderiv ℝ η z stdComplexLineReal + J z.2 (fderiv ℝ η z stdComplexLineImag - S z.2 (η z))

/-- The defining formula of the formal adjoint of the stationary cylinder operator. -/
theorem stationaryCylinderAdjoint_def (J : ℝ → AlmostComplexStructure V) (S : ℝ → V →L[ℝ] V)
    (η : ℝ × ℝ → V) (z : ℝ × ℝ) :
    stationaryCylinderAdjoint J S η z =
      -fderiv ℝ η z stdComplexLineReal + J z.2 (fderiv ℝ η z stdComplexLineImag - S z.2 (η z)) :=
  (rfl)

/-- The formal adjoint vanishes on the zero map. -/
@[simp]
theorem stationaryCylinderAdjoint_zero : stationaryCylinderAdjoint J S 0 = 0 := by
  funext z
  simp [stationaryCylinderAdjoint_def]

/-- The formal adjoint commutes with real scaling. -/
@[simp]
theorem stationaryCylinderAdjoint_smul (c : ℝ) :
    stationaryCylinderAdjoint J S (c • η) = c • stationaryCylinderAdjoint J S η := by
  funext z
  simp only [stationaryCylinderAdjoint_def, fderiv_const_smul_field, Pi.smul_apply,
    smul_apply, map_sub, map_smul, smul_sub, smul_add, smul_neg]

/-- The formal adjoint is additive on maps differentiable at the point. -/
theorem stationaryCylinderAdjoint_add (hξ : DifferentiableAt ℝ ξ z)
    (hη : DifferentiableAt ℝ η z) :
    stationaryCylinderAdjoint J S (ξ + η) z =
      stationaryCylinderAdjoint J S ξ z + stationaryCylinderAdjoint J S η z := by
  simp only [stationaryCylinderAdjoint_def, fderiv_add hξ hη, Pi.add_apply,
    add_apply, map_add, map_sub, neg_add]
  abel

/-- On a map differentiable at `z`, the formal adjoint is `-∂s` plus the asymptotic operator
applied to the loop `t ↦ η(s, t)`. -/
theorem stationaryCylinderAdjoint_eq_neg_add_asymptoticOperator (hη : DifferentiableAt ℝ η z) :
    stationaryCylinderAdjoint J S η z =
      -fderiv ℝ η z stdComplexLineReal + asymptoticOperator J S (fun t ↦ η (z.1, t)) z.2 := by
  have h := stationaryCylinderOperator_eq_add_asymptoticOperator (J := J) (S := S) hη
  rw [stationaryCylinderOperator_def] at h
  rw [stationaryCylinderAdjoint_def, add_left_cancel h]

/-- **The formal adjoint is the reflected operator.** For the reflection `ρ (s, t) = (-s, t)`,
`D† η (s, t) = D (η ∘ ρ) (-s, t)`. -/
theorem stationaryCylinderAdjoint_eq_stationaryCylinderOperator_comp (η : ℝ × ℝ → V)
    (z : ℝ × ℝ) :
    stationaryCylinderAdjoint J S η z =
      stationaryCylinderOperator J S (fun w ↦ η (-w.1, w.2)) (-z.1, z.2) := by
  simp only [stationaryCylinderAdjoint_def, stationaryCylinderOperator_def, stdComplexLineReal,
    stdComplexLineImag, fderiv_comp_neg_fst_apply_one_zero, fderiv_comp_neg_fst_apply_zero_one,
    neg_neg]

/-- The formal adjoint at `z` depends only on the germ of the map at `z`. -/
theorem _root_.Filter.EventuallyEq.stationaryCylinderAdjoint_eq {η₁ η₂ : ℝ × ℝ → V}
    (h : η₁ =ᶠ[𝓝 z] η₂) :
    stationaryCylinderAdjoint J S η₁ z = stationaryCylinderAdjoint J S η₂ z := by
  rw [stationaryCylinderAdjoint_def, stationaryCylinderAdjoint_def, h.fderiv_eq, h.eq_of_nhds]

/-- The formal adjoint vanishes off the topological support of the map. -/
theorem stationaryCylinderAdjoint_of_notMem_tsupport (hz : z ∉ tsupport η) :
    stationaryCylinderAdjoint J S η z = 0 := by
  rw [stationaryCylinderAdjoint_def, image_eq_zero_of_notMem_tsupport hz,
    fderiv_of_notMem_tsupport ℝ hz]
  simp

/-- **The weighted adjoint.** Conjugating the formal adjoint by the weight `e^{δ s}` shifts it by
`+δ`, the opposite sign to `Floer.stationaryCylinderOperator_exp_smul` since `D†` contains `-∂s`:
`D†(e^{-δ s} η) = e^{-δ s} (D† + δ) η`. -/
theorem stationaryCylinderAdjoint_exp_smul (δ : ℝ) (hη : DifferentiableAt ℝ η z) :
    stationaryCylinderAdjoint J S (fun w ↦ Real.exp (-(δ * w.1)) • η w) z =
      Real.exp (-(δ * z.1)) • (stationaryCylinderAdjoint J S η z + δ • η z) := by
  have hc : HasFDerivAt (fun w : ℝ × ℝ ↦ Real.exp (-(δ * w.1)))
      (Real.exp (-(δ * z.1)) • -(δ • ContinuousLinearMap.fst ℝ ℝ ℝ)) z := by
    simpa using ((hasFDerivAt_fst (p := z)).const_smul δ).neg.exp
  have hd : HasFDerivAt (fun w ↦ Real.exp (-(δ * w.1)) • η w) _ z := hc.smul hη.hasFDerivAt
  rw [stationaryCylinderAdjoint_def, hd.fderiv, stationaryCylinderAdjoint_def]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, neg_apply,
    ContinuousLinearMap.coe_fst', stdComplexLineReal_fst, stdComplexLineImag_fst, map_sub,
    map_smul, smul_eq_mul, mul_zero, mul_one, neg_zero, zero_smul, add_zero]
  module

section Weight

variable [FiniteDimensional ℝ V]

/-- **Shifting the formal adjoint by a weight.** Replacing `S_t` by `S_t - δ J_t` shifts the
formal adjoint by `-δ`, as for `Floer.stationaryCylinderOperator_sub_smul`. -/
theorem stationaryCylinderAdjoint_sub_smul (δ : ℝ) (η : ℝ × ℝ → V) (z : ℝ × ℝ) :
    stationaryCylinderAdjoint J
        (fun t ↦ S t - δ • LinearMap.toContinuousLinearMap (J t).toLinearMap) η z =
      stationaryCylinderAdjoint J S η z - δ • η z := by
  simpa only [stationaryCylinderAdjoint_eq_stationaryCylinderOperator_comp, neg_neg] using
    stationaryCylinderOperator_sub_smul δ (fun w ↦ η (-w.1, w.2)) (-z.1, z.2)

end Weight

section Green

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V}

omit [FiniteDimensional ℝ V] in
/-- The pointwise Green identity: for `ω`-invariant `J` and infinitesimally symplectic `T`,
`g(xs + J (xt - T x), y) = g(x, -ys + J (yt - T y)) + (ω(xs, J y) + ω(x, J ys)) + (ω(xt, y) +
ω(x, yt))` for `g = ω(·, J ·)`. The last two brackets are the derivatives of `g(ξ, η)` in `s` and
of `ω(ξ, η)` in `t` when `x, xs, xt` and `y, ys, yt` are the values and partial derivatives of
`ξ` and `η`. -/
private theorem associatedBilinForm_add_apply_eq {J : AlmostComplexStructure V} {T : V →L[ℝ] V}
    (hJ : ω.Invariant J) (hT : ∀ v w, ω (T v) w + ω v (T w) = 0) (x xs xt y ys yt : V) :
    ω.associatedBilinForm J (xs + J (xt - T x)) y =
      ω.associatedBilinForm J x (-ys + J (yt - T y)) + (ω xs (J y) + ω x (J ys)) +
        (ω xt y + ω x yt) := by
  have h₁ := (ω.invariant_iff J).mp hJ (xt - T x) y
  have h₂ := hT x y
  simp only [SymplecticForm.associatedBilinForm_apply, AlmostComplexStructure.apply_apply,
    map_add, map_sub, map_neg, LinearMap.add_apply, LinearMap.sub_apply] at h₁ h₂ ⊢
  linarith

omit [FiniteDimensional ℝ V] in
/-- For continuous `(t, v) ↦ J_t v` and `t ↦ S_t`, the formal adjoint `D† η` is continuous on an
open set on which `η` is `C¹`. -/
theorem continuousOn_stationaryCylinderAdjoint (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hSc : Continuous S) {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hη : ContDiffOn ℝ 1 η U) :
    ContinuousOn (stationaryCylinderAdjoint J S η) U := by
  have hdη : ContinuousOn (fderiv ℝ η) U := hη.continuousOn_fderiv_of_isOpen hU le_rfl
  rw [funext (stationaryCylinderAdjoint_def J S η)]
  exact (hdη.clm_apply continuousOn_const).neg.add (hJc.comp_continuousOn
    (continuousOn_snd.prodMk ((hdη.clm_apply continuousOn_const).sub
      ((hSc.comp continuous_snd).continuousOn.clm_apply hη.continuousOn))))

omit [FiniteDimensional ℝ V] in
/-- For continuous `(t, v) ↦ J_t v` and `t ↦ S_t` and a `C¹` map `η`, the formal adjoint `D† η`
is continuous. -/
theorem continuous_stationaryCylinderAdjoint (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hSc : Continuous S) (hη : ContDiff ℝ 1 η) :
    Continuous (stationaryCylinderAdjoint J S η) :=
  continuousOn_univ.1 (continuousOn_stationaryCylinderAdjoint hJc hSc isOpen_univ hη.contDiffOn)

/-- Green's formula for maps which are `C¹` on the whole plane. -/
private theorem setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_add_of_contDiff
    (hJ : ∀ t, ω.Invariant (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) (hξ : ContDiff ℝ 1 ξ)
    (hη : ContDiff ℝ 1 η) {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂,
        ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) =
      (∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂,
          ω.associatedBilinForm (J z.2) (ξ z) (stationaryCylinderAdjoint J S η z)) +
        (∫ t in Icc a₂ b₂, (ω.associatedBilinForm (J t) (ξ (b₁, t)) (η (b₁, t)) -
          ω.associatedBilinForm (J t) (ξ (a₁, t)) (η (a₁, t)))) +
        ∫ s in Icc a₁ b₁, (ω (ξ (s, b₂)) (η (s, b₂)) - ω (ξ (s, a₂)) (η (s, a₂))) := by
  have hξd : Differentiable ℝ ξ := hξ.differentiable one_ne_zero
  have hηd : Differentiable ℝ η := hη.differentiable one_ne_zero
  have hdξ : Continuous (fderiv ℝ ξ) := hξ.continuous_fderiv one_ne_zero
  have hdη : Continuous (fderiv ℝ η) := hη.continuous_fderiv one_ne_zero
  have hJf {f : ℝ × ℝ → V} (hf : Continuous f) : Continuous fun z : ℝ × ℝ ↦ J z.2 (f z) :=
    hJc.comp (continuous_snd.prodMk hf)
  -- The partial derivatives of `ξ` and `η`.
  set ξs : ℝ × ℝ → V := fun z ↦ fderiv ℝ ξ z (1, 0)
  set ξt : ℝ × ℝ → V := fun z ↦ fderiv ℝ ξ z (0, 1)
  set ηs : ℝ × ℝ → V := fun z ↦ fderiv ℝ η z (1, 0)
  set ηt : ℝ × ℝ → V := fun z ↦ fderiv ℝ η z (0, 1)
  have hξs : Continuous ξs := hdξ.clm_apply continuous_const
  have hξt : Continuous ξt := hdξ.clm_apply continuous_const
  have hηs : Continuous ηs := hdη.clm_apply continuous_const
  have hηt : Continuous ηt := hdη.clm_apply continuous_const
  -- `g(D ξ, η) - g(ξ, D† η) = ∂s φ₁ + ∂t φ₂` with `Φ₁ = g(ξ, η)` and `Φ₂ = ω(ξ, η)`.
  set φ₁ : ℝ × ℝ → ℝ := fun z ↦ ω (ξs z) (J z.2 (η z)) + ω (ξ z) (J z.2 (ηs z))
  set φ₂ : ℝ × ℝ → ℝ := fun z ↦ ω (ξt z) (η z) + ω (ξ z) (ηt z)
  set A : ℝ × ℝ → ℝ := fun z ↦
    ω.associatedBilinForm (J z.2) (ξ z) (stationaryCylinderAdjoint J S η z)
  have hφ₁ : Continuous φ₁ :=
    (ω.continuous_apply_comp hξs (hJf hη.continuous)).add
      (ω.continuous_apply_comp hξ.continuous (hJf hηs))
  have hφ₂ : Continuous φ₂ :=
    (ω.continuous_apply_comp hξt hη.continuous).add (ω.continuous_apply_comp hξ.continuous hηt)
  have hA : Continuous A := ω.continuous_apply_comp hξ.continuous
    (hJf (continuous_stationaryCylinderAdjoint hJc hSc hη))
  have hpt : ∀ z : ℝ × ℝ,
      ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) =
        A z + φ₁ z + φ₂ z := fun z ↦ by
    simp only [A, stationaryCylinderOperator_def, stationaryCylinderAdjoint_def,
      stdComplexLineReal_eq, stdComplexLineImag_eq]
    exact associatedBilinForm_add_apply_eq (hJ z.2) (hS z.2) _ _ _ _ _ _
  have hR : IsCompact (Icc a₁ b₁ ×ˢ Icc a₂ b₂) := isCompact_Icc.prod isCompact_Icc
  have hJs (t : ℝ) (s : ℝ) : HasDerivAt (fun s ↦ J t (η (s, t))) (J t (ηs (s, t))) s := by
    simpa only [LinearMap.coe_toContinuousLinearMap', Function.comp_def] using
      (LinearMap.toContinuousLinearMap (J t).toLinearMap).hasFDerivAt.comp_hasDerivAt s
        (hasDerivAt_slice_left (hηd (s, t)))
  have hI₁ : ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, φ₁ z = ∫ t in Icc a₂ b₂,
      (ω.associatedBilinForm (J t) (ξ (b₁, t)) (η (b₁, t)) -
        ω.associatedBilinForm (J t) (ξ (a₁, t)) (η (a₁, t))) :=
    setIntegral_rect_eq_setIntegral_sub_of_hasDerivAt_fst (Φ := fun z ↦ ω (ξ z) (J z.2 (η z)))
      hφ₁ (fun s t ↦ ω.hasDerivAt_apply_comp (hasDerivAt_slice_left (hξd (s, t))) (hJs t s)) h₁
  have hI₂ : ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, φ₂ z =
      ∫ s in Icc a₁ b₁, (ω (ξ (s, b₂)) (η (s, b₂)) - ω (ξ (s, a₂)) (η (s, a₂))) :=
    setIntegral_rect_eq_setIntegral_sub_of_hasDerivAt_snd (Φ := fun z ↦ ω (ξ z) (η z)) hφ₂
      (fun s t ↦ ω.hasDerivAt_apply_comp (hasDerivAt_slice_right (hξd (s, t)))
        (hasDerivAt_slice_right (hηd (s, t)))) h₂
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_add (f := fun z ↦ A z + φ₁ z) ((hA.add hφ₁).continuousOn.integrableOn_compact hR)
      (hφ₂.continuousOn.integrableOn_compact hR),
    integral_add (hA.continuousOn.integrableOn_compact hR)
      (hφ₁.continuousOn.integrableOn_compact hR), hI₁, hI₂]

/-- **Green's formula for the stationary cylinder operator.** Let each `J_t` leave `ω` invariant
and let `(t, v) ↦ J_t v` be continuous, and let each `S_t` be infinitesimally symplectic and
depend continuously on `t`. For maps `ξ` and `η` which are `C¹` near each point of a rectangle
`[a₁, b₁] × [a₂, b₂]`, with `g_t = ω(·, J_t ·)`,

`∫∫ g(D ξ, η) = ∫∫ g(ξ, D† η) + ∫ (g_t(ξ, η)(b₁, t) - g_t(ξ, η)(a₁, t)) dt
  + ∫ (ω(ξ, η)(s, b₂) - ω(ξ, η)(s, a₂)) ds`. -/
theorem setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_add
    (hJ : ∀ t, ω.Invariant (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) {a₁ b₁ a₂ b₂ : ℝ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (hξ : ∀ z ∈ Icc a₁ b₁ ×ˢ Icc a₂ b₂, ContDiffAt ℝ 1 ξ z)
    (hη : ∀ z ∈ Icc a₁ b₁ ×ˢ Icc a₂ b₂, ContDiffAt ℝ 1 η z) :
    ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂,
        ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) =
      (∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂,
          ω.associatedBilinForm (J z.2) (ξ z) (stationaryCylinderAdjoint J S η z)) +
        (∫ t in Icc a₂ b₂, (ω.associatedBilinForm (J t) (ξ (b₁, t)) (η (b₁, t)) -
          ω.associatedBilinForm (J t) (ξ (a₁, t)) (η (a₁, t)))) +
        ∫ s in Icc a₁ b₁, (ω (ξ (s, b₂)) (η (s, b₂)) - ω (ξ (s, a₂)) (η (s, a₂))) := by
  have hR : IsCompact (Icc a₁ b₁ ×ˢ Icc a₂ b₂) := isCompact_Icc.prod isCompact_Icc
  have hm : MeasurableSet (Icc a₁ b₁ ×ˢ Icc a₂ b₂) := measurableSet_Icc.prod measurableSet_Icc
  -- Replace `ξ` and `η` by `C¹` maps of the plane which agree with them near the rectangle.
  obtain ⟨ξ', hξ', -, hξξ'⟩ := hR.exists_contDiff_eventuallyEq 1 hξ
  obtain ⟨η', hη', -, hηη'⟩ := hR.exists_contDiff_eventuallyEq 1 hη
  have hv {s t : ℝ} (hs : s ∈ Icc a₁ b₁) (ht : t ∈ Icc a₂ b₂) :
      ξ' (s, t) = ξ (s, t) ∧ η' (s, t) = η (s, t) :=
    ⟨(hξξ' _ ⟨hs, ht⟩).eq_of_nhds, (hηη' _ ⟨hs, ht⟩).eq_of_nhds⟩
  calc ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂,
        ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z)
      = ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂,
          ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ' z) (η' z) :=
        setIntegral_congr_fun hm fun z hz ↦ by
          rw [(hξξ' z hz).stationaryCylinderOperator_eq, (hηη' z hz).eq_of_nhds]
    _ = _ := setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_add_of_contDiff
        hJ hJc hS hSc hξ' hη' h₁ h₂
    _ = _ := by
      refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
      · exact setIntegral_congr_fun hm fun z hz ↦ by
          rw [(hηη' z hz).stationaryCylinderAdjoint_eq, (hξξ' z hz).eq_of_nhds]
      · exact setIntegral_congr_fun measurableSet_Icc fun t ht ↦ by
          rw [(hv (right_mem_Icc.2 h₁) ht).1, (hv (right_mem_Icc.2 h₁) ht).2,
            (hv (left_mem_Icc.2 h₁) ht).1, (hv (left_mem_Icc.2 h₁) ht).2]
      · exact setIntegral_congr_fun measurableSet_Icc fun s hs ↦ by
          rw [(hv hs (right_mem_Icc.2 h₂)).1, (hv hs (right_mem_Icc.2 h₂)).2,
            (hv hs (left_mem_Icc.2 h₂)).1, (hv hs (left_mem_Icc.2 h₂)).2]

/-- **Green's formula on a finite cylinder.** Under the hypotheses of
`Floer.setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_add` on `[a, b] × [0, 1]`,
let `ξ` and `η` take equal values on the slices `t = 0` and `t = 1`, and at each point of the
slices `s = a` and `s = b` let `ξ` or `η` vanish. Then `∫∫ g(D ξ, η) = ∫∫ g(ξ, D† η)` over
`[a, b] × [0, 1]`. -/
theorem setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_of_periodic
    (hJ : ∀ t, ω.Invariant (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) {a b : ℝ}
    (hξ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ContDiffAt ℝ 1 ξ z)
    (hη : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ContDiffAt ℝ 1 η z)
    (hξp : ∀ s ∈ Icc a b, ξ (s, 1) = ξ (s, 0)) (hηp : ∀ s ∈ Icc a b, η (s, 1) = η (s, 0))
    (ha : ∀ t ∈ Icc (0 : ℝ) 1, ξ (a, t) = 0 ∨ η (a, t) = 0)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ξ (b, t) = 0 ∨ η (b, t) = 0) :
    ∫ z in Icc a b ×ˢ Icc 0 1,
        ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) =
      ∫ z in Icc a b ×ˢ Icc 0 1,
        ω.associatedBilinForm (J z.2) (ξ z) (stationaryCylinderAdjoint J S η z) := by
  rcases lt_or_ge b a with hab | hab
  · simp [Icc_eq_empty_of_lt hab]
  have hv : ∫ t in Icc (0 : ℝ) 1, (ω.associatedBilinForm (J t) (ξ (b, t)) (η (b, t)) -
      ω.associatedBilinForm (J t) (ξ (a, t)) (η (a, t))) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ by
      rcases ha t ht with h | h <;> rcases hb t ht with h' | h' <;> simp [h, h']
  have hh : ∫ s in Icc a b, (ω (ξ (s, 1)) (η (s, 1)) - ω (ξ (s, 0)) (η (s, 0))) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun s hs ↦ by simp [hξp s hs, hηp s hs]
  rw [setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_add hJ hJc hS hSc hab
    zero_le_one hξ hη, hv, hh, add_zero, add_zero]

/-- Green's formula over the whole plane for `C¹` maps `ξ` and `η` such that at each point outside
an open square one of them vanishes nearby. -/
private theorem integral_associatedBilinForm_stationaryCylinderOperator_eq_of_contDiff
    (hJ : ∀ t, ω.Invariant (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) (hξ : ContDiff ℝ 1 ξ)
    (hη : ContDiff ℝ 1 η) {r : ℝ} (hr : 0 < r)
    (h0 : ∀ z ∉ Ioo (-r) r ×ˢ Ioo (-r) r, z ∉ tsupport ξ ∨ z ∉ tsupport η) :
    ∫ z, ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) =
      ∫ z, ω.associatedBilinForm (J z.2) (ξ z) (stationaryCylinderAdjoint J S η z) := by
  have hout {z : ℝ × ℝ} (hz : z ∉ Icc (-r) r ×ˢ Icc (-r) r) : z ∉ Ioo (-r) r ×ˢ Ioo (-r) r :=
    fun h ↦ hz (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self h)
  -- Both integrals live on the closed square.
  have hL := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
    (s := Icc (-r) r ×ˢ Icc (-r) r)
    (f := fun z ↦ ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z))
    fun z hz ↦ by
      rcases h0 z (hout hz) with h | h
      · rw [stationaryCylinderOperator_of_notMem_tsupport h, map_zero, LinearMap.zero_apply]
      · rw [image_eq_zero_of_notMem_tsupport h, map_zero]
  have hR := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
    (s := Icc (-r) r ×ˢ Icc (-r) r)
    (f := fun z ↦ ω.associatedBilinForm (J z.2) (ξ z) (stationaryCylinderAdjoint J S η z))
    fun z hz ↦ by
      rcases h0 z (hout hz) with h | h
      · rw [image_eq_zero_of_notMem_tsupport h, map_zero, LinearMap.zero_apply]
      · rw [stationaryCylinderAdjoint_of_notMem_tsupport h, map_zero]
  rw [← hL, ← hR, setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_add hJ hJc hS hSc
    (by linarith) (by linarith) (fun z _ ↦ hξ.contDiffAt) (fun z _ ↦ hη.contDiffAt)]
  -- On the sides of the square `ξ` or `η` vanishes.
  have hb {z : ℝ × ℝ} (hz : z ∉ Ioo (-r) r ×ˢ Ioo (-r) r) : ξ z = 0 ∨ η z = 0 :=
    (h0 z hz).imp image_eq_zero_of_notMem_tsupport image_eq_zero_of_notMem_tsupport
  have hv (t : ℝ) : ω.associatedBilinForm (J t) (ξ (r, t)) (η (r, t)) -
      ω.associatedBilinForm (J t) (ξ (-r, t)) (η (-r, t)) = 0 := by
    rcases hb (z := (r, t)) fun h ↦ lt_irrefl r h.1.2 with h | h <;>
      rcases hb (z := (-r, t)) fun h ↦ lt_irrefl (-r) h.1.1 with h' | h' <;> simp [h, h']
  have hh (s : ℝ) : ω (ξ (s, r)) (η (s, r)) - ω (ξ (s, -r)) (η (s, -r)) = 0 := by
    rcases hb (z := (s, r)) fun h ↦ lt_irrefl r h.2.2 with h | h <;>
      rcases hb (z := (s, -r)) fun h ↦ lt_irrefl (-r) h.2.1 with h' | h' <;> simp [h, h']
  simp only [hv, hh, integral_zero, add_zero]

/-- **Green's formula for compactly supported maps.** Under the hypotheses of
`Floer.setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_add`, if `ξ` is `C¹` with
compact support and `η` is `C¹` near each point of the support of `ξ`, then
`∫∫ g(D ξ, η) = ∫∫ g(ξ, D† η)` over the whole plane. -/
theorem integral_associatedBilinForm_stationaryCylinderOperator_eq_of_hasCompactSupport
    (hJ : ∀ t, ω.Invariant (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) (hξ : ContDiff ℝ 1 ξ)
    (hξc : HasCompactSupport ξ) (hη : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 1 η z) :
    ∫ z, ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) =
      ∫ z, ω.associatedBilinForm (J z.2) (ξ z) (stationaryCylinderAdjoint J S η z) := by
  -- Replace `η` by a `C¹` map of the plane which agrees with it near the support of `ξ`.
  obtain ⟨η', hη', -, hηη'⟩ := hξc.isCompact.exists_contDiff_eventuallyEq 1 hη
  have h₁ : ∫ z, ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) =
      ∫ z, ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η' z) :=
    integral_congr_ae (Eventually.of_forall fun z ↦ by
      by_cases hz : z ∈ tsupport ξ
      · dsimp only
        rw [(hηη' z hz).eq_of_nhds]
      · simp only [stationaryCylinderOperator_of_notMem_tsupport hz, map_zero,
          LinearMap.zero_apply])
  have h₂ : ∫ z, ω.associatedBilinForm (J z.2) (ξ z) (stationaryCylinderAdjoint J S η' z) =
      ∫ z, ω.associatedBilinForm (J z.2) (ξ z) (stationaryCylinderAdjoint J S η z) :=
    integral_congr_ae (Eventually.of_forall fun z ↦ by
      by_cases hz : z ∈ tsupport ξ
      · dsimp only
        rw [(hηη' z hz).stationaryCylinderAdjoint_eq]
      · simp only [image_eq_zero_of_notMem_tsupport hz, map_zero, LinearMap.zero_apply])
  rw [h₁, ← h₂]
  -- The support of `ξ` lies in an open square.
  obtain ⟨r, hr, hsub⟩ := hξc.isCompact.isBounded.subset_ball_lt 0 ((0 : ℝ), (0 : ℝ))
  rw [← ball_prod_same, Real.ball_zero_eq_Ioo] at hsub
  exact integral_associatedBilinForm_stationaryCylinderOperator_eq_of_contDiff hJ hJc hS hSc hξ hη'
    hr fun z hz ↦ .inl fun h ↦ hz (hsub h)

/-- **Green's formula for compactly supported maps, tested on the right.** Under the hypotheses
of `Floer.setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_add`, if `η` is `C¹` with
compact support and `ξ` is `C¹` near each point of the support of `η`, then
`∫∫ g(D ξ, η) = ∫∫ g(ξ, D† η)` over the whole plane. -/
theorem integral_associatedBilinForm_stationaryCylinderOperator_eq_of_hasCompactSupport_right
    (hJ : ∀ t, ω.Invariant (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η) (hξ : ∀ z ∈ tsupport η, ContDiffAt ℝ 1 ξ z) :
    ∫ z, ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) =
      ∫ z, ω.associatedBilinForm (J z.2) (ξ z) (stationaryCylinderAdjoint J S η z) := by
  -- Replace `ξ` by a `C¹` map of the plane which agrees with it near the support of `η`.
  obtain ⟨ξ', hξ', -, hξξ'⟩ := hηc.isCompact.exists_contDiff_eventuallyEq 1 hξ
  have h₁ : ∫ z, ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) =
      ∫ z, ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ' z) (η z) :=
    integral_congr_ae (Eventually.of_forall fun z ↦ by
      by_cases hz : z ∈ tsupport η
      · dsimp only
        rw [(hξξ' z hz).stationaryCylinderOperator_eq]
      · simp only [image_eq_zero_of_notMem_tsupport hz, map_zero])
  have h₂ : ∫ z, ω.associatedBilinForm (J z.2) (ξ' z) (stationaryCylinderAdjoint J S η z) =
      ∫ z, ω.associatedBilinForm (J z.2) (ξ z) (stationaryCylinderAdjoint J S η z) :=
    integral_congr_ae (Eventually.of_forall fun z ↦ by
      by_cases hz : z ∈ tsupport η
      · dsimp only
        rw [(hξξ' z hz).eq_of_nhds]
      · simp only [stationaryCylinderAdjoint_of_notMem_tsupport hz, map_zero])
  rw [h₁, ← h₂]
  -- The support of `η` lies in an open square.
  obtain ⟨r, hr, hsub⟩ := hηc.isCompact.isBounded.subset_ball_lt 0 ((0 : ℝ), (0 : ℝ))
  rw [← ball_prod_same, Real.ball_zero_eq_Ioo] at hsub
  exact integral_associatedBilinForm_stationaryCylinderOperator_eq_of_contDiff hJ hJc hS hSc hξ' hη
    hr fun z hz ↦ .inr fun h ↦ hz (hsub h)

/-- **`C¹` weak solutions of the adjoint equation are classical solutions.** Let each `J_t`
leave `ω` invariant and let `(t, v) ↦ J_t v` be continuous, and let each `S_t` be infinitesimally
symplectic and depend continuously on `t`. If a map `η` which is `C¹` on an open set `U` is
`L²`-orthogonal to `D ξ` for every smooth map `ξ` compactly supported in `U`, for the pairing
`∫∫ g(·, ·)` with `g_t = ω(·, J_t ·)`, then `D† η = 0` on `U`. The pairing need not be positive
definite: `J_t` need only leave `ω` invariant, not tame it. -/
theorem eqOn_stationaryCylinderAdjoint_zero_of_forall_integral_eq_zero
    (hJ : ∀ t, ω.Invariant (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hη : ContDiffOn ℝ 1 η U)
    (h : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
      ∫ z, ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) = 0) :
    EqOn (stationaryCylinderAdjoint J S η) 0 U := by
  set f := stationaryCylinderAdjoint J S η
  have hf : ContinuousOn f U := continuousOn_stationaryCylinderAdjoint hJc hSc hU hη
  -- Testing against `ξ = φ • v` shows that each component `g(v, D† η)` vanishes on `U`.
  have hv (v : V) : EqOn (fun z : ℝ × ℝ ↦ ω.associatedBilinForm (J z.2) v (f z)) 0 U := by
    have hF : ContinuousOn (fun z : ℝ × ℝ ↦ ω.associatedBilinForm (J z.2) v (f z)) U :=
      ω.continuousOn_apply_comp continuousOn_const
        (hJc.comp_continuousOn (continuousOn_snd.prodMk hf))
    have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
      (hF.locallyIntegrableOn hU.measurableSet) fun φ hφ hφc hφU ↦ by
        have hξ : ContDiff ℝ (⊤ : ℕ∞) fun z ↦ φ z • v := hφ.smul contDiff_const
        have hξc : HasCompactSupport fun z ↦ φ z • v := hφc.smul_right (f' := fun _ ↦ v)
        have hξU : tsupport (fun z ↦ φ z • v) ⊆ U :=
          (tsupport_smul_subset_left φ fun _ ↦ v).trans hφU
        have h₀ := h _ hξ hξc hξU
        rw [integral_associatedBilinForm_stationaryCylinderOperator_eq_of_hasCompactSupport
          hJ hJc hS hSc (hξ.of_le (by simp)) hξc
          fun z hz ↦ hη.contDiffAt (hU.mem_nhds (hξU hz))] at h₀
        simpa [smul_eq_mul] using h₀
    exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).2 hae) hU
      hF continuousOn_const
  -- The associated form `g_t` is nondegenerate, so `D† η = 0` on `U`.
  exact fun z hz ↦ (ω.associatedBilinForm_nondegenerate (J z.2)).2 (f z) fun v ↦ hv v hz

/-- **Decaying solutions of the adjoint equation vanish.** Let each `J_t` be `ω`-compatible and
let `(t, v) ↦ J_t v` be continuous, and let each `S_t` be infinitesimally symplectic and depend
continuously on `t`. A `C²` map `η` of period one in `t` with
`D† η = -∂s η + J_t (∂t η - S_t η) = 0` on `ℝ × (0, 1)`, which tends to zero together with `∂t η`
as `|s| → ∞`, uniformly in `t`, is identically zero. -/
theorem eq_zero_of_stationaryCylinderAdjoint_eq_zero (hJ : ∀ t, ω.Compatible (J t))
    (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) (hη : ContDiff ℝ 2 η)
    (hper : ∀ s t, η (s, t + 1) = η (s, t))
    (hD : EqOn (stationaryCylinderAdjoint J S η) 0 (univ ×ˢ Ioo 0 1))
    (hdecay : Tendsto (fun z ↦ (η z, fderiv ℝ η z stdComplexLineImag))
      (comap Prod.fst (cocompact ℝ)) (𝓝 0)) :
    η = 0 := by
  -- The reflection `ρ (s, t) = (-s, t)` turns `D†` into `D`.
  set ρ := LinearIsometryEquiv.negFst ℝ ℝ ℝ
  have hρ (z : ℝ × ℝ) : ρ z = (-z.1, z.2) := LinearIsometryEquiv.negFst_apply ℝ ℝ ℝ z
  have hfd (z : ℝ × ℝ) :
      fderiv ℝ (η ∘ ρ) z stdComplexLineImag = fderiv ℝ η (ρ z) stdComplexLineImag := by
    simp only [Function.comp_def, hρ, stdComplexLineImag, fderiv_comp_neg_fst_apply_zero_one]
  have hρF : Tendsto ρ (comap Prod.fst (cocompact ℝ)) (comap Prod.fst (cocompact ℝ)) := by
    rw [tendsto_comap_iff]
    simpa [Function.comp_def, hρ] using
      (Homeomorph.neg ℝ).isClosedEmbedding.tendsto_cocompact.comp tendsto_comap
  have h₀ : η ∘ ρ = 0 := by
    refine eq_zero_of_stationaryCylinderOperator_eq_zero hJ hJc hS hSc (hη.comp ρ.contDiff)
      (fun s t ↦ by simp [hρ, hper (-s) t]) (fun z hz ↦ ?_) ?_
    · simpa [stationaryCylinderAdjoint_eq_stationaryCylinderOperator_comp, hρ, Function.comp_def]
        using hD (x := ρ z) (by simpa [hρ] using hz)
    · simp_rw [hfd]
      exact hdecay.comp hρF
  funext z
  simpa [hρ] using congrFun h₀ (ρ z)

/-- **The stationary cylinder operator has no classical cokernel.** Let each `J_t` be
`ω`-compatible and let `(t, v) ↦ J_t v` be continuous, and let each `S_t` be infinitesimally
symplectic and depend continuously on `t`. Let `η` be a `C²` map of period one in `t`, which tends
to zero together with `∂t η` as `|s| → ∞`, uniformly in `t`. If `η` is `L²`-orthogonal on the
cylinder `ℝ × [0, 1]` to `D ξ` for every smooth map `ξ` of period one in `t` which vanishes for
large `|s|`, for the pairing `∫∫ ω(·, J_t ·)`, then `η` is identically zero. No nondegeneracy of
the orbit is needed. -/
theorem eq_zero_of_forall_integral_associatedBilinForm_stationaryCylinderOperator_eq_zero
    (hJ : ∀ t, ω.Compatible (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) (hη : ContDiff ℝ 2 η)
    (hper : ∀ s t, η (s, t + 1) = η (s, t))
    (hdecay : Tendsto (fun z ↦ (η z, fderiv ℝ η z stdComplexLineImag))
      (comap Prod.fst (cocompact ℝ)) (𝓝 0))
    (h : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      (∀ᶠ z in comap Prod.fst (cocompact ℝ), ξ z = 0) →
      ∫ z in univ ×ˢ Icc 0 1,
        ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) = 0) :
    η = 0 := by
  set U : Set (ℝ × ℝ) := univ ×ˢ Ioo 0 1
  have hU : IsOpen U := isOpen_univ.prod isOpen_Ioo
  have hη₁ : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  -- `D† η = 0` on the open strip `ℝ × (0, 1)`: test against periodizations of maps supported
  -- there.
  have hU0 : EqOn (stationaryCylinderAdjoint J S η) 0 U :=
    eqOn_stationaryCylinderAdjoint_zero_of_forall_integral_eq_zero (fun t ↦ (hJ t).invariant)
      hJc hS hSc hU hη₁.contDiffOn fun ξ₀ hξ₀ hξ₀c hξ₀U ↦ by
        obtain ⟨ξ, hξ, hξp, hξd, hξξ₀⟩ := exists_contDiff_periodic_eventuallyEq hξ₀ hξ₀c hξ₀U
        have hUc : U =ᵐ[volume] univ ×ˢ Icc (0 : ℝ) 1 :=
          Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ioo_ae_eq_Icc
        calc ∫ z, ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ₀ z) (η z)
            = ∫ z in U,
                ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ₀ z) (η z) :=
              (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
                rw [stationaryCylinderOperator_of_notMem_tsupport fun h ↦ hz (hξ₀U h), map_zero,
                  LinearMap.zero_apply]).symm
          _ = ∫ z in U,
                ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) :=
              setIntegral_congr_fun hU.measurableSet fun z hz ↦ by
                rw [(hξξ₀ z hz).stationaryCylinderOperator_eq]
          _ = ∫ z in univ ×ˢ Icc 0 1,
                ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) :=
              setIntegral_congr_set hUc
          _ = 0 := h ξ hξ hξp hξd
  -- The adjoint equation has no decaying solutions.
  exact eq_zero_of_stationaryCylinderAdjoint_eq_zero hJ hJc hS hSc hη hper hU0 hdecay

end Green

end Floer

end TauCeti
