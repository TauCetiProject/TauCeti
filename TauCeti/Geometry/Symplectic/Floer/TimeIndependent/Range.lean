/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Sobolev
import TauCeti.Analysis.Calculus.Morse.NormSq
import TauCeti.Analysis.Sobolev.Cylinder.Slice.NonzeroMode
import TauCeti.Geometry.Symplectic.Floer.Sobolev.UnitaryFrame
import TauCeti.Geometry.Symplectic.Hamiltonian.ConstantOrbit
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Hamiltonian.Hessian

/-!
# The range of the linearized operator along a time-independent cylinder

Let `(V, ω)` be a finite-dimensional symplectic vector space whose inner product is the metric
`ω(·, J ·)` of a constant compatible almost complex structure `J` admitting a unitary frame, let
`H = H_s : V → ℝ` be jointly `C²` Hamiltonians depending on `s ∈ ℝ` alone, such as an autonomous
Hamiltonian or continuation data `K = H_s dt`, and `γ` a continuous curve with
`‖dX_H(γ(s))‖ ≤ a < 2π` for every `s`, where `dX_H(γ(s))` stands for `dX_{H_s}(γ(s))`. Along the
time-independent cylinder `(s, t) ↦ γ(s)` the Sobolev realization

`D : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)`, `D ξ = ∂s ξ + J (∂t ξ - dX_H(γ(s)) ξ)`

of the linearized Floer operator commutes with the slice average, the projection onto the zero
Fourier mode in `t`, and on the zero mode it is the Morse operator `M ζ = ζ' - J dX_H(γ) ζ`
(`TauCeti/Geometry/Symplectic/Floer/TimeIndependent/Sobolev.lean`, where the kernels of `D` and
`M` are identified). This file describes the range of `D`.

* **`D` is onto the nonzero modes.** Every `y ∈ L²` whose slice average vanishes is `D x` for some
  `x ∈ W^{1,2}` whose slice average vanishes
  (`TauCeti.SymplecticForm.exists_floerSobolevOperator_eq_of_sliceAverageLp_eq_zero`).
* **The range of `D` is read off on the zero mode.** Consequently `y` lies in the range of `D`
  exactly when its slice average is the zero mode `(s, t) ↦ (M ζ)(s)` of an element of the range
  of the Morse operator (`TauCeti.SymplecticForm.mem_range_floerSobolevOperator_iff`). In
  particular the nonzero modes contribute nothing to the cokernel of `D`.

On the nonzero modes `D` is bounded below with a constant depending only on `2π - a`
(`mul_sq_norm_le_mul_sq_norm_floerSobolevOperator_of_sliceAverageL_eq_zero` in the namespace
`TauCeti.SymplecticForm`). Onto-ness comes from the method of continuity. Join `H_s` to the
quadratic Hamiltonian `ε ‖y‖²` by the segment `(1 - τ) ε ‖y‖² + τ H_s`: for small `ε > 0` every
member keeps `‖dX‖ ≤ max a (1 / 2) < 2π` along `γ`, so the restrictions of the operators to the
nonzero modes form a continuous family bounded below with one constant along the segment. At
`τ = 0` the coefficient `-2ε J` is constant and the constant orbit at `0` is nondegenerate, so the
operator is invertible
(`isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt_of_compatible` in the namespace
`TauCeti.SymplecticForm`) and its restriction is onto. Hence every restriction is onto
(`TauCeti.CylinderSobolev.exists_eq_of_sliceAverageLp_eq_zero_of_isPreconnected`).

## References

* A. Floer, *Witten's complex and infinite dimensional Morse theory*, J. Differential Geom.
  **30** (1989), 207–221.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360, on the linearized operator at
  time-independent solutions of a small Hamiltonian.
-/

public section

open Real Set MeasureTheory ContinuousLinearMap
open TauCeti.StripSobolev TauCeti.CylinderSobolev
open scoped RealInnerProductSpace ENNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {H : ℝ → V → ℝ} {γ : ℝ → V}

/-- The linearized operator of the quadratic Hamiltonian `ε ‖y‖²` has the constant coefficient
`-2ε J`, whatever the curve; when `ε ≠ 0` and `2 |ε| ‖J‖ < log 2` it is invertible. -/
private theorem isInvertible_floerSobolevOperator_const_mul_norm_sq
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] {Φ : F ≃L[ℝ] V} (hΦ : ∀ v, Φ (Complex.I • v) = J (Φ v))
    (hΦω : ∀ v w, ω (Φ v) (Φ w) = (inner ℂ v w).im) {ε : ℝ} (hε : ε ≠ 0)
    (hsmall : |ε| * (2 * ‖J.toLinearMap.toContinuousLinearMap‖) < Real.log 2) (u : ℝ × ℝ → V) :
    (ω.floerSobolevOperator 2 (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
      (fun _ y ↦ ε * ‖y‖ ^ 2) u).IsInvertible := by
  set Jc := J.toLinearMap.toContinuousLinearMap
  have hX : ω.hamiltonianVectorField (fun y ↦ ε * ‖y‖ ^ 2) = ⇑((ε * -2) • Jc) := by
    funext y
    rw [hamiltonianVectorField_const_mul, hamiltonianVectorField_norm_sq hg]
    simp [Jc, smul_smul]
  have hL : LipschitzWith ‖(ε * -2) • Jc‖₊
      (ω.timeDependentHamiltonianSuspension fun _ y ↦ ε * ‖y‖ ^ 2) :=
    ω.lipschitzWith_timeDependentHamiltonianSuspension_const _ (by rw [hX]; exact lipschitzWith _)
  have hF : ContDiff ℝ 2 (fun y : V ↦ ‖y‖ ^ 2) := contDiff_norm_sq ℝ
  have hp : fderiv ℝ (fun y : V ↦ ‖y‖ ^ 2) 0 = 0 :=
    isNondegenerateCriticalPoint_norm_sq.fderiv_eq_zero
  have hnd := (ω.isNondegenerateFixedPt_timeDependentHamiltonianFlow_const_mul_iff hF hp hL
    (s := 0) (t := 1) (by simpa using hε) (by
      rw [hamiltonianVectorField_norm_sq hg, ContinuousLinearMap.fderiv, norm_smul]
      simpa using hsmall)).2 isNondegenerateCriticalPoint_norm_sq
  have hJ : ω.Compatible J :=
    ω.compatible_of_isInvertible_of_forall_eq_im_inner (Φ := (Φ : F →L[ℝ] V)) ⟨Φ, rfl⟩ hΦω
      fun v ↦ (hΦ v).symm
  have hinv := ω.isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt_of_compatible hL
    (contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_snd)) (fun _ ↦ rfl) (x := fun _ ↦ 0)
    (fun t ↦ by simpa only [hX, map_zero] using hasDerivAt_const t (0 : V)) (fun _ ↦ rfl)
    (J := fun _ _ ↦ J) hg hΦ hΦω (fun _ ↦ hJ) contDiff_const (fun _ ↦ rfl) hnd
  convert hinv using 1
  rw [floerSobolevOperator_def, floerSobolevOperator_def]
  congr 2
  funext z
  rw [floerJetCoeff_const_eq, floerJetCoeff_const_eq]
  simp only [hX, ContinuousLinearMap.fderiv]

/-- Along the segment `(1 - τ) ε ‖y‖² + τ G` of Hamiltonians, the derivative of the Hamiltonian
vector field is the affine combination `(1 - τ) (-2ε J) + τ dX_G`. -/
private theorem fderiv_hamiltonianVectorField_lineMap (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    {G : V → ℝ} (hG : ContDiff ℝ 2 G) (ε τ : ℝ) (y : V) :
    fderiv ℝ (ω.hamiltonianVectorField fun y ↦ (1 - τ) * (ε * ‖y‖ ^ 2) + τ * G y) y =
      (1 - τ) • (ε * -2) • J.toLinearMap.toContinuousLinearMap +
        τ • fderiv ℝ (ω.hamiltonianVectorField G) y := by
  set Jc := J.toLinearMap.toContinuousLinearMap
  have hXH : Differentiable ℝ (ω.hamiltonianVectorField G) :=
    (ω.contDiff_hamiltonianVectorField (n := 1) hG).differentiable one_ne_zero
  have hX : (ω.hamiltonianVectorField fun y ↦ (1 - τ) * (ε * ‖y‖ ^ 2) + τ * G y) =
      fun y ↦ (1 - τ) • ((ε * -2) • Jc) y + τ • ω.hamiltonianVectorField G y := by
    funext z
    rw [ω.hamiltonianVectorField_const_mul_add_const_mul
      ((contDiff_const.mul (contDiff_norm_sq ℝ)).differentiable two_ne_zero z)
      (hG.differentiable two_ne_zero z), hamiltonianVectorField_const_mul,
      hamiltonianVectorField_norm_sq hg]
    simp [Jc, smul_smul]
  rw [hX]
  exact (((((ε * -2) • Jc).hasFDerivAt (x := y)).const_smul (1 - τ)).add
    ((hXH y).hasFDerivAt.const_smul τ)).fderiv

/-- The derivative of the Hamiltonian vector field along the segment of Hamiltonians is bounded by
the affine combination of the bounds at its ends. -/
private theorem norm_fderiv_hamiltonianVectorField_lineMap_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {a : ℝ}
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a) (ε τ s : ℝ) :
    ‖fderiv ℝ (ω.hamiltonianVectorField fun y ↦ (1 - τ) * (ε * ‖y‖ ^ 2) + τ * H s y) (γ s)‖ ≤
      |1 - τ| * ‖(ε * -2) • J.toLinearMap.toContinuousLinearMap‖ + |τ| * a := by
  rw [fderiv_hamiltonianVectorField_lineMap hg (G := H s)
    (hH.comp (contDiff_const.prodMk contDiff_id))]
  refine (norm_add_le _ _).trans (add_le_add (by rw [norm_smul, Real.norm_eq_abs]) ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (haγ s) (abs_nonneg τ)

/-- The Sobolev realizations of the linearized operators along `(s, t) ↦ γ(s)` for the segment
`(1 - τ) ε ‖y‖² + τ H_s` of Hamiltonians depending on `s`. -/
private noncomputable def segmentOperator (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (H : ℝ → V → ℝ) (γ : ℝ → V) (ε τ : ℝ) : H1 V →L[ℝ] Lp V 2 stripMeasure :=
  ω.floerSobolevOperator 2 (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
    (fun z y ↦ (1 - τ) * (ε * ‖y‖ ^ 2) + τ * H z.1 y) (fun z ↦ γ z.1)

omit [FiniteDimensional ℝ V] in
private theorem contDiff_lineMap (hH : ContDiff ℝ 2 (Function.uncurry H)) (ε τ : ℝ) :
    ContDiff ℝ 2 (Function.uncurry fun s (y : V) ↦ (1 - τ) * (ε * ‖y‖ ^ 2) + τ * H s y) :=
  (contDiff_const.mul (contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_snd))).add
    (contDiff_const.mul hH)

/-- The operators of the segment depend affinely on the parameter. -/
private theorem segmentOperator_eq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 2 (Function.uncurry H)) (hγ : Continuous γ) {a : ℝ}
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a) (ε τ : ℝ) :
    segmentOperator ω J H γ ε τ = segmentOperator ω J H γ ε 0 +
      τ • (segmentOperator ω J H γ ε 1 - segmentOperator ω J H γ ε 0) := by
  have hM (σ : ℝ) := memLp_floerJetCoeff_const_comp_fst (J := J) (contDiff_lineMap hH ε σ) hγ
    (norm_fderiv_hamiltonianVectorField_lineMap_le hg hH haγ ε σ)
  ext1 x
  rw [add_apply, _root_.smul_apply, sub_apply]
  refine Lp.ext ?_
  filter_upwards [coeFn_floerSobolevOperator ω (hM τ) x, coeFn_floerSobolevOperator ω (hM 0) x,
    coeFn_floerSobolevOperator ω (hM 1) x, Lp.coeFn_add (segmentOperator ω J H γ ε 0 x)
      (τ • (segmentOperator ω J H γ ε 1 x - segmentOperator ω J H γ ε 0 x)),
    Lp.coeFn_smul τ (segmentOperator ω J H γ ε 1 x - segmentOperator ω J H γ ε 0 x),
    Lp.coeFn_sub (segmentOperator ω J H γ ε 1 x) (segmentOperator ω J H γ ε 0 x)]
    with z h h₀ h₁ hadd hsmul hsub
  simp only [segmentOperator] at h h₀ h₁ hadd hsmul hsub ⊢
  simp only [hadd, Pi.add_apply, hsmul, Pi.smul_apply, hsub, Pi.sub_apply, h, h₀, h₁,
    floerJetCoeff_const_eq,
    fderiv_hamiltonianVectorField_lineMap hg (G := H z.1)
      (hH.comp (contDiff_const.prodMk contDiff_id)),
    firstOrderJetCoeff_apply, neg_apply, comp_apply, add_apply, _root_.smul_apply, map_add,
    map_smul]
  module

/-- On the nonzero modes, every operator of the segment for `τ ∈ [0, 1]` is bounded below with
constants independent of `τ`. -/
private theorem mul_norm_le_mul_norm_segmentOperator (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 2 (Function.uncurry H)) (hγ : Continuous γ) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a) {ε : ℝ}
    (hε : |ε| * (2 * ‖J.toLinearMap.toContinuousLinearMap‖) ≤ 1 / 2) {τ : ℝ} (hτ : τ ∈ Icc 0 1)
    {x : H1 V} (hx : sliceAverageL x = 0) :
    (2 * π - max a (1 / 2)) * ‖x‖ ≤ (2 * π + 1) * ‖segmentOperator ω J H γ ε τ x‖ := by
  have hb : max a (1 / 2) < 2 * π := max_lt ha (by linarith [two_le_pi])
  have hQ : ‖(ε * -2) • J.toLinearMap.toContinuousLinearMap‖ ≤ max a (1 / 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_two]
    refine le_trans ?_ (le_max_right _ _)
    linarith
  have hbound : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField
      fun y ↦ (1 - τ) * (ε * ‖y‖ ^ 2) + τ * H s y) (γ s)‖ ≤ max a (1 / 2) := fun s ↦
    (norm_fderiv_hamiltonianVectorField_lineMap_le hg hH haγ ε τ s).trans (by
      rw [abs_of_nonneg (sub_nonneg.2 hτ.2), abs_of_nonneg hτ.1]
      nlinarith [hτ.1, hτ.2, le_max_left a (1 / 2)])
  have h := mul_sq_norm_le_mul_sq_norm_floerSobolevOperator_of_sliceAverageL_eq_zero hg
    (contDiff_lineMap hH ε τ) hγ hb.le hbound hx
  rw [← segmentOperator] at h
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  nlinarith [pi_pos]

private theorem segmentOperator_one (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (H : ℝ → V → ℝ) (γ : ℝ → V) (ε : ℝ) :
    segmentOperator ω J H γ ε 1 = ω.floerSobolevOperator 2
      (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun z ↦ H z.1)
        (fun z ↦ γ z.1) := by
  rw [segmentOperator]
  congr 1
  funext _ y
  ring

private theorem isInvertible_segmentOperator_zero (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] {Φ : F ≃L[ℝ] V}
    (hΦ : ∀ v, Φ (Complex.I • v) = J (Φ v)) (hΦω : ∀ v w, ω (Φ v) (Φ w) = (inner ℂ v w).im)
    {ε : ℝ} (hε : ε ≠ 0)
    (hsmall : |ε| * (2 * ‖J.toLinearMap.toContinuousLinearMap‖) < Real.log 2) :
    (segmentOperator ω J H γ ε 0).IsInvertible := by
  have h : (fun (z : ℝ × ℝ) (y : V) ↦ (1 - 0) * (ε * ‖y‖ ^ 2) + 0 * H z.1 y) =
      fun _ y ↦ ε * ‖y‖ ^ 2 := by
    funext _ y
    ring
  rw [segmentOperator, h]
  exact isInvertible_floerSobolevOperator_const_mul_norm_sq hg hΦ hΦω hε hsmall _

private theorem segmentOperator_sliceAverageL (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (H : ℝ → V → ℝ) (γ : ℝ → V) (ε τ : ℝ) (x : H1 V) :
    segmentOperator ω J H γ ε τ (sliceAverageL x) =
      sliceAverageLp (segmentOperator ω J H γ ε τ x) :=
  floerSobolevOperator_sliceAverageL ω J (fun s y ↦ (1 - τ) * (ε * ‖y‖ ^ 2) + τ * H s y) γ x

/-- At `τ = 0` the segment operator is invertible and commutes with the slice average, so it maps
the nonzero modes of `W^{1,2}` onto those of `L²`. -/
private theorem exists_segmentOperator_zero_eq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] {Φ : F ≃L[ℝ] V}
    (hΦ : ∀ v, Φ (Complex.I • v) = J (Φ v)) (hΦω : ∀ v w, ω (Φ v) (Φ w) = (inner ℂ v w).im)
    {ε : ℝ} (hε : ε ≠ 0)
    (hsmall : |ε| * (2 * ‖J.toLinearMap.toContinuousLinearMap‖) < Real.log 2)
    {y : Lp V 2 stripMeasure} (hy : sliceAverageLp y = 0) :
    ∃ x, sliceAverageL x = 0 ∧ segmentOperator ω J H γ ε 0 x = y := by
  obtain ⟨e, he⟩ := isInvertible_segmentOperator_zero (H := H) (γ := γ) hg hΦ hΦω hε hsmall
  have hDx : segmentOperator ω J H γ ε 0 (e.symm y) = y := by
    rw [← he, ContinuousLinearEquiv.coe_coe, e.apply_symm_apply]
  refine ⟨e.symm y, e.injective ?_, hDx⟩
  rw [map_zero, ← ContinuousLinearEquiv.coe_coe, he, segmentOperator_sliceAverageL, hDx, hy]

/-- **The linearized operator is onto the nonzero modes.** Let the inner product of `V` be the
metric `ω(·, J ·)` of a structure `J` with a unitary frame `Φ : F ≃ V` from a finite-dimensional
complex inner product space (`Φ (i v) = J (Φ v)` and `ω (Φ v) (Φ w) = Im ⟪v, w⟫`), let `H_s` be
jointly `C²` Hamiltonians depending on `s` and `γ` a continuous curve with
`‖dX_{H_s}(γ(s))‖ ≤ a < 2π` for every `s`. Then every `y ∈ L²(ℝ × S¹, V)` whose slice average
vanishes is `D x` for the Sobolev realization `D` of the linearized operator along `(s, t) ↦ γ(s)`
and some `x ∈ W^{1,2}(ℝ × S¹, V)` whose slice average vanishes. -/
theorem exists_floerSobolevOperator_eq_of_sliceAverageLp_eq_zero
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] {Φ : F ≃L[ℝ] V} (hΦ : ∀ v, Φ (Complex.I • v) = J (Φ v))
    (hΦω : ∀ v w, ω (Φ v) (Φ w) = (inner ℂ v w).im) (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hγ : Continuous γ) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a)
    {y : Lp V 2 stripMeasure} (hy : sliceAverageLp y = 0) :
    ∃ x : H1 V, sliceAverageL x = 0 ∧
      ω.floerSobolevOperator 2 (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun z ↦ H z.1) (fun z ↦ γ z.1) x = y := by
  set Jc := J.toLinearMap.toContinuousLinearMap
  -- The quadratic end `ε ‖y‖²` of the segment is small enough for the gap and nondegenerate.
  set ε : ℝ := Real.log 2 / (4 * (‖Jc‖ + 1)) with hεdef
  have hε0 : 0 < ε := by positivity
  have hεJ : |ε| * (2 * ‖Jc‖) ≤ Real.log 2 / 2 := by
    rw [abs_of_pos hε0, hεdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith [norm_nonneg Jc, Real.log_pos one_lt_two]
  have hlog : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos two_pos).trans (by norm_num)
  have hsmall : |ε| * (2 * ‖Jc‖) < Real.log 2 :=
    hεJ.trans_lt (by linarith [Real.log_pos one_lt_two])
  have hb : 0 < 2 * π - max a (1 / 2) := sub_pos.2 (max_lt ha (by linarith [two_le_pi]))
  have hcont : Continuous (segmentOperator ω J H γ ε) := by
    rw [funext (segmentOperator_eq hg hH hγ haγ ε)]
    -- Instance search for `ContinuousAdd` on operators out of the submodule `H1 V` exhausts the
    -- default typeclass heartbeats: unifying the generic addition with that of the operator space
    -- needs the unexposed body of `jetClosure`. Project it from the operator-space instance.
    have : ContinuousAdd (H1 V →L[ℝ] Lp V 2 stripMeasure) :=
      (isTopologicalAddGroup (E := H1 V) (F := Lp V 2 stripMeasure)).toContinuousAdd
    exact continuous_const.add (continuous_id.smul continuous_const)
  rw [← segmentOperator_one ω J H γ ε]
  refine exists_eq_of_sliceAverageLp_eq_zero_of_isPreconnected hcont.continuousOn
    isPreconnected_Icc (fun τ _ ↦ segmentOperator_sliceAverageL ω J H γ ε τ)
    (C := (2 * π + 1) / (2 * π - max a (1 / 2))) (fun τ hτ x hx ↦ ?_) (left_mem_Icc.2 zero_le_one)
    (fun _ hz ↦ exists_segmentOperator_zero_eq hg hΦ hΦω hε0.ne' hsmall hz)
    (right_mem_Icc.2 zero_le_one) hy
  rw [div_mul_eq_mul_div, le_div_iff₀ hb, mul_comm]
  exact mul_norm_le_mul_norm_segmentOperator hg hH hγ ha haγ (hεJ.trans (by linarith)) hτ hx

variable {A : Lp (V →L[ℝ] V) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}

/-- **The range of the linearized operator is read off on the zero mode.** Under the hypotheses of
`TauCeti.SymplecticForm.exists_floerSobolevOperator_eq_of_sliceAverageLp_eq_zero`, let `A` be the
`L∞` class of `s ↦ -J dX_{H_s}(γ(s))`. An element `y` of `L²(ℝ × S¹, V)` lies in the range of the
Sobolev realization of the linearized operator along `(s, t) ↦ γ(s)` exactly when its slice average
is the zero mode `(s, t) ↦ (M ζ)(s)` of the image of some `ζ ∈ W^{1,2}(ℝ, V)` under the Morse
operator `M ζ = ζ' - J dX_{H_s}(γ) ζ`. -/
theorem mem_range_floerSobolevOperator_iff (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] {Φ : F ≃L[ℝ] V}
    (hΦ : ∀ v, Φ (Complex.I • v) = J (Φ v)) (hΦω : ∀ v w, ω (Φ v) (Φ w) = (inner ℂ v w).im)
    (hH : ContDiff ℝ 2 (Function.uncurry H)) (hγ : Continuous γ) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -(J.toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s))))
    (y : Lp V 2 stripMeasure) :
    y ∈ range (ω.floerSobolevOperator 2 (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1)) ↔
      ∃ ζ : WeakDerivStep volume ⊤ 2 (ContinuousLinearMap.id ℝ
          (Lp V 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)))),
        sliceAverageLp y = zeroModeLp V (WeakDerivStep.trajectoryOperator A ζ) := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨u, hu⟩ := sliceAverageL_mem_range_zeroModeL x
    refine ⟨u, ?_⟩
    rw [← floerSobolevOperator_sliceAverageL, ← hu, floerSobolevOperator_zeroModeL hH hγ haγ hA]
  · rintro ⟨ζ, hζ⟩
    obtain ⟨x, -, hx⟩ := exists_floerSobolevOperator_eq_of_sliceAverageLp_eq_zero hg hΦ hΦω hH hγ
      ha haγ (y := y - sliceAverageLp y) (by rw [map_sub, sliceAverageLp_sliceAverageLp, sub_self])
    refine ⟨zeroModeL V ζ + x, ?_⟩
    rw [map_add, floerSobolevOperator_zeroModeL hH hγ haγ hA, ← hζ, hx, add_sub_cancel]

end TauCeti.SymplecticForm
