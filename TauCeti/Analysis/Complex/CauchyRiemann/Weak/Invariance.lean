/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Analysis.Complex.RealDeriv
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.MeasureTheory.Function.Jacobian

/-!
# Invariance of the planar weak Cauchy–Riemann equation

The weak equation `TauCeti.IsWeakCauchyRiemannOn p U J η u`, that is
`∂ₛu + J(z, u) ∂ₜu = η(z, u)` almost everywhere, is invariant under biholomorphic changes of the
domain variable and under real-linear isomorphisms of the target, with `J` and `η` transported.

For a holomorphic map `φ` with nonvanishing derivative `φ' = a + b i`, the weak derivative of
`u ∘ φ` is `D(φ z) ∘ (φ' ·)`, so it sends `1` to `a D 1 + b D i` and `i` to `a D i - b D 1`.
Hence `∂ₛ(u ∘ φ) + J ∂ₜ(u ∘ φ) = a (D 1 + J D i) + b (D i - J D 1)`, and when `J² = -1` the
second bracket is `-J η` (`ContinuousLinearMap.add_apply_eq_iff_sub_apply_eq_neg_apply`). The
pulled back map solves the equation with the same field `J ∘ φ` and the inhomogeneous term
`a η(φ z, x) - b J(φ z, x) η(φ z, x)`. In invariant form the equation says that the
`J`-antilinear part `½ (du + J du j)` of `du` is a given `J`-antilinear one-form `ν`
(McDuff–Salamon, Section 3.1), and since `j ∂ₛ = ∂ₜ`, the term `η` is the coordinate form of
`2ν(∂ₛ)`. The antilinear part of `d(u ∘ φ)` is `ν ∘ dφ` and `dφ ∂ₛ = a ∂ₛ + b ∂ₜ`, so the new
term is the coordinate form of `2ν(dφ ∂ₛ)`. For `η = 0` the equation is unchanged, and for real
dilations `z ↦ c z + b` the term is simply scaled by `c`, with no hypothesis on `J`.

Almost-everywhere identities are transported along `φ` with
`MeasureTheory.ae_restrict_comp_of_differentiableOn`, a consequence of the change of variables
formula `map_withDensity_abs_det_fderiv_eq_addHaar`: the image of the Lebesgue measure under a map
with invertible derivative has a density, so preimages of null sets are null.

## Main results

* `TauCeti.IsWeakCauchyRiemannOn.comp_differentiableOn`: invariance under a holomorphic map,
  injective with nonvanishing derivative, between arbitrary sets `U → U'` (half-discs allowed),
  holomorphic on an open neighbourhood of `U`; `comp_differentiableOn_of_isOpen` is the open form.
* `TauCeti.isWeakCauchyRiemannOn_image_iff_comp_openPartialHomeomorph`: for a holomorphic open
  partial homeomorphism `φ`, the invariance is an equivalence, since the inverse is holomorphic
  with derivative `1 / φ'` (`OpenPartialHomeomorph.hasDerivAt_symm_of_differentiableOn`)
  and, when `J² = -1`, the map `a + b i ↦ a - b J` is multiplicative, so the two transformations
  of `η` compose to multiplication by `φ'(z) · (1 / φ'(z)) = 1`.
* `TauCeti.IsWeakCauchyRiemannOn.comp_differentiableOn_homogeneous`: the homogeneous equation is
  invariant.
* `TauCeti.IsWeakCauchyRiemannOn.comp_real_mul_add`: real dilations and translations, with the
  inhomogeneous term scaled, for every field `J`.
* `ContinuousLinearEquiv.isWeakCauchyRiemannOn_comp_iff`: transport along a real-linear
  isomorphism `A : V ≃L[ℝ] W` of the target, `u ↦ A ∘ u`, `J ↦ A J A⁻¹`, `η ↦ A η(z, A⁻¹ x)`.
* Examples: the dilation `z ↦ 2 z` doubles the inhomogeneous term, and the rotation `z ↦ i z`
  carries the solution `conj z` of `∂ₛu + i ∂ₜu = 2` to the solution `z ↦ conj (i z)` of
  `∂ₛu + i ∂ₜu = -2 i`, which pins the sign of the `J η` term.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Sections 2.2 and 3.1.
-/

public noncomputable section

open Complex MeasureTheory Set TopologicalSpace
open scoped ComplexConjugate

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] {p : ENNReal} {U U' O : Set ℂ} {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V}
  {u : ℂ → V} {φ : ℂ → ℂ}

/-! ### Changes of the domain variable -/

/-- The data of a weak solution pulled back along a `C¹` change of variables, with the equation
still evaluated at the image point. -/
private theorem IsWeakCauchyRiemannOn.exists_comp (h : IsWeakCauchyRiemannOn p U' J η u)
    (hO : IsOpen O) (hφ : ContDiffOn ℝ 1 φ O) (hUO : U ⊆ O) (hinj : InjOn φ U)
    (hdet : ∀ z ∈ U, (fderiv ℝ φ z).det ≠ 0) (hmaps : MapsTo φ U U') :
    ContinuousOn (fun z => u (φ z)) U ∧ MemLpLoc p U (fun z => u (φ z)) ∧
      ∃ D : ℂ → ℂ →L[ℝ] V,
        HasWeakFDerivOn volume (Opens.interior U) (fun z => u (φ z))
          (fun z => (D (φ z)).comp (fderiv ℝ φ z)) ∧
        MemLpLoc p U (fun z => (D (φ z)).comp (fderiv ℝ φ z)) ∧
        ∀ᵐ z ∂volume.restrict (interior U),
          D (φ z) 1 + J (φ z) (u (φ z)) (D (φ z) I) = η (φ z) (u (φ z)) := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := isWeakCauchyRiemannOn_iff.1 h
  have hφi : ContDiffOn ℝ 1 φ (interior U) := hφ.mono (interior_subset.trans hUO)
  have hdeti : ∀ z ∈ interior U, (fderiv ℝ φ z).det ≠ 0 := fun z hz =>
    hdet z (interior_subset hz)
  have hint : MapsTo φ (interior U) (interior U') :=
    hmaps.interior_of_contDiffOn (hφ.mono hUO) le_rfl fun z hz =>
      ⟨(fderiv ℝ φ z).toContinuousLinearEquivOfDetNeZero (hdeti z hz),
        ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _⟩
  exact ⟨hc.comp (hφ.continuousOn.mono hUO) hmaps,
    hu.comp_contDiffOn_diffeo hO hφ hinj hdet hUO hmaps, D,
    hD.comp_contDiffOn_diffeo hφi (hinj.mono interior_subset) hdeti (by simpa using hint),
    hDp.comp_fderiv_contDiffOn_diffeo hO hφ hinj hdet hUO hmaps,
    ae_restrict_comp_of_differentiableOn volume isOpen_interior (hφi.differentiableOn one_ne_zero)
      (hinj.mono interior_subset) hdeti hint hae⟩

/-- **Invariance under biholomorphic changes of the domain variable.** Let `φ` be holomorphic on
an open neighbourhood `O` of `U`, injective with nonvanishing derivative on `U` and mapping `U`
into `U'`, and let `J(φ z, u(φ z))` square to `-1` on the interior of `U`. If `u` is a weak
solution on `U'`, then `u ∘ φ` is a weak solution on `U` for the field `J ∘ φ` and the
inhomogeneous term `a η(φ z, x) - b J(φ z, x) η(φ z, x)`, where `φ'(z) = a + b i`. The sets may
reach their boundaries, as half-discs do. -/
theorem IsWeakCauchyRiemannOn.comp_differentiableOn (h : IsWeakCauchyRiemannOn p U' J η u)
    (hO : IsOpen O) (hφ : DifferentiableOn ℂ φ O) (hUO : U ⊆ O) (hinj : InjOn φ U)
    (hφ' : ∀ z ∈ U, deriv φ z ≠ 0) (hmaps : MapsTo φ U U')
    (hJ : ∀ z ∈ interior U, J (φ z) (u (φ z)) * J (φ z) (u (φ z)) = -1) :
    IsWeakCauchyRiemannOn p U (fun z => J (φ z))
      (fun z x => (deriv φ z).re • η (φ z) x - (deriv φ z).im • J (φ z) x (η (φ z) x))
      (fun z => u (φ z)) := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := h.exists_comp hO
    ((hφ.contDiffOn hO).restrict_scalars ℝ) hUO hinj
    (fun z hz => by
      simpa [(hφ.differentiableAt (hO.mem_nhds (hUO hz))).det_complexToReal_fderiv] using hφ' z hz)
    hmaps
  refine isWeakCauchyRiemannOn_iff.2 ⟨hc, hu, _, hD, hDp, ?_⟩
  filter_upwards [hae, self_mem_ae_restrict isOpen_interior.measurableSet] with z hz hzU
  have hd := hφ.differentiableAt (hO.mem_nhds (hUO (interior_subset hzU)))
  rw [hd.comp_fderiv_apply_one_add_apply_I, hz,
    ((ContinuousLinearMap.add_apply_eq_iff_sub_apply_eq_neg_apply (hJ z hzU)).1 hz), smul_neg,
    ← sub_eq_add_neg]

/-- **Invariance under biholomorphisms of open sets.** The form of
`TauCeti.IsWeakCauchyRiemannOn.comp_differentiableOn` for open sets `Ω` and `Ω'`. -/
theorem IsWeakCauchyRiemannOn.comp_differentiableOn_of_isOpen {Ω Ω' : Opens ℂ}
    (h : IsWeakCauchyRiemannOn p Ω' J η u) (hφ : DifferentiableOn ℂ φ Ω) (hinj : InjOn φ Ω)
    (hφ' : ∀ z ∈ (Ω : Set ℂ), deriv φ z ≠ 0) (hmaps : MapsTo φ Ω Ω')
    (hJ : ∀ z ∈ (Ω : Set ℂ), J (φ z) (u (φ z)) * J (φ z) (u (φ z)) = -1) :
    IsWeakCauchyRiemannOn p Ω (fun z => J (φ z))
      (fun z x => (deriv φ z).re • η (φ z) x - (deriv φ z).im • J (φ z) x (η (φ z) x))
      (fun z => u (φ z)) :=
  h.comp_differentiableOn Ω.isOpen hφ subset_rfl hinj hφ' hmaps fun z hz =>
    hJ z (interior_subset hz)

/-- When `J ∘ J = -1`, the map `a + b i ↦ a - b J` is multiplicative: transforming by `d` and
then by `c` is transforming by `c * d`. -/
private theorem re_smul_sub_im_smul_apply_mul {J : V →L[ℝ] V} (hJ : J * J = -1) (c d : ℂ) (x : V) :
    c.re • (d.re • x - d.im • J x) - c.im • J (d.re • x - d.im • J x) =
      (c * d).re • x - (c * d).im • J x := by
  have hJJ : J (J x) = -x := by simpa using congrArg (fun T : V →L[ℝ] V => T x) hJ
  rw [map_sub, map_smul, map_smul, hJJ, mul_re, mul_im]
  module

/-- **Invariance under a biholomorphic change of the domain chart, as an equivalence.** Let `φ`
be an open partial homeomorphism of `ℂ`, holomorphic on its source, with `φ' = a + b i`, let `U` be
a subset of its source, and let `J(w, u w)` square to `-1` on the interior of `φ '' U`. Then `u` is
a weak solution on `φ '' U` if and only if `u ∘ φ` is a weak solution on `U` for the field `J ∘ φ`
and the term `a η(φ z, x) - b J(φ z, x) η(φ z, x)`. -/
theorem isWeakCauchyRiemannOn_image_iff_comp_openPartialHomeomorph
    {φ : OpenPartialHomeomorph ℂ ℂ} (hφ : DifferentiableOn ℂ φ φ.source) (hU : U ⊆ φ.source)
    (hJ : ∀ w ∈ interior (φ '' U), J w (u w) * J w (u w) = -1) :
    IsWeakCauchyRiemannOn p (φ '' U) J η u ↔
      IsWeakCauchyRiemannOn p U (fun z => J (φ z))
        (fun z x => (deriv φ z).re • η (φ z) x - (deriv φ z).im • J (φ z) x (η (φ z) x))
        (fun z => u (φ z)) := by
  have hφ' : ∀ z ∈ φ.source, deriv φ z ≠ 0 := fun z hz =>
    deriv_ne_zero_of_injOn hφ φ.open_source φ.injOn hz
  have hUt : φ '' U ⊆ φ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact φ.map_source (hU hz)
  constructor
  · intro h
    refine h.comp_differentiableOn φ.open_source hφ hU (φ.injOn.mono hU)
      (fun z hz => hφ' z (hU hz)) (mapsTo_image _ _) fun z hz => hJ _ ?_
    exact interior_maximal (image_mono interior_subset)
      (φ.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hU)) ⟨z, hz, rfl⟩
  · intro h
    have hsd : ∀ {w}, w ∈ φ.target → HasDerivAt φ.symm (deriv φ (φ.symm w))⁻¹ w :=
      φ.hasDerivAt_symm_of_differentiableOn hφ
    have h₂ := h.comp_differentiableOn φ.open_target
      (fun w hw => (hsd hw).differentiableAt.differentiableWithinAt) hUt (φ.symm.injOn.mono hUt)
      (fun w hw => by
        rw [(hsd (hUt hw)).deriv]
        exact inv_ne_zero (hφ' _ (φ.map_target (hUt hw))))
      (by
        rintro _ ⟨z, hz, rfl⟩
        rwa [φ.left_inv (hU hz)])
      (fun w hw => by
        rw [φ.right_inv (hUt (interior_subset hw))]
        exact hJ w hw)
    have h₃ := h₂.congr (v := u) fun w hw => by
      simp only [φ.right_inv (hUt hw)]
    refine (isWeakCauchyRiemannOn_congr_ae ?_ ?_).1 h₃ <;>
      refine (ae_restrict_iff' measurableSet_interior).2 (.of_forall fun w hw => ?_)
    · simp only [φ.right_inv (hUt (interior_subset hw))]
    · have hwt := hUt (interior_subset hw)
      rw [(hsd hwt).deriv, φ.right_inv hwt, re_smul_sub_im_smul_apply_mul (hJ w hw),
        inv_mul_cancel₀ (hφ' _ (φ.map_target hwt)), one_re, one_im, one_smul, zero_smul,
        sub_zero]

/-- **The homogeneous equation is invariant** under biholomorphic changes of the domain variable,
with the field `J ∘ φ`. -/
theorem IsWeakCauchyRiemannOn.comp_differentiableOn_homogeneous
    (h : IsWeakCauchyRiemannOn p U' J (fun _ _ => 0) u) (hO : IsOpen O)
    (hφ : DifferentiableOn ℂ φ O) (hUO : U ⊆ O) (hinj : InjOn φ U)
    (hφ' : ∀ z ∈ U, deriv φ z ≠ 0) (hmaps : MapsTo φ U U')
    (hJ : ∀ z ∈ interior U, J (φ z) (u (φ z)) * J (φ z) (u (φ z)) = -1) :
    IsWeakCauchyRiemannOn p U (fun z => J (φ z)) (fun _ _ => 0) (fun z => u (φ z)) := by
  simpa using h.comp_differentiableOn hO hφ hUO hinj hφ' hmaps hJ

/-- **Real dilations and translations.** For `c : ℝ` nonzero and `b : ℂ` with `z ↦ c z + b`
mapping `U` into `U'`, a weak solution `u` on `U'` pulls back to a weak solution on `U` with the
field `J(c z + b, ·)` and the inhomogeneous term `c η(c z + b, ·)`. No hypothesis on `J` is
needed, since the derivative is real. -/
theorem IsWeakCauchyRiemannOn.comp_real_mul_add (h : IsWeakCauchyRiemannOn p U' J η u) {c : ℝ}
    (hc : c ≠ 0) (b : ℂ) (hmaps : MapsTo (fun z => (c : ℂ) * z + b) U U') :
    IsWeakCauchyRiemannOn p U (fun z => J (c * z + b)) (fun z x => c • η (c * z + b) x)
      (fun z => u (c * z + b)) := by
  have hφ : Differentiable ℂ (fun z : ℂ => (c : ℂ) * z + b) :=
    (differentiable_id.const_mul _).add_const _
  have hderiv : ∀ z, deriv (fun z : ℂ => (c : ℂ) * z + b) z = c := fun z => by
    simp
  obtain ⟨hcU, hu, D, hD, hDp, hae⟩ := h.exists_comp isOpen_univ
    ((hφ.differentiableOn.contDiffOn isOpen_univ).restrict_scalars ℝ) (subset_univ U)
    (((add_left_injective b).comp (mul_right_injective₀ (ofReal_ne_zero.2 hc))).injOn)
    (fun z _ => by rw [(hφ z).det_complexToReal_fderiv, hderiv]; simpa using hc)
    hmaps
  refine isWeakCauchyRiemannOn_iff.2 ⟨hcU, hu, _, hD, hDp, ?_⟩
  filter_upwards [hae] with z hz
  rw [(hφ z).comp_fderiv_apply_one_add_apply_I, hz, hderiv]
  simp

/-! ### Changes of the target -/

/-- **Transport along a linear isomorphism of the target.** For `A : V ≃L[ℝ] W`, a weak solution
`u` for `(J, η)` gives the weak solution `A ∘ u` for the conjugated field `A J(z, A⁻¹ y) A⁻¹` and
the inhomogeneous term `A η(z, A⁻¹ y)`, on any set `U`. -/
theorem IsWeakCauchyRiemannOn.continuousLinearEquiv_comp (h : IsWeakCauchyRiemannOn p U J η u)
    (A : V ≃L[ℝ] W) :
    IsWeakCauchyRiemannOn p U
      (fun z y => (A : V →L[ℝ] W) ∘L J z (A.symm y) ∘L (A.symm : W →L[ℝ] V))
      (fun z y => A (η z (A.symm y))) (fun z => A (u z)) := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := isWeakCauchyRiemannOn_iff.1 h
  have := hD.completeSpace
  have : CompleteSpace W :=
    (completeSpace_congr (e := A.toLinearEquiv.toEquiv) A.isUniformEmbedding).1 ‹_›
  refine isWeakCauchyRiemannOn_iff.2 ⟨A.continuous.comp_continuousOn hc,
    hu.clm_comp (A : V →L[ℝ] W), fun z => (A : V →L[ℝ] W).comp (D z),
    by simpa using hD.clm_comp (A : V →L[ℝ] W),
    hDp.clm_comp (ContinuousLinearMap.compL ℝ ℂ V W (A : V →L[ℝ] W)), ?_⟩
  filter_upwards [hae] with z hz
  simp [← hz]

/-- **Invariance under linear isomorphisms of the target.** For `A : V ≃L[ℝ] W`, the map `A ∘ u`
solves the weak equation for the transported data `A J(z, A⁻¹ y) A⁻¹` and `A η(z, A⁻¹ y)` exactly
when `u` solves it for `(J, η)`. -/
theorem _root_.ContinuousLinearEquiv.isWeakCauchyRiemannOn_comp_iff (A : V ≃L[ℝ] W) :
    IsWeakCauchyRiemannOn p U
        (fun z y => (A : V →L[ℝ] W) ∘L J z (A.symm y) ∘L (A.symm : W →L[ℝ] V))
        (fun z y => A (η z (A.symm y))) (fun z => A (u z)) ↔
      IsWeakCauchyRiemannOn p U J η u := by
  refine ⟨fun h => ?_, fun h => h.continuousLinearEquiv_comp A⟩
  convert h.continuousLinearEquiv_comp A.symm using 2 with z y
  · ext x
    simp
  · simp
  · simp

/-! ### Examples -/

/-- **Dilation.** Pulling back along `z ↦ 2 z` from the disc of radius `2` to the unit disc keeps
the field, evaluated at `2 z`, and doubles the inhomogeneous term. -/
example (h : IsWeakCauchyRiemannOn p (Metric.ball 0 2) J η u) :
    IsWeakCauchyRiemannOn p (Metric.ball 0 1) (fun z => J (2 * z))
      (fun z x => (2 : ℝ) • η (2 * z) x) (fun z => u (2 * z)) := by
  have hmaps : MapsTo (fun z : ℂ => ((2 : ℝ) : ℂ) * z + 0) (Metric.ball 0 1) (Metric.ball 0 2) :=
    fun z hz => by
      simp only [Metric.mem_ball, dist_zero_right, add_zero, norm_mul, ofReal_ofNat,
        Complex.norm_ofNat] at hz ⊢
      linarith
  simpa using h.comp_real_mul_add (c := 2) two_ne_zero 0 hmaps

/-- Conjugation solves `∂ₛu + i ∂ₜu = 2` on every open set: `1 + i·(-i) = 2`. -/
private theorem isWeakCauchyRiemannOn_conj_two {Ω : Opens ℂ} :
    IsWeakCauchyRiemannOn p Ω (fun _ _ => I • ContinuousLinearMap.id ℝ ℂ) (fun _ _ => 2)
      conj := by
  refine isWeakCauchyRiemannOn_of_contDiffOn conjCLE.contDiff.contDiffOn fun z _ => ?_
  have hconj : (conj : ℂ → ℂ) = conjCLE := funext fun x => (conjCLE_apply x).symm
  rw [hconj, conjCLE.fderiv]
  norm_num [Complex.ext_iff]

/-- **Rotation.** The rotation `φ z = i z` has `φ' = i`, so `a = 0`, `b = 1`, and it
carries the solution `conj z` of `∂ₛu + i ∂ₜu = 2` to the solution `z ↦ conj (i z)` of
`∂ₛu + i ∂ₜu = -2 i`. Since the inhomogeneous term of a weak solution is determined almost
everywhere, the opposite sign `+ b J η` in the transformed term would give `2 i` and is ruled
out. -/
example {Ω : Opens ℂ} :
    IsWeakCauchyRiemannOn p Ω (fun _ _ => I • ContinuousLinearMap.id ℝ ℂ) (fun _ _ => -2 * I)
      (fun z => conj (I * z)) := by
  have h := (isWeakCauchyRiemannOn_conj_two (p := p) (Ω := ⊤)).comp_differentiableOn_of_isOpen
    (Ω := Ω) (φ := fun z => I * z) (differentiable_id.const_mul _).differentiableOn
    ((mul_right_injective₀ I_ne_zero).injOn) (fun z _ => by simp) (mapsTo_univ _ _)
    fun z _ => by ext x; simp [← mul_assoc]
  convert h using 2 with z x
  simp [mul_comm]

end TauCeti
