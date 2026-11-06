/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Geometry.Symplectic.Cayley.Tangent
import TauCeti.MeasureTheory.Integral.Bochner.Set
import TauCeti.Topology.Compactness.Compact

/-!
# Variations of the almost complex structure detect cokernel elements at injective points

On a sphere component of a Floer configuration the almost complex structure is frozen: it is a
target structure `J(x)` that does not depend on the domain point. Free Hamiltonian directions
`δK` are not available there, so transversality for such components uses variations `Y` of `J`
alone. In the universal linearization of `∂s u - X_Ks + J(u)(∂t u - X_Kt)` a variation `Y` of `J`
contributes the term `Y(u)(∂t u - X_Kt)`
(`SymplecticForm.hasDerivAt_floerOperator_add_smul`). Since `Y` is a function on the target, its
pairing with a cokernel element can only be localized in the domain near points that `u` does not
revisit. This is the step of the transversality argument that uses simplicity of the curve.

The main result (`SymplecticForm.eq_zero_of_integral_apply_compatibleVariation_eq_zero`) is the
following. Let `ω` be a constant symplectic form on `V` and `J` a `Cⁿ` family of `ω`-compatible
complex structures on `V`. Let `u`, `ξ` and `η` be continuous on an open set `Ω` of the domain,
with `η` taking values in covectors, and suppose that
`∫_Ω η(z)(Y(u z)(ξ z)) dμ = 0` for every compactly supported `Cⁿ` field `Y` of compatible
variations, `Y(x) ∈ T_{J(x)}`. Then `η(z₀) = 0` at every point `z₀ ∈ Ω` where `ξ(z₀) ≠ 0` and
which is *injective* in the following sense: points of `Ω` whose images are close to `u(z₀)` are
close to `z₀` (`comap u (𝓝 (u z₀)) ⊓ 𝓟 Ω ≤ 𝓝 z₀`). If `u` is continuous on a compact set `K`
and `z₀` is the only point of `K` sent to `u(z₀)`, this holds for every `Ω ⊆ K`
(`IsCompact.comap_nhds_inf_principal_le_nhds`); for a curve defined on the whole sphere, `K` is
the sphere.

The proof follows McDuff–Salamon. If `η(z₀) ≠ 0`, there is a `Cⁿ` field `B` of compatible
variations of all the structures `J(x)` with `η(z₀)(B(u z₀) ξ(z₀)) = 1`
(`SymplecticForm.exists_contDiff_mem_compatibleTangentSpace_apply_eq`). Multiplying `B` by a bump
function of `x` supported where the localization condition confines `z` to a compact
neighbourhood of `z₀` on which the pairing is positive gives a variation whose integral against
`η` is positive. Neither a Floer equation nor nonvanishing of `ξ` away from `z₀` is assumed.

For the coordinate Floer operator (`SymplecticForm.floerOperator`) with a frozen structure, the
pairing is with its derivative along the line `J + q Y`, and the vector `ξ` is the component
`∂t u - X_Kt` of the perturbed derivative
(`SymplecticForm.eq_zero_of_integral_apply_deriv_floerOperator_eq_zero`).

These are statements about one cokernel pairing for a constant symplectic form in local
coordinates. They do not assert that simple curves have a dense set of injective points, nor any
Sobolev or Fredholm surjectivity of the universal operator.

## Main results

* `SymplecticForm.eq_zero_of_integral_apply_compatibleVariation_eq_zero`: compatible variations
  of a frozen structure detect a covector field at an injective point.
* `SymplecticForm.hasDerivAt_floerOperator_add_smul`: the derivative of the coordinate Floer
  operator along the line `J + q Y` of endomorphism fields is `Y(u)(∂t u - X_Kt)`.
* `SymplecticForm.eq_zero_of_integral_apply_deriv_floerOperator_eq_zero`: the same detection
  statement for the `J`-direction derivatives of the coordinate Floer operator.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1 and Lemma 3.2.2.
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292.
-/

public section

open Filter MeasureTheory Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

section Detection

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [T2Space E] [LocallyCompactSpace E] {μ : Measure E} [μ.IsOpenPosMeasure]
  [IsFiniteMeasureOnCompacts μ]

/-- **Compatible variations of a frozen structure detect cokernel elements at injective
points.** Let `J` be a `Cⁿ` family of `ω`-compatible structures on `V`, and let `u`, `ξ` and the
covector field `η` be continuous on an open set `Ω`. Suppose that
`∫_Ω η(z)(Y(u z)(ξ z)) dμ = 0` for every compactly supported `Cⁿ` field `Y` with `Y(x)` in the
compatible tangent space of `J(x)`. Then `η` vanishes at every point `z₀ ∈ Ω`
with `ξ(z₀) ≠ 0` at which `u` is injective in the sense that points of `Ω` with images near
`u(z₀)` lie near `z₀`. -/
theorem eq_zero_of_integral_apply_compatibleVariation_eq_zero {n : ℕ∞} (ω : SymplecticForm V)
    {J : V → AlmostComplexStructure V} (hJc : ∀ x, ω.Compatible (J x))
    (hJ : ContDiff ℝ n fun x ↦ (J x).toLinearMap.toContinuousLinearMap)
    {Ω : Set E} (hΩ : IsOpen Ω) {u ξ : E → V} {η : E → V →L[ℝ] ℝ}
    (hu : ContinuousOn u Ω) (hξ : ContinuousOn ξ Ω) (hη : ContinuousOn η Ω)
    {z₀ : E} (hz₀ : z₀ ∈ Ω) (hloc : comap u (𝓝 (u z₀)) ⊓ 𝓟 Ω ≤ 𝓝 z₀) (hξ₀ : ξ z₀ ≠ 0)
    (h : ∀ Y : V → V →L[ℝ] V, ContDiff ℝ n Y → HasCompactSupport Y →
      (∀ x, (Y x : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J x)) →
        ∫ z in Ω, η z (Y (u z) (ξ z)) ∂μ = 0) :
    η z₀ = 0 := by
  by_contra hη₀
  obtain ⟨w, hw⟩ : ∃ w, η z₀ w = 1 := by
    obtain ⟨w, hw⟩ := DFunLike.ne_iff.1 hη₀
    exact ⟨(η z₀ w)⁻¹ • w, by simpa using inv_mul_cancel₀ hw⟩
  -- A field of compatible variations whose pairing with `η` at `z₀` is one; the pairing `f`
  -- exceeds `1/2` on a compact neighbourhood `K ⊆ Ω` of `z₀`.
  obtain ⟨B, hBs, hBmem, hB₀⟩ := exists_contDiff_mem_compatibleTangentSpace_apply_eq
    (fun x ↦ (hJc x).invariant) hJ (hJc (u z₀)) hξ₀ w
  set f : E → ℝ := fun z ↦ η z (B (u z) (ξ z))
  have hf : ContinuousOn f Ω := hη.clm_apply ((hBs.continuous.comp_continuousOn hu).clm_apply hξ)
  have hfK : {z | 1 / 2 < f z} ∩ Ω ∈ 𝓝 z₀ :=
    inter_mem ((hf.continuousAt (hΩ.mem_nhds hz₀)).eventually
      (lt_mem_nhds (by norm_num [f, hB₀, hw]))) (hΩ.mem_nhds hz₀)
  obtain ⟨K, hKn, hKsub, hK⟩ := local_compact_nhds hfK
  -- Injectivity confines the points of `Ω` sent near `u z₀` to `K`; cut `B` off there.
  obtain ⟨W, hW, hWK⟩ := mem_comap.1 (mem_inf_principal.1 (hloc hKn))
  obtain ⟨β, hβW, hβc, hβs, hβr, hβ₀⟩ := exists_contDiff_tsupport_subset (n := n) hW
  have hβK {z : E} (hz : z ∈ Ω) (hβz : β (u z) ≠ 0) : z ∈ K :=
    hWK (hβW (subset_tsupport _ hβz)) hz
  have hint := h (fun x ↦ β x • B x) (hβs.smul hBs) hβc.smul_right
    fun x ↦ Submodule.smul_mem _ (β x) (hBmem x)
  -- The integrand `β (u z) * f z` is nonnegative on `Ω`, zero off `K` and positive at `z₀`.
  simp only [_root_.smul_apply, map_smul, smul_eq_mul] at hint
  have hgK : ∀ z ∈ Ω \ K, β (u z) * f z = 0 := fun z hz ↦ by
    rw [not_imp_comm.1 (hβK hz.1) hz.2, zero_mul]
  refine hint.not_gt (ContinuousOn.setIntegral_pos_of_nonneg_ne_zero hΩ
    ((hβs.continuous.comp_continuousOn hu).mul hf) hK (fun z hz ↦ (hKsub hz).2) hgK
    (fun z hz ↦ ?_) hz₀ (by norm_num [f, hβ₀, hB₀, hw]))
  by_cases hzK : z ∈ K
  · exact mul_nonneg (hβr (mem_range_self (u z))).1 ((one_half_pos).trans (hKsub hzK).1).le
  · rw [hgK z ⟨hz, hzK⟩]

end Detection

section FloerOperator

variable {ω : SymplecticForm V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}

/-- **The `J`-direction derivative of the Floer operator.** Along the line `J + q Y` of
endomorphism fields, the coordinate Floer operator has derivative `Y(u)(∂t u - X_Kt)` at every
parameter `q`. The fields may depend on the domain point. -/
theorem hasDerivAt_floerOperator_add_smul (J Y : ℝ × ℝ → V → V →L[ℝ] V) (z : ℝ × ℝ) (q : ℝ) :
    HasDerivAt (fun q : ℝ ↦ ω.floerOperator (fun w x ↦ J w x + q • Y w x) Ks Kt u z)
      (Y z (u z) (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z))) q := by
  set ξ := fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)
  have h (q : ℝ) : ω.floerOperator (fun w x ↦ J w x + q • Y w x) Ks Kt u z =
      ω.floerOperator J Ks Kt u z + q • Y z (u z) ξ := by
    simp only [floerOperator_def, _root_.add_apply, _root_.smul_apply, ξ]
    abel
  simp only [h]
  simpa using
    ((hasDerivAt_id q).smul_const (Y z (u z) ξ)).const_add (ω.floerOperator J Ks Kt u z)

/-- **`J`-variations of the Floer operator detect cokernel elements at injective points.** For a
frozen `Cⁿ` family `J` of `ω`-compatible structures, suppose a continuous covector field `η` on an
open set `Ω ⊆ ℝ × ℝ` annihilates the derivative of the coordinate Floer operator along `J + q Y`
for every compactly supported `Cⁿ` field `Y` of compatible variations. Then `η` vanishes at every
injective point `z₀ ∈ Ω` of `u` where `∂t u - X_Kt` is nonzero. -/
theorem eq_zero_of_integral_apply_deriv_floerOperator_eq_zero {n : ℕ∞}
    {J : V → AlmostComplexStructure V} (hJc : ∀ x, ω.Compatible (J x))
    (hJ : ContDiff ℝ n fun x ↦ (J x).toLinearMap.toContinuousLinearMap)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {η : ℝ × ℝ → V →L[ℝ] ℝ} (hu : ContinuousOn u Ω)
    (hξ : ContinuousOn
      (fun z ↦ fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) Ω)
    (hη : ContinuousOn η Ω) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω)
    (hloc : comap u (𝓝 (u z₀)) ⊓ 𝓟 Ω ≤ 𝓝 z₀)
    (hξ₀ : fderiv ℝ u z₀ stdComplexLineImag - ω.hamiltonianVectorField (Kt z₀) (u z₀) ≠ 0)
    (h : ∀ Y : V → V →L[ℝ] V, ContDiff ℝ n Y → HasCompactSupport Y →
      (∀ x, (Y x : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J x)) →
        ∫ z in Ω, η z (deriv (fun q : ℝ ↦ ω.floerOperator
          (fun _ x ↦ (J x).toLinearMap.toContinuousLinearMap + q • Y x) Ks Kt u z) 0) = 0) :
    η z₀ = 0 :=
  eq_zero_of_integral_apply_compatibleVariation_eq_zero ω hJc hJ hΩ hu hξ hη hz₀ hloc hξ₀
    fun Y hY hYc hYm ↦ by
      simpa only [(hasDerivAt_floerOperator_add_smul _ (fun _ ↦ Y) _ 0).deriv] using
        h Y hY hYc hYm

end FloerOperator

end TauCeti.SymplecticForm
