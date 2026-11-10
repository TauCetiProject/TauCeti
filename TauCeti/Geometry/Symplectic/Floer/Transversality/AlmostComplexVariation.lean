/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex.Variation
public import TauCeti.Geometry.Symplectic.Floer.CovariantLinearization
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Variation

/-!
# `J`-variations of the Floer operator detect cokernel elements at injective points

On a sphere component of a Floer configuration the almost complex structure is frozen: it is a
target structure `J(x)` that does not depend on the domain point. Free Hamiltonian directions
`δK` are not available there, so transversality for such components uses variations `Y` of `J`
alone. Along the line `J + q Y` the coordinate Floer operator `∂s u - X_Ks + J(u)(∂t u - X_Kt)`
has derivative `Y(u)(∂t u - X_Kt)` (`SymplecticForm.hasDerivAt_floerOperator_add_smul`).

The pairing of such terms with a covector field is
`SymplecticForm.eq_zero_of_forall_mem_compatibleTangentSpace_integral_eq_zero`, applied to the
vector field `w = ∂t u - X_Kt`. This file states the result for the Floer operator itself
(`SymplecticForm.eq_zero_of_integral_apply_deriv_floerOperator_eq_zero`): a continuous covector
field annihilating the `J`-direction derivatives of the Floer operator for every compactly
supported variation of compatible structures vanishes at every injective point of `u` where
`∂t u - X_Kt` is nonzero.

This is a statement about one cokernel pairing for a constant symplectic form in local
coordinates.

For a target manifold `M`, the intrinsic Floer operator `SmoothTwoForm.floerOperator` is affine in
its endomorphism field: along `J + q Y` it changes by `q Y(u)(∂t u - X_Kt)`, with all vectors in
the actual tangent fibre at `u z`
(`SmoothTwoForm.floerOperator_add_smul_endomorphism`,
`SmoothTwoForm.hasDerivAt_floerOperator_add_smul_endomorphism`). For a frozen structure
`J : ContMDiffAlmostComplexStructure I n M`, the pairing statement on the manifold
(`ContMDiffAlmostComplexStructure.eq_zero_of_forall_mem_tangentSpace_integral_eq_zero`) gives
`SmoothTwoForm.eq_zero_of_integral_apply_deriv_floerOperator_eq_zero`: a covector field along `u`,
continuous into the cotangent bundle near an injective point of `u` at which `∂t u - X_Kt` is
nonzero, vanishes there once it annihilates the integrable `J`-direction derivatives of the Floer
operator for every compactly supported section `Y` of the endomorphism bundle of `TM`
anticommuting with `J`.
These are the variations of tame almost complex structures; no two-form constrains them, and none
is assumed to be nondegenerate.

Neither statement asserts that simple curves have a dense set of injective points, nor any
Sobolev or Fredholm surjectivity of the universal operator.

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
  {ω : SymplecticForm V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
  {μ : Measure (ℝ × ℝ)} [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]

/-- **`J`-variations of the Floer operator detect cokernel elements at injective points.** Let
`J` be a frozen `Cⁿ` family of complex structures preserving `ω`, tamed by `ω` at `u z₀`.
Suppose a covector field `η` annihilates the derivative of the coordinate Floer operator along
`J + q Y` for every compactly supported `Cⁿ` field `Y` supported in a neighbourhood `W` of
`u z₀`, with `Y x` in the compatible tangent space of `J x`. Then `η` vanishes at every injective
point `z₀` of `u` where `∂t u - X_Kt` is nonzero, provided `u`, `∂t u - X_Kt` and `η` are
continuous near `z₀`. -/
theorem eq_zero_of_integral_apply_deriv_floerOperator_eq_zero {n : ℕ∞}
    {J : V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ n fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap)
    (hJω : ∀ x, ω.Invariant (J x)) {η : ℝ × ℝ → V →L[ℝ] ℝ} {z₀ : ℝ × ℝ}
    (hJ₀ : ω.Tames (J (u z₀))) (hu : ∀ᶠ z in 𝓝 z₀, ContinuousAt u z)
    (hξ : ∀ᶠ z in 𝓝 z₀, ContinuousAt
      (fun z ↦ fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt η z) (hinj : (𝓝 (u z₀)).comap u ≤ 𝓝 z₀)
    (hξ₀ : fderiv ℝ u z₀ stdComplexLineImag - ω.hamiltonianVectorField (Kt z₀) (u z₀) ≠ 0)
    {W : Set V} (hW : W ∈ 𝓝 (u z₀))
    (h : ∀ Y : V → V →L[ℝ] V, ContDiff ℝ n Y → HasCompactSupport Y → tsupport Y ⊆ W →
      (∀ x, (Y x : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J x)) →
        ∫ z, η z (deriv (fun q : ℝ ↦ ω.floerOperator
          (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap + q • Y x) Ks Kt u z)
            0) ∂μ = 0) :
    η z₀ = 0 :=
  eq_zero_of_forall_mem_compatibleTangentSpace_integral_eq_zero (μ := μ) hJ hJω hJ₀ hu hξ hη
    hinj hξ₀ hW fun Y hY hYc hYW hYm ↦ by
      simpa only [(hasDerivAt_floerOperator_add_smul ω _ (fun _ ↦ Y) Ks Kt u _ 0).deriv] using
        h Y hY hYc hYW hYm

end TauCeti.SymplecticForm

namespace TauCeti.SmoothTwoForm

open TauCeti.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The intrinsic Floer operator is affine in its endomorphism field: along `J + q Y` it changes
by `q Y(u)(∂t u - X_Kt)`. No differentiability of the map or of the coefficients is needed. -/
theorem floerOperator_add_smul_endomorphism (ω : SmoothTwoForm I M)
    (J Y : ℝ × ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M) (z : ℝ × ℝ) (q : ℝ) :
    ω.floerOperator (fun p x ↦ J p x + q • Y p x) Ks Kt u z =
      ω.floerOperator J Ks Kt u z + q • Y z (u z)
        (curveVelocity I (fun t ↦ u (z.1, t)) z.2 - ω.hamiltonianVectorField (Kt z) (u z)) := by
  simp only [floerOperator_def, add_apply, map_sub, smul_apply, smul_sub]
  abel

/-- The derivative of the intrinsic Floer operator along the line `J + q Y` of endomorphism
fields is `Y(u)(∂t u - X_Kt)`. The tangent fibre is read in its model normed space `E`, in which
derivatives are unique. -/
theorem hasDerivAt_floerOperator_add_smul_endomorphism (ω : SmoothTwoForm I M)
    (J Y : ℝ × ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M) (z : ℝ × ℝ) (q : ℝ) :
    HasDerivAt (F := E) (fun a : ℝ ↦ ω.floerOperator (fun p x ↦ J p x + a • Y p x) Ks Kt u z)
      (Y z (u z) (curveVelocity I (fun t ↦ u (z.1, t)) z.2 -
        ω.hamiltonianVectorField (Kt z) (u z))) q := by
  -- Name the two vectors in the model space `E`, so that the affine function of `a` is formed
  -- with the normed structure of `E` rather than that of the tangent fibre.
  obtain ⟨c, hc⟩ : ∃ c : E, c = ω.floerOperator J Ks Kt u z := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : E, v = Y z (u z) (curveVelocity I (fun t ↦ u (z.1, t)) z.2 -
      ω.hamiltonianVectorField (Kt z) (u z)) := ⟨_, rfl⟩
  have hf : (fun a : ℝ ↦ ω.floerOperator (fun p x ↦ J p x + a • Y p x) Ks Kt u z) =
      fun a ↦ c + id a • v := by
    funext a
    rw [hc, hv]
    exact floerOperator_add_smul_endomorphism ω J Y Ks Kt u z a
  rw [← hv, hf]
  have h := ((hasDerivAt_id q).smul_const v).const_add c
  simp only [id, one_smul] at h
  exact h

variable [FiniteDimensional ℝ E] [T2Space M]
  {μ : Measure (ℝ × ℝ)} [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]

/-- **`J`-variations of the intrinsic Floer operator detect cokernel elements at injective
points.** Let `J` be a frozen `Cⁿ` almost complex structure on `M`, and let `η` be a covector field
along `u`, continuous into the cotangent bundle near `z₀`, which annihilates the derivative of the
Floer operator along `J + q Y` for every `Cⁿ` section `Y` of the endomorphism bundle of `TM` with
compact support in a neighbourhood `W` of `u z₀` and with `Y x` anticommuting with `J x`, whenever
that pairing is integrable. Then `η` vanishes at every injective point `z₀` of `u` where
`∂t u - X_Kt` is nonzero, provided `∂t u - X_Kt` is continuous into the tangent bundle near
`z₀`. -/
theorem eq_zero_of_integral_apply_deriv_floerOperator_eq_zero {n : ℕ∞}
    (J : ContMDiffAlmostComplexStructure I n M) {ω : SmoothTwoForm I M}
    {Ks Kt : ℝ × ℝ → M → ℝ} {u : ℝ × ℝ → M} {η : ∀ z, TangentSpace I (u z) →L[ℝ] ℝ}
    {z₀ : ℝ × ℝ}
    (hξ : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z,
      curveVelocity I (fun t ↦ u (z.1, t)) z.2 - ω.hamiltonianVectorField (Kt z) (u z)⟩ :
        TangentBundle I M)) z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)) z)
    (hinj : (𝓝 (u z₀)).comap u ≤ 𝓝 z₀)
    (hξ₀ : curveVelocity I (fun t ↦ u (z₀.1, t)) z₀.2 -
      ω.hamiltonianVectorField (Kt z₀) (u z₀) ≠ 0)
    {W : Set M} (hW : W ∈ 𝓝 (u z₀))
    (h : ∀ Y : ContMDiffSection I (E →L[ℝ] E) n
        (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x),
      IsCompact Y.tsupport → Y.tsupport ⊆ W →
      (∀ x, (Y x : Module.End ℝ (TangentSpace I x)) ∈
        (J.almostComplexStructureAt x).tangentSpace) →
      Integrable (fun z ↦ η z (deriv (F := E) (fun q : ℝ ↦
        ω.floerOperator (fun _ x ↦ J.toEndomorphism x + q • Y x) Ks Kt u z) 0)) μ →
      ∫ z, η z (deriv (F := E) (fun q : ℝ ↦
        ω.floerOperator (fun _ x ↦ J.toEndomorphism x + q • Y x) Ks Kt u z) 0) ∂μ = 0) :
    η z₀ = 0 := by
  refine J.eq_zero_of_forall_mem_tangentSpace_integral_eq_zero (μ := μ) hξ hη hinj hξ₀ hW
    fun Y hYc hYW hYJ hi ↦ ?_
  have hd (z : ℝ × ℝ) : deriv (F := E) (fun q : ℝ ↦
      ω.floerOperator (fun _ x ↦ J.toEndomorphism x + q • Y x) Ks Kt u z) 0 =
        Y (u z) (curveVelocity I (fun t ↦ u (z.1, t)) z.2 -
          ω.hamiltonianVectorField (Kt z) (u z)) :=
    (hasDerivAt_floerOperator_add_smul_endomorphism ω
      (fun _ x ↦ J.toEndomorphism x) (fun _ x ↦ Y x) Ks Kt u z 0).deriv
  simpa only [hd] using h Y hYc hYW hYJ (by simpa only [hd] using hi)

end TauCeti.SmoothTwoForm
