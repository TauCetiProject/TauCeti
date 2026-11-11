/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex.Variation
public import TauCeti.Geometry.Symplectic.Floer.Linearization

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
coordinates. It does not assert that simple curves have a dense set of injective points, nor any
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
