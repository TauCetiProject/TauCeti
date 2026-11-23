/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex.Variation
public import TauCeti.Geometry.Symplectic.Floer.CovariantLinearization
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Variation
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

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

The same holds for the intrinsic Floer operator of a map into a manifold with a fiberwise
nondegenerate two-form `σ` preserved by a smooth almost complex structure `J`
(`SmoothTwoForm.IsNondegenerate.eq_zero_of_integral_apply_deriv_floerOperator_eq_zero`). The
variations `Y` are then smooth sections of `End(TM)` in the compatible tangent space of `J`, the
derivative along `J + q Y` is `SmoothTwoForm.hasDerivAt_floerOperator_add_smul`, and the pairing
statement is
`SmoothTwoForm.IsNondegenerate.eq_zero_of_forall_mem_compatibleTangentSpace_integral_eq_zero`.

On a Floer cylinder the almost complex structure `J_t` depends on the time `t`, and transversality
of the cylinders for a generic periodic `J_t` uses variations `Y_t` depending on the time as well.
Such a variation is a function of `(t, u(s, t))`, so it is localized near `(t₀, u(z₀))` and the
relevant points `z₀ = (s₀, t₀)` are the injective points of `(s, t) ↦ (t, u(s, t))`, which need
not be injective points of `u`. In general, let the structure at the domain point `z` be
`J (π z, ·)` for a parameter map `π` from the domain to a finite-dimensional space `P`, and vary it
by fields `Y` on `P × V`. A covector field annihilating the derivatives of the Floer operator along
all such compatible variations supported near `(π z₀, u z₀)` vanishes at every injective point `z₀`
of `z ↦ (π z, u z)` where `∂t u - X_Kt` is nonzero
(`SymplecticForm.eq_zero_of_integral_apply_deriv_floerOperator_parametric_eq_zero`). This is the
pairing statement of `TauCeti.Geometry.Symplectic.AlmostComplex.Variation` for the map
`z ↦ (π z, u z)` into `P × V`. Its two cases are:

* time-dependent structures, `π z = z.2`
  (`SymplecticForm.eq_zero_of_integral_apply_deriv_floerOperator_timeDependent_eq_zero`), with
  variations compactly supported in time and target, and the periodic form
  (`SymplecticForm.eq_zero_of_setIntegral_apply_deriv_floerOperator_periodic_eq_zero`), for
  structures and variations of period one in time and compactly supported in the target, paired
  with `η` over the strip `ℝ × (0, 1)`. The periodic form follows from the compactly supported
  one: a variation supported in `(0, 1) × V` extends to a variation of period one in time
  (`TauCeti.exists_contDiff_periodic_eventuallyEq`) which agrees with it on the strip;
* domain-dependent structures, `π z = z`
  (`SymplecticForm.eq_zero_of_integral_apply_deriv_floerOperator_domainDependent_eq_zero`). Then
  every point is an injective point of `z ↦ (z, u z)`, so the conclusion holds wherever
  `∂t u - X_Kt` is nonzero.

These are statements about one cokernel pairing. They do not assert that simple curves have a
dense set of injective points, nor any Sobolev or Fredholm surjectivity of the universal operator.

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

/-- **Parametrized `J`-variations of the Floer operator detect cokernel elements.** Let
`J (p, x)` be a `Cⁿ` family of complex structures preserving `ω`, depending on a parameter `p` in
a finite-dimensional space `P` as well as on the target point `x`, and tamed by `ω` at
`(π z₀, u z₀)`, and let the Floer operator use the structure `J (π z, ·)` at the domain point `z`,
for a map `π` from the domain to `P`. Suppose a covector field `η` annihilates the derivative of
the Floer operator along `J + q Y` for every compactly supported `Cⁿ` field `Y` on `P × V`
supported in a neighbourhood `W` of `(π z₀, u z₀)`, with `Y (p, x)` in the compatible tangent
space of `J (p, x)`. Then `η` vanishes at every point `z₀` where `∂t u - X_Kt` is nonzero and
which is an injective point of `z ↦ (π z, u z)`, provided `π`, `u`, `∂t u - X_Kt` and `η` are
continuous near `z₀`. -/
theorem eq_zero_of_integral_apply_deriv_floerOperator_parametric_eq_zero {n : ℕ∞}
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {J : P × V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ n fun p ↦ LinearMap.toContinuousLinearMap (J p).toLinearMap)
    (hJω : ∀ p, ω.Invariant (J p)) {π : ℝ × ℝ → P} {η : ℝ × ℝ → V →L[ℝ] ℝ} {z₀ : ℝ × ℝ}
    (hJ₀ : ω.Tames (J (π z₀, u z₀))) (hπ : ∀ᶠ z in 𝓝 z₀, ContinuousAt π z)
    (hu : ∀ᶠ z in 𝓝 z₀, ContinuousAt u z)
    (hξ : ∀ᶠ z in 𝓝 z₀, ContinuousAt
      (fun z ↦ fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt η z)
    (hinj : (𝓝 (π z₀, u z₀)).comap (fun z ↦ (π z, u z)) ≤ 𝓝 z₀)
    (hξ₀ : fderiv ℝ u z₀ stdComplexLineImag - ω.hamiltonianVectorField (Kt z₀) (u z₀) ≠ 0)
    {W : Set (P × V)} (hW : W ∈ 𝓝 (π z₀, u z₀))
    (h : ∀ Y : P × V → V →L[ℝ] V, ContDiff ℝ n Y → HasCompactSupport Y → tsupport Y ⊆ W →
      (∀ p, (Y p : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J p)) →
        ∫ z, η z (deriv (fun q : ℝ ↦ ω.floerOperator
          (fun z x ↦ LinearMap.toContinuousLinearMap (J (π z, x)).toLinearMap + q • Y (π z, x))
            Ks Kt u z) 0) ∂μ = 0) :
    η z₀ = 0 :=
  eq_zero_of_forall_mem_compatibleTangentSpace_integral_eq_zero (μ := μ) hJ hJω hJ₀
    (hπ.and hu |>.mono fun _ h ↦ h.1.prodMk h.2) hξ hη hinj hξ₀ hW fun Y hY hYc hYW hYm ↦ by
      simpa only [(hasDerivAt_floerOperator_add_smul ω _ (fun z x ↦ Y (π z, x)) Ks Kt u _ 0).deriv]
        using h Y hY hYc hYW hYm

/-- **Time-dependent `J`-variations of the Floer operator detect cokernel elements at
slice-injective points.** Let `J (t, x)` be a `Cⁿ` family of complex structures preserving `ω`,
depending on the time `t` as well as on the target point `x`, tamed by `ω` at
`(z₀.2, u z₀)`, and let the Floer operator use the structure `J (t, ·)` at the domain point
`(s, t)`. Suppose a covector field `η` annihilates the derivative of the Floer operator along
`J + q Y` for every compactly supported `Cⁿ` time-dependent field `Y` supported in a
neighbourhood `W` of `(z₀.2, u z₀)`, with `Y (t, x)` in the compatible tangent space of
`J (t, x)`. Then `η` vanishes at every point `z₀` where `∂t u - X_Kt` is nonzero and which is an
injective point of `(s, t) ↦ (t, u(s, t))`, provided `u`, `∂t u - X_Kt` and `η` are continuous
near `z₀`. -/
theorem eq_zero_of_integral_apply_deriv_floerOperator_timeDependent_eq_zero {n : ℕ∞}
    {J : ℝ × V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ n fun p ↦ LinearMap.toContinuousLinearMap (J p).toLinearMap)
    (hJω : ∀ p, ω.Invariant (J p)) {η : ℝ × ℝ → V →L[ℝ] ℝ} {z₀ : ℝ × ℝ}
    (hJ₀ : ω.Tames (J (z₀.2, u z₀))) (hu : ∀ᶠ z in 𝓝 z₀, ContinuousAt u z)
    (hξ : ∀ᶠ z in 𝓝 z₀, ContinuousAt
      (fun z ↦ fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt η z)
    (hinj : (𝓝 (z₀.2, u z₀)).comap (fun z ↦ (z.2, u z)) ≤ 𝓝 z₀)
    (hξ₀ : fderiv ℝ u z₀ stdComplexLineImag - ω.hamiltonianVectorField (Kt z₀) (u z₀) ≠ 0)
    {W : Set (ℝ × V)} (hW : W ∈ 𝓝 (z₀.2, u z₀))
    (h : ∀ Y : ℝ × V → V →L[ℝ] V, ContDiff ℝ n Y → HasCompactSupport Y → tsupport Y ⊆ W →
      (∀ p, (Y p : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J p)) →
        ∫ z, η z (deriv (fun q : ℝ ↦ ω.floerOperator
          (fun z x ↦ LinearMap.toContinuousLinearMap (J (z.2, x)).toLinearMap + q • Y (z.2, x))
            Ks Kt u z) 0) ∂μ = 0) :
    η z₀ = 0 :=
  eq_zero_of_integral_apply_deriv_floerOperator_parametric_eq_zero (μ := μ) hJ hJω hJ₀
    (Eventually.of_forall fun _ ↦ continuousAt_snd) hu hξ hη hinj hξ₀ hW h

/-- **Domain-dependent `J`-variations of the Floer operator detect cokernel elements.** Let
`J (z, x)` be a `Cⁿ` family of complex structures preserving `ω`, depending on the domain point
`z` as well as on the target point `x`, tamed by `ω` at `(z₀, u z₀)`. Suppose a covector field
`η` annihilates the derivative of the Floer operator along `J + q Y` for every compactly supported
`Cⁿ` domain-dependent field `Y` supported in a neighbourhood `W` of `(z₀, u z₀)`, with `Y (z, x)`
in the compatible tangent space of `J (z, x)`. Then `η` vanishes at every point `z₀` where
`∂t u - X_Kt` is nonzero, provided `u`, `∂t u - X_Kt` and `η` are continuous near `z₀`. Since
such variations can be localized in the domain, no injectivity of `u` is needed. -/
theorem eq_zero_of_integral_apply_deriv_floerOperator_domainDependent_eq_zero {n : ℕ∞}
    {J : (ℝ × ℝ) × V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ n fun p ↦ LinearMap.toContinuousLinearMap (J p).toLinearMap)
    (hJω : ∀ p, ω.Invariant (J p)) {η : ℝ × ℝ → V →L[ℝ] ℝ} {z₀ : ℝ × ℝ}
    (hJ₀ : ω.Tames (J (z₀, u z₀))) (hu : ∀ᶠ z in 𝓝 z₀, ContinuousAt u z)
    (hξ : ∀ᶠ z in 𝓝 z₀, ContinuousAt
      (fun z ↦ fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt η z)
    (hξ₀ : fderiv ℝ u z₀ stdComplexLineImag - ω.hamiltonianVectorField (Kt z₀) (u z₀) ≠ 0)
    {W : Set ((ℝ × ℝ) × V)} (hW : W ∈ 𝓝 (z₀, u z₀))
    (h : ∀ Y : (ℝ × ℝ) × V → V →L[ℝ] V, ContDiff ℝ n Y → HasCompactSupport Y → tsupport Y ⊆ W →
      (∀ p, (Y p : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J p)) →
        ∫ z, η z (deriv (fun q : ℝ ↦ ω.floerOperator
          (fun z x ↦ LinearMap.toContinuousLinearMap (J (z, x)).toLinearMap + q • Y (z, x))
            Ks Kt u z) 0) ∂μ = 0) :
    η z₀ = 0 :=
  eq_zero_of_integral_apply_deriv_floerOperator_parametric_eq_zero (μ := μ) (π := id) hJ hJω hJ₀
    (Eventually.of_forall fun _ ↦ continuousAt_id) hu hξ hη
    (by
      rw [nhds_prod_eq, comap_prod]
      exact inf_le_left.trans_eq comap_id) hξ₀ hW h

/-- **Periodic time-dependent `J`-variations of the Floer operator detect cokernel elements at
slice-injective points.** Let `J (t, x)` be a `Cⁿ` family of complex structures preserving `ω`, of
period one in the time `t`, tamed by `ω` at `(z₀.2, u z₀)`, and let the Floer operator use the
structure `J (t, ·)` at the domain point `(s, t)`. Suppose a covector field `η` annihilates, over
the strip `ℝ × (0, 1)`, the derivative of the Floer operator along `J + q Y` for every `Cⁿ` field
`Y` of period one in time which vanishes for `x` outside a compact set, with `Y (t, x)` in the
compatible tangent space of `J (t, x)`. Then `η` vanishes at every point `z₀` of the strip where
`∂t u - X_Kt` is nonzero and which is an injective point of `(s, t) ↦ (t, u(s, t))`, provided `u`,
`∂t u - X_Kt` and `η` are continuous near `z₀`. -/
theorem eq_zero_of_setIntegral_apply_deriv_floerOperator_periodic_eq_zero {n : ℕ∞}
    {J : ℝ × V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ n fun p ↦ LinearMap.toContinuousLinearMap (J p).toLinearMap)
    (hJω : ∀ p, ω.Invariant (J p)) (hJper : ∀ t x, J (t + 1, x) = J (t, x))
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {z₀ : ℝ × ℝ} (hz₀ : z₀.2 ∈ Ioo 0 1)
    (hJ₀ : ω.Tames (J (z₀.2, u z₀))) (hu : ∀ᶠ z in 𝓝 z₀, ContinuousAt u z)
    (hξ : ∀ᶠ z in 𝓝 z₀, ContinuousAt
      (fun z ↦ fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt η z)
    (hinj : (𝓝 (z₀.2, u z₀)).comap (fun z ↦ (z.2, u z)) ≤ 𝓝 z₀)
    (hξ₀ : fderiv ℝ u z₀ stdComplexLineImag - ω.hamiltonianVectorField (Kt z₀) (u z₀) ≠ 0)
    (h : ∀ Y : ℝ × V → V →L[ℝ] V, ContDiff ℝ n Y → (∀ t x, Y (t + 1, x) = Y (t, x)) →
      (∀ᶠ p in comap Prod.snd (cocompact V), Y p = 0) →
      (∀ p, (Y p : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J p)) →
        ∫ z in univ ×ˢ Ioo 0 1, η z (deriv (fun q : ℝ ↦ ω.floerOperator
          (fun z x ↦ LinearMap.toContinuousLinearMap (J (z.2, x)).toLinearMap + q • Y (z.2, x))
            Ks Kt u z) 0) ∂μ = 0) :
    η z₀ = 0 := by
  refine eq_zero_of_integral_apply_deriv_floerOperator_timeDependent_eq_zero (μ := μ) (Ks := Ks)
    hJ hJω hJ₀ hu hξ hη hinj hξ₀ (prod_mem_nhds (Ioo_mem_nhds hz₀.1 hz₀.2) univ_mem)
    fun Y₀ hY₀ hY₀c hY₀W hY₀J ↦ ?_
  -- Extend `Y₀`, which is supported in the strip `(0, 1) × V`, to a field `Y` of period one in
  -- time. The periodization is stated with time as the last coordinate, hence the swaps.
  -- `Prod.swap p` is `(p.2, p.1)` by definition, which gives its smoothness below.
  have hswap : ContDiff ℝ n (Prod.swap : V × ℝ → ℝ × V) := contDiff_snd.prodMk contDiff_fst
  have hcomm : ⇑(Homeomorph.prodComm V ℝ) = Prod.swap := Homeomorph.coe_prodComm V ℝ
  obtain ⟨g, hg, hgper, hgK, hgeq⟩ := exists_contDiff_periodic_eventuallyEq
    (f := Y₀ ∘ Prod.swap) (hY₀.comp hswap) (hcomm ▸ hY₀c.comp_homeomorph _) (by
      rw [← hcomm, tsupport_comp_eq_preimage, hcomm]
      exact fun q hq ↦ ⟨mem_univ _, (hY₀W hq).1⟩)
  set Y : ℝ × V → V →L[ℝ] V := fun p ↦ g p.swap
  have hYc : Continuous Y := hg.continuous.comp continuous_swap
  have hYK : ∀ᶠ p in comap Prod.snd (cocompact V), Y p = 0 := by
    simpa only [comap_comap, Function.comp_def, Prod.fst_swap] using hgK.comap Prod.swap
  -- `Y = Y₀` on the open strip, hence on its closure `[0, 1] × V`.
  have hYeq : EqOn Y Y₀ (Icc 0 1 ×ˢ univ) := by
    refine EqOn.of_subset_closure (s := Ioo 0 1 ×ˢ univ)
      (fun p hp ↦ (hgeq p.swap ⟨mem_univ _, hp.1⟩).eq_of_nhds.trans (congrArg Y₀ p.swap_swap))
      hYc.continuousOn hY₀.continuous.continuousOn (prod_mono Ioo_subset_Icc_self subset_rfl) ?_
    rw [closure_prod_eq, closure_Ioo zero_ne_one, closure_univ]
  -- Both `Y` and `J` are periodic, so tangency reduces to the fundamental domain `[0, 1)`.
  have hYJ (p : ℝ × V) : (Y p : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J p) := by
    obtain ⟨t, x⟩ := p
    have hJt := (show Function.Periodic (fun t ↦ J (t, x)) 1 from
      fun t ↦ hJper t x).sub_int_mul_eq (x := t) ⌊t⌋
    have hYt := (show Function.Periodic (fun t ↦ Y (t, x)) 1 from
      fun t ↦ hgper x t).sub_int_mul_eq (x := t) ⌊t⌋
    simp only [mul_one, Int.self_sub_floor] at hJt hYt
    rw [← hJt, ← hYt, hYeq ⟨⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, mem_univ x⟩]
    exact hY₀J _
  have hint := h Y (hg.comp (contDiff_snd.prodMk contDiff_fst)) (fun t x ↦ hgper x t) hYK hYJ
  simp only [(hasDerivAt_floerOperator_add_smul ω _ (fun z x ↦ Y (z.2, x)) Ks Kt u _ 0).deriv]
    at hint
  simp only [(hasDerivAt_floerOperator_add_smul ω _ (fun z x ↦ Y₀ (z.2, x)) Ks Kt u _ 0).deriv]
  -- The integrand of `Y₀` vanishes off the strip and agrees there with that of `Y`.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := univ ×ˢ Ioo 0 1) fun z hz ↦ by
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ hz ⟨mem_univ _, (hY₀W h).1⟩,
      zero_apply, map_zero]]
  refine (setIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ioo) fun z hz ↦ ?_).trans
    hint
  simp only [hYeq (show (z.2, u z) ∈ Icc 0 1 ×ˢ univ from
    ⟨Ioo_subset_Icc_self hz.2, mem_univ _⟩)]

end TauCeti.SymplecticForm

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M} {Ks Kt : ℝ × ℝ → M → ℝ}
  {u : ℝ × ℝ → M} {η : ∀ z, TangentSpace I (u z) →L[ℝ] ℝ}
  {μ : Measure (ℝ × ℝ)} [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]

/-- **`J`-variations of the intrinsic Floer operator detect cokernel elements at injective
points.** Let `σ` be fiberwise nondegenerate and preserved by the frozen smooth structure `J`,
tame at `u z₀`. Suppose a covector field `η` along `u` annihilates the derivative of the Floer
operator along `J + q Y` for every smooth section `Y` of `End(TM)` with compact support in a
neighbourhood `W` of `u z₀`, with `Y x` in the compatible tangent space of `J x`. Then `η`
vanishes at every injective point `z₀` of `u` where `∂t u - X_Kt` is nonzero, provided
`∂t u - X_Kt` and `η` are continuous near `z₀` as maps into the tangent and cotangent bundles. -/
theorem IsNondegenerate.eq_zero_of_integral_apply_deriv_floerOperator_eq_zero
    (hσ : σ.IsNondegenerate) (hJ : σ.Invariant J) {z₀ : ℝ × ℝ}
    (hJ₀ : (hσ.symplecticFormAt (u z₀)).Tames (J.almostComplexStructureAt (u z₀)))
    (hξ : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, Manifold.curveVelocity I (fun t ↦ u (z.1, t))
      z.2 - σ.hamiltonianVectorField (Kt z) (u z)⟩ : TangentBundle I M)) z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)) z)
    (hinj : (𝓝 (u z₀)).comap u ≤ 𝓝 z₀)
    (hξ₀ : Manifold.curveVelocity I (fun t ↦ u (z₀.1, t)) z₀.2 -
      σ.hamiltonianVectorField (Kt z₀) (u z₀) ≠ 0)
    {W : Set M} (hW : W ∈ 𝓝 (u z₀))
    (h : ∀ Y : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯,
      IsCompact Y.tsupport → Y.tsupport ⊆ W →
      (∀ x, (Y x : Module.End ℝ (TangentSpace I x)) ∈
        (hσ.symplecticFormAt x).compatibleTangentSpace (J.almostComplexStructureAt x)) →
      ∫ z, η z (deriv (fun q : ℝ ↦ (σ.floerOperator
        (fun _ x ↦ J.toEndomorphism x + q • Y x) Ks Kt u z : E)) 0) ∂μ = 0) :
    η z₀ = 0 :=
  hσ.eq_zero_of_forall_mem_compatibleTangentSpace_integral_eq_zero (μ := μ) hJ hJ₀ hξ hη hinj
    hξ₀ hW fun Y hYc hYW hYJ ↦ by
      have hd (z : ℝ × ℝ) : deriv (fun q : ℝ ↦ (σ.floerOperator
          (fun _ x ↦ J.toEndomorphism x + q • Y x) Ks Kt u z : E)) 0 =
            (Y (u z) (Manifold.curveVelocity I (fun t ↦ u (z.1, t)) z.2 -
              σ.hamiltonianVectorField (Kt z) (u z)) : E) :=
        HasDerivAt.deriv (F := E) (hasDerivAt_floerOperator_add_smul σ
          (fun _ x ↦ J.toEndomorphism x) (fun _ x ↦ Y x) Ks Kt u z 0)
      simpa only [hd] using h Y hYc hYW hYJ

end TauCeti.SmoothTwoForm
