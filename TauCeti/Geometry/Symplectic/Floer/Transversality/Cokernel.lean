/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Perturbation.Basic
public import TauCeti.Geometry.Symplectic.Floer.Transversality.AlmostComplexVariation
public import TauCeti.Geometry.Symplectic.Floer.Transversality.RegularPoint
public import TauCeti.Geometry.Symplectic.Floer.UniqueContinuation

/-!
# Cokernel elements of the universal linearized Floer operator vanish

Let `u : ℝ × ℝ → V` be a `C¹` map into a finite-dimensional symplectic vector space, on a
connected open set `Ω` of the domain, and let `D_u` be the linearized Floer operator at `u`
(`TauCeti.SymplecticForm.floerLinearization`). The universal linearized operator adds to `D_u`
the directions in which the Floer operator moves when the perturbation data vary. A cokernel
element of the universal operator is a covector field `η` along `u` annihilating, for the
pairing `∫ η(·) ds dt`, both the range of `D_u` and these extra directions. Transversality of
Floer moduli spaces is the statement that only `η = 0` does so. This file proves it for `C¹`
covector fields, for each of three kinds of variation.

* **Hamiltonian variations on a core.** If `η` annihilates `D_u ξ` for every smooth test map `ξ`
  compactly supported in `Ω`, and annihilates the change of the Floer operator under every
  smooth Hamiltonian variation `δK` of the `ds` component supported near the graph of `u` over a
  nonempty open subset `U ⊆ Ω`, then `η = 0` on `Ω`
  (`SymplecticForm.eqOn_zero_of_integral_floerLinearization_of_integral_floerOperator_add_sub`).
  There is no hypothesis on `u` over `U`: in particular `u` may be constant there. This is the
  argument for an inhomogeneous core of a punctured domain, where the Hamiltonian perturbation
  is free.
* **Variations of a frozen almost complex structure.** If `J` does not depend on the domain
  point, `η` annihilates the range of `D_u` on `Ω`, and every point `z₀` of a nonempty open
  subset `U ⊆ Ω` is an injective point of `u` with `∂ₜu - X_{K_t} ≠ 0` at which `η` annihilates
  the derivative of the Floer operator along every compatible variation of `J` supported near
  `u z₀`, then `η = 0` on `Ω`
  (`SymplecticForm.eqOn_zero_of_integral_floerLinearization_of_integral_deriv_floerOperator`).
  This is the argument for a component on which the almost complex structure is frozen, such as
  a sphere bubble, where only variations of `J` are available.
* **Periodic variations of `J_t` along a Floer trajectory.** Let `u` be a nonstationary `C²`
  solution of `∂ₛu + J_t(u)(∂ₜu - X_{H_t}(u)) = 0` on `ℝ × ℝ`, for a family `J_t` of period one in
  time, with limits `xm` and `xp` along its ends. If `η` annihilates the range of `D_u` and, over
  the strip `ℝ × (0, 1)`, the derivative of the Floer operator along every compatible variation
  `Y_t` of `J_t` of period one in time, then `η = 0`
  (`SymplecticForm.eq_zero_of_integral_floerLinearization_of_setIntegral_deriv_floerOperator`).
  This is the argument of Floer, Hofer and Salamon for generic periodic `J_t`, where a
  variation of `J_t` near `(t, u(s, t))` is felt by the trajectory away from `(s, t)` unless
  `(s, t)` is an injective point of `(s, t) ↦ (t, u(s, t))`. The regular points of `u`
  (`TauCeti.Floer.regularPoints`) are such injective points
  (`TauCeti.comap_nhds_le_nhds_of_forall_slice_eq_imp_eq`), with
  `∂ₜu - X_{H_t} = J_t ∂ₛu ≠ 0`, and they are dense (`TauCeti.Floer.dense_regularPoints`), so `η`
  vanishes on the strip.

In each case the first hypothesis says that `η` solves the adjoint equation `D_u^* η = 0` on `Ω`
(`TauCeti.SymplecticForm.forall_integral_apply_floerLinearization_eq_zero_iff`), the second that
`η` vanishes on a nonempty open set `U`
(`TauCeti.SymplecticForm.eqOn_zero_of_forall_integral_apply_floerOperator_add_sub_eq_zero`,
`TauCeti.SymplecticForm.eq_zero_of_integral_apply_deriv_floerOperator_eq_zero`,
`TauCeti.SymplecticForm.eq_zero_of_setIntegral_apply_deriv_floerOperator_periodic_eq_zero`), and
unique
continuation for the adjoint equation
(`TauCeti.SymplecticForm.eqOn_zero_of_floerLinearizationAdjoint_eq_zero_of_eqOn_zero`) spreads the
vanishing over `Ω`.

These are statements about classical (`C¹`) cokernel elements. Weak (`Lᵖ`) cokernel elements of a
Sobolev realization of `D_u` are regular, and vanish under the same variations, by
`TauCeti.Geometry.Symplectic.Floer.Transversality.WeakCokernel`; the surjectivity of the universal
operator on Banach spaces that follows is not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1 and Section 8.1.
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292.
-/

public section

open Function Filter MeasureTheory Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {η : ℝ × ℝ → V →L[ℝ] ℝ}
  {Ω U : Set (ℝ × ℝ)}

/-- **Hamiltonian variations on a core kill the cokernel of the universal operator.** Let `J` be
`C¹` and the Hamiltonians `K_s`, `K_t` be `C²` near the graph of a `C¹` map `u` over a connected
open set `Ω`, with `J(z, u z)² = -1` on `Ω`. Let `η` be a `C¹` covector field on `Ω` annihilating
`D_u ξ` for every smooth test map `ξ` compactly supported in `Ω`, and annihilating the change of
the Floer operator under every smooth compactly supported variation `δK` of `K_s` supported in a
neighbourhood `W` of the graph of `u` over a nonempty open set `U ⊆ Ω`. Then `η = 0` on `Ω`. -/
theorem eqOn_zero_of_integral_floerLinearization_of_integral_floerOperator_add_sub
    {J : ℝ × ℝ → V → V →L[ℝ] V} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hη : ContDiffOn ℝ 1 η Ω)
    (hD : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ → tsupport ξ ⊆ Ω →
      ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) = 0)
    (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) {W : Set ((ℝ × ℝ) × V)}
    (hW : ∀ z ∈ U, W ∈ 𝓝 (z, u z))
    (hK : ∀ δK : ℝ × ℝ → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (uncurry δK) →
      HasCompactSupport (uncurry δK) → tsupport (uncurry δK) ⊆ W →
        ∫ z, η z (ω.floerOperator J (fun w y ↦ Ks w y + δK w y) Kt u z -
          ω.floerOperator J Ks Kt u z) = 0) :
    EqOn η 0 Ω := by
  have hD' := (forall_integral_apply_floerLinearization_eq_zero_iff hΩ hJ hKs hKt
    (fun z hz ↦ hu.contDiffAt (hΩ.mem_nhds hz)) fun z hz ↦ hη.contDiffAt (hΩ.mem_nhds hz)).1 hD
  have hKsd (z : ℝ × ℝ) (hz : z ∈ U) : DifferentiableAt ℝ (Ks z) (u z) :=
    ((hKs z (hUΩ hz)).differentiableAt two_ne_zero).comp (u z)
      ((differentiableAt_const z).prodMk differentiableAt_id)
  exact eqOn_zero_of_floerLinearizationAdjoint_eq_zero_of_eqOn_zero hΩ hΩc hJ hJJ hKs hKt hu hη
    hD' hU hUne hUΩ <| eqOn_zero_of_forall_integral_apply_floerOperator_add_sub_eq_zero
      (μ := volume) ω J Ks Kt u hU (hu.continuousOn.mono hUΩ) hKsd hW (hη.continuousOn.mono hUΩ) hK

/-- **Variations of a frozen almost complex structure kill the cokernel of the universal
operator.** Let `J` be a `Cⁿ` family of complex structures preserving `ω`, with `1 ≤ n`, frozen in
the sense that it does not depend on the domain point, and let the Hamiltonians `K_s`, `K_t` be `C²`
near the graph of a `C¹` map `u` over a connected open set `Ω`. Let `η` be a `C¹` covector field on
`Ω` annihilating `D_u ξ` for every smooth test map `ξ` compactly supported in `Ω`. Suppose that on
a nonempty open set `U ⊆ Ω`, every point `z` is an injective point of `u`, with `J` tamed by `ω`
at `u z` and `∂ₜu - X_{K_t} ≠ 0` at `z`, and that `η` annihilates the derivative of the Floer
operator along `J + q Y` for every compactly supported `Cⁿ` field `Y` of compatible variations
of `J` supported in a neighbourhood `W` of `u(U)`. Then `η = 0` on `Ω`. -/
theorem eqOn_zero_of_integral_floerLinearization_of_integral_deriv_floerOperator {n : ℕ∞}
    {J : V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ n fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) (hn : 1 ≤ n)
    (hJω : ∀ x, ω.Invariant (J x)) (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hη : ContDiffOn ℝ 1 η Ω)
    (hD : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ → tsupport ξ ⊆ Ω →
      ∫ z, η z (ω.floerLinearization (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap)
        Ks Kt u ξ z) = 0)
    (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (hJ₀ : ∀ z ∈ U, ω.Tames (J (u z)))
    (hinj : ∀ z ∈ U, (𝓝 (u z)).comap u ≤ 𝓝 z)
    (hξ₀ : ∀ z ∈ U, fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z) ≠ 0)
    {W : Set V} (hW : ∀ z ∈ U, W ∈ 𝓝 (u z))
    (hY : ∀ Y : V → V →L[ℝ] V, ContDiff ℝ n Y → HasCompactSupport Y → tsupport Y ⊆ W →
      (∀ x, (Y x : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J x)) →
        ∫ z, η z (deriv (fun q : ℝ ↦ ω.floerOperator
          (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap + q • Y x) Ks Kt u z)
            0) = 0) :
    EqOn η 0 Ω := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap
  have hJ' (z : ℝ × ℝ) : ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J' p.1 p.2) (z, u z) :=
    ((hJ.of_le (mod_cast hn)).comp contDiff_snd).contDiffAt
  have hJJ (z : ℝ × ℝ) : J' z (u z) ∘L J' z (u z) = -ContinuousLinearMap.id ℝ V := by
    ext v
    simp [J']
  have huΩ (z : ℝ × ℝ) (hz : z ∈ Ω) : ContDiffAt ℝ 1 u z := hu.contDiffAt (hΩ.mem_nhds hz)
  have hD' := (forall_integral_apply_floerLinearization_eq_zero_iff hΩ (fun z _ ↦ hJ' z) hKs hKt
    huΩ fun z hz ↦ hη.contDiffAt (hΩ.mem_nhds hz)).1 hD
  refine eqOn_zero_of_floerLinearizationAdjoint_eq_zero_of_eqOn_zero hΩ hΩc (fun z _ ↦ hJ' z)
    (fun z _ ↦ hJJ z) hKs hKt hu hη hD' hU hUne hUΩ fun z₀ hz₀ ↦ ?_
  -- At each point of `U`, the detection lemma applies: near `z₀ ∈ Ω`, the map `u`, the field
  -- `∂ₜu - X_{K_t}` and `η` are continuous.
  have hev : ∀ᶠ z in 𝓝 z₀, z ∈ Ω := hΩ.mem_nhds (hUΩ hz₀)
  have hξ : ∀ᶠ z in 𝓝 z₀, ContinuousAt
      (fun z ↦ fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) z := by
    filter_upwards [hev] with z hz
    have hX := (ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) (hKt z hz)).continuousAt.comp
      (x := z) (continuousAt_id.prodMk (huΩ z hz).continuousAt)
    exact (((huΩ z hz).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const).sub hX
  exact eq_zero_of_integral_apply_deriv_floerOperator_eq_zero (μ := volume) hJ hJω (hJ₀ z₀ hz₀)
    (hev.mono fun z hz ↦ (huΩ z hz).continuousAt) hξ
    (hev.mono fun z hz ↦ (hη.contDiffAt (hΩ.mem_nhds hz)).continuousAt) (hinj z₀ hz₀)
    (hξ₀ z₀ hz₀) (hW z₀ hz₀) hY

/-- At a regular point `z` of a Floer trajectory `u` in the strip `ℝ × (0, 1)`, periodic
variations of `J_t` detect cokernel elements: `z` is an injective point of
`(s, t) ↦ (t, u(s, t))`, and `∂ₜu - X_{H_t} = J_t ∂ₛu` does not vanish there. -/
private theorem eq_zero_of_mem_regularPoints_of_setIntegral_deriv_floerOperator {n : ℕ∞}
    {J : ℝ × V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ n fun p ↦ LinearMap.toContinuousLinearMap (J p).toLinearMap)
    (hJω : ∀ p, ω.Invariant (J p)) (hJper : ∀ t x, J (t + 1, x) = J (t, x))
    {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (uncurry H)) (hu : ContDiff ℝ 1 u) {z : ℝ × ℝ}
    (hF : ω.floerOperator
      (fun z x ↦ LinearMap.toContinuousLinearMap (J (z.2, x)).toLinearMap) (fun _ _ ↦ 0)
        (fun z ↦ H z.2) u z = 0)
    {xm xp : ℝ → V} (hm : Tendsto u (atBot ×ˢ 𝓝 z.2) (𝓝 (xm z.2)))
    (hp : Tendsto u (atTop ×ˢ 𝓝 z.2) (𝓝 (xp z.2))) (hη : Continuous η)
    (hY : ∀ Y : ℝ × V → V →L[ℝ] V, ContDiff ℝ n Y → (∀ t x, Y (t + 1, x) = Y (t, x)) →
      (∀ᶠ p in comap Prod.snd (cocompact V), Y p = 0) →
      (∀ p, (Y p : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J p)) →
        ∫ z in univ ×ˢ Ioo 0 1, η z (deriv (fun q : ℝ ↦ ω.floerOperator
          (fun z x ↦ LinearMap.toContinuousLinearMap (J (z.2, x)).toLinearMap + q • Y (z.2, x))
            (fun _ _ ↦ 0) (fun z ↦ H z.2) u z) 0) = 0)
    (hzS : z.2 ∈ Ioo 0 1) (hJ₀ : ω.Tames (J (z.2, u z)))
    (hz : z ∈ Floer.regularPoints u xm xp) :
    η z = 0 := by
  obtain ⟨hd, hzm, hzp, hzs⟩ := Floer.mem_regularPoints.1 hz
  -- By the Floer equation, `∂ₛu = -J_t (∂ₜu - X_{H_t})`, which is nonzero at `z`.
  have hξ₀ : fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (u z) ≠ 0 := by
    intro h
    exact hd (by simpa [floerOperator_def, h] using hF)
  have hξ : ∀ᶠ w in 𝓝 z, ContinuousAt
      (fun w ↦ fderiv ℝ u w stdComplexLineImag - ω.hamiltonianVectorField (H w.2) (u w)) w :=
    Eventually.of_forall fun w ↦ by
      have hKt : ContDiffAt ℝ 2 (uncurry fun w : ℝ × ℝ ↦ H w.2) (w, u w) :=
        (hH.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)).contDiffAt
      have hX := (ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) hKt).continuousAt.comp
        (x := w) (continuousAt_id.prodMk hu.continuous.continuousAt)
      exact ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousAt.sub hX
  exact eq_zero_of_setIntegral_apply_deriv_floerOperator_periodic_eq_zero (μ := volume)
    (Ks := fun _ _ ↦ 0) hJ hJω hJper hzS hJ₀
    (Eventually.of_forall fun _ ↦ hu.continuous.continuousAt) hξ
    (Eventually.of_forall fun _ ↦ hη.continuousAt)
    (comap_nhds_le_nhds_of_forall_slice_eq_imp_eq hu.continuous hm hp hzm hzp hzs) hξ₀ hY

/-- **Periodic variations of `J_t` kill the cokernel of the universal operator along a Floer
trajectory** (Floer, Hofer and Salamon). Let `J (t, x)` be a `Cⁿ` family of complex structures
preserving `ω`, with `1 ≤ n`, of period one in the time `t` and tamed by `ω` along `u`, and let
`u` be a nonstationary `C²` solution of the Floer equation `∂ₛu + J_t(u)(∂ₜu - X_{H_t}(u)) = 0`
for a `C²` Hamiltonian `H`. Suppose that `u(s, t)` tends to `xm(t₀)` and `xp(t₀)`, for continuous
loops `xm` and `xp`, as `s → -∞` and `s → +∞` and `t → t₀`. Let `η` be a `C¹` covector field
annihilating `D_u ξ` for every smooth compactly supported test map `ξ`, and annihilating, over the
strip `ℝ × (0, 1)`, the derivative of the Floer operator along `J + q Y` for every `Cⁿ` field `Y`
of period one in time, vanishing for `x` outside a compact set, with `Y (t, x)` in the compatible
tangent space of `J (t, x)`. Then `η = 0`. -/
theorem eq_zero_of_integral_floerLinearization_of_setIntegral_deriv_floerOperator {n : ℕ∞}
    {J : ℝ × V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ n fun p ↦ LinearMap.toContinuousLinearMap (J p).toLinearMap) (hn : 1 ≤ n)
    (hJω : ∀ p, ω.Invariant (J p)) (hJper : ∀ t x, J (t + 1, x) = J (t, x))
    (hJ₀ : ∀ z, ω.Tames (J (z.2, u z))) {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (uncurry H))
    (hu : ContDiff ℝ 2 u)
    (hF : ∀ z, ω.floerOperator
      (fun z x ↦ LinearMap.toContinuousLinearMap (J (z.2, x)).toLinearMap) (fun _ _ ↦ 0)
        (fun z ↦ H z.2) u z = 0)
    (hne : ∃ z, fderiv ℝ u z stdComplexLineReal ≠ 0) {xm xp : ℝ → V} (hxm : Continuous xm)
    (hxp : Continuous xp) (hm : ∀ t, Tendsto u (atBot ×ˢ 𝓝 t) (𝓝 (xm t)))
    (hp : ∀ t, Tendsto u (atTop ×ˢ 𝓝 t) (𝓝 (xp t))) (hη : ContDiff ℝ 1 η)
    (hD : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ →
      ∫ z, η z (ω.floerLinearization
        (fun z x ↦ LinearMap.toContinuousLinearMap (J (z.2, x)).toLinearMap) (fun _ _ ↦ 0)
          (fun z ↦ H z.2) u ξ z) = 0)
    (hY : ∀ Y : ℝ × V → V →L[ℝ] V, ContDiff ℝ n Y → (∀ t x, Y (t + 1, x) = Y (t, x)) →
      (∀ᶠ p in comap Prod.snd (cocompact V), Y p = 0) →
      (∀ p, (Y p : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J p)) →
        ∫ z in univ ×ˢ Ioo 0 1, η z (deriv (fun q : ℝ ↦ ω.floerOperator
          (fun z x ↦ LinearMap.toContinuousLinearMap (J (z.2, x)).toLinearMap + q • Y (z.2, x))
            (fun _ _ ↦ 0) (fun z ↦ H z.2) u z) 0) = 0) :
    η = 0 := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V :=
    fun z x ↦ LinearMap.toContinuousLinearMap (J (z.2, x)).toLinearMap
  have hJ1 : ContDiff ℝ 1 fun p ↦ LinearMap.toContinuousLinearMap (J p).toLinearMap :=
    hJ.of_le (mod_cast hn)
  have hJ' (z : ℝ × ℝ) : ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J' p.1 p.2) (z, u z) :=
    (hJ1.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)).contDiffAt
  have hJJ (z : ℝ × ℝ) : J' z (u z) ∘L J' z (u z) = -ContinuousLinearMap.id ℝ V := by
    ext v
    simp [J']
  have hKs (z : ℝ × ℝ) :
      ContDiffAt ℝ 2 (uncurry fun (_ : ℝ × ℝ) (_ : V) ↦ (0 : ℝ)) (z, u z) :=
    contDiff_const.contDiffAt
  have hKt (z : ℝ × ℝ) : ContDiffAt ℝ 2 (uncurry fun z : ℝ × ℝ ↦ H z.2) (z, u z) :=
    (hH.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)).contDiffAt
  have hu1 : ContDiff ℝ 1 u := hu.of_le one_le_two
  have hD' := (forall_integral_apply_floerLinearization_eq_zero_iff isOpen_univ
    (fun z _ ↦ hJ' z) (fun z _ ↦ hKs z) (fun z _ ↦ hKt z) (fun _ _ ↦ hu1.contDiffAt)
    fun _ _ ↦ hη.contDiffAt).1 fun ξ hξ hξc _ ↦ hD ξ hξ hξc
  -- `η` vanishes at the regular points of `u` in the strip `S = ℝ × (0, 1)`.
  set S : Set (ℝ × ℝ) := univ ×ˢ Ioo 0 1
  have hS : IsOpen S := isOpen_univ.prod isOpen_Ioo
  have hreg : EqOn η 0 (S ∩ Floer.regularPoints u xm xp) := fun z hz ↦
    eq_zero_of_mem_regularPoints_of_setIntegral_deriv_floerOperator hJ hJω hJper hH hu1 (hF z)
      (hm z.2) (hp z.2) hη.continuous hY hz.1.2 (hJ₀ z) hz.2
  -- The regular points are dense, so `η` vanishes on the strip, and by unique continuation for
  -- the adjoint equation everywhere.
  have hdense := Floer.dense_regularPoints (J := fun t x ↦
      LinearMap.toContinuousLinearMap (J (t, x)).toLinearMap) hJ1 (fun z ↦ hJJ z) hH hu hF hne
    hxm hxp (fun t ↦ (hm t).comp (tendsto_id.prodMk tendsto_const_nhds))
    (fun t ↦ (hp t).comp (tendsto_id.prodMk tendsto_const_nhds))
  have hSη : EqOn η 0 S := fun z hz ↦
    hreg.closure hη.continuous continuous_const (hdense.open_subset_closure_inter hS hz)
  funext z
  exact eqOn_zero_of_floerLinearizationAdjoint_eq_zero_of_eqOn_zero isOpen_univ isPreconnected_univ
    (fun z _ ↦ hJ' z) (fun z _ ↦ hJJ z) (fun z _ ↦ hKs z) (fun z _ ↦ hKt z) hu1.contDiffOn
    hη.contDiffOn (fun _ hz ↦ hD' hz) hS ⟨(0, 1 / 2), mem_univ _, by norm_num, by norm_num⟩
    (subset_univ _) hSη (mem_univ z)

end TauCeti.SymplecticForm
