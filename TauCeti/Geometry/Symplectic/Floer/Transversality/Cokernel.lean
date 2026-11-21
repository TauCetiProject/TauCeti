/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Perturbation.Basic
public import TauCeti.Geometry.Symplectic.Floer.Transversality.AlmostComplexVariation
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
covector fields, for each of the two kinds of variation.

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

In both cases the first hypothesis says that `η` solves the adjoint equation `D_u^* η = 0` on `Ω`
(`TauCeti.SymplecticForm.forall_integral_apply_floerLinearization_eq_zero_iff`), the second that
`η` vanishes on `U`
(`TauCeti.SymplecticForm.eqOn_zero_of_forall_integral_apply_floerOperator_add_sub_eq_zero`,
`TauCeti.SymplecticForm.eq_zero_of_integral_apply_deriv_floerOperator_eq_zero`), and unique
continuation for the adjoint equation
(`TauCeti.SymplecticForm.eqOn_zero_of_floerLinearizationAdjoint_eq_zero_of_eqOn_zero`) spreads the
vanishing over `Ω`.

These are statements about classical (`C¹`) cokernel elements. The regularity of weak (`Lᵖ`)
cokernel elements of a Sobolev realization of `D_u`, and the surjectivity of the universal
operator on Banach spaces that follows, are not treated here.

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

end TauCeti.SymplecticForm
