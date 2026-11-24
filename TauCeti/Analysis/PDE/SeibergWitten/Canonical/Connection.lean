/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import TauCeti.Analysis.PDE.SeibergWitten.Canonical.Dirac
import TauCeti.Analysis.Calculus.FDeriv.Submodule

/-!
# The canonical connection on a field of canonical spinors

On a symplectic four-manifold with compatible almost complex structure `J` and Kähler form `ω`,
Taubes writes a positive spinor of the canonical `Spinᶜ` structure as `α u₀ + β`, where `u₀` is a
unit section of the canonical line, the range of `P_α = (1 + C(iω) / 2) / 2`
(`TauCeti.SeibergWitten.cliffordProjection`). The **canonical connection** `A₀` is the connection
on the determinant line for which the covariant derivative of `u₀` has no component along `u₀`.
Its Dirac operator on `u₀` vanishes when `dω = 0`; the pointwise algebra behind this is in
`TauCeti.Analysis.PDE.SeibergWitten.Canonical.Dirac`, with the derivatives taken as data.

This file supplies those derivatives for fields on a normed space, with the trivial connection on
`W`. If `ω` is a field of two-vectors and `u` a field of positive spinors with `P_α(ω y) u y = u y`
near `x`, then differentiating `C(iω) u = 2 u` gives the differentiated eigenvalue equation
`C(iω'(v)) u + C(iω) u'(v) = 2 u'(v)` at `x`
(`cliffordRestriction_apply_add_cliffordRestriction_apply_of_hasFDerivAt`), the input of the
pointwise projected-connection and Dirac identities. For a field `ω` of self-dual two-vectors on the
oriented four-space `V`, such as the Kähler two-vectors of a varying orthogonal complex structure,
and a field `u` with `‖u x‖ = 1`, if `dω = 0` at `x` then
`∑ₖ c(eₖ) (∂_{eₖ} u - ⟪u, ∂_{eₖ} u⟫ u) = 0` at `x`
(`sum_ι_apply_sub_inner_smul_eq_zero_of_hasFDerivAt`). When moreover `u` has unit norm near `x`,
the left side is the Dirac operator of the canonical connection applied to `u`.

## Main results

* `TauCeti.SeibergWitten.cliffordRestriction_apply_add_cliffordRestriction_apply_of_hasFDerivAt`:
  the differentiated eigenvalue equation of a field of canonical spinors.
* `TauCeti.SeibergWitten.sum_ι_apply_sub_inner_smul_eq_zero_of_hasFDerivAt`: Taubes's identity
  `D_{A₀} u₀ = 0` for a field of canonical spinors on `V`, from the derivatives of the fields.

## References

* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module Filter Topology
open scoped RealInnerProductSpace InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

/-- **The differentiated eigenvalue equation**: if `ω` is a field of two-vectors and `u` a field
of positive spinors on a real normed space with `P_α(ω y) u y = u y` near `x`, so that
`C(iω) u = 2 u` near `x`, then their derivatives `ω'` and `u'` at `x` satisfy
`C(iω'(v)) u + C(iω) u'(v) = 2 u'(v)`. -/
theorem cliffordRestriction_apply_add_cliffordRestriction_apply_of_hasFDerivAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {ω : E → ⋀[ℝ]^2 V} {ω' : E →L[ℝ] ⋀[ℝ]^2 V}
    {u : E → positiveHalfSpinors o ρ} {u' : E →L[ℝ] positiveHalfSpinors o ρ} {x : E}
    (hω : HasFDerivAt ω ω' x) (hu : HasFDerivAt u u' x)
    (hP : ∀ᶠ y in 𝓝 x, cliffordProjection o ρ (ω y) (u y) = u y) (v : E) :
    cliffordRestriction o ρ (ω' v) (u x) + cliffordRestriction o ρ (ω x) (u' v) =
      (2 : ℂ) • u' v := by
  -- The Clifford map, as a continuous real-linear map into real-linear endomorphisms of `W⁺`.
  let L : ⋀[ℝ]^2 V →L[ℝ] positiveHalfSpinors o ρ →L[ℝ] positiveHalfSpinors o ρ :=
    LinearMap.toContinuousLinearMap
      ((ContinuousLinearMap.restrictScalarsₗ ℂ (positiveHalfSpinors o ρ)
        (positiveHalfSpinors o ρ) ℝ ℝ) ∘ₗ cliffordRestriction o ρ)
  have hL (F : ⋀[ℝ]^2 V) (ψ : positiveHalfSpinors o ρ) : L F ψ = cliffordRestriction o ρ F ψ := by
    simp [L]
  have hd := ((L.hasFDerivAt.comp x hω).clm_apply hu).unique
    ((hu.const_smul (2 : ℝ)).congr_of_eventuallyEq (by
      filter_upwards [hP] with y hy
      rw [Function.comp_apply, hL, (cliffordProjection_apply_eq_self_iff o ρ).1 hy, Pi.smul_apply,
        ← Complex.coe_smul, Complex.ofReal_ofNat]))
  have h := congrArg (fun T ↦ T v) hd
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply, hL, smul_apply] at h
  rw [add_comm, h, ← Complex.coe_smul, Complex.ofReal_ofNat]

/-- **Taubes's identity `D_{A₀} u₀ = 0` for a field of canonical spinors**: let `ω` be a field of
self-dual two-vectors on `V` near `x`, and `u` a field of spinors on the canonical lines,
`P_α(ω y) u y = u y` near `x`, with `‖u x‖ = 1` and `W⁺` of complex dimension two. If
`∑ₖ vₖ ∧ ∂_{vₖ} ω = 0` at `x`, then

`∑ₖ c(vₖ) (∂_{vₖ} u - ⟪u, ∂_{vₖ} u⟫ u) = 0` at `x`.

For an orthonormal frame `vₖ = eₖ` the hypothesis is `dω = 0` at `x`. If moreover `‖u y‖ = 1` near
`x`, then `∂u - ⟪u, ∂u⟫ u` is the covariant derivative of `u` for the canonical connection, for the
trivial connection on `W`, and the left side is its Dirac operator applied to `u` at `x`. -/
theorem sum_ι_apply_sub_inner_smul_eq_zero_of_hasFDerivAt (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hkl : 2 + 2 = finrank ℝ V) (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hW : finrank ℂ (positiveHalfSpinors o ρ) = 2) {ω : V → ⋀[ℝ]^2 V}
    {ω' : V →L[ℝ] ⋀[ℝ]^2 V} {u : V → positiveHalfSpinors o ρ}
    {u' : V →L[ℝ] positiveHalfSpinors o ρ} {x : V} (hω : HasFDerivAt ω ω' x)
    (hu : HasFDerivAt u u' x) (hsd : ∀ᶠ y in 𝓝 x, o.hodgeStar hkl (ω y) = ω y)
    (hP : ∀ᶠ y in 𝓝 x, cliffordProjection o ρ (ω y) (u y) = u y) (hu₁ : ‖u x‖ = 1)
    {κ : Type*} {s : Finset κ} (v : κ → V)
    (hdω : ∑ k ∈ s, ExteriorAlgebra.wedgeLeft (v k) 2 (ω' (v k)) = 0) :
    ∑ k ∈ s, ρ (ι Q (v k)) ((u' (v k) - ⟪u x, u' (v k)⟫_ℂ • u x : positiveHalfSpinors o ρ) : W) =
      0 := by
  refine sum_ι_apply_sub_inner_smul_eq_zero hQ hkl hρ hW (mem_of_mem_nhds hsd)
    (mem_of_mem_nhds hP) hu₁ v (fun k _ ↦ ?_)
    (fun k _ ↦
      cliffordRestriction_apply_add_cliffordRestriction_apply_of_hasFDerivAt hω hu hP (v k))
    hdω
  -- The derivative of the field `ω` of self-dual two-vectors is self-dual.
  let S : Submodule ℝ (⋀[ℝ]^2 V) := LinearMap.ker ((o.hodgeStar hkl).toLinearMap - LinearMap.id)
  have hx : o.hodgeStar hkl (ω x) = ω x := mem_of_mem_nhds hsd
  have hmem := hω.apply_mem_of_eventually_sub_mem (Submodule.isClosed_of_finiteDimensional S) (by
    filter_upwards [hsd] with y hy
    simp [S, hy, hx]) (v k)
  simpa [S, sub_eq_zero] using hmem

end TauCeti.SeibergWitten
