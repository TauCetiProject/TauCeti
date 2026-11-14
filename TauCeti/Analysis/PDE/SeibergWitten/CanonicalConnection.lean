/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Contraction
public import TauCeti.Analysis.PDE.SeibergWitten.CanonicalLine
import TauCeti.Analysis.Calculus.FDeriv.Submodule
import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor

/-!
# The canonical connection and the Dirac operator on Taubes's canonical spinor

On a symplectic four-manifold with compatible almost complex structure `J`, Kähler form `ω` and
metric `g = ω(·, J ·)`, Taubes writes a positive spinor of the canonical `Spinᶜ` structure as
`α u₀ + β`, where `u₀` is a unit section of the `-2i`-eigenline of Clifford multiplication by `ω`,
the range of `P_α = (1 + C(iω) / 2) / 2` (`TauCeti.SeibergWitten.cliffordProjection`), and `β` lies
in the complementary line, the range of `P_β = 1 - P_α`. The **canonical connection** `A₀` is the
connection on the determinant line for which the covariant derivative of `u₀` has no component
along `u₀`: if `∇` is any `Spinᶜ` connection and `∇_v u₀` its derivative, then
`∇^{A₀}_v u₀ = ∇_v u₀ - ⟪u₀, ∇_v u₀⟫ u₀ = P_β ∇_v u₀`. This file proves Taubes's identity

`D_{A₀} u₀ = ∑ₖ c(eₖ) ∇^{A₀}_{eₖ} u₀ = 0`

when `dω = 0`, together with the general formula behind it.

Everything is pointwise algebra at one point, for an arbitrary Hermitian Clifford module `W` over an
oriented four-space `V`. The derivative of `u₀` along a vector is recorded as a positive spinor `ψ'`
and the covariant derivative of `ω` along it as a two-vector `ω'`. Differentiating the eigenvalue
equation `C(iω) u₀ = 2 u₀` with a Clifford-compatible connection gives

`C(iω') u₀ + C(iω) ψ' = 2 ψ'`,

and this relation alone determines the component of `ψ'` off the canonical line:
`P_β ψ' = C(iω') u₀ / 4` (`cliffordProjection_neg_apply_eq_smul_cliffordRestriction_apply`). So the
canonical covariant derivative of `u₀` is `C(i ∇ω) u₀ / 4`, controlled by the intrinsic torsion
`∇ω` of the almost Hermitian structure.

The derivative `ω'` of the self-dual form `ω` is again self-dual. For a positive spinor `ψ`, a
vector `v` and a self-dual `β`, Clifford multiplication satisfies `c(v) c₂(β) ψ = -2 c(v ⌟ β) ψ`
(`CliffordAlgebra.ι_apply_bivectorExterior_apply_of_hodgeStar_eq_self`), because `c₂(β)` kills
the negative spinor `c(v) ψ` and `⁅c₂(β), c(v)⁆ = 2 c(v ⌟ β)`
(`CliffordAlgebra.bivectorExterior_lie_ι`). Summing over an orthonormal frame, the Dirac operator
of the canonical connection is

`D_{A₀} u₀ = ∑ₖ c(eₖ) P_β ∇_{eₖ} u₀ = -(i / 2) c(θ) u₀`,  `θ = ∑ₖ eₖ ⌟ ∇_{eₖ} ω = -d*ω`

(`sum_ι_apply_cliffordProjection_neg_apply`). For self-dual `ω` in dimension four, if
`dω = ∑ₖ eₖ ∧ ∇_{eₖ} ω` vanishes then so does `d*ω`
(`Orientation.sum_twoVectorContraction_eq_zero_of_hodgeStar_eq_self`), so on a symplectic manifold
`D_{A₀} u₀ = 0` (`sum_ι_apply_cliffordProjection_neg_apply_eq_zero`,
`sum_ι_apply_sub_inner_smul_eq_zero`). In the Dirac equation `D_A (α u₀ + β) = 0`, with
`A = A₀ + 2a`, the term `α D_{A₀} u₀` therefore drops out, and the equation equates the Clifford
symbol of `∇_a α` on `u₀`, which sees only `∂bar_a α`
(`TauCeti.SeibergWitten.sum_apply_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self`),
with `-D_A β`.

The last part applies this to fields on `V` itself, with the trivial connection on `W` and a field
`ω` of self-dual two-vectors, such as the Kähler two-vectors of a varying orthogonal complex
structure: if `u` is a field of unit spinors with `P_α(ω) u = u` and `dω = 0` at `x`, then
`∑ₖ c(eₖ) (∂_{eₖ} u - ⟪u, ∂_{eₖ} u⟫ u) = 0` at `x`
(`sum_ι_apply_sub_inner_smul_eq_zero_of_hasFDerivAt`).

## Main results

* `TauCeti.SeibergWitten.cliffordProjection_neg_apply_eq_smul_cliffordRestriction_apply`: if
  `C(iω') ψ + C(iω) ψ' = 2 ψ'` then `P_β ψ' = C(iω') ψ / 4`.
* `TauCeti.SeibergWitten.sum_ι_apply_cliffordProjection_neg_apply`: the Dirac operator of the
  canonical connection on `u₀` is `-(i / 2) c(∑ₖ eₖ ⌟ ∇_{eₖ} ω) u₀`.
* `TauCeti.SeibergWitten.sum_ι_apply_cliffordProjection_neg_apply_eq_zero` and
  `TauCeti.SeibergWitten.sum_ι_apply_sub_inner_smul_eq_zero`: it vanishes when `dω = 0`.
* `TauCeti.SeibergWitten.sum_ι_apply_sub_inner_smul_eq_zero_of_hasFDerivAt`: the same for a field of
  canonical spinors on `V`, from the derivatives of the fields.

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

/-! ### The canonical covariant derivative of `u₀` -/

/-- **The off-diagonal part of the derivative of a canonical spinor**: if `ψ'` satisfies the
differentiated eigenvalue equation `C(iω') ψ + C(iω) ψ' = 2 ψ'`, then its component off the
canonical line is `P_β ψ' = C(iω') ψ / 4`. -/
theorem cliffordProjection_neg_apply_eq_smul_cliffordRestriction_apply {ω ω' : ⋀[ℝ]^2 V}
    {ψ ψ' : positiveHalfSpinors o ρ}
    (h : cliffordRestriction o ρ ω' ψ + cliffordRestriction o ρ ω ψ' = (2 : ℂ) • ψ') :
    cliffordProjection o ρ (-ω) ψ' = (4⁻¹ : ℂ) • cliffordRestriction o ρ ω' ψ := by
  -- `C(iω) = 4 P_α - 2`, so the hypothesis says `C(iω') ψ = 4 (ψ' - P_α ψ')`.
  rw [cliffordRestriction_eq_cliffordProjection o ρ ω, sub_apply, smul_apply, smul_apply,
    one_apply_eq_self] at h
  rw [cliffordProjection_neg_apply]
  linear_combination (norm := module) (-4⁻¹ : ℂ) • h

/-! ### The Dirac operator of the canonical connection -/

/-- **The Dirac operator of the canonical connection on the canonical spinor**: if `ψ'ₖ` are the
derivatives of `ψ` along `vₖ`, satisfying the differentiated eigenvalue equations
`C(iω'ₖ) ψ + C(iω) ψ'ₖ = 2 ψ'ₖ` with self-dual `ω'ₖ`, then

`∑ₖ c(vₖ) P_β ψ'ₖ = -(i / 2) c(∑ₖ vₖ ⌟ ω'ₖ) ψ`.

For an orthonormal frame `vₖ = eₖ`, `ψ = u₀`, `ψ'ₖ = ∇_{eₖ} u₀` and `ω'ₖ = ∇_{eₖ} ω`, the left side
is `D_{A₀} u₀` and `∑ₖ eₖ ⌟ ∇_{eₖ} ω = -d*ω`. -/
theorem sum_ι_apply_cliffordProjection_neg_apply (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hkl : 2 + 2 = finrank ℝ V) {κ : Type*} [Fintype κ] {ω : ⋀[ℝ]^2 V}
    {ψ : positiveHalfSpinors o ρ} (v : κ → V) {ω' : κ → ⋀[ℝ]^2 V}
    {ψ' : κ → positiveHalfSpinors o ρ} (hω' : ∀ k, o.hodgeStar hkl (ω' k) = ω' k)
    (hψ' : ∀ k, cliffordRestriction o ρ (ω' k) ψ + cliffordRestriction o ρ ω (ψ' k) =
      (2 : ℂ) • ψ' k) :
    ∑ k, ρ (ι Q (v k)) (cliffordProjection o ρ (-ω) (ψ' k)) =
      (-Complex.I / 2) • ρ (ι Q (∑ k, twoVectorContraction (ω' k) (v k))) ψ := by
  simp only [cliffordProjection_neg_apply_eq_smul_cliffordRestriction_apply (hψ' _),
    Submodule.coe_smul, coe_cliffordRestriction_apply, map_smul,
    ι_apply_bivectorExterior_apply_of_hodgeStar_eq_self o hQ hkl (hω' _), map_sum,
    LinearMap.sum_apply, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  congr 1
  ring

/-- **Taubes's identity `D_{A₀} u₀ = 0`**: under the hypotheses of
`sum_ι_apply_cliffordProjection_neg_apply`, if moreover `∑ₖ vₖ ∧ ω'ₖ = 0`, then
`∑ₖ c(vₖ) P_β ψ'ₖ = 0`. For an orthonormal frame the hypothesis is `dω = 0`. -/
theorem sum_ι_apply_cliffordProjection_neg_apply_eq_zero (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hkl : 2 + 2 = finrank ℝ V) {κ : Type*} [Fintype κ] {ω : ⋀[ℝ]^2 V}
    {ψ : positiveHalfSpinors o ρ} (v : κ → V) {ω' : κ → ⋀[ℝ]^2 V}
    {ψ' : κ → positiveHalfSpinors o ρ} (hω' : ∀ k, o.hodgeStar hkl (ω' k) = ω' k)
    (hψ' : ∀ k, cliffordRestriction o ρ (ω' k) ψ + cliffordRestriction o ρ ω (ψ' k) =
      (2 : ℂ) • ψ' k)
    (hdω : ∑ k, ExteriorAlgebra.wedgeLeft (v k) 2 (ω' k) = 0) :
    ∑ k, ρ (ι Q (v k)) (cliffordProjection o ρ (-ω) (ψ' k)) = 0 := by
  rw [sum_ι_apply_cliffordProjection_neg_apply hQ hkl v hω' hψ',
    o.sum_twoVectorContraction_eq_zero_of_hodgeStar_eq_self hkl (fun k _ ↦ hω' k) hdω]
  simp

/-- **Taubes's identity `D_{A₀} u₀ = 0` on a spin module**: when `W⁺` has complex dimension two
and `u₀` is a unit spinor on the canonical line of a self-dual `ω`, the canonical covariant
derivative of `u₀` is `ψ' - ⟪u₀, ψ'⟫ u₀`, and under the hypotheses of
`sum_ι_apply_cliffordProjection_neg_apply_eq_zero`,

`∑ₖ c(vₖ) (ψ'ₖ - ⟪u₀, ψ'ₖ⟫ u₀) = 0`. -/
theorem sum_ι_apply_sub_inner_smul_eq_zero (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hkl : 2 + 2 = finrank ℝ V) (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) {κ : Type*} [Fintype κ] {ω : ⋀[ℝ]^2 V}
    (hω : o.hodgeStar hkl ω = ω) {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ ω u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1) (v : κ → V)
    {ω' : κ → ⋀[ℝ]^2 V} {ψ' : κ → positiveHalfSpinors o ρ}
    (hω' : ∀ k, o.hodgeStar hkl (ω' k) = ω' k)
    (hψ' : ∀ k, cliffordRestriction o ρ (ω' k) u₀ + cliffordRestriction o ρ ω (ψ' k) =
      (2 : ℂ) • ψ' k)
    (hdω : ∑ k, ExteriorAlgebra.wedgeLeft (v k) 2 (ω' k) = 0) :
    ∑ k, ρ (ι Q (v k)) ((ψ' k - ⟪u₀, ψ' k⟫_ℂ • u₀ : positiveHalfSpinors o ρ) : W) = 0 := by
  -- On a spin module `P_α ψ = ⟪u₀, ψ⟫ u₀`, so `P_β ψ = ψ - ⟪u₀, ψ⟫ u₀`.
  have hP (ψ : positiveHalfSpinors o ρ) : cliffordProjection o ρ (-ω) ψ = ψ - ⟪u₀, ψ⟫_ℂ • u₀ := by
    rw [cliffordProjection_neg_apply,
      cliffordProjection_apply_eq_inner_smul o hQ hkl hω hρ h₂ hu₀ hu₀₁]
  simp_rw [← hP]
  exact sum_ι_apply_cliffordProjection_neg_apply_eq_zero hQ hkl v hω' hψ' hdω

/-! ### Fields of canonical spinors -/

section Fields

variable {ω : V → ⋀[ℝ]^2 V} {ω' : V →L[ℝ] ⋀[ℝ]^2 V} {u : V → positiveHalfSpinors o ρ}
  {u' : V →L[ℝ] positiveHalfSpinors o ρ} {x : V}

/-- Differentiating the eigenvalue equation `C(iω) u = 2 u` of a field of canonical spinors gives
`C(iω'(v)) u + C(iω) u'(v) = 2 u'(v)`. -/
private theorem cliffordRestriction_apply_add_cliffordRestriction_apply_of_hasFDerivAt
    (hω : HasFDerivAt ω ω' x) (hu : HasFDerivAt u u' x)
    (hP : ∀ᶠ y in 𝓝 x, cliffordProjection o ρ (ω y) (u y) = u y) (v : V) :
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

For an orthonormal frame `vₖ = eₖ` the hypothesis is `dω = 0` at `x` and the left side is the
Dirac operator of the canonical connection, for the trivial connection on `W`, applied to `u`. -/
theorem sum_ι_apply_sub_inner_smul_eq_zero_of_hasFDerivAt (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hkl : 2 + 2 = finrank ℝ V) (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (hω : HasFDerivAt ω ω' x)
    (hu : HasFDerivAt u u' x) (hsd : ∀ᶠ y in 𝓝 x, o.hodgeStar hkl (ω y) = ω y)
    (hP : ∀ᶠ y in 𝓝 x, cliffordProjection o ρ (ω y) (u y) = u y) (hu₁ : ‖u x‖ = 1)
    {κ : Type*} [Fintype κ] (v : κ → V)
    (hdω : ∑ k, ExteriorAlgebra.wedgeLeft (v k) 2 (ω' (v k)) = 0) :
    ∑ k, ρ (ι Q (v k)) ((u' (v k) - ⟪u x, u' (v k)⟫_ℂ • u x : positiveHalfSpinors o ρ) : W) =
      0 := by
  refine sum_ι_apply_sub_inner_smul_eq_zero hQ hkl hρ h₂ (mem_of_mem_nhds hsd)
    (mem_of_mem_nhds hP) hu₁ v (fun k ↦ ?_)
    (fun k ↦ cliffordRestriction_apply_add_cliffordRestriction_apply_of_hasFDerivAt hω hu hP (v k))
    hdω
  -- The derivative of the field `ω` of self-dual two-vectors is self-dual.
  let S : Submodule ℝ (⋀[ℝ]^2 V) := LinearMap.ker ((o.hodgeStar hkl).toLinearMap - LinearMap.id)
  have hx : o.hodgeStar hkl (ω x) = ω x := mem_of_mem_nhds hsd
  have hmem := hω.apply_mem_of_eventually_sub_mem (Submodule.isClosed_of_finiteDimensional S) (by
    filter_upwards [hsd] with y hy
    simp [S, hy, hx]) (v k)
  simpa [S, sub_eq_zero] using hmem

end Fields

end TauCeti.SeibergWitten
