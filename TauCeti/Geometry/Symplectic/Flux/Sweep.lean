/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Flux
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Homotopy
public import TauCeti.Geometry.Manifold.DeRham.HomologyPeriod
import TauCeti.Geometry.Manifold.Instances.Icc

/-!
# The flux pairs with a cycle as the area of the cylinder it sweeps

Let `σ` be a two-form on a manifold `M` and let `φ_t`, `t ∈ [0, 1]`, be a smooth diffeotopy of
`M`, with flux form `Flux φ = ∫₀¹ φ_t^* (ι_{X_t} σ) dt` (`TauCeti.Diffeotopy.fluxForm`). A curve
`γ : [a, b] → M` sweeps out the two-chain

`(t, s) ↦ φ_t (γ s)`,  `(t, s) ∈ [0, 1] × [a, b]`,

under the motion. This file proves that the line integral of the flux form along `γ` is the
integral of `σ` over this swept chain, oriented by `dt` followed by the orientation of `γ`
(`TauCeti.Diffeotopy.pathIntegral_fluxForm`):

`∫_γ Flux φ = ∫_a^b ∫₀¹ σ(∂ₜ φ_t (γ s), ∂_s φ_t (γ s)) dt ds`.

In the convention of `TauCeti.rectangleIntegral`, which orders the coordinates `(s, t)`, the right
side is minus the integral over `(s, t) ↦ φ_t (γ s)`. No closedness of `σ` and no symplectic
condition on the diffeotopy is used, and `M` need not be compact.

For a closed `σ` preserved by the final map `φ₁`, the flux form is closed and its periods are
defined on `H₁(M; ℤ)` (`TauCeti.homologyPeriodHom`). The period of the flux form on the class of a
`C¹` loop is then the `σ`-area of the cylinder swept by the loop
(`TauCeti.Diffeotopy.homologyPeriodHom_fluxForm_loopClass`). This is the pairing of the flux
`Flux(φ) ∈ H¹_dR(M)` with integral one-cycles: when `φ` is a loop of symplectomorphisms the swept
cylinder closes up to a torus, and its area computes the flux pairing.

The general statement behind this is the line integral of a homotopy operator
(`TauCeti.pathIntegral_homotopyOperator`): the flux form is the homotopy operator of the pullback
of `σ` along the motion `(x, t) ↦ φ_t x`.

## Main results

* `TauCeti.Diffeotopy.pathIntegral_fluxForm`: the line integral of the flux form along a curve is
  the integral of `σ` over the swept chain.
* `TauCeti.Diffeotopy.homologyPeriodHom_fluxForm_loopClass`: the period of the flux form on the
  class of a loop is the `σ`-area of the swept cylinder.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism and its pairing with loops).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Chapter 3.
-/

public section

noncomputable section

open Set CategoryTheory TauCeti.HurewiczOne TauCeti.TopCat
open scoped ContDiff Manifold Interval

namespace TauCeti

namespace Diffeotopy

section Curve

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] (Φ : Diffeotopy J ∞ M)

/-- **The flux form along a curve is the area of the swept chain.** For a smooth diffeotopy `φ_t`
and a two-form `σ`, the line integral of the flux form along a curve `γ` differentiable on
`[a, b]` is the integral of `σ` over the chain `(t, s) ↦ φ_t (γ s)` swept by `γ` under the
motion, oriented by `dt` followed by `ds`. Since `TauCeti.rectangleIntegral` orders the
coordinates `(s, t)`, this is minus the integral over `(s, t) ↦ φ_t (γ s)`. -/
theorem pathIntegral_fluxForm (σ : SmoothForm J M ℝ 2) {γ : ℝ → M} {a b : ℝ}
    (hγ : ∀ s ∈ [[a, b]], MDifferentiableAt 𝓘(ℝ) J γ s) :
    pathIntegral (Φ.fluxForm σ).1 γ a b =
      -rectangleIntegral σ.1 (fun p ↦ Φ (projIcc 0 1 zero_le_one p.2, γ p.1)) (a, 0) (b, 1) := by
  have hβ := (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap σ).isSmoothForm
  -- On the open rectangle, the curve and the interval coordinate are both differentiable.
  have hu : ∀ z ∈ uIoo a b ×ˢ uIoo (0 : ℝ) 1, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) (J.prod (𝓡∂ 1))
      (fun p ↦ (γ p.1, projIcc 0 1 zero_le_one p.2)) z := fun z hz ↦
    (hasMFDerivAt_prodMk_projIcc (hγ z.1 (uIoo_subset_uIcc_self hz.1))
      (uIoo_of_le (zero_le_one (α := ℝ)) ▸ hz.2)).mdifferentiableAt
  rw [coe_fluxForm, pathIntegral_homotopyOperator (hβ.of_le (by simp)) hγ,
    SmoothForm.coe_mpullback, rectangleIntegral_mpullback σ.1
      (fun _ _ ↦ Φ.contMDiff_cylinderMap.mdifferentiableAt (by simp)) hu, Function.comp_def]
  simp only [cylinderMap_apply]

end Curve

section Loop

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold J ∞ M] (Φ : Diffeotopy J ∞ M)

/-- **The flux pairs with a loop as the area of the swept cylinder.** Let `σ` be a closed
two-form preserved by the final map of a smooth diffeotopy `φ_t`, so that the flux form is closed.
For a `C¹` loop `c`, read on `[0, 1]` as the loop `γ` in `M`, the period of the flux form on the
class of `γ` in `H₁(M; ℤ)` is the integral of `σ` over the cylinder `(t, s) ↦ φ_t (c s)` swept by
the loop, oriented by `dt` followed by `ds`. -/
theorem homologyPeriodHom_fluxForm_loopClass (σ : closedForms J M 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.1) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ) J 1 c) {x : M} {γ : Path x x} (hγ : ∀ t : unitInterval, γ t = c t) :
    homologyPeriodHom (Φ.fluxForm σ.1).1 (H₁AddEquivHomology (.of M) (loopClass (X := .of M) γ)) =
      -rectangleIntegral σ.1.1 (fun p ↦ Φ (projIcc 0 1 zero_le_one p.2, c p.1)) (0, 0) (1, 1) := by
  have hclosed : Φ.fluxForm σ.1 ∈ closedForms J M 1 := Φ.fluxForm_mem_closedForms
    ((SmoothForm.isClosed_def _).mpr ((mem_closedForms J σ.1).mp σ.2)) hΦ
  rw [homologyPeriodHom_loopClass,
    pathClassIntegral_mk_eq_pathIntegral ((Φ.fluxForm σ.1).isSmoothForm.of_le (by simp))
      ((mem_closedForms J _).mp hclosed) hc hγ,
    Φ.pathIntegral_fluxForm σ.1 fun s _ ↦ hc.mdifferentiableAt one_ne_zero]

end Loop

end Diffeotopy

end TauCeti
