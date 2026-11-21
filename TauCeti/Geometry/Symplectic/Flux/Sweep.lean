/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Flux
public import TauCeti.Geometry.Symplectic.Flux.Hamiltonian
public import TauCeti.Geometry.Manifold.DeRham.Period
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

The swept chain is also packaged as a map `TauCeti.Diffeotopy.sweep`, `(t, s) ↦ φ_t (γ s)` with
the time clamped to `[0, 1]`, so that its coordinates come in the order `(t, s)` of the chain's
orientation. In that order, the line integral of the flux form along a `C¹` curve is the rectangle
integral of `σ` over `sweep` itself, with no sign
(`TauCeti.Diffeotopy.pathIntegral_fluxForm_eq_rectangleIntegral`). The swept map is not
differentiable across the time ends, where the time is clamped, so this comparison uses its
derivatives within the strip `[0, 1] × ℝ`, which extend the partial derivatives continuously up to
the ends. Consequently the period of the flux class `TauCeti.Diffeotopy.flux` on a `C¹` loop is the
swept area (`TauCeti.Diffeotopy.period_flux_ofMul_eq_rectangleIntegral`), and a Hamiltonian isotopy
sweeps zero area along every `C¹` loop
(`TauCeti.Diffeotopy.IsHamiltonian.rectangleIntegral_sweep_eq_zero`).

The general statement behind this is the line integral of a homotopy operator
(`TauCeti.pathIntegral_homotopyOperator`): the flux form is the homotopy operator of the pullback
of `σ` along the motion `(x, t) ↦ φ_t x`.

## Main definitions

* `TauCeti.Diffeotopy.sweep`: the map `(t, s) ↦ φ_t (γ s)` sweeping a curve along a diffeotopy.

## Main results

* `TauCeti.Diffeotopy.pathIntegral_fluxForm`: the line integral of the flux form along a curve is
  the integral of `σ` over the swept chain.
* `TauCeti.Diffeotopy.homologyPeriodHom_fluxForm_loopClass`: the period of the flux form on the
  class of a loop is the `σ`-area of the swept cylinder.
* `TauCeti.Diffeotopy.pathIntegral_fluxForm_eq_rectangleIntegral`: the line integral of the flux
  form along a `C¹` curve is the integral of the form over `TauCeti.Diffeotopy.sweep`.
* `TauCeti.Diffeotopy.period_flux_ofMul_eq_rectangleIntegral`: the period of the flux on the class
  of a `C¹` loop is the area swept by the loop.
* `TauCeti.Diffeotopy.IsHamiltonian.rectangleIntegral_sweep_eq_zero`: a Hamiltonian isotopy sweeps
  zero area along every `C¹` loop.

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
    pathIntegral (Φ.fluxForm σ).val γ a b =
      -rectangleIntegral σ.val (fun p ↦ Φ (projIcc 0 1 zero_le_one p.2, γ p.1)) (a, 0) (b, 1) := by
  have hβ := (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap σ).isSmoothForm
  -- On the open rectangle, the curve and the interval coordinate are both differentiable.
  have hu : ∀ z ∈ uIoo a b ×ˢ uIoo (0 : ℝ) 1, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) (J.prod (𝓡∂ 1))
      (fun p ↦ (γ p.1, projIcc 0 1 zero_le_one p.2)) z := fun z hz ↦
    (hasMFDerivAt_prodMk_projIcc (hγ z.1 (uIoo_subset_uIcc_self hz.1))
      (uIoo_of_le (zero_le_one (α := ℝ)) ▸ hz.2)).mdifferentiableAt
  rw [coe_fluxForm, pathIntegral_homotopyOperator (hβ.of_le (by simp)) hγ,
    SmoothForm.coe_mpullback, rectangleIntegral_mpullback σ.val
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
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ) J 1 c) {x : M} {γ : Path x x} (hγ : ∀ t : unitInterval, γ t = c t) :
    homologyPeriodHom (Φ.fluxForm σ.val).val (H₁AddEquivHomology (.of M) (loopClass (X
        := .of M) γ)) =
      -rectangleIntegral σ.val.val (fun p ↦ Φ (projIcc 0 1 zero_le_one p.2, c p.1)) (0, 0) (1, 1)
          := by
  have hclosed : Φ.fluxForm σ.val ∈ closedForms J M 1 := Φ.fluxForm_mem_closedForms
    ((SmoothForm.isClosed_def _).mpr ((mem_closedForms J σ.val).mp σ.property)) hΦ
  rw [homologyPeriodHom_loopClass,
    pathClassIntegral_mk_eq_pathIntegral ((Φ.fluxForm σ.val).isSmoothForm.of_le (by simp))
      ((mem_closedForms J _).mp hclosed) hc hγ,
    Φ.pathIntegral_fluxForm σ.val fun s _ ↦ hc.mdifferentiableAt one_ne_zero]

end Loop

section SweptMap

open MeasureTheory

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ### The swept map -/

section Sweep

variable {n : WithTop ℕ∞} (Φ : Diffeotopy J n M)

/-- The map `(t, s) ↦ φ_t (γ s)` sweeping the curve `γ` along the diffeotopy `φ`, with the time `t`
clamped to `[0, 1]`. On the rectangle `[0, 1] × [a, b]` it is the two-chain swept out by the arc of
`γ` over `[a, b]` during the isotopy, oriented by the time followed by the curve parameter. -/
def sweep (γ : ℝ → M) (z : ℝ × ℝ) : M :=
  Φ.cylinderMap (γ z.2, projIcc 0 1 zero_le_one z.1)

/-- The swept map sends `(t, s)` to `φ_t (γ s)`, with `t` clamped to `[0, 1]`. -/
@[simp]
theorem sweep_apply (γ : ℝ → M) (z : ℝ × ℝ) :
    Φ.sweep γ z = Φ (projIcc 0 1 zero_le_one z.1, γ z.2) :=
  Φ.cylinderMap_apply _

/-- At time zero the swept map is the curve. -/
theorem sweep_zero (γ : ℝ → M) (s : ℝ) : Φ.sweep γ (0, s) = γ s := by
  rw [sweep_apply, projIcc_left, Set.Icc.mk_zero, Φ.apply_zero]

/-- At time one the swept map is the curve moved by the final diffeomorphism. -/
theorem sweep_one (γ : ℝ → M) (s : ℝ) : Φ.sweep γ (1, s) = Φ.final (γ s) := by
  rw [sweep_apply, projIcc_right, Set.Icc.mk_one, Φ.final_apply]

/-- The swept map along a `C^m` curve, for a `C^n` diffeotopy with `m ≤ n`, is `C^m` on the strip
`[0, 1] × ℝ`. -/
theorem contMDiffOn_sweep {m : WithTop ℕ∞} (hm : m ≤ n) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) J m γ) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) J m (Φ.sweep γ) (Icc 0 1 ×ˢ univ) := by
  have hfst : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡∂ 1) m
      (fun z : ℝ × ℝ ↦ projIcc (0 : ℝ) 1 zero_le_one z.1) (Icc 0 1 ×ˢ univ) :=
    contMDiffOn_projIcc.comp contDiff_fst.contMDiff.contMDiffOn fun z hz ↦ hz.1
  exact (Φ.contMDiff_cylinderMap.of_le hm).comp_contMDiffOn
    ((hγ.comp contDiff_snd.contMDiff).contMDiffOn.prodMk hfst)

end Sweep

/-! ### Derivatives of the swept map -/

variable (Φ : Diffeotopy J ∞ M)

/-- The strip `[0, 1] × ℝ` has unique derivatives. -/
private theorem uniqueMDiffOn_strip :
    UniqueMDiffOn 𝓘(ℝ, ℝ × ℝ) (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) :=
  ((uniqueDiffOn_Icc zero_lt_one).prod uniqueDiffOn_univ).uniqueMDiffOn

/-- On the strip `[0, 1] × ℝ`, the derivative within the strip of the swept map at `(t, s)` sends
`(a, b)` to the derivative of the motion `(x, t) ↦ φ_t x` at `(γ s, t)` applied to
`(b γ'(s), a ∂ₜ)`: the chain rule for `sweep = cylinderMap ∘ (γ ∘ snd, projIcc ∘ fst)`. -/
private theorem hasMFDerivWithinAt_sweep {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) J 1 γ)
    {z : ℝ × ℝ} (hz : z.1 ∈ Icc (0 : ℝ) 1) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ × ℝ) J (Φ.sweep γ) (Icc 0 1 ×ˢ univ) z
      ((mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (γ z.2, projIcc 0 1 zero_le_one z.1)).comp
        (((mfderiv 𝓘(ℝ, ℝ) J γ z.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
          ((mfderivWithin 𝓘(ℝ, ℝ) (𝓡∂ 1) (projIcc (0 : ℝ) 1 zero_le_one) (Icc 0 1) z.1).comp
            (ContinuousLinearMap.fst ℝ ℝ ℝ)))) := by
  have hsnd : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) Prod.snd z (ContinuousLinearMap.snd ℝ ℝ ℝ) :=
    hasMFDerivAt_iff_hasFDerivAt.2 (hasFDerivAt_snd (p := z))
  have hfst : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) Prod.fst z (ContinuousLinearMap.fst ℝ ℝ ℝ) :=
    hasMFDerivAt_iff_hasFDerivAt.2 (hasFDerivAt_fst (p := z))
  have hγz := ((hγ z.2).mdifferentiableAt one_ne_zero).hasMFDerivAt.comp z hsnd
  have hproj := ((contMDiffOn_projIcc (x := (0 : ℝ)) (y := 1) (n := 1) z.1
    hz).mdifferentiableWithinAt one_ne_zero).hasMFDerivWithinAt.comp z hfst.hasMFDerivWithinAt
      (prod_subset_preimage_fst _ (univ : Set ℝ))
  have hcyl : MDifferentiableAt (J.prod (𝓡∂ 1)) J Φ.cylinderMap
      (γ z.2, projIcc 0 1 zero_le_one z.1) :=
    (Φ.contMDiff_cylinderMap _).mdifferentiableAt (by simp)
  exact hcyl.hasMFDerivAt.comp_hasMFDerivWithinAt z (hγz.hasMFDerivWithinAt.prodMk hproj)

/-- On the strip `[0, 1] × ℝ`, the derivative within the strip of the swept map at `(t, s)` sends
`v` to the derivative of the motion `(x, t) ↦ φ_t x` at `(γ s, t)` applied to
`(dγ v.2, d(projIcc) v.1)`. -/
private theorem mfderivWithin_sweep_apply {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) J 1 γ)
    {z : ℝ × ℝ} (hz : z.1 ∈ Icc (0 : ℝ) 1) (v : ℝ × ℝ) :
    mfderivWithin 𝓘(ℝ, ℝ × ℝ) J (Φ.sweep γ) (Icc 0 1 ×ˢ univ) z v =
      mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (γ z.2, projIcc 0 1 zero_le_one z.1)
        (mfderiv 𝓘(ℝ, ℝ) J γ z.2 v.2,
          mfderivWithin 𝓘(ℝ, ℝ) (𝓡∂ 1) (projIcc (0 : ℝ) 1 zero_le_one) (Icc 0 1) z.1 v.1) := by
  rw [(Φ.hasMFDerivWithinAt_sweep hγ hz).mfderivWithin (uniqueMDiffOn_strip z ⟨hz, mem_univ _⟩)]
  -- `ContinuousLinearMap.comp`, `prod`, `fst` and `snd` evaluate this way by definition. Their
  -- evaluation lemmas do not rewrite here: the source of `dγ` is `TangentSpace 𝓘(ℝ, ℝ) z.2`, a type
  -- synonym of `ℝ`, so the composite only typechecks up to unfolding that synonym.
  rfl

/-- On the strip `[0, 1] × ℝ`, the time derivative of the swept map at `(t, s)` is the time
derivative `∂ₜ φ_t (γ s)` of the motion. -/
private theorem mfderivWithin_sweep_fst {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) J 1 γ)
    {z : ℝ × ℝ} (hz : z.1 ∈ Icc (0 : ℝ) 1) :
    mfderivWithin 𝓘(ℝ, ℝ × ℝ) J (Φ.sweep γ) (Icc 0 1 ×ˢ univ) z (1, 0) =
      mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (γ z.2, projIcc 0 1 zero_le_one z.1)
        ((0 : E), (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one z.1))) := by
  exact (Φ.mfderivWithin_sweep_apply hγ hz (1, 0)).trans <|
    congrArg (mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (γ z.2, projIcc 0 1 zero_le_one z.1))
      (congrArg₂ Prod.mk (map_zero _) (mfderivWithin_projIcc_one hz))

/-- On the strip `[0, 1] × ℝ`, the derivative of the swept map along the curve at `(t, s)` is the
image `dφ_t (γ' s)` of the velocity of the curve. -/
private theorem mfderivWithin_sweep_snd {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) J 1 γ)
    {z : ℝ × ℝ} (hz : z.1 ∈ Icc (0 : ℝ) 1) :
    mfderivWithin 𝓘(ℝ, ℝ × ℝ) J (Φ.sweep γ) (Icc 0 1 ×ˢ univ) z (0, 1) =
      mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (γ z.2, projIcc 0 1 zero_le_one z.1)
        (Manifold.curveVelocity J γ z.2, (0 : EuclideanSpace ℝ (Fin 1))) := by
  exact (Φ.mfderivWithin_sweep_apply hγ hz (0, 1)).trans <|
    congrArg (mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (γ z.2, projIcc 0 1 zero_le_one z.1))
      (congrArg₂ Prod.mk Manifold.curveVelocity_apply.symm (map_zero _))

variable [IsManifold J ∞ M]

/-- The pullback of `σ` along the swept map, taken with the derivatives within the strip
`[0, 1] × ℝ`, evaluated on the coordinate vectors `∂ₜ, ∂ₛ`, is continuous on the strip. -/
private theorem continuousOn_sweep_integrand (σ : SmoothForm J M ℝ 2) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) J 1 γ) :
    ContinuousOn (fun z ↦ mpullbackWithin 𝓘(ℝ, ℝ × ℝ) J (Φ.sweep γ)
      (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) σ.val z ![(1, 0), (0, 1)])
      (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
  have hσ : IsSmoothForm J 0 σ.val := σ.isSmoothForm.of_le (by simp)
  have hpull := ContMDiffOn.mpullbackWithin_form (m := 0) (n := 1) (t := univ)
    hσ.contMDiff.contMDiffOn
    (Φ.contMDiffOn_sweep (by simp) hγ) (by simp) (mapsTo_univ _ _) uniqueMDiffOn_strip
  have hc : ContinuousOn (X := ℝ × ℝ) (Y := (ℝ × ℝ) [⋀^Fin 2]→L[ℝ] ℝ)
      (mpullbackWithin 𝓘(ℝ, ℝ × ℝ) J (Φ.sweep γ) (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) σ.val)
      (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
    intro z hz
    exact (RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace
      (hpull z hz)).continuousWithinAt
  exact (ContinuousAlternatingMap.apply ℝ (ℝ × ℝ) ℝ ![(1, 0), (0, 1)]).continuous.comp_continuousOn
    hc

/-! ### The flux form along a curve -/

/-- **The flux form integrates along a curve to the area it sweeps.** For a `C¹` curve `γ`, the
line integral of the flux form `∫₀¹ φ_t^* (ι_{X_t} σ) dt` along `γ` from `a` to `b` is the integral
of `σ` over the two-chain `(t, s) ↦ φ_t (γ s)` on `[0, 1] × [a, b]`, oriented by the time followed
by the curve parameter. -/
theorem pathIntegral_fluxForm_eq_rectangleIntegral (σ : SmoothForm J M ℝ 2) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) J 1 γ) (a b : ℝ) :
    pathIntegral (Φ.fluxForm σ).val γ a b = rectangleIntegral σ.val (Φ.sweep γ) (0, a) (1, b) := by
  set S : Set (ℝ × ℝ) := Icc 0 1 ×ˢ univ
  set G : ℝ × ℝ → ℝ := fun z ↦ mpullbackWithin 𝓘(ℝ, ℝ × ℝ) J (Φ.sweep γ) S σ.val z
    ![(1, 0), (0, 1)]
  have hψ : IsSmoothForm (J.prod (𝓡∂ 1)) 0
      (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap σ).val :=
    (SmoothForm.mpullback _ _ σ).isSmoothForm.of_le (by simp)
  -- The flux form along `γ'(s)` is the time integral of `G (·, s)`.
  have hleft (s : ℝ) : (Φ.fluxForm σ).val (γ s) (fun _ ↦ Manifold.curveVelocity J γ s) =
      ∫ t in (0 : ℝ)..1, G (t, s) := by
    rw [coe_fluxForm]
    -- `homotopyOperator_apply_apply` takes vectors in `E`, of which the tangent space of `M` is a
    -- type synonym, so it applies up to unfolding rather than by `rw`.
    refine (homotopyOperator_apply_apply hψ (γ s) _).trans <|
      intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le zero_le_one] at ht
    simp only [G, SmoothForm.coe_mpullback, mpullback_apply, mpullbackWithin_apply]
    rw [sweep.eq_1 Φ γ (t, s)]
    congr 1
    funext i
    -- The entries of `Matrix.vecCons` and of `![(1, 0), (0, 1)]` at `0` and `1` reduce by
    -- definition; their evaluation lemmas do not rewrite, since the vectors on the left live in
    -- tangent-space type synonyms of `E × EuclideanSpace ℝ (Fin 1)`.
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact (Φ.mfderivWithin_sweep_fst hγ (z := (t, s)) ht).symm
    · rw [Fin.fin_one_eq_zero j]
      exact (Φ.mfderivWithin_sweep_snd hγ (z := (t, s)) ht).symm
  -- Inside the strip the derivatives within `S` are the derivatives of the swept map.
  have hright : rectangleIntegral σ.val (Φ.sweep γ) (0, a) (1, b) =
      ∫ t in (0 : ℝ)..1, ∫ s in a..b, G (t, s) := by
    rw [rectangleIntegral_def]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume 1] with t ht1 ht
    rw [uIoc_of_le zero_le_one] at ht
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    have hS : S ∈ nhds (t, s) :=
      prod_mem_nhds (Icc_mem_nhds ht.1 (lt_of_le_of_ne ht.2 ht1)) Filter.univ_mem
    have hd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) J (Φ.sweep γ) (t, s) :=
      ((Φ.contMDiffOn_sweep (by simp) hγ).contMDiffAt hS).mdifferentiableAt one_ne_zero
    have hu := uniqueMDiffOn_strip (t, s) ⟨Ioc_subset_Icc_self ht, mem_univ _⟩
    exact (congrArg (fun A : (ℝ × ℝ) [⋀^Fin 2]→L[ℝ] ℝ ↦ A ![(1, 0), (0, 1)])
      (mpullbackWithin_eq_mpullback hu hd σ.val)).symm
  -- `G` is continuous on the closed strip, so Fubini applies on the compact rectangle.
  have hint : IntegrableOn (Function.uncurry fun t s ↦ G (t, s)) (Ι (0 : ℝ) 1 ×ˢ Ι a b) :=
    ((Φ.continuousOn_sweep_integrand σ hγ).mono (prod_mono (uIcc_of_le zero_le_one).subset
      (subset_univ _))).integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
      |>.mono_set (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  rw [hright, intervalIntegral_intervalIntegral_swap hint, pathIntegral_def]
  exact intervalIntegral.integral_congr fun s _ ↦ hleft s

/-! ### Periods of the flux -/

/-- **The flux on a loop is the swept area.** Let `σ` be a closed two-form preserved by the final
diffeomorphism of `φ`. The period of the flux of `φ` on the class of a `C¹` loop `c` at `x`,
parametrized by `[0, 1]`, is the integral of `σ` over the cylinder `(t, s) ↦ φ_t (c s)`,
`(t, s) ∈ [0, 1] × [0, 1]`, swept out by the loop during the isotopy. -/
theorem period_flux_ofMul_eq_rectangleIntegral [FiniteDimensional ℝ E] [T2Space M]
    (σ : closedForms J M 2) (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ, ℝ) J 1 c) {x : M} {γ : Path x x} (hγ : ∀ t : unitInterval, γ t = c t) :
    deRhamCohomology.period x (Φ.flux σ hΦ) (Additive.ofMul (.of (.mk γ))) =
      rectangleIntegral σ.val.val (Φ.sweep c) (0, 0) (1, 1) := by
  have hcl := Φ.fluxForm_mem_closedForms
    ((SmoothForm.isClosed_def _).mpr ((mem_closedForms J σ.val).mp σ.property)) hΦ
  rw [flux_def, deRhamCohomology.period_mk, periodHom_ofMul_eq_pathIntegral
    ((Φ.fluxForm σ.val).isSmoothForm.of_le (by simp)) ((mem_closedForms J _).mp hcl) hc hγ,
    pathIntegral_fluxForm_eq_rectangleIntegral Φ σ.val hc]

/-- **Hamiltonian isotopies sweep zero area along loops.** If `φ` is a Hamiltonian isotopy for
`σ`, then for every `C¹` curve `c` with `c a = c b`, the integral of `σ` over the two-chain
`(t, s) ↦ φ_t (c s)` on `[0, 1] × [a, b]` vanishes. -/
theorem IsHamiltonian.rectangleIntegral_sweep_eq_zero {σ : SmoothForm J M ℝ 2}
    (hΦ : Φ.IsHamiltonian σ) {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) J 1 c) {a b : ℝ}
    (hab : c a = c b) : rectangleIntegral σ.val (Φ.sweep c) (0, a) (1, b) = 0 := by
  rw [← pathIntegral_fluxForm_eq_rectangleIntegral Φ σ hc]
  exact pathIntegral_eq_zero_of_mem_exactForms hΦ.fluxForm_mem_exactForms hc hab

end SweptMap

end Diffeotopy

end TauCeti
