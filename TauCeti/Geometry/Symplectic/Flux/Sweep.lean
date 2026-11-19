/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Period
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Homotopy
public import TauCeti.Geometry.Symplectic.Flux.Hamiltonian

/-!
# The flux of a diffeotopy pairs with curves as the area they sweep

Let `φ_t`, `t ∈ [0, 1]`, be a smooth diffeotopy of a manifold `M` and let `σ` be a two-form on `M`.
A curve `γ : ℝ → M` is carried along by the isotopy, and its arc over `[a, b]` sweeps out the
two-chain

`(t, s) ↦ φ_t (γ s)`,  `(t, s) ∈ [0, 1] × [a, b]`,

oriented by `dt` followed by the orientation of the curve
(`TauCeti.Diffeotopy.sweep`; outside `[0, 1]` the time is clamped to the nearest end). This file
proves that the line integral of the flux form `∫₀¹ φ_t^* (ι_{X_t} σ) dt` along `γ` is the integral
of `σ` over this swept two-chain
(`TauCeti.Diffeotopy.pathIntegral_fluxForm_eq_rectangleIntegral`):

`∫_a^b (Flux φ)(γ' s) ds = ∫₀¹ ∫_a^b σ(∂ₜ φ_t (γ s), ∂ₛ φ_t (γ s)) ds dt`.

At `(t, s)` the integrand of the flux form is `σ(∂ₜ φ_t (γ s), dφ_t (γ' s))`, and these two vectors
are the partial derivatives of the swept map, so the identity is Fubini's theorem. The swept map is
not differentiable across the time ends, where the time is clamped, so the comparison uses its
derivatives within the strip `[0, 1] × ℝ`, which extend the partial derivatives continuously up to
the ends and agree with them in the interior.

For a closed `σ` preserved by `φ₁`, the flux is the de Rham class of the flux form. Its period on
the class of a `C¹` loop is therefore the `σ`-area swept by the loop during the isotopy
(`TauCeti.Diffeotopy.period_flux_ofMul_eq_rectangleIntegral`). For a symplectic form this is the
classical description of the flux of a symplectic isotopy as the symplectic area swept out by
loops, and it shows at once that a Hamiltonian isotopy sweeps zero area along every `C¹` loop
(`TauCeti.Diffeotopy.IsHamiltonian.rectangleIntegral_sweep_eq_zero`).

## Main definitions

* `TauCeti.Diffeotopy.sweep`: the map `(t, s) ↦ φ_t (γ s)` sweeping a curve along a diffeotopy.

## Main results

* `TauCeti.Diffeotopy.pathIntegral_fluxForm_eq_rectangleIntegral`: the line integral of the flux
  form along a `C¹` curve is the integral of the form over the swept two-chain.
* `TauCeti.Diffeotopy.period_flux_ofMul_eq_rectangleIntegral`: the period of the flux on the class
  of a `C¹` loop is the area swept by the loop.
* `TauCeti.Diffeotopy.IsHamiltonian.rectangleIntegral_sweep_eq_zero`: a Hamiltonian isotopy sweeps
  zero area along every `C¹` loop.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism, and its values on loops as swept
  areas).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Chapter 3.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff Manifold Interval

namespace TauCeti

namespace Diffeotopy

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
    rw [coe_fluxForm, hψ.homotopyOperator_apply_apply]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le zero_le_one] at ht
    simp only [G, SmoothForm.coe_mpullback, mpullback_apply, mpullbackWithin_apply]
    rw [sweep.eq_1 Φ γ (t, s)]
    congr 1
    funext i
    -- The entries of `Fin.cons` and of `![(1, 0), (0, 1)]` at `0` and `1` reduce by definition;
    -- their evaluation lemmas do not rewrite, since the vectors on the left live in tangent-space
    -- type synonyms of `E × EuclideanSpace ℝ (Fin 1)`.
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

end Diffeotopy

end TauCeti
