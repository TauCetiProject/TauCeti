/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.CylinderShear
public import TauCeti.Geometry.Manifold.DeRham.NormedSpace
public import TauCeti.Geometry.Manifold.DeRham.RealLine
public import TauCeti.Geometry.Symplectic.Flux.CompactSupport
public import TauCeti.Geometry.Symplectic.Manifold.Cylinder

/-!
# Compactly supported flux on the cylinder

On the cylinder `ℝ × AddCircle p`, with coordinates `(r, θ)`, consider the area form

`ω = dr ∧ dθ` (`TauCeti.cylinderAreaForm p`),

which pairs `v` and `w` to `v₁ w₂ - w₁ v₂`. For a smooth compactly supported function
`g : ℝ → ℝ`, the shear diffeotopy `φ_t (r, θ) = (r, θ + [t g(r)])`
(`TauCeti.cylinderShearDiffeotopy`) is the identity outside the compact band
`tsupport g × AddCircle p`, and each `φ_t` preserves `ω`, because its derivative is a unipotent
shear matrix. Its velocity is the vertical field `g(r) ∂_θ`, with contraction `ι ω = -g(r) dr`,
and since `φ_t` preserves `r` its flux form is exactly

`-g(r) dr` (`TauCeti.fluxForm_cylinderShearDiffeotopy_cylinderAreaForm`),

pulled back from the line along the proper projection `pr : ℝ × AddCircle p → ℝ`. For the
shear `(r, θ) ↦ (r, θ - t f(r - R))`, that is for `g(r) = -f(r - R)`, this is `f(r - R) dr`.

This example separates the two fluxes of a compactly supported symplectic isotopy:

* Every closed one-form on `ℝ` is exact, so the flux form is exact and the ordinary flux
  `Flux(φ) ∈ H¹_dR` vanishes for every `g`
  (`TauCeti.flux_cylinderShearDiffeotopy`).
* The compactly supported flux `Flux_c(φ) ∈ H¹_c` is minus the pullback along `pr` of the class
  of `g dr` in `H¹_c(ℝ)` (`TauCeti.compactFlux_cylinderShearDiffeotopy`). Integration identifies
  `H¹_c(ℝ)` with `ℝ`, and pullback along `pr` is injective, since `pr` has the proper section
  `r ↦ (r, 0)`. So the compactly supported flux depends exactly on `∫ g`: two shears have the
  same compactly supported flux exactly when the integrals of their functions agree
  (`TauCeti.compactFlux_cylinderShearDiffeotopy_eq_iff`), and it vanishes exactly when `∫ g = 0`
  (`TauCeti.compactFlux_cylinderShearDiffeotopy_eq_zero_iff`).

In particular, for `g(r) = -f(r - R)` with `∫ f = 1`, the compactly supported flux is nonzero and
does not depend on `R`, although the band carrying the isotopy moves off to infinity as `R` grows.
Vanishing of the ordinary flux is therefore a strictly weaker condition than vanishing of the
compactly supported flux.

The same shears show that the compactly supported flux is not continuous in the endpoint for the
weak Whitney `C^∞` topology of the ambient map space. As `R → ∞` the final maps of the shears
along `r ↦ -f(r - R)` converge to the identity in that topology
(`TauCeti.tendsto_final_cylinderShearDiffeotopy_of_apply_eq_sub`), while their compactly supported
fluxes stay equal to one nonzero class. So, for any `T₁` topology on `H¹_c`, no function of the
endpoint which agrees with the compactly supported flux on these shears and vanishes at the
identity is continuous at the identity
(`TauCeti.not_continuousWithinAt_of_eq_compactFlux_cylinderShearDiffeotopy`).

## Main results

* `TauCeti.fluxForm_cylinderShearDiffeotopy_cylinderAreaForm`: the flux form of the shear is
  `-g(r) dr`.
* `TauCeti.timeSlice_cylinderShearDiffeotopy_mem_diffeomorphStabilizer`: every map of the shear
  preserves `dr ∧ dθ`.
* `TauCeti.flux_cylinderShearDiffeotopy`: the flux of the shear vanishes.
* `TauCeti.compactFlux_cylinderShearDiffeotopy`: its compactly supported flux is the pullback of
  `-[g dr] ∈ H¹_c(ℝ)`.
* `TauCeti.compactFlux_cylinderShearDiffeotopy_eq_iff`,
  `TauCeti.compactFlux_cylinderShearDiffeotopy_eq_zero_iff`: the compactly supported flux is
  determined by `∫ g`, and vanishes exactly when `∫ g = 0`.
* `TauCeti.not_continuousWithinAt_of_eq_compactFlux_cylinderShearDiffeotopy`: the compactly
  supported flux, read as a function of the endpoint, is not continuous at the identity for the
  weak Whitney `C^∞` topology.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism on open manifolds, with compactly
  supported isotopies).
-/

public section

noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff

namespace TauCeti

variable (p : ℝ) [Fact (0 < p)]

/-! ### The shear diffeotopy preserves the area form -/

variable (g : C^∞⟮𝓘(ℝ), ℝ; ℝ⟯)

/-- **Shears are area preserving.** Every map `(r, θ) ↦ (r, θ + [t g(r)])` of the shear
diffeotopy preserves the area form `dr ∧ dθ`: its derivative is a unipotent shear matrix. -/
theorem timeSlice_cylinderShearDiffeotopy_mem_diffeomorphStabilizer (t : unitInterval) :
    (cylinderShearDiffeotopy p g).timeSlice t ∈
      SmoothForm.diffeomorphStabilizer (cylinderAreaForm p) := by
  have hslice : ⇑((cylinderShearDiffeotopy p g).timeSlice t) =
      fun y : ℝ × AddCircle p ↦ (y.1, y.2 + (((t : ℝ) * g y.1 : ℝ) : AddCircle p)) :=
    funext fun y ↦ (Diffeotopy.timeSlice_apply _ t y).trans (cylinderShearDiffeotopy_apply p g _)
  refine SmoothForm.mem_diffeomorphStabilizer_iff_forall.2 fun y ↦
    ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [TauCeti.mpullback_apply, hslice, cylinderAreaForm_apply, cylinderAreaForm_apply]
  simp only [mfderiv_cylinderShear_apply p _
    (((g.contMDiff.contDiff.differentiable (by simp)) _).const_mul _)]
  ring

/-- The final map of the shear diffeotopy preserves the closed area form `dr ∧ dθ`. -/
theorem final_cylinderShearDiffeotopy_mem_diffeomorphStabilizer :
    (cylinderShearDiffeotopy p g).final ∈
      SmoothForm.diffeomorphStabilizer (cylinderAreaClosedForm p).val := by
  rw [coe_cylinderAreaClosedForm, Diffeotopy.final_def]
  exact timeSlice_cylinderShearDiffeotopy_mem_diffeomorphStabilizer p g 1

/-! ### The flux form of a shear -/

/-- **The flux form of a shear.** For the area form `dr ∧ dθ`, the shear diffeotopy
`(r, θ) ↦ (r, θ + [t g(r)])` has flux form `-g(r) dr`, pulled back from the line. -/
theorem fluxForm_cylinderShearDiffeotopy_cylinderAreaForm :
    (cylinderShearDiffeotopy p g).fluxForm (cylinderAreaForm p) =
      -SmoothForm.mpullback Prod.fst contMDiff_fst
        (SmoothForm.funSMulₗ g SmoothForm.realLineCoordForm) := by
  refine Subtype.ext (funext fun y ↦ ?_)
  rw [Diffeotopy.fluxForm_apply]
  -- At every time the integrand is `-g(r) dr`: the velocity is `(0, g r)` and the spatial
  -- derivative preserves the `r`-component. The `show` states the type of the integrand, the
  -- alternating maps on the tangent space at `y`, which is by definition `ℝ × ℝ`.
  refine (intervalIntegral.integral_congr (g := fun _ ↦ show (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ from
      ((-SmoothForm.mpullback Prod.fst contMDiff_fst
        (SmoothForm.funSMulₗ g SmoothForm.realLineCoordForm) :
          SmoothForm (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × AddCircle p) ℝ 1)).val y)
    fun t _ ↦ ContinuousAlternatingMap.ext fun v ↦ ?_).trans ?_
  · rw [Diffeotopy.curryLeft_mfderiv_cylinderMap_apply, cylinderAreaForm_apply]
    simp only [mfderiv_cylinderMap_cylinderShearDiffeotopy_apply_one,
      mfderiv_cylinderMap_cylinderShearDiffeotopy_space, Fin.isValue, Matrix.cons_val,
      zero_mul, zero_sub, NegMemClass.coe_neg, Pi.neg_apply]
    have hR : (SmoothForm.mpullback Prod.fst contMDiff_fst
        (SmoothForm.funSMulₗ g SmoothForm.realLineCoordForm) :
          SmoothForm (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × AddCircle p) ℝ 1).val y v = g y.1 * (v 0).1 := by
      refine (SmoothForm.mpullback_fst_apply _ y v).trans ?_
      rw [SmoothForm.coe_funSMulₗ]
      simp only [ContinuousAlternatingMap.coe_smul, Pi.smul_apply,
        SmoothForm.realLineCoordForm_apply]
      -- The identification of the tangent space of the product with the product of the tangent
      -- spaces is the identity of `ℝ × ℝ`, and scalar multiplication on `ℝ` is multiplication.
      exact congrArg (fun a : ℝ × ℝ ↦ g y.1 * a.1)
        (Manifold.tangentSpaceProdEquiv_apply (I := 𝓘(ℝ)) (J := 𝓘(ℝ)) y (v 0))
    -- Negation of forms and of alternating maps is pointwise.
    exact (congrArg Neg.neg (hR.trans (mul_comm _ _))).symm
  · rw [intervalIntegral.integral_const, sub_zero, one_smul]

/-! ### Supports -/

/-- For compactly supported `g`, the flux form of the shear is compactly supported. -/
theorem fluxForm_cylinderShearDiffeotopy_mem_compactlySupportedForms (hgc : HasCompactSupport g) :
    (cylinderShearDiffeotopy p g).fluxForm (cylinderAreaClosedForm p).val ∈
      compactlySupportedForms (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × AddCircle p) 1 :=
  (cylinderShearDiffeotopy p g).fluxForm_mem_compactlySupportedForms _
    (hgc.isCompact.prod isCompact_univ) (cylinderShearDiffeotopy_eqOn_compl_tsupport p g)

/-! ### The two fluxes of a shear -/

/-- **The compactly supported flux of a shear.** For compactly supported `g`, the compactly
supported flux of the shear diffeotopy is minus the pullback along the projection to the line of
the class of `g dr` in `H¹_c(ℝ)`. -/
theorem compactFlux_cylinderShearDiffeotopy (hgc : HasCompactSupport g) :
    (cylinderShearDiffeotopy p g).compactFlux (cylinderAreaClosedForm p)
        (final_cylinderShearDiffeotopy_mem_diffeomorphStabilizer p g)
        (fluxForm_cylinderShearDiffeotopy_mem_compactlySupportedForms p g hgc) =
      -compactlySupportedDeRhamCohomology.map Prod.fst contMDiff_fst
        isProperMap_fst_of_compactSpace 1
        (compactlySupportedDeRhamCohomology.mk 𝓘(ℝ) 1
          ⟨_, funSMulₗ_realLineCoordForm_mem_compactlySupportedClosedForms hgc⟩) := by
  rw [Diffeotopy.compactFlux_def, compactlySupportedDeRhamCohomology.map_mk, ← map_neg]
  congr 1
  refine Subtype.ext ?_
  rw [Submodule.coe_neg, compactlySupportedClosedForms.coe_mpullback]
  simpa only [coe_cylinderAreaClosedForm] using
    fluxForm_cylinderShearDiffeotopy_cylinderAreaForm p g

/-- **The flux of a shear vanishes.** The ordinary flux of the shear diffeotopy in
`H¹_dR(ℝ × AddCircle p)` is zero: its flux form is pulled back from the line, on which every
closed one-form is exact. -/
theorem flux_cylinderShearDiffeotopy :
    (cylinderShearDiffeotopy p g).flux (cylinderAreaClosedForm p)
      (final_cylinderShearDiffeotopy_mem_diffeomorphStabilizer p g) = 0 := by
  rw [Diffeotopy.flux_def, deRhamCohomology.mk_eq_zero_iff]
  -- The form `g dr` is exact, by the Poincaré lemma on the line.
  have hexact : SmoothForm.funSMulₗ g SmoothForm.realLineCoordForm ∈
      exactForms 𝓘(ℝ) ℝ 1 := by
    rw [exactForms_succ_eq_closedForms_normedSpace (E := ℝ) (k := 0)]
    exact mem_closedForms_of_finrank_le 𝓘(ℝ) (by simp) _
  have hpull := closedForms.mpullback_mem_exactForms (I := 𝓘(ℝ).prod 𝓘(ℝ))
    (M := ℝ × AddCircle p) Prod.fst contMDiff_fst 1
    ⟨_, mem_closedForms_of_finrank_le 𝓘(ℝ) (by simp) _⟩ hexact
  rw [closedForms.coe_mpullback] at hpull
  simpa only [coe_cylinderAreaClosedForm, fluxForm_cylinderShearDiffeotopy_cylinderAreaForm]
    using neg_mem hpull

/-- Pullback along the projection of the cylinder to the line is injective on `H¹_c`: the proper
section `r ↦ (r, 0)` gives a left inverse. -/
private theorem injective_map_fst :
    Function.Injective (compactlySupportedDeRhamCohomology.map (I := 𝓘(ℝ).prod 𝓘(ℝ)) (I' := 𝓘(ℝ))
      (Prod.fst : ℝ × AddCircle p → ℝ) contMDiff_fst isProperMap_fst_of_compactSpace 1) :=
  compactlySupportedDeRhamCohomology.map_injective_of_leftInverse Prod.fst
    (fun r : ℝ ↦ (r, (0 : AddCircle p))) contMDiff_fst (contMDiff_id.prodMk contMDiff_const)
    isProperMap_fst_of_compactSpace
    (isProperMap_of_isClosedMap_of_inj (continuous_id.prodMk continuous_const)
      (Prod.mk_left_injective 0) (isClosedMap_prodMk_right 0))
    (fun _ ↦ rfl) 1

/-- **The compactly supported flux of a shear is determined by `∫ g`.** For compactly supported
`g` and `g'`, the shear diffeotopies along `g` and `g'` have the same compactly supported flux
exactly when `∫ g = ∫ g'`. -/
theorem compactFlux_cylinderShearDiffeotopy_eq_iff (g' : C^∞⟮𝓘(ℝ), ℝ; ℝ⟯)
    (hgc : HasCompactSupport g) (hgc' : HasCompactSupport g') :
    (cylinderShearDiffeotopy p g).compactFlux (cylinderAreaClosedForm p)
        (final_cylinderShearDiffeotopy_mem_diffeomorphStabilizer p g)
        (fluxForm_cylinderShearDiffeotopy_mem_compactlySupportedForms p g hgc) =
      (cylinderShearDiffeotopy p g').compactFlux (cylinderAreaClosedForm p)
        (final_cylinderShearDiffeotopy_mem_diffeomorphStabilizer p g')
        (fluxForm_cylinderShearDiffeotopy_mem_compactlySupportedForms p g' hgc') ↔
      ∫ r, g r = ∫ r, g' r := by
  rw [compactFlux_cylinderShearDiffeotopy p g hgc, compactFlux_cylinderShearDiffeotopy p g' hgc',
    neg_inj, (injective_map_fst p).eq_iff,
    (compactlySupportedDeRhamCohomology.bijective_integral_real
      Manifold.Orientation.real).injective.eq_iff.symm,
    compactlySupportedDeRhamCohomology.integral_mk_funSMulₗ_realLineCoordForm hgc,
    compactlySupportedDeRhamCohomology.integral_mk_funSMulₗ_realLineCoordForm hgc']

/-- **Nonvanishing of the compactly supported flux.** For compactly supported `g`, the shear
diffeotopy along `g` has zero compactly supported flux exactly when `∫ g = 0`, although its
ordinary flux always vanishes (`TauCeti.flux_cylinderShearDiffeotopy`). -/
theorem compactFlux_cylinderShearDiffeotopy_eq_zero_iff (hgc : HasCompactSupport g) :
    (cylinderShearDiffeotopy p g).compactFlux (cylinderAreaClosedForm p)
        (final_cylinderShearDiffeotopy_mem_diffeomorphStabilizer p g)
        (fluxForm_cylinderShearDiffeotopy_mem_compactlySupportedForms p g hgc) = 0 ↔
      ∫ r, g r = 0 := by
  rw [compactFlux_cylinderShearDiffeotopy p g hgc, neg_eq_zero,
    map_eq_zero_iff _ (injective_map_fst p),
    ← map_eq_zero_iff _ (compactlySupportedDeRhamCohomology.bijective_integral_real
      Manifold.Orientation.real).injective,
    compactlySupportedDeRhamCohomology.integral_mk_funSMulₗ_realLineCoordForm hgc]

/-! ### The compactly supported flux is not continuous in the endpoint -/

section Discontinuity

open Filter Topology
open scoped TauCeti.ManifoldWeakWhitney

/-- **The endpoint compactly supported flux is not weakly continuous.** Let `G i` be smooth
compactly supported functions with the same nonzero integral `c` which eventually vanish on each
bounded subset of `ℝ`, for instance the translates `r ↦ g (r - R)` of a compactly supported `g`
with `∫ g ≠ 0`, as `R → ∞`. The final maps `φ_i` of the shear diffeotopies along `G i` converge to
the identity in the weak Whitney `C^∞` topology
(`TauCeti.tendsto_timeSlice_cylinderShearDiffeotopy`), but their compactly supported fluxes are
all equal and nonzero. Hence, for any `T₁` topology on `H¹_c(ℝ × AddCircle p)`, a function `F` of
the endpoint which agrees with the compactly supported flux at every `φ_i` and vanishes at the
identity is not continuous at the identity, even within the set of the `φ_i`. -/
theorem not_continuousWithinAt_of_eq_compactFlux_cylinderShearDiffeotopy {ι : Type*}
    {l : Filter ι} [l.NeBot] {G : ι → C^∞⟮𝓘(ℝ), ℝ; ℝ⟯} (hGc : ∀ i, HasCompactSupport (G i))
    (hG : ∀ A : Set ℝ, Bornology.IsBounded A → ∀ᶠ i in l, ∀ r ∈ A, G i r = 0) {c : ℝ}
    (hc : c ≠ 0) (hint : ∀ i, ∫ r, G i r = c)
    [TopologicalSpace (compactlySupportedDeRhamCohomology (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × AddCircle p) 1)]
    [T1Space (compactlySupportedDeRhamCohomology (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × AddCircle p) 1)]
    (F : C^∞⟮𝓘(ℝ).prod 𝓘(ℝ), ℝ × AddCircle p; 𝓘(ℝ).prod 𝓘(ℝ), ℝ × AddCircle p⟯ →
      compactlySupportedDeRhamCohomology (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × AddCircle p) 1)
    (hF : ∀ i, F (cylinderShearDiffeotopy p (G i)).final.toContMDiffMap =
      (cylinderShearDiffeotopy p (G i)).compactFlux (cylinderAreaClosedForm p)
        (final_cylinderShearDiffeotopy_mem_diffeomorphStabilizer p (G i))
        (fluxForm_cylinderShearDiffeotopy_mem_compactlySupportedForms p (G i) (hGc i)))
    (hF₀ : F ContMDiffMap.id = 0) :
    ¬ ContinuousWithinAt F
      (range fun i ↦ (cylinderShearDiffeotopy p (G i)).final.toContMDiffMap) ContMDiffMap.id := by
  intro hF_cont
  obtain ⟨i₀⟩ := l.nonempty_of_neBot
  -- The endpoints converge to the identity from within their range.
  have hφ : Tendsto (fun i ↦ (cylinderShearDiffeotopy p (G i)).final.toContMDiffMap) l
      (𝓝[range fun i ↦ (cylinderShearDiffeotopy p (G i)).final.toContMDiffMap]
        ContMDiffMap.id) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun i ↦ mem_range_self i⟩
    simpa only [Diffeotopy.final_def] using tendsto_timeSlice_cylinderShearDiffeotopy p hG 1
  -- Equal integrals give equal compactly supported fluxes, so `F` is constant on the endpoints.
  have hconst : ∀ i, (F ∘ fun i ↦ (cylinderShearDiffeotopy p (G i)).final.toContMDiffMap) i =
      (cylinderShearDiffeotopy p (G i₀)).compactFlux (cylinderAreaClosedForm p)
        (final_cylinderShearDiffeotopy_mem_diffeomorphStabilizer p (G i₀))
        (fluxForm_cylinderShearDiffeotopy_mem_compactlySupportedForms p (G i₀) (hGc i₀)) :=
    fun i ↦ (hF i).trans ((compactFlux_cylinderShearDiffeotopy_eq_iff p (G i) (G i₀) (hGc i)
      (hGc i₀)).2 ((hint i).trans (hint i₀).symm))
  have h := hF_cont.tendsto.comp hφ
  rw [hF₀] at h
  exact hc ((hint i₀).symm.trans ((compactFlux_cylinderShearDiffeotopy_eq_zero_iff p (G i₀)
    (hGc i₀)).1 (tendsto_const_nhds_iff.1 (h.congr hconst))))

end Discontinuity

end TauCeti
