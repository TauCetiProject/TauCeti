/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.CylinderShear
public import TauCeti.Geometry.Manifold.DeRham.Integration.Surjective
public import TauCeti.Geometry.Manifold.DeRham.NormedSpace
public import TauCeti.Geometry.Manifold.DifferentialForm.AddCircle
public import TauCeti.Geometry.Symplectic.Flux.CompactSupport
import TauCeti.Geometry.Manifold.DeRham.RealLine

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

## Main definitions

* `TauCeti.cylinderAreaForm p`: the area form `dr ∧ dθ` of `ℝ × AddCircle p`.
* `TauCeti.cylinderAreaClosedForm p`: the same form, bundled as a closed form.

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

/-! ### The area form of the cylinder -/

/-- The **area form** `dr ∧ dθ` of the cylinder `ℝ × AddCircle p`: the wedge of the coordinate
form of the line with the time form of the circle. -/
def cylinderAreaForm : SmoothForm (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × AddCircle p) ℝ 2 :=
  SmoothForm.wedge (SmoothForm.mpullback Prod.fst contMDiff_fst SmoothForm.realLineCoordForm)
    (SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm p))

/-- The area form `dr ∧ dθ` evaluates as the determinant of the two tangent vectors. -/
theorem eval₂_cylinderAreaForm (y : ℝ × AddCircle p) (v w : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) y) :
    SmoothBundleForm.eval₂ (cylinderAreaForm p) y v w = v.1 * w.2 - w.1 * v.2 := by
  simp only [cylinderAreaForm, SmoothForm.eval₂_wedge_one_one, SmoothForm.mpullback_fst_apply,
    SmoothForm.mpullback_snd_apply, AddCircle.timeForm_apply, SmoothForm.realLineCoordForm_apply,
    Manifold.tangentSpaceProdEquiv_apply, Matrix.cons_val_zero]

/-- The area form `dr ∧ dθ` on a pair of tangent vectors, given as a family indexed by `Fin 2`. -/
theorem cylinderAreaForm_apply (y : ℝ × AddCircle p)
    (v : Fin 2 → TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) y) :
    (cylinderAreaForm p).1 y v = (v 0).1 * (v 1).2 - (v 1).1 * (v 0).2 := by
  have hv : v = ![v 0, v 1] := funext fun i ↦ by fin_cases i <;> rfl
  calc (cylinderAreaForm p).1 y v = (cylinderAreaForm p).1 y ![v 0, v 1] := congrArg _ hv
    _ = _ := (SmoothBundleForm.eval₂_apply _ y (v 0) (v 1)).symm.trans
      (eval₂_cylinderAreaForm p y (v 0) (v 1))

/-- The area form of the cylinder is closed, as is every two-form on a surface. -/
theorem isClosed_cylinderAreaForm : (cylinderAreaForm p).IsClosed := by
  rw [SmoothForm.isClosed_def, ← mextDerivₗ_apply]
  exact congrArg Subtype.val (SmoothForm.eq_zero_of_finrank_lt (by simp) _)

/-- The area form `dr ∧ dθ` of the cylinder, as a closed form. -/
def cylinderAreaClosedForm : closedForms (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × AddCircle p) 2 :=
  ⟨cylinderAreaForm p, (mem_closedForms _ _).mpr
    ((SmoothForm.isClosed_def _).mp (isClosed_cylinderAreaForm p))⟩

/-- The underlying form of the closed area form is `dr ∧ dθ`. -/
@[simp]
theorem coe_cylinderAreaClosedForm : (cylinderAreaClosedForm p).1 = cylinderAreaForm p :=
  (rfl)

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
  simp only [mfderiv_cylinderShear_apply p
    (contDiff_const.mul (g.contMDiff.contDiff.of_le (by simp)))]
  ring

/-- The final map of the shear diffeotopy preserves the closed area form `dr ∧ dθ`. -/
theorem final_cylinderShearDiffeotopy_mem_diffeomorphStabilizer :
    (cylinderShearDiffeotopy p g).final ∈
      SmoothForm.diffeomorphStabilizer (cylinderAreaClosedForm p).1 := by
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
  -- derivative preserves the `r`-component.
  refine (intervalIntegral.integral_congr (g := fun _ ↦ show (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ from
      ((-SmoothForm.mpullback Prod.fst contMDiff_fst
        (SmoothForm.funSMulₗ g SmoothForm.realLineCoordForm) :
          SmoothForm (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × AddCircle p) ℝ 1)).1 y)
    fun t _ ↦ ContinuousAlternatingMap.ext fun v ↦ ?_).trans ?_
  · rw [Diffeotopy.curryLeft_mfderiv_cylinderMap_apply, cylinderAreaForm_apply]
    simp only [mfderiv_cylinderMap_cylinderShearDiffeotopy_apply_one,
      mfderiv_cylinderMap_cylinderShearDiffeotopy_apply_zero, Fin.isValue, Matrix.cons_val,
      zero_mul, zero_sub, NegMemClass.coe_neg, Pi.neg_apply]
    have hR : (SmoothForm.mpullback Prod.fst contMDiff_fst
        (SmoothForm.funSMulₗ g SmoothForm.realLineCoordForm) :
          SmoothForm (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × AddCircle p) ℝ 1).1 y v = g y.1 * (v 0).1 := by
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

/-- The shear by a compactly supported `g` is the identity outside the compact band
`tsupport g × AddCircle p`. -/
theorem cylinderShearDiffeotopy_eqOn_compl_tsupport (t : unitInterval) :
    EqOn (fun y ↦ cylinderShearDiffeotopy p g (t, y)) id
      (tsupport g ×ˢ (univ : Set (AddCircle p)))ᶜ :=
  cylinderShearDiffeotopy_eqOn_compl p g (fun _ hr ↦ image_eq_zero_of_notMem_tsupport hr) t

/-- For compactly supported `g`, the flux form of the shear is compactly supported. -/
theorem fluxForm_cylinderShearDiffeotopy_mem_compactlySupportedForms (hgc : HasCompactSupport g) :
    (cylinderShearDiffeotopy p g).fluxForm (cylinderAreaClosedForm p).1 ∈
      compactlySupportedForms (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × AddCircle p) 1 :=
  (cylinderShearDiffeotopy p g).fluxForm_mem_compactlySupportedForms _
    (hgc.isCompact.prod isCompact_univ) (cylinderShearDiffeotopy_eqOn_compl_tsupport p g)

/-- For compactly supported `g`, the one-form `g dr` of the line is compactly supported and
closed. -/
theorem funSMulₗ_realLineCoordForm_mem_compactlySupportedClosedForms
    (hgc : HasCompactSupport g) :
    SmoothForm.funSMulₗ g SmoothForm.realLineCoordForm ∈
      compactlySupportedClosedForms 𝓘(ℝ) ℝ 1 := by
  refine (mem_compactlySupportedClosedForms _).mpr ⟨(mem_compactlySupportedForms _).mpr ?_,
    mem_closedForms_of_finrank_le 𝓘(ℝ) (by simp) _⟩
  rw [SmoothForm.coe_funSMulₗ]
  exact hgc.isCompact.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _ _)

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
          ⟨_, funSMulₗ_realLineCoordForm_mem_compactlySupportedClosedForms g hgc⟩) := by
  rw [Diffeotopy.compactFlux_def, compactlySupportedDeRhamCohomology.map_mk, ← map_neg]
  congr 1
  refine Subtype.ext ?_
  rw [Submodule.coe_neg, compactlySupportedClosedForms.coe_mpullback]
  exact fluxForm_cylinderShearDiffeotopy_cylinderAreaForm p g

/-- **The flux of a shear vanishes.** For compactly supported `g`, the ordinary flux of the shear
diffeotopy in `H¹_dR(ℝ × AddCircle p)` is zero: its flux form is pulled back from the line, on
which every closed one-form is exact. -/
theorem flux_cylinderShearDiffeotopy (hgc : HasCompactSupport g) :
    (cylinderShearDiffeotopy p g).flux (cylinderAreaClosedForm p)
      (final_cylinderShearDiffeotopy_mem_diffeomorphStabilizer p g) = 0 := by
  rw [← Diffeotopy.toDeRhamCohomology_compactFlux _ _ _
      (fluxForm_cylinderShearDiffeotopy_mem_compactlySupportedForms p g hgc),
    compactFlux_cylinderShearDiffeotopy p g hgc, map_neg,
    compactlySupportedDeRhamCohomology.toDeRhamCohomology_map,
    compactlySupportedDeRhamCohomology.toDeRhamCohomology_mk, neg_eq_zero]
  -- The class of `g dr` vanishes in `H¹_dR(ℝ)`, by the Poincaré lemma on the line.
  have hexact : SmoothForm.funSMulₗ g SmoothForm.realLineCoordForm ∈
      exactForms 𝓘(ℝ) ℝ 1 := by
    rw [exactForms_succ_eq_closedForms_normedSpace (E := ℝ) (k := 0)]
    exact mem_closedForms_of_finrank_le 𝓘(ℝ) (by simp) _
  rw [(deRhamCohomology.mk_eq_zero_iff 𝓘(ℝ) 1 _).mpr hexact, map_zero]

omit [Fact (0 < p)] in
/-- The section `r ↦ (r, 0)` of the projection of the cylinder to the line is proper. -/
private theorem isProperMap_prodMk_zero :
    IsProperMap (fun r : ℝ ↦ (r, (0 : AddCircle p))) := by
  refine IsClosedEmbedding.isProperMap ⟨isEmbedding_prodMkLeft (0 : AddCircle p), ?_⟩
  have : range (fun r : ℝ ↦ (r, (0 : AddCircle p))) = univ ×ˢ {0} := by
    ext ⟨r, θ⟩
    simp [eq_comm]
  rw [this]
  exact isClosed_univ.prod isClosed_singleton

/-- Pullback along the projection of the cylinder to the line is injective on `H¹_c`: the proper
section `r ↦ (r, 0)` gives a left inverse. -/
private theorem injective_map_fst :
    Function.Injective (compactlySupportedDeRhamCohomology.map (I := 𝓘(ℝ).prod 𝓘(ℝ)) (I' := 𝓘(ℝ))
      (Prod.fst : ℝ × AddCircle p → ℝ) contMDiff_fst isProperMap_fst_of_compactSpace 1) := by
  have h := compactlySupportedDeRhamCohomology.map_comp (I := 𝓘(ℝ)) (I' := 𝓘(ℝ).prod 𝓘(ℝ))
    (I'' := 𝓘(ℝ)) (fun r : ℝ ↦ (r, (0 : AddCircle p)))
    Prod.fst (contMDiff_id.prodMk contMDiff_const) contMDiff_fst (isProperMap_prodMk_zero p)
    isProperMap_fst_of_compactSpace 1
  refine Function.LeftInverse.injective (g := compactlySupportedDeRhamCohomology.map
    (fun r : ℝ ↦ (r, (0 : AddCircle p))) (contMDiff_id.prodMk contMDiff_const)
    (isProperMap_prodMk_zero p) 1) fun c ↦ ?_
  rw [← LinearMap.comp_apply, ← h]
  -- The composite `r ↦ (r, 0) ↦ r` is the identity, by definition.
  exact LinearMap.congr_fun (compactlySupportedDeRhamCohomology.map_id 1) c

/-- The integral of the class of `g dr` in `H¹_c(ℝ)` is `∫ g`. -/
private theorem integral_mk_funSMulₗ_realLineCoordForm (hgc : HasCompactSupport g) :
    compactlySupportedDeRhamCohomology.integral Manifold.Orientation.real
        (compactlySupportedDeRhamCohomology.mk 𝓘(ℝ) 1
          ⟨_, funSMulₗ_realLineCoordForm_mem_compactlySupportedClosedForms g hgc⟩) =
      ∫ r, g r := by
  rw [compactlySupportedDeRhamCohomology.integral_mk, integralTopForm_real_eq_integral
    (SmoothForm.isSmoothForm _ |>.of_le (by simp)) ((mem_compactlySupportedForms _).mp
      ((mem_compactlySupportedClosedForms _).mp
        (funSMulₗ_realLineCoordForm_mem_compactlySupportedClosedForms g hgc)).1)]
  simp only [SmoothForm.coe_funSMulₗ, ContinuousAlternatingMap.coe_smul, Pi.smul_apply,
    SmoothForm.realLineCoordForm_apply]
  -- The value of `g dr` on the unit vector `1` is `g r • 1 = g r`.
  exact congrArg (fun f : ℝ → ℝ ↦ ∫ r, f r) (funext fun r ↦ mul_one (g r))

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
    integral_mk_funSMulₗ_realLineCoordForm g hgc, integral_mk_funSMulₗ_realLineCoordForm g' hgc']

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
    integral_mk_funSMulₗ_realLineCoordForm g hgc]

end TauCeti
