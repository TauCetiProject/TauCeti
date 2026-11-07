/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Bergman.Basic
public import TauCeti.Analysis.Complex.HolomorphicFunctions.Bounded
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Function.Lp.CastMeasure

/-!
# Compact restriction from Bergman spaces

Restriction from the native `L²` Bergman space to bounded holomorphic functions on a
relatively compact open set is continuous. For finite-dimensional values it is compact:
factor through an intermediate relatively compact open set and use native Montel compactness
for bounded holomorphic functions.

These are actual analytic bonding maps, rather than compactness assumptions on an abstract
cochain space. Finite-dimensional sheaf cohomology additionally needs the Čech comparison,
lifting and iteration arguments.
-/

public noncomputable section

open MeasureTheory Metric Set TopologicalSpace BoundedContinuousFunction
open scoped ENNReal

namespace TauCeti.BergmanSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
variable {U V W : Opens ℂ}

private def restrictBoundedAux (hV : IsCompact (closure (V : Set ℂ)))
    (hVU : closure (V : Set ℂ) ⊆ U) (u : bergmanSpace F U) :
    boundedHolomorphicFunctions F V :=
  BoundedHolomorphicFunctions.of V (representative u)
    ((differentiableOn_representative u).mono (subset_closure.trans hVU))
    (hV.image_of_continuousOn ((differentiableOn_representative u).continuousOn.mono hVU)
      |>.isBounded.exists_norm_le.choose)
    fun x hx ↦ hV.image_of_continuousOn
      ((differentiableOn_representative u).continuousOn.mono hVU)
      |>.isBounded.exists_norm_le.choose_spec _ ⟨x, subset_closure hx, rfl⟩

omit [CompleteSpace F] in
private theorem restrictBoundedAux_apply (hV : IsCompact (closure (V : Set ℂ)))
    (hVU : closure (V : Set ℂ) ⊆ U) (u : bergmanSpace F U) (x : V) :
    (restrictBoundedAux hV hVU u : V →ᵇ F) x = representative u x := by
  simp [restrictBoundedAux]

/-- Restrict a native Bergman class to bounded holomorphic functions on a relatively compact
open subset. The value is the unique holomorphic representative, independent of choices. -/
def restrictBounded (hV : IsCompact (closure (V : Set ℂ)))
    (hVU : closure (V : Set ℂ) ⊆ U) :
    bergmanSpace F U →L[ℂ] boundedHolomorphicFunctions F V := by
  let T : bergmanSpace F U →ₗ[ℂ] boundedHolomorphicFunctions F V :=
    { toFun := restrictBoundedAux hV hVU
      map_add' := fun u v ↦ Subtype.ext (BoundedContinuousFunction.ext fun x ↦ by
        simpa [restrictBoundedAux_apply] using
          representative_add u v (hVU (subset_closure x.property)))
      map_smul' := fun c u ↦ Subtype.ext (BoundedContinuousFunction.ext fun x ↦ by
        simpa [restrictBoundedAux_apply] using
          representative_smul c u (hVU (subset_closure x.property))) }
  let C := (exists_norm_representative_le (F := F) hV hVU).choose
  have hC := (exists_norm_representative_le (F := F) hV hVU).choose_spec
  refine T.mkContinuous C fun u ↦ (BoundedContinuousFunction.norm_le
    (mul_nonneg hC.1 (norm_nonneg u))).2 fun x ↦ ?_
  simpa [T, restrictBoundedAux_apply] using hC.2 u x (subset_closure x.property)

@[simp]
theorem restrictBounded_apply (hV : IsCompact (closure (V : Set ℂ)))
    (hVU : closure (V : Set ℂ) ⊆ U) (u : bergmanSpace F U) (x : V) :
    (restrictBounded hV hVU u : V →ᵇ F) x = representative u x := by
  simp [restrictBounded, restrictBoundedAux_apply]

/-- Restriction through a further bounded-holomorphic stage agrees with direct restriction. -/
theorem restrict_comp_restrictBounded (hW : IsCompact (closure (W : Set ℂ)))
    (hWU : closure (W : Set ℂ) ⊆ U) (hV : IsCompact (closure (V : Set ℂ)))
    (hVW : closure (V : Set ℂ) ⊆ W) :
    (BoundedHolomorphicFunctions.restrict (subset_closure.trans hVW)).comp
      (restrictBounded (F := F) hW hWU) =
        restrictBounded hV (hVW.trans (subset_closure.trans hWU)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  exact (BoundedHolomorphicFunctions.restrict_apply (subset_closure.trans hVW)
    (restrictBounded hW hWU u) x).trans ((restrictBounded_apply hW hWU u _).trans
      (restrictBounded_apply hV _ u x).symm)

/-- For proper (in particular, finite-dimensional) values, Bergman restriction to a
relatively compact open set is compact. -/
theorem isCompactOperator_restrictBounded [ProperSpace F]
    (hV : IsCompact (closure (V : Set ℂ))) (hVU : closure (V : Set ℂ) ⊆ U) :
    IsCompactOperator (restrictBounded (F := F) hV hVU) := by
  obtain ⟨r, hr, hrU⟩ := hV.exists_cthickening_subset_open U.isOpen hVU
  let W : Opens ℂ := ⟨thickening r (closure (V : Set ℂ)), isOpen_thickening⟩
  have hW : IsCompact (closure (W : Set ℂ)) :=
    hV.cthickening.of_isClosed_subset isClosed_closure (closure_thickening_subset_cthickening _ _)
  have hWU : closure (W : Set ℂ) ⊆ U :=
    (closure_thickening_subset_cthickening _ _).trans hrU
  have hVW : closure (V : Set ℂ) ⊆ W := self_subset_thickening hr _
  have hcompact := BoundedHolomorphicFunctions.isCompactOperator_restrict_of_isCompact_closure
    (E := F) hV hVW
  have heq := restrict_comp_restrictBounded (F := F) hW hWU hV hVW
  rw [← heq]
  exact hcompact.comp_clm (restrictBounded hW hWU)

section Inclusion

omit [CompleteSpace F]

/-- On a finite-measure open set, bounded holomorphic functions define native Bergman classes. -/
def ofBounded [IsFiniteMeasure (volume.restrict (V : Set ℂ))] :
    boundedHolomorphicFunctions F V →L[ℂ] bergmanSpace F V := by
  let T : boundedHolomorphicFunctions F V →ₗ[ℂ] bergmanSpace F V :=
    { toFun := fun f ↦ ⟨(BoundedHolomorphicFunctions.memLp_extend (μ := volume) 2 f).toLp _,
        (mem_bergmanSpace_iff F V).2 ⟨
        BoundedHolomorphicFunctions.extend f,
        BoundedHolomorphicFunctions.differentiableOn_extend f, MemLp.coeFn_toLp _⟩⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        simp only [Submodule.coe_add]
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
        exact (BoundedHolomorphicFunctions.extend_apply (f + g) ⟨x, hx⟩).trans
          (by simp [← BoundedHolomorphicFunctions.extend_apply f ⟨x, hx⟩,
            ← BoundedHolomorphicFunctions.extend_apply g ⟨x, hx⟩])
      map_smul' := by
        intro c f
        apply Subtype.ext
        simp only [Submodule.coe_smul]
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
        exact (BoundedHolomorphicFunctions.extend_apply (c • f) ⟨x, hx⟩).trans
          (by simp [← BoundedHolomorphicFunctions.extend_apply f ⟨x, hx⟩]) }
  refine T.mkContinuous ((measureUnivNNReal (volume.restrict (V : Set ℂ))) ^
    (2 : ℝ≥0∞).toReal⁻¹) fun f ↦ ?_
  -- Expose the native `L²` class constructed by the linear map before applying its norm bound.
  change ‖(BoundedHolomorphicFunctions.memLp_extend (μ := volume) 2 f).toLp _‖ ≤ _
  exact Lp.norm_le_of_ae_bound (norm_nonneg f)
    ((MemLp.coeFn_toLp
      (BoundedHolomorphicFunctions.memLp_extend (μ := volume) 2 f)).mono fun x hx ↦ by
      rw [hx]
      exact BoundedHolomorphicFunctions.norm_extend_apply_le f x)

/-- The inclusion from the supremum norm to `L²` has the explicit finite-measure bound. -/
theorem norm_ofBounded_le [IsFiniteMeasure (volume.restrict (V : Set ℂ))] :
    ‖ofBounded (F := F) (V := V)‖ ≤
      (measureUnivNNReal (volume.restrict (V : Set ℂ))) ^ (2 : ℝ≥0∞).toReal⁻¹ := by
  unfold ofBounded
  apply LinearMap.mkContinuous_norm_le
  positivity

/-- The inclusion into Bergman space preserves the holomorphic representative almost everywhere. -/
theorem coeFn_ofBounded [IsFiniteMeasure (volume.restrict (V : Set ℂ))]
    (f : boundedHolomorphicFunctions F V) :
    (ofBounded f : Lp F 2 (volume.restrict (V : Set ℂ))) =ᵐ[volume.restrict (V : Set ℂ)]
      BoundedHolomorphicFunctions.extend f := by
  simp only [ofBounded, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact MemLp.coeFn_toLp (BoundedHolomorphicFunctions.memLp_extend (μ := volume) 2 f)


/-- Restriction of native Bergman classes along any inclusion of open sets. It is the native
`L²` restriction, and does not require compactness, finite measure or complete values. -/
def restrict (hVU : V ≤ U) : bergmanSpace F U →L[ℂ] bergmanSpace F V := by
  have hμ : (volume.restrict (U : Set ℂ)).restrict (V : Set ℂ) =
      volume.restrict (V : Set ℂ) :=
    Measure.restrict_restrict_of_subset (SetLike.coe_subset_coe.mpr hVU)
  let L : Lp F 2 (volume.restrict (U : Set ℂ)) →L[ℂ]
      Lp F 2 (volume.restrict (V : Set ℂ)) :=
    (castLpₗᵢ (𝕜 := ℂ) hμ).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (MeasureTheory.LpToLpRestrictCLM ℂ F ℂ (volume.restrict (U : Set ℂ)) 2 (V : Set ℂ))
  refine ContinuousLinearMap.codRestrict (L.comp (bergmanSpace F U).subtypeL)
    (bergmanSpace F V) fun u ↦ (mem_bergmanSpace_iff F V).mpr
      ⟨representative u,
        (differentiableOn_representative u).mono (SetLike.coe_subset_coe.mpr hVU), ?_⟩
  have hL : L u.val =ᵐ[volume.restrict (V : Set ℂ)] u.val := by
    have h := MeasureTheory.LpToLpRestrictCLM_coeFn
      (μ := volume.restrict (U : Set ℂ)) ℂ (V : Set ℂ) u.val
    have h := h.filter_mono (ae_mono hμ.ge)
    filter_upwards [h] with x hx
    simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, coeFn_castLpₗᵢ] using hx
  exact hL.trans ((coeFn_ae_eq_representative u).filter_mono
    (ae_mono (Measure.restrict_mono_set volume (SetLike.coe_subset_coe.mpr hVU))))

/-- Restriction preserves the original `L²` representative on the smaller open set. -/
theorem coeFn_restrict (hVU : V ≤ U) (u : bergmanSpace F U) :
    (restrict hVU u : Lp F 2 (volume.restrict (V : Set ℂ))) =ᵐ[volume.restrict (V : Set ℂ)]
      (u : Lp F 2 (volume.restrict (U : Set ℂ))) := by
  have h := MeasureTheory.LpToLpRestrictCLM_coeFn (μ := volume.restrict (U : Set ℂ))
    ℂ (V : Set ℂ) u.val
  have h := h.filter_mono (ae_mono
    (Measure.restrict_restrict_of_subset (SetLike.coe_subset_coe.mpr hVU)).ge)
  filter_upwards [h] with x hx
  simpa only [restrict, ContinuousLinearMap.coe_codRestrict_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, coeFn_castLpₗᵢ] using hx

/-- Restriction does not increase the actual Bergman `L²` norm. -/
theorem norm_restrict_apply_le (hVU : V ≤ U) (u : bergmanSpace F U) :
    ‖restrict hVU u‖ ≤ ‖u‖ := by
  rw [← Submodule.norm_coe (restrict hVU u), ← Submodule.norm_coe u]
  simpa only [restrict, ContinuousLinearMap.coe_codRestrict_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map,
    MeasureTheory.LpToLpRestrictCLM, LinearMap.mkContinuous_apply,
    LinearMap.coe_mk, AddHom.coe_mk] using
      (MeasureTheory.norm_Lp_toLp_restrict_le (μ := volume.restrict (U : Set ℂ)) (V : Set ℂ) u.val)

/-- Bergman restriction is a contraction. -/
theorem norm_restrict_le (hVU : V ≤ U) : ‖restrict (F := F) hVU‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa only [one_mul] using norm_restrict_apply_le hVU u

/-- The holomorphic representative of a restriction agrees on its open set with the original
representative. Thus restriction is independent of every representative choice. -/
@[simp]
theorem representative_restrict (hVU : V ≤ U) (u : bergmanSpace F U) {x : ℂ} (hx : x ∈ V) :
    representative (restrict hVU u) x = representative u x :=
  eqOn_representative ((differentiableOn_representative u).mono (SetLike.coe_subset_coe.mpr hVU))
    ((coeFn_restrict hVU u).trans ((coeFn_ae_eq_representative u).filter_mono
      (ae_mono (Measure.restrict_mono_set volume (SetLike.coe_subset_coe.mpr hVU))))) hx

@[simp]
theorem representative_ofBounded [IsFiniteMeasure (volume.restrict (V : Set ℂ))]
    (f : boundedHolomorphicFunctions F V) {x : ℂ} (hx : x ∈ V) :
    representative (ofBounded f) x = BoundedHolomorphicFunctions.extend f x :=
  eqOn_representative (BoundedHolomorphicFunctions.differentiableOn_extend f)
    (coeFn_ofBounded f) hx

/-- Restriction to the same open set is the identity. -/
@[simp]
theorem restrict_refl : restrict (F := F) (le_refl U) = ContinuousLinearMap.id ℂ _ := by
  ext u x hx
  exact representative_restrict _ _ hx

/-- Successive Bergman restrictions agree with direct restriction. -/
theorem restrict_comp_restrict (hVU : V ≤ U) (hWV : W ≤ V) :
    (restrict (F := F) hWV).comp (restrict hVU) = restrict (hWV.trans hVU) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext
  intro x hx
  simp only [ContinuousLinearMap.comp_apply, representative_restrict hWV _ hx,
    representative_restrict hVU _ (hWV hx), representative_restrict (hWV.trans hVU) _ hx]

end Inclusion

/-- Relatively compact Bergman restriction factors through the native bounded-holomorphic
stage, identifying the analytic bonding map used in the compactness argument. -/
theorem ofBounded_comp_restrictBounded (hV : IsCompact (closure (V : Set ℂ)))
    (hVU : closure (V : Set ℂ) ⊆ U)
    [IsFiniteMeasure (volume.restrict (V : Set ℂ))] :
    (ofBounded (F := F) (V := V)).comp (restrictBounded hV hVU) =
      restrict (SetLike.coe_subset_coe.mp (subset_closure.trans hVU)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply Lp.ext
  simp only [ContinuousLinearMap.comp_apply]
  filter_upwards [coeFn_ofBounded (restrictBounded hV hVU u),
    coeFn_ae_eq_representative (restrict (SetLike.coe_subset_coe.mp (subset_closure.trans hVU)) u),
    ae_restrict_mem V.isOpen.measurableSet] with x h1 h2 hx
  rw [h1, h2, representative_restrict _ _ hx,
    BoundedHolomorphicFunctions.extend_apply _ ⟨x, hx⟩, restrictBounded_apply]

/-- Bergman restriction is compact for proper, in particular finite-dimensional, values. -/
theorem isCompactOperator_restrict [ProperSpace F]
    (hV : IsCompact (closure (V : Set ℂ))) (hVU : closure (V : Set ℂ) ⊆ U) :
    IsCompactOperator
      (restrict (F := F) (SetLike.coe_subset_coe.mp (subset_closure.trans hVU))) := by
  let : IsFiniteMeasure (volume.restrict (V : Set ℂ)) :=
    isFiniteMeasure_restrict.2 ((measure_mono subset_closure).trans_lt hV.measure_lt_top).ne
  rw [← ofBounded_comp_restrictBounded hV hVU]
  exact (isCompactOperator_restrictBounded (F := F) hV hVU).clm_comp ofBounded

end TauCeti.BergmanSpace
