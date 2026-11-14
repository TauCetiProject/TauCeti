/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Connection
public import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Acceleration
public import Mathlib.Geometry.Manifold.Riemannian.PathELength
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Integrability
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Hom

/-!
# Curves and covariant differentiation along curves under Riemannian submersions

For a Riemannian submersion `f : M → N`, the differential at every point is norm-decreasing and
restricts to a linear isometry on the horizontal space `(mfderiv I J f x).kerᗮ`. Consequently,
projecting a differentiable curve does not increase its speed or its `Manifold.pathELength`, and a
curve is horizontal precisely when its velocity is the horizontal lift of the projected velocity
(equivalently, when projection preserves its speed).

For a differentiable tangent field `U` along the projected curve `f ∘ γ`, lifting `U` horizontally
along `γ` preserves differentiability in local bundle coordinates. At any parameter where `γ` has
horizontal velocity, the Levi-Civita covariant derivative of the lifted field along `γ` projects to
the base covariant derivative of `U` along `f ∘ γ` (`mfderiv_alongCurveWithin_horizontalLift`). On
smooth Riemannian manifolds, its vertical part is given by O'Neill's horizontal fundamental tensor
`oneillA`, yielding the full decomposition

`D_t (horizontalLift U) = horizontalLift (D_t U) + A_{γ'}(horizontalLift U)`

(`alongCurveWithin_horizontalLift`). Since `oneillA` is alternating on horizontal vectors,
specializing to the velocity field of a `C²` horizontal curve shows that its total-space covariant
acceleration is the horizontal lift of the projected curve's acceleration
(`accelerationWithin_eq_horizontalLift`).

All curve identities are stated within an arbitrary parameter set `s : Set ℝ`, so they apply to
closed intervals as well as open intervals and the whole real line. Neither completeness nor
surjectivity of the submersion is required.

## Main results

* `TauCeti.IsRiemannianSubmersion.curveVelocityWithin_eq_horizontalLift_iff`,
  `TauCeti.IsRiemannianSubmersion.norm_curveVelocityWithin_comp_le`,
  `TauCeti.IsRiemannianSubmersion.norm_curveVelocityWithin_comp_eq_iff`: velocity comparison and
  characterizations of horizontal velocity.
* `TauCeti.IsRiemannianSubmersion.pathELength_comp_le`,
  `TauCeti.IsRiemannianSubmersion.pathELength_comp_eq_of_mem_orthogonal_ker`: Riemannian path
  length decreases under projection and is preserved for horizontal curves.
* `TauCeti.IsRiemannianSubmersion.differentiableWithinAt_sectionCoord_horizontalLift`: horizontal
  lifting along a curve preserves differentiability in local bundle coordinates.
* `TauCeti.IsRiemannianSubmersion.mfderiv_alongCurveWithin_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.starProjection_alongCurveWithin_horizontalLift`: horizontal
  component of the along-curve Levi-Civita derivative of a lifted field at a horizontal velocity.
* `TauCeti.IsRiemannianSubmersion.alongCurveWithin_horizontalLift`: full along-curve derivative of
  a lifted field in terms of the lifted base derivative and `oneillA`.
* `TauCeti.IsRiemannianSubmersion.accelerationWithin_eq_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.accelerationWithin_eq_zero_iff_comp`: covariant acceleration of
  a horizontal `C²` curve is the horizontal lift of the base acceleration.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966), 459–469,
  Lemma 1 and Corollary 1.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 2, Proposition 2.2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 5.
-/

public section

open Bundle CovariantDerivative Filter Manifold Set
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

open TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)

include h

/-! ### Velocity and path length -/

section Velocity

open scoped ENNReal

variable {γ : ℝ → M} {s : Set ℝ} {t : ℝ}

/-- Along a curve differentiable within `s` at `t` with unique derivatives, the velocity is the
horizontal lift of the projected velocity if and only if it is horizontal. -/
theorem curveVelocityWithin_eq_horizontalLift_iff (hs : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t) :
    curveVelocityWithin I γ s t =
        h.horizontalLift (γ t) (curveVelocityWithin J (f ∘ γ) s t) ↔
      curveVelocityWithin I γ s t ∈ (mfderiv I J f (γ t)).kerᗮ := by
  have hf : MDifferentiableAt I J f (γ t) :=
    h.isSubmersion.contMDiff.mdifferentiableAt (by simp)
  rw [curveVelocityWithin_map hf hs hγ, h.eq_horizontalLift_iff, and_iff_left rfl]

/-- Along a curve differentiable at `t`, the velocity is the horizontal lift of the projected
velocity if and only if it is horizontal. -/
theorem curveVelocity_eq_horizontalLift_iff (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    curveVelocity I γ t = h.horizontalLift (γ t) (curveVelocity J (f ∘ γ) t) ↔
      curveVelocity I γ t ∈ (mfderiv I J f (γ t)).kerᗮ := by
  simpa only [curveVelocityWithin_univ] using
    h.curveVelocityWithin_eq_horizontalLift_iff uniqueDiffWithinAt_univ hγ.mdifferentiableWithinAt

/-- Projecting a differentiable curve through a Riemannian submersion does not increase the norm
of its velocity within `s`. -/
theorem norm_curveVelocityWithin_comp_le (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t) :
    ‖curveVelocityWithin J (f ∘ γ) s t‖ ≤ ‖curveVelocityWithin I γ s t‖ := by
  by_cases hs : UniqueDiffWithinAt ℝ s t
  · rw [curveVelocityWithin_map (h.isSubmersion.contMDiff.mdifferentiableAt (by simp)) hs hγ]
    exact h.norm_mfderiv_le (γ t) _
  · simp [curveVelocityWithin_eq_zero_of_not_uniqueDiffWithinAt hs]

/-- Projecting a differentiable curve through a Riemannian submersion does not increase its
speed. -/
theorem norm_curveVelocity_comp_le (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    ‖curveVelocity J (f ∘ γ) t‖ ≤ ‖curveVelocity I γ t‖ := by
  simpa only [curveVelocityWithin_univ] using
    h.norm_curveVelocityWithin_comp_le (s := Set.univ) hγ.mdifferentiableWithinAt

/-- With unique derivatives, the projected velocity has the same norm as the source velocity if
and only if the source velocity is horizontal. -/
theorem norm_curveVelocityWithin_comp_eq_iff (hs : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t) :
    ‖curveVelocityWithin J (f ∘ γ) s t‖ = ‖curveVelocityWithin I γ s t‖ ↔
      curveVelocityWithin I γ s t ∈ (mfderiv I J f (γ t)).kerᗮ := by
  rw [curveVelocityWithin_map (h.isSubmersion.contMDiff.mdifferentiableAt (by simp)) hs hγ]
  exact h.norm_mfderiv_eq_iff (γ t) _

/-- A differentiable curve has the same speed as its projection if and only if its velocity is
horizontal. -/
theorem norm_curveVelocity_comp_eq_iff (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    ‖curveVelocity J (f ∘ γ) t‖ = ‖curveVelocity I γ t‖ ↔
      curveVelocity I γ t ∈ (mfderiv I J f (γ t)).kerᗮ := by
  simpa only [curveVelocityWithin_univ] using
    h.norm_curveVelocityWithin_comp_eq_iff uniqueDiffWithinAt_univ hγ.mdifferentiableWithinAt

/-- Projecting a curve differentiable on `(a, b)` through a Riemannian submersion does not
increase its Riemannian path length on `[a, b]`. -/
theorem pathELength_comp_le {a b : ℝ} (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ (Ioo a b)) :
    Manifold.pathELength J (f ∘ γ) a b ≤ Manifold.pathELength I γ a b := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo, Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  refine MeasureTheory.lintegral_mono_ae
    ((MeasureTheory.ae_restrict_mem measurableSet_Ioo).mono fun r hr ↦ ?_)
  have hγr : MDifferentiableAt 𝓘(ℝ, ℝ) I γ r :=
    (hγ r hr).mdifferentiableAt (Ioo_mem_nhds hr.1 hr.2)
  have hv₁ : mfderiv 𝓘(ℝ, ℝ) J (f ∘ γ) r 1 = curveVelocity J (f ∘ γ) r :=
    (curveVelocity_apply (I := J)).symm
  have hv₂ : mfderiv 𝓘(ℝ, ℝ) I γ r 1 = curveVelocity I γ r :=
    (curveVelocity_apply (I := I)).symm
  rw [hv₁, hv₂, ← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (h.norm_curveVelocity_comp_le hγr)

/-- A curve differentiable on `(a, b)` whose velocity is horizontal at every parameter in `(a, b)`
has the same Riemannian path length on `[a, b]` as its projection. -/
theorem pathELength_comp_eq_of_mem_orthogonal_ker {a b : ℝ}
    (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ (Ioo a b))
    (hhor : ∀ r ∈ Ioo a b, curveVelocity I γ r ∈ (mfderiv I J f (γ r)).kerᗮ) :
    Manifold.pathELength J (f ∘ γ) a b = Manifold.pathELength I γ a b := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo, Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_
  have hγr : MDifferentiableAt 𝓘(ℝ, ℝ) I γ r :=
    (hγ r hr).mdifferentiableAt (Ioo_mem_nhds hr.1 hr.2)
  have hv₁ : mfderiv 𝓘(ℝ, ℝ) J (f ∘ γ) r 1 = curveVelocity J (f ∘ γ) r :=
    (curveVelocity_apply (I := J)).symm
  have hv₂ : mfderiv 𝓘(ℝ, ℝ) I γ r 1 = curveVelocity I γ r :=
    (curveVelocity_apply (I := I)).symm
  rw [hv₁, hv₂, ← ofReal_norm, ← ofReal_norm,
    (h.norm_curveVelocity_comp_eq_iff hγr).mpr (hhor r hr)]

end Velocity

/-! ### Horizontal lifts of tangent fields along curves -/

section HorizontalProjection

variable [IsManifold I 2 M] [IsManifold J 2 N]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  {γ : ℝ → M} {U : ∀ r, TangentSpace J ((f ∘ γ) r)} {s : Set ℝ} {t : ℝ}

local instance : IsManifold I ((1 : ℕ∞ω) + 1) M := by
  rw [one_add_one_eq_two]
  infer_instance

/-- Horizontally lifting a tangent field along `f ∘ γ` preserves differentiability in local bundle
coordinates within `s`. -/
theorem differentiableWithinAt_sectionCoord_horizontalLift
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hU : DifferentiableWithinAt ℝ (sectionCoord (F := F) (f ∘ γ) U (f (γ t))) s t) :
    DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ h.horizontalLift (γ r) (U r)) (γ t)) s t := by
  set e := trivializationAt F (TangentSpace J) (f (γ t))
  let b := Module.finBasis ℝ F
  let c := fun i r ↦ b.repr (sectionCoord (F := F) (f ∘ γ) U (f (γ t)) r) i
  let L := fun i (x : M) ↦ h.horizontalLift x (e.localFrame b i (f x))
  have hbase : f (γ t) ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f (γ t))
  have hfγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) J (f ∘ γ) s t :=
    (h.isSubmersion.contMDiff.mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt t hγ
  have hnear : ∀ᶠ r in 𝓝[s] t, f (γ r) ∈ e.baseSet :=
    hfγ.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hbase)
  have hexp (r : ℝ) (hr : f (γ r) ∈ e.baseSet) :
      h.horizontalLift (γ r) (U r) = ∑ i, c i r • L i (γ r) := by
    conv_lhs => rw [b.eq_sum_repr_continuousLinearMapAt_smul_localFrame (𝕜 := ℝ) hr (U r)]
    simp only [map_sum, map_smul, c, L, e, sectionCoord_apply, Function.comp_apply]
  have hsum : DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ ∑ i, c i r • L i (γ r)) (γ t)) s t := by
    refine differentiableWithinAt_sectionCoord_sum γ fun i _ ↦ ?_
    have hc : DifferentiableWithinAt ℝ (c i) s t :=
      (b.coord i).toContinuousLinearMap.differentiableAt.comp_differentiableWithinAt t hU
    have hE : CMDiffAt 1 (T% (e.localFrame b i)) (f (γ t)) :=
      (e.contMDiffOn_localFrame_baseSet (I := J) 1 b i).contMDiffAt
        (e.open_baseSet.mem_nhds hbase)
    have hL : MDiffAt (T% (L i)) (γ t) :=
      (h.contMDiffAt_horizontalLift hE (by norm_num)).mdifferentiableAt one_ne_zero
    rw [sectionCoord_smul]
    exact hc.smul (differentiableWithinAt_sectionCoord γ (fun r ↦ L i (γ r))
      (hL.comp_mdifferentiableWithinAt t hγ)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
  refine hsum.congr_of_eventuallyEq (hnear.mono fun r hr ↦ ?_) ?_
  · simp only [sectionCoord_apply, hexp r hr]
  · simp only [sectionCoord_apply, hexp t hbase]

/-- Horizontally lifting a tangent field along `f ∘ γ` preserves differentiability in local bundle
coordinates. -/
theorem differentiableAt_sectionCoord_horizontalLift (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hU : DifferentiableAt ℝ (sectionCoord (F := F) (f ∘ γ) U (f (γ t))) t) :
    DifferentiableAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ h.horizontalLift (γ r) (U r)) (γ t)) t := by
  rw [← differentiableWithinAt_univ]
  exact h.differentiableWithinAt_sectionCoord_horizontalLift
    hγ.mdifferentiableWithinAt hU.differentiableWithinAt

variable {covM : CovariantDerivative I E (TangentSpace I : M → Type _)}
  {covN : CovariantDerivative J F (TangentSpace J : N → Type _)}

/-- At a parameter where `γ` has horizontal velocity within `s`, the Levi-Civita derivative along
`γ` of the horizontal lift of `U` projects to the Levi-Civita derivative of `U` along `f ∘ γ`. -/
theorem mfderiv_alongCurveWithin_horizontalLift
    (hM : covM.IsLeviCivitaConnection) (hN : covN.IsLeviCivitaConnection)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hU : DifferentiableWithinAt ℝ (sectionCoord (F := F) (f ∘ γ) U (f (γ t))) s t)
    (hhor : curveVelocityWithin I γ s t ∈ (mfderiv I J f (γ t)).kerᗮ) :
    mfderiv I J f (γ t)
        (alongCurveWithin covM γ (fun r ↦ h.horizontalLift (γ r) (U r)) s t) =
      alongCurveWithin covN (f ∘ γ) U s t := by
  by_cases hs : UniqueDiffWithinAt ℝ s t
  swap
  · simp [alongCurveWithin_of_not_uniqueDiffWithinAt _ _ _ hs]
  set e := trivializationAt F (TangentSpace J) (f (γ t))
  let b := Module.finBasis ℝ F
  let c := fun i r ↦ b.repr (sectionCoord (F := F) (f ∘ γ) U (f (γ t)) r) i
  let E₀ := fun i ↦ e.localFrame b i
  let L := fun i (x : M) ↦ h.horizontalLift x (E₀ i (f x))
  have hbase : f (γ t) ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f (γ t))
  have hfγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) J (f ∘ γ) s t :=
    (h.isSubmersion.contMDiff.mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt t hγ
  have hnear : ∀ᶠ r in 𝓝[s] t, f (γ r) ∈ e.baseSet :=
    hfγ.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hbase)
  have hexpN (r : ℝ) (hr : f (γ r) ∈ e.baseSet) : U r = ∑ i, c i r • E₀ i ((f ∘ γ) r) := by
    simpa only [c, E₀, sectionCoord_apply, Function.comp_apply] using
      b.eq_sum_repr_continuousLinearMapAt_smul_localFrame (𝕜 := ℝ) hr (U r)
  have hexpM (r : ℝ) (hr : f (γ r) ∈ e.baseSet) :
      h.horizontalLift (γ r) (U r) = ∑ i, c i r • L i (γ r) := by
    rw [hexpN r hr, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ map_smul _ _ _
  have hc (i : Fin (Module.finrank ℝ F)) : DifferentiableWithinAt ℝ (c i) s t :=
    (b.coord i).toContinuousLinearMap.differentiableAt.comp_differentiableWithinAt t hU
  have hE (i : Fin (Module.finrank ℝ F)) : CMDiffAt 1 (T% (E₀ i)) (f (γ t)) :=
    (e.contMDiffOn_localFrame_baseSet (I := J) 1 b i).contMDiffAt (e.open_baseSet.mem_nhds hbase)
  have hL (i : Fin (Module.finrank ℝ F)) : MDiffAt (T% (L i)) (γ t) :=
    (h.contMDiffAt_horizontalLift (hE i) (by norm_num)).mdifferentiableAt one_ne_zero
  have hEcoord (i : Fin (Module.finrank ℝ F)) :
      DifferentiableWithinAt ℝ (sectionCoord (F := F) (f ∘ γ) (fun r ↦ E₀ i ((f ∘ γ) r))
        (f (γ t))) s t :=
    differentiableWithinAt_sectionCoord (f ∘ γ) _
      (((hE i).mdifferentiableAt one_ne_zero).comp_mdifferentiableWithinAt t hfγ) hbase
  have hLcoord (i : Fin (Module.finrank ℝ F)) :
      DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (fun r ↦ L i (γ r)) (γ t)) s t :=
    differentiableWithinAt_sectionCoord γ _ ((hL i).comp_mdifferentiableWithinAt t hγ)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  rw [alongCurveWithin_congr covM γ _ (hnear.mono hexpM) (hexpM t hbase),
    alongCurveWithin_congr covN (f ∘ γ) _ (hnear.mono hexpN) (hexpN t hbase),
    alongCurveWithin_sum covM γ Finset.univ _
      (fun i _ ↦ by rw [sectionCoord_smul]; exact (hc i).smul (hLcoord i)),
    alongCurveWithin_sum covN (f ∘ γ) Finset.univ _
      (fun i _ ↦ by rw [sectionCoord_smul]; exact (hc i).smul (hEcoord i)),
    map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [alongCurveWithin_smul covM γ _ (c i) s (hc i) (hLcoord i),
    alongCurveWithin_smul covN (f ∘ γ) _ (c i) s (hc i) (hEcoord i),
    alongCurveWithin_pullback_curveVelocityWithin covM γ (L i) hs hγ (hL i),
    alongCurveWithin_pullback_curveVelocityWithin covN (f ∘ γ) (E₀ i) hs hfγ
      ((hE i).mdifferentiableAt one_ne_zero),
    (h.curveVelocityWithin_eq_horizontalLift_iff hs hγ).mpr hhor,
    map_add, map_smul, map_smul, h.mfderiv_horizontalLift,
    h.mfderiv_covariantDerivative_horizontalLift hM hN (hE i)]
  simp only [Function.comp_apply]

/-- Unrestricted form of `mfderiv_alongCurveWithin_horizontalLift`. -/
theorem mfderiv_alongCurve_horizontalLift
    (hM : covM.IsLeviCivitaConnection) (hN : covN.IsLeviCivitaConnection)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hU : DifferentiableAt ℝ (sectionCoord (F := F) (f ∘ γ) U (f (γ t))) t)
    (hhor : curveVelocity I γ t ∈ (mfderiv I J f (γ t)).kerᗮ) :
    mfderiv I J f (γ t) (alongCurve covM γ (fun r ↦ h.horizontalLift (γ r) (U r)) t) =
      alongCurve covN (f ∘ γ) U t := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ]
  exact h.mfderiv_alongCurveWithin_horizontalLift hM hN hγ.mdifferentiableWithinAt
    hU.differentiableWithinAt (by rwa [curveVelocityWithin_univ])

/-- At a parameter where `γ` has horizontal velocity within `s`, the horizontal projection of the
total-space Levi-Civita derivative along `γ` of the horizontal lift of `U` is the horizontal lift
of the base Levi-Civita derivative of `U` along `f ∘ γ`. -/
theorem starProjection_alongCurveWithin_horizontalLift
    (hM : covM.IsLeviCivitaConnection) (hN : covN.IsLeviCivitaConnection)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hU : DifferentiableWithinAt ℝ (sectionCoord (F := F) (f ∘ γ) U (f (γ t))) s t)
    (hhor : curveVelocityWithin I γ s t ∈ (mfderiv I J f (γ t)).kerᗮ) :
    (mfderiv I J f (γ t)).kerᗮ.starProjection
        (alongCurveWithin covM γ (fun r ↦ h.horizontalLift (γ r) (U r)) s t) =
      h.horizontalLift (γ t) (alongCurveWithin covN (f ∘ γ) U s t) := by
  rw [← h.horizontalLift_mfderiv,
    h.mfderiv_alongCurveWithin_horizontalLift hM hN hγ hU hhor]

/-- Unrestricted form of `starProjection_alongCurveWithin_horizontalLift`. -/
theorem starProjection_alongCurve_horizontalLift
    (hM : covM.IsLeviCivitaConnection) (hN : covN.IsLeviCivitaConnection)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hU : DifferentiableAt ℝ (sectionCoord (F := F) (f ∘ γ) U (f (γ t))) t)
    (hhor : curveVelocity I γ t ∈ (mfderiv I J f (γ t)).kerᗮ) :
    (mfderiv I J f (γ t)).kerᗮ.starProjection
        (alongCurve covM γ (fun r ↦ h.horizontalLift (γ r) (U r)) t) =
      h.horizontalLift (γ t) (alongCurve covN (f ∘ γ) U t) := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ]
  exact h.starProjection_alongCurveWithin_horizontalLift hM hN hγ.mdifferentiableWithinAt
    hU.differentiableWithinAt (by rwa [curveVelocityWithin_univ])

end HorizontalProjection

/-! ### Full along-curve derivative and acceleration of horizontal curves -/

section Smooth

variable [IsManifold I ∞ M] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {γ : ℝ → M} {U : ∀ r, TangentSpace J ((f ∘ γ) r)} {s : Set ℝ} {t : ℝ}

/-- **Covariant derivative of a horizontal lift along a curve.** At a parameter where `γ` has
horizontal velocity within `s`, the total-space Levi-Civita derivative of `horizontalLift U`
decomposes into the horizontal lift of the base Levi-Civita derivative of `U` and O'Neill's
horizontal tensor `A_{γ'}(horizontalLift U)`. -/
theorem alongCurveWithin_horizontalLift
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hU : DifferentiableWithinAt ℝ (sectionCoord (F := F) (f ∘ γ) U (f (γ t))) s t)
    (hhor : curveVelocityWithin I γ s t ∈ (mfderiv I J f (γ t)).kerᗮ) :
    alongCurveWithin (leviCivitaConnection I M) γ
        (fun r ↦ h.horizontalLift (γ r) (U r)) s t =
      h.horizontalLift (γ t) (alongCurveWithin (leviCivitaConnection J N) (f ∘ γ) U s t) +
        h.oneillA (γ t) (curveVelocityWithin I γ s t) (h.horizontalLift (γ t) (U t)) := by
  by_cases hs : UniqueDiffWithinAt ℝ s t
  swap
  · simp [alongCurveWithin_of_not_uniqueDiffWithinAt _ _ _ hs,
      curveVelocityWithin_eq_zero_of_not_uniqueDiffWithinAt hs]
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let V : ∀ r, TangentSpace I (γ r) := fun r ↦ h.horizontalLift (γ r) (U r)
  let Q : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x :=
    fun x ↦ (mfderiv I J f x).ker.starProjection
  let D := alongCurveWithin (leviCivitaConnection I M) γ V s t
  have hP := h.starProjection_alongCurveWithin_horizontalLift
    (isLeviCivitaConnection_leviCivitaConnection I (M := M))
    (isLeviCivitaConnection_leviCivitaConnection J (M := N)) hγ hU hhor
  have hQd := (h.contMDiff_starProjection_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := γ t)
  have hVt : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I.tangent
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s t := by
    set e := trivializationAt E (TangentSpace I) (γ t)
    have hbase : γ t ∈ e.baseSet :=
      FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
    have hnear : ∀ᶠ r in 𝓝[s] t, γ r ∈ e.baseSet :=
      hγ.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hbase)
    have hcoord : DifferentiableWithinAt ℝ (fun r ↦ (e (TotalSpace.mk' E (γ r) (V r))).2) s t :=
      (h.differentiableWithinAt_sectionCoord_horizontalLift hγ hU).congr_of_eventuallyEq
        (hnear.mono fun r hr ↦ by
          rw [sectionCoord_apply, e.continuousLinearMapAt_apply_of_mem ℝ hr])
        (by rw [sectionCoord_apply, e.continuousLinearMapAt_apply_of_mem ℝ hbase])
    rw [e.mdifferentiableWithinAt_totalSpace_iff I _ ((Bundle.Trivialization.mem_source e).2 hbase)]
    exact ⟨hγ, mdifferentiableWithinAt_iff_differentiableWithinAt.mpr hcoord⟩
  have hclm := CovariantDerivative.alongCurveWithin_clm_apply
    (leviCivitaConnection I M) γ V Q hs hQd hVt
  have hQV : (fun r ↦ Q (γ r) (V r)) = fun r ↦ 0 := funext fun r ↦
    (Submodule.starProjection_apply_eq_zero_iff _).mpr
      (h.horizontalLift_mem_orthogonal_ker (γ r) (U r))
  rw [hQV, alongCurveWithin_zero] at hclm
  have hT0 : h.oneillT (γ t) (curveVelocityWithin I γ s t) (V t) = 0 := by
    rw [← Submodule.starProjection_eq_self_iff.mpr hhor,
      h.oneillT_starProjection_orthogonal_ker, zero_apply]
  have hAker : h.oneillA (γ t) (curveVelocityWithin I γ s t) (V t) ∈
      (mfderiv I J f (γ t)).ker :=
    h.oneillA_apply_mem_ker (curveVelocityWithin I γ s t)
      (h.horizontalLift_mem_orthogonal_ker (γ t) (U t))
  have hhom : (leviCivitaConnection I M).hom (leviCivitaConnection I M) Q (γ t)
      (curveVelocityWithin I γ s t) (V t) =
      -h.oneillA (γ t) (curveVelocityWithin I γ s t) (V t) := by
    rw [h.hom_starProjection_ker_apply, hT0, add_zero,
      Submodule.starProjection_orthogonal_apply_eq_zero hAker,
      Submodule.starProjection_eq_self_iff.mpr hAker, zero_sub]
  rw [hhom] at hclm
  have hQ : Q (γ t) D = h.oneillA (γ t) (curveVelocityWithin I γ s t) (V t) :=
    (eq_of_neg_add_eq_zero hclm.symm).symm
  have hsplit : D = (mfderiv I J f (γ t)).kerᗮ.starProjection D + Q (γ t) D := by
    simp only [Q, Submodule.starProjection_orthogonal, sub_apply, ContinuousLinearMap.id_apply,
      sub_add_cancel]
  exact hsplit.trans (congrArg₂ (· + ·) hP hQ)

/-- Unrestricted form of `alongCurveWithin_horizontalLift`. -/
theorem alongCurve_horizontalLift (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hU : DifferentiableAt ℝ (sectionCoord (F := F) (f ∘ γ) U (f (γ t))) t)
    (hhor : curveVelocity I γ t ∈ (mfderiv I J f (γ t)).kerᗮ) :
    alongCurve (leviCivitaConnection I M) γ (fun r ↦ h.horizontalLift (γ r) (U r)) t =
      h.horizontalLift (γ t) (alongCurve (leviCivitaConnection J N) (f ∘ γ) U t) +
        h.oneillA (γ t) (curveVelocity I γ t) (h.horizontalLift (γ t) (U t)) := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ, ← curveVelocityWithin_univ]
  exact h.alongCurveWithin_horizontalLift hγ.mdifferentiableWithinAt
    hU.differentiableWithinAt (by rwa [curveVelocityWithin_univ])

/-- Along a `C²` horizontal curve within a parameter set with unique derivatives, the total-space
covariant acceleration is the horizontal lift of the projected curve's covariant acceleration: the
O'Neill `A`-term `A_{γ'}(γ')` vanishes because `A` is alternating on horizontal vectors. -/
theorem accelerationWithin_eq_horizontalLift (hs : UniqueDiffOn ℝ s)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s)
    (hhor : ∀ r ∈ s, curveVelocityWithin I γ s r ∈ (mfderiv I J f (γ r)).kerᗮ) (ht : t ∈ s) :
    accelerationWithin (leviCivitaConnection I M) γ s t =
      h.horizontalLift (γ t) (accelerationWithin (leviCivitaConnection J N) (f ∘ γ) s t) := by
  have hfγ : ContMDiffOn 𝓘(ℝ, ℝ) J 2 (f ∘ γ) s :=
    (h.isSubmersion.contMDiff.of_le (by norm_num)).comp_contMDiffOn hγ
  have hvel (r : ℝ) (hr : r ∈ s) :
      curveVelocityWithin I γ s r =
        h.horizontalLift (γ r) (curveVelocityWithin J (f ∘ γ) s r) :=
    (h.curveVelocityWithin_eq_horizontalLift_iff (hs r hr)
      ((hγ.mdifferentiableOn (by norm_num)) r hr)).mpr (hhor r hr)
  have hU : DifferentiableWithinAt ℝ
      (sectionCoord (F := F) (f ∘ γ) (curveVelocityWithin J (f ∘ γ) s) (f (γ t))) s t :=
    differentiableWithinAt_sectionCoord_curveVelocityWithin (f ∘ γ) hs hfγ ht
      (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f (γ t)))
  rw [accelerationWithin_def, accelerationWithin_def,
    alongCurveWithin_congr _ _ _ (eventually_mem_nhdsWithin.mono hvel) (hvel t ht),
    h.alongCurveWithin_horizontalLift ((hγ.mdifferentiableOn (by norm_num)) t ht) hU (hhor t ht),
    ← hvel t ht, h.oneillA_self (hhor t ht), add_zero]

/-- Unrestricted form of `accelerationWithin_eq_horizontalLift` for a globally `C²` horizontal
curve. -/
theorem acceleration_eq_horizontalLift (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ)
    (hhor : ∀ r, curveVelocity I γ r ∈ (mfderiv I J f (γ r)).kerᗮ) (t : ℝ) :
    acceleration (leviCivitaConnection I M) γ t =
      h.horizontalLift (γ t) (acceleration (leviCivitaConnection J N) (f ∘ γ) t) := by
  rw [← accelerationWithin_univ, ← accelerationWithin_univ]
  exact h.accelerationWithin_eq_horizontalLift uniqueDiffOn_univ hγ.contMDiffOn
    (fun r _ ↦ by rw [curveVelocityWithin_univ]; exact hhor r) (mem_univ t)

/-- A `C²` curve whose velocity is horizontal throughout `s` has zero total-space acceleration at
`t ∈ s` if and only if its projection has zero base acceleration at `t`. -/
theorem accelerationWithin_eq_zero_iff_comp (hs : UniqueDiffOn ℝ s)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s)
    (hhor : ∀ r ∈ s, curveVelocityWithin I γ s r ∈ (mfderiv I J f (γ r)).kerᗮ) (ht : t ∈ s) :
    accelerationWithin (leviCivitaConnection I M) γ s t = 0 ↔
      accelerationWithin (leviCivitaConnection J N) (f ∘ γ) s t = 0 := by
  rw [h.accelerationWithin_eq_horizontalLift hs hγ hhor ht]
  exact map_eq_zero_iff _ (h.horizontalLift (γ t)).injective

/-- A globally `C²` horizontal curve has zero total-space acceleration at `t` if and only if its
projection has zero base acceleration at `t`. -/
theorem acceleration_eq_zero_iff_comp (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ)
    (hhor : ∀ r, curveVelocity I γ r ∈ (mfderiv I J f (γ r)).kerᗮ) (t : ℝ) :
    acceleration (leviCivitaConnection I M) γ t = 0 ↔
      acceleration (leviCivitaConnection J N) (f ∘ γ) t = 0 := by
  rw [h.acceleration_eq_horizontalLift hγ hhor t]
  exact map_eq_zero_iff _ (h.horizontalLift (γ t)).injective

end Smooth

end TauCeti.IsRiemannianSubmersion

end
