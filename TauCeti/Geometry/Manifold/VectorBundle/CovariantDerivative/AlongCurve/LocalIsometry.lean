/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.NondegenerateMetric
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.LocalIsometry
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongCurve.Tangent

/-!
# Covariant differentiation along curves under local isometries of nondegenerate metrics

Let `g` and `g'` be smooth symmetric nondegenerate metrics on `M` and `N`, of any signature, with
Levi-Civita connections `∇` and `∇'`, and let `f : M → N` be a local isometry from `g` to `g'`.
For a curve `γ` in `M` and a tangent field `V` along `γ`, this file proves that covariant
differentiation along curves commutes with the differential of `f`:

`df (D V / dt) = D' (df V) / dt` along `f ∘ γ`.

This holds for arbitrary differentiable tangent fields along `γ`, not only those pulled back from
an ambient vector field, and on any parameter set with unique derivatives, including closed
intervals. Applied to the velocity field, it says that `f` carries the covariant acceleration of
`γ` to that of `f ∘ γ`. Since the differential of a local isometry is invertible, a curve has
vanishing covariant acceleration exactly when its image does: local isometries carry geodesics of
`∇` to geodesics of `∇'`, and every curve whose image is a geodesic is itself one.

The proof tests both sides against pullbacks of differentiable vector fields on `N`: the product
rules for the metric-compatible connections `∇` and `∇'` differentiate the same pairing, and the
pulled-back fields are handled by the naturality of Levi-Civita connections
`IsLocalIsometry.mfderiv_apply_mpullback_of_isLeviCivitaConnection`.

## Main results

In the namespace `TauCeti.Manifold.ContMDiffNondegenerateMetric.IsLocalIsometry`:

* `mfderiv_alongCurveWithin_mpullback` and `mfderiv_alongCurve_mpullback`: naturality for a field
  pulled back from the target.
* `mfderiv_alongCurveWithin` and `mfderiv_alongCurve`: naturality for an arbitrary differentiable
  tangent field along the curve.
* `mfderiv_accelerationWithin` and `mfderiv_acceleration`: local isometries carry covariant
  acceleration to covariant acceleration.
* `accelerationWithin_comp_eq_zero_iff` and `acceleration_comp_eq_zero_iff`: a curve has vanishing
  covariant acceleration exactly when its image under a local isometry does.

## References

* B. O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic Press, 1983,
  Ch. 3: isometries preserve covariant derivatives along curves and geodesics.
* `TauCeti.Geometry.Manifold.Riemannian.Isometry.AlongCurve` and
  `TauCeti.Geometry.Manifold.Riemannian.Isometry.Geodesic`: the argument for smooth Riemannian
  isometries, followed here with the inner product replaced by `g` and positivity by
  nondegeneracy.
-/

public section

open Bundle CovariantDerivative Filter Set VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold.ContMDiffNondegenerateMetric.IsLocalIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {g : ContMDiffNondegenerateMetric (I := I) (M := M)}
  {g' : ContMDiffNondegenerateMetric (I := J) (M := N)} {f : M → N}
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {cov' : CovariantDerivative J F (fun y : N ↦ TangentSpace J y)}
  {γ : ℝ → M} {s : Set ℝ} {t : ℝ}

/-! ### Fields pulled back from the target -/

/-- Covariant differentiation along a curve of an ambient vector field commutes with a local
isometry of nondegenerate metrics: the field on the source is the pullback of a vector field `Y`
on the target, differentiable at `f (γ t)`. -/
theorem mfderiv_alongCurveWithin_mpullback (hf : g.IsLocalIsometry g' f)
    (h : g.IsLeviCivitaConnection cov) (h' : g'.IsLeviCivitaConnection cov')
    {Y : Π y : N, TangentSpace J y} (hs : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t) (hY : MDiffAt (T% Y) (f (γ t))) :
    mfderiv I J f (γ t) (alongCurveWithin cov γ (fun r ↦ mpullback I J f Y (γ r)) s t) =
      alongCurveWithin cov' (f ∘ γ) (fun r ↦ Y ((f ∘ γ) r)) s t := by
  have hfγ : MDiffAt f (γ t) := hf.contMDiff.mdifferentiableAt (by simp)
  rw [alongCurveWithin_pullback cov γ (mpullback I J f Y) hs
      (hasMFDerivWithinAt_curveVelocityWithin hγ) (hf.mdifferentiableAt_mpullback hY),
    alongCurveWithin_pullback cov' (f ∘ γ) Y hs
      (hasMFDerivWithinAt_curveVelocityWithin (hfγ.comp_mdifferentiableWithinAt t hγ)) hY,
    curveVelocityWithin_map hfγ hs hγ]
  exact hf.mfderiv_apply_mpullback_of_isLeviCivitaConnection h h' hY _

/-- The unrestricted form of `IsLocalIsometry.mfderiv_alongCurveWithin_mpullback`. -/
theorem mfderiv_alongCurve_mpullback (hf : g.IsLocalIsometry g' f)
    (h : g.IsLeviCivitaConnection cov) (h' : g'.IsLeviCivitaConnection cov')
    {Y : Π y : N, TangentSpace J y} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hY : MDiffAt (T% Y) (f (γ t))) :
    mfderiv I J f (γ t) (alongCurve cov γ (fun r ↦ mpullback I J f Y (γ r)) t) =
      alongCurve cov' (f ∘ γ) (fun r ↦ Y ((f ∘ γ) r)) t := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ]
  exact hf.mfderiv_alongCurveWithin_mpullback h h' uniqueDiffWithinAt_univ
    hγ.mdifferentiableWithinAt hY

/-! ### Arbitrary tangent fields along a curve -/

/-- **Naturality of covariant differentiation along a curve under a local isometry.** Let `f` be a
local isometry from the nondegenerate metric `g` to `g'`, with Levi-Civita connections `∇` and
`∇'`. For a tangent field `V` along a differentiable curve `γ` whose coordinate reading is
differentiable within `s` at `t`, the differential of `f` carries `D V / dt` to the derivative
along `f ∘ γ` of the transported field `df V`. -/
theorem mfderiv_alongCurveWithin (hf : g.IsLocalIsometry g' f)
    (h : g.IsLeviCivitaConnection cov) (h' : g'.IsLeviCivitaConnection cov')
    {V : ∀ r, TangentSpace I (γ r)} (hs : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t) :
    mfderiv I J f (γ t) (alongCurveWithin cov γ V s t) =
      alongCurveWithin cov' (f ∘ γ) (fun r ↦ mfderiv I J f (γ r) (V r)) s t := by
  have hfγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) J (f ∘ γ) s t :=
    (hf.contMDiff.mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt t hγ
  have hfV : DifferentiableWithinAt ℝ
      (sectionCoord (F := F) (f ∘ γ) (fun r ↦ mfderiv I J f (γ r) (V r)) (f (γ t))) s t :=
    hf.contMDiff.contMDiffAt.differentiableWithinAt_sectionCoord_mfderiv (by simp) hγ hV
  -- Test both sides against differentiable vector fields `Y` on the target. The product rules
  -- on source and target differentiate the same pairing, of `V` with the pullback of `Y`.
  refine g'.injective_apply_mdifferentiableAt_vectorField (f (γ t)) ?_
  ext Y hY
  dsimp only
  set X : Π x : M, TangentSpace I x := mpullback I J f Y
  have hXcoord : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (fun r ↦ X (γ r)) (γ t)) s t :=
    differentiableWithinAt_sectionCoord γ (fun r ↦ X (γ r))
      ((hf.mdifferentiableAt_mpullback hY).comp_mdifferentiableWithinAt t hγ)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hYcoord : DifferentiableWithinAt ℝ
      (sectionCoord (F := F) (f ∘ γ) (fun r ↦ Y ((f ∘ γ) r)) (f (γ t))) s t :=
    differentiableWithinAt_sectionCoord (f ∘ γ) (fun r ↦ Y ((f ∘ γ) r))
      (hY.comp_mdifferentiableWithinAt t hfγ)
      (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f (γ t)))
  have hsource := h.isMetricCompatible.derivWithin_apply_alongCurveWithin hs hγ hV hXcoord
  have htarget := h'.isMetricCompatible.derivWithin_apply_alongCurveWithin hs hfγ hfV hYcoord
  -- Pairing with a pulled-back field is pairing with the field after applying `df`.
  have hpair (r : ℝ) (v : TangentSpace I (γ r)) :
      g (γ r) v (X (γ r)) = g' (f (γ r)) (mfderiv I J f (γ r) v) (Y (f (γ r))) := by
    rw [← hf.apply_mfderiv, hf.mfderiv_apply_mpullback]
  have hderiv : derivWithin (fun r ↦ g (γ r) (V r) (X (γ r))) s t =
      derivWithin (fun r ↦ g' (f (γ r)) (mfderiv I J f (γ r) (V r)) (Y (f (γ r)))) s t :=
    congrArg (derivWithin · s t) (funext fun r ↦ hpair r (V r))
  have hsecond : g (γ t) (V t) (alongCurveWithin cov γ (fun r ↦ X (γ r)) s t) =
      g' (f (γ t)) (mfderiv I J f (γ t) (V t))
        (alongCurveWithin cov' (f ∘ γ) (fun r ↦ Y ((f ∘ γ) r)) s t) := by
    rw [← hf.mfderiv_alongCurveWithin_mpullback h h' hs hγ hY, hf.apply_mfderiv]
  rw [← hpair]
  simp only [Function.comp_apply] at htarget hsecond ⊢
  linarith

/-- The unrestricted form of naturality of covariant differentiation along a curve under a local
isometry of nondegenerate metrics. -/
theorem mfderiv_alongCurve (hf : g.IsLocalIsometry g' f)
    (h : g.IsLeviCivitaConnection cov) (h' : g'.IsLeviCivitaConnection cov')
    {V : ∀ r, TangentSpace I (γ r)} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t) :
    mfderiv I J f (γ t) (alongCurve cov γ V t) =
      alongCurve cov' (f ∘ γ) (fun r ↦ mfderiv I J f (γ r) (V r)) t := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ]
  exact hf.mfderiv_alongCurveWithin h h' uniqueDiffWithinAt_univ hγ.mdifferentiableWithinAt
    hV.differentiableWithinAt

/-! ### Covariant acceleration and geodesics -/

/-- **Local isometries preserve covariant acceleration.** For a `C²` curve `γ` on a parameter set
with unique derivatives, the differential of a local isometry `f` of nondegenerate metrics carries
the covariant acceleration of `γ` for `∇` to the covariant acceleration of `f ∘ γ` for `∇'`. -/
theorem mfderiv_accelerationWithin (hf : g.IsLocalIsometry g' f)
    (h : g.IsLeviCivitaConnection cov) (h' : g'.IsLeviCivitaConnection cov')
    (hs : UniqueDiffOn ℝ s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s) (ht : t ∈ s) :
    mfderiv I J f (γ t) (accelerationWithin cov γ s t) = accelerationWithin cov' (f ∘ γ) s t := by
  have hvelocity (r : ℝ) (hr : r ∈ s) :
      curveVelocityWithin J (f ∘ γ) s r = mfderiv I J f (γ r) (curveVelocityWithin I γ s r) :=
    curveVelocityWithin_map (hf.contMDiff.mdifferentiableAt (by simp)) (hs r hr)
      ((hγ.mdifferentiableOn (by norm_num)) r hr)
  have hcoord : DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ (curveVelocityWithin I γ s) (γ t)) s t :=
    differentiableWithinAt_sectionCoord_curveVelocityWithin γ hs hγ ht
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  rw [accelerationWithin_def, accelerationWithin_def,
    hf.mfderiv_alongCurveWithin h h' (hs t ht) ((hγ.mdifferentiableOn (by norm_num)) t ht) hcoord,
    alongCurveWithin_congr cov' (f ∘ γ) (curveVelocityWithin J (f ∘ γ) s)
      (eventually_mem_nhdsWithin.mono hvelocity) (hvelocity t ht)]

/-- The unrestricted form of `IsLocalIsometry.mfderiv_accelerationWithin`, for a `C²` curve. -/
theorem mfderiv_acceleration (hf : g.IsLocalIsometry g' f)
    (h : g.IsLeviCivitaConnection cov) (h' : g'.IsLeviCivitaConnection cov')
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) (t : ℝ) :
    mfderiv I J f (γ t) (acceleration cov γ t) = acceleration cov' (f ∘ γ) t := by
  rw [← accelerationWithin_univ, ← accelerationWithin_univ]
  exact hf.mfderiv_accelerationWithin h h' uniqueDiffOn_univ hγ.contMDiffOn (mem_univ t)

/-- **Local isometries carry geodesics to geodesics.** A `C²` curve `γ` on a parameter set with
unique derivatives has vanishing covariant acceleration at `t ∈ s` for `∇` exactly when its image
under a local isometry `f` of nondegenerate metrics has vanishing covariant acceleration at `t`
for `∇'`. -/
theorem accelerationWithin_comp_eq_zero_iff (hf : g.IsLocalIsometry g' f)
    (h : g.IsLeviCivitaConnection cov) (h' : g'.IsLeviCivitaConnection cov')
    (hs : UniqueDiffOn ℝ s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s) (ht : t ∈ s) :
    accelerationWithin cov' (f ∘ γ) s t = 0 ↔ accelerationWithin cov γ s t = 0 := by
  rw [← hf.mfderiv_accelerationWithin h h' hs hγ ht]
  exact map_eq_zero_iff _ (hf.isInvertible_mfderiv (γ t)).injective

/-- The unrestricted form of `IsLocalIsometry.accelerationWithin_comp_eq_zero_iff`, for a `C²`
curve. -/
theorem acceleration_comp_eq_zero_iff (hf : g.IsLocalIsometry g' f)
    (h : g.IsLeviCivitaConnection cov) (h' : g'.IsLeviCivitaConnection cov')
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) (t : ℝ) :
    acceleration cov' (f ∘ γ) t = 0 ↔ acceleration cov γ t = 0 := by
  rw [← hf.mfderiv_acceleration h h' hγ t]
  exact map_eq_zero_iff _ (hf.isInvertible_mfderiv (γ t)).injective

end TauCeti.Manifold.ContMDiffNondegenerateMetric.IsLocalIsometry
