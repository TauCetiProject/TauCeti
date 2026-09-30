/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.LeviCivita
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric

/-!
# Covariant differentiation along curves under Riemannian isometries

For a smooth Riemannian isometry `Φ : M → N`, covariant differentiation along a curve commutes
with the tangent map of `Φ`. This is the along-curve form of the naturality of the Levi-Civita
connection. It applies to differentiable tangent fields along arbitrary parameter sets with
unique derivatives, including closed intervals.

Naturality for arbitrary tangent fields along a curve, rather than only for fields pulled back
from an ambient vector field, is what allows intrinsic equations involving covariant derivatives
along curves to be transported by an isometry. The main example is the geodesic equation: the
velocity field of a curve is generally not the restriction of an ambient vector field.

## Main results

* `mfderiv_alongCurveWithin_mpullback`: naturality for a field pulled back from the target.
* `differentiableWithinAt_sectionCoord_mfderiv` and
  `differentiableAt_sectionCoord_mfderiv`: regularity of a tangent field transported by an
  isometry.
* `mfderiv_alongCurveWithin`: naturality for an arbitrary differentiable tangent field along the
  curve.
* `mfderiv_alongCurve`: the unrestricted form.

See do Carmo, *Riemannian Geometry*, Chapter 2, Theorem 3.6.
-/

public section

open Bundle CovariantDerivative Filter Manifold VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.RiemannianIsometry

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I 2 M] [IsManifold J 2 N]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]

/-- Covariant differentiation along a curve of an ambient vector field commutes with a
Riemannian isometry. The field on the source is the pullback of the field on the target. -/
theorem mfderiv_alongCurveWithin_mpullback (Φ : RiemannianIsometry I J M N)
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ} {Y : Π y : N, TangentSpace J y}
    (hs : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hY : MDiffAt (T% Y) (Φ (γ t))) :
    mfderiv I J Φ (γ t)
        (alongCurveWithin (leviCivitaConnection I M) γ
          (fun r ↦ mpullback I J Φ Y (γ r)) s t) =
      alongCurveWithin (leviCivitaConnection J N) (Φ ∘ γ)
        (fun r ↦ Y ((Φ ∘ γ) r)) s t := by
  have hX : MDiffAt (T% (mpullback I J Φ Y)) (γ t) :=
    hY.mpullback_vectorField (Φ.toDiffeomorph.contMDiff.contMDiffAt)
      (Φ.toDiffeomorph.isInvertible_mfderiv (by simp)) (by simp)
  rw [alongCurveWithin_pullback (leviCivitaConnection I M) γ (mpullback I J Φ Y)
      hs (hasMFDerivWithinAt_curveVelocityWithin hγ) hX]
  rw [alongCurveWithin_pullback (leviCivitaConnection J N) (Φ ∘ γ) Y hs
      (hasMFDerivWithinAt_curveVelocityWithin
        ((Φ.mdifferentiableAt (γ t)).comp_mdifferentiableWithinAt t hγ)) hY]
  rw [TauCeti.Manifold.curveVelocityWithin_map (Φ.mdifferentiableAt (γ t)) hs hγ]
  exact Φ.mfderiv_leviCivitaConnection_mpullback hY _

/-- For a differentiable curve, the unrestricted along-curve Levi-Civita derivative of a
pulled-back ambient field is carried to the derivative of that field along the image curve. -/
theorem mfderiv_alongCurve_mpullback (Φ : RiemannianIsometry I J M N)
    {γ : ℝ → M} {t : ℝ} {Y : Π y : N, TangentSpace J y}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hY : MDiffAt (T% Y) (Φ (γ t))) :
    mfderiv I J Φ (γ t)
        (alongCurve (leviCivitaConnection I M) γ
          (fun r ↦ mpullback I J Φ Y (γ r)) t) =
      alongCurve (leviCivitaConnection J N) (Φ ∘ γ)
        (fun r ↦ Y ((Φ ∘ γ) r)) t := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ]
  exact Φ.mfderiv_alongCurveWithin_mpullback uniqueDiffWithinAt_univ
    hγ.mdifferentiableWithinAt hY

/-! ### Arbitrary tangent fields along a curve -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)] in
/-- The differential of a Riemannian isometry carries a tangent field along `γ` that is
differentiable in local coordinates to a tangent field along `Φ ∘ γ` that is differentiable in
local coordinates. -/
theorem differentiableWithinAt_sectionCoord_mfderiv (Φ : RiemannianIsometry I J M N)
    {γ : ℝ → M} {V : ∀ r, TangentSpace I (γ r)} {s : Set ℝ} {t : ℝ}
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t) :
    DifferentiableWithinAt ℝ
      (sectionCoord (F := F) (Φ ∘ γ) (fun r ↦ mfderiv I J Φ (γ r) (V r)) (Φ (γ t))) s t := by
  -- Lift `V` to a differentiable curve in the tangent bundle, then push it forward by the
  -- smooth tangent map of `Φ`.
  let e := trivializationAt E (TangentSpace I) (γ t)
  have hbase : γ t ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hnear : ∀ᶠ r in 𝓝[s] t, γ r ∈ e.baseSet :=
    hγ.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hbase)
  have hcoord : DifferentiableWithinAt ℝ
      (fun r ↦ (e (TotalSpace.mk' E (γ r) (V r))).2) s t := by
    apply hV.congr_of_eventuallyEq
    · filter_upwards [hnear] with r hr
      rw [sectionCoord_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hr]
    · rw [sectionCoord_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hbase]
  have htotal : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I.tangent
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s t := by
    rw [e.mdifferentiableWithinAt_totalSpace_iff I]
    · exact ⟨hγ, mdifferentiableWithinAt_iff_differentiableWithinAt.mpr hcoord⟩
    · exact (Bundle.Trivialization.mem_source e).2 hbase
  have hΦtotal : MDifferentiableWithinAt 𝓘(ℝ, ℝ) J.tangent
      (fun r ↦ TotalSpace.mk' F (Φ (γ r)) (mfderiv I J Φ (γ r) (V r))) s t := by
    have htotal' :=
      Φ.toDiffeomorph.tangent.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
        |>.comp_mdifferentiableWithinAt t htotal
    have hmap : tangentMap I J Φ ∘ (fun r ↦ TotalSpace.mk' E (γ r) (V r)) =
        fun r ↦ TotalSpace.mk' F (Φ (γ r)) (mfderiv I J Φ (γ r) (V r)) := by
      funext r
      exact TotalSpace.ext tangentMap_proj (heq_of_eq tangentMap_snd)
    simpa only [Diffeomorph.coe_tangent, coe_toDiffeomorph, hmap] using htotal'
  exact differentiableWithinAt_sectionCoord (Φ ∘ γ)
    (fun r ↦ mfderiv I J Φ (γ r) (V r)) hΦtotal
    (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (Φ (γ t)))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)] in
/-- The differential of a Riemannian isometry carries a tangent field along `γ` that is
differentiable in local coordinates to a tangent field along `Φ ∘ γ` that is differentiable in
local coordinates. -/
theorem differentiableAt_sectionCoord_mfderiv (Φ : RiemannianIsometry I J M N)
    {γ : ℝ → M} {V : ∀ r, TangentSpace I (γ r)} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t) :
    DifferentiableAt ℝ
      (sectionCoord (F := F) (Φ ∘ γ) (fun r ↦ mfderiv I J Φ (γ r) (V r)) (Φ (γ t))) t := by
  rw [← differentiableWithinAt_univ]
  exact Φ.differentiableWithinAt_sectionCoord_mfderiv hγ.mdifferentiableWithinAt
    hV.differentiableWithinAt

/-- **Naturality of covariant differentiation along a curve under a Riemannian isometry.**
The differential of an isometry carries the Levi-Civita derivative of a differentiable tangent
field along `γ` to the derivative of the transported field along `Φ ∘ γ`.

Differentiability of a tangent field along a curve is expressed in the local coordinates used by
`CovariantDerivative.alongCurveWithin`. This is the weakest hypothesis needed by the product rule
which characterizes the derivative. -/
theorem mfderiv_alongCurveWithin (Φ : RiemannianIsometry I J M N)
    {γ : ℝ → M} {V : ∀ r, TangentSpace I (γ r)} {s : Set ℝ} {t : ℝ}
    (hs : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hV : DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ V (γ t)) s t) :
    mfderiv I J Φ (γ t)
        (alongCurveWithin (leviCivitaConnection I M) γ V s t) =
      alongCurveWithin (leviCivitaConnection J N) (Φ ∘ γ)
        (fun r ↦ mfderiv I J Φ (γ r) (V r)) s t := by
  let W : ∀ r, TangentSpace J ((Φ ∘ γ) r) :=
    fun r ↦ mfderiv I J Φ (γ r) (V r)
  have hΦγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) J (Φ ∘ γ) s t :=
    (Φ.mdifferentiableAt (γ t)).comp_mdifferentiableWithinAt t hγ
  have hΦV := Φ.differentiableWithinAt_sectionCoord_mfderiv hγ hV
  -- Test both sides against pullbacks of differentiable fields `Y` on the target: the
  -- metric-compatible product rules on source and target differentiate the same inner product.
  refine TauCeti.eq_of_forall_inner_section_eq (I := J)
    (V := fun y : N ↦ TangentSpace J y) F fun Y hY ↦ ?_
  let X : ∀ x : M, TangentSpace I x := mpullback I J Φ Y
  have hX : MDiffAt (T% X) (γ t) :=
    hY.mpullback_vectorField (Φ.toDiffeomorph.contMDiff.contMDiffAt)
      (Φ.toDiffeomorph.isInvertible_mfderiv (by simp)) (by simp)
  have hXcoord : DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ X (γ r)) (γ t)) s t :=
    differentiableWithinAt_sectionCoord γ (fun r ↦ X (γ r))
      (hX.comp_mdifferentiableWithinAt t hγ)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hYcoord : DifferentiableWithinAt ℝ
      (sectionCoord (F := F) (Φ ∘ γ) (fun r ↦ Y ((Φ ∘ γ) r)) (Φ (γ t))) s t :=
    differentiableWithinAt_sectionCoord (Φ ∘ γ) (fun r ↦ Y ((Φ ∘ γ) r))
      (hY.comp_mdifferentiableWithinAt t hΦγ)
      (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (Φ (γ t)))
  have hsource :=
    (isMetricCompatible_leviCivitaConnection (I := I) (M := M)).derivWithin_inner_alongCurveWithin
      hs hγ hV hXcoord
  have htarget :=
    (isMetricCompatible_leviCivitaConnection (I := J) (M := N)).derivWithin_inner_alongCurveWithin
      hs hΦγ hΦV hYcoord
  have hXY (r : ℝ) : mfderiv I J Φ (γ r) (X (γ r)) = Y ((Φ ∘ γ) r) := by
    dsimp only [X, Function.comp_apply]
    exact Φ.toDiffeomorph.mfderiv_apply_mpullback (by simp) Y (γ r)
  have hinner : (fun r ↦ inner ℝ (V r) (X (γ r))) =
      fun r ↦ inner ℝ (W r) (Y ((Φ ∘ γ) r)) := by
    funext r
    dsimp only [W]
    rw [← Φ.inner_mfderiv (γ r), hXY]
  have hderiv : derivWithin (fun r ↦ inner ℝ (V r) (X (γ r))) s t =
      derivWithin (fun r ↦ inner ℝ (W r) (Y ((Φ ∘ γ) r))) s t :=
    congrArg (fun f : ℝ → ℝ ↦ derivWithin f s t) hinner
  have htransport := Φ.mfderiv_alongCurveWithin_mpullback hs hγ hY
  have hleft :
      inner ℝ
          (mfderiv I J Φ (γ t)
            (alongCurveWithin (leviCivitaConnection I M) γ V s t))
          (Y (Φ (γ t))) =
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s t) (X (γ t)) := by
    rw [← Φ.inner_mfderiv (γ t), hXY]
    rfl
  have hsecond :
      inner ℝ (V t)
          (alongCurveWithin (leviCivitaConnection I M) γ (fun r ↦ X (γ r)) s t) =
        inner ℝ (W t)
          (alongCurveWithin (leviCivitaConnection J N) (Φ ∘ γ)
            (fun r ↦ Y ((Φ ∘ γ) r)) s t) := by
    rw [← htransport, Φ.inner_mfderiv]
  rw [hleft]
  simp only [Function.comp_apply] at htarget hderiv hsecond ⊢
  dsimp only [W] at hderiv hsecond
  linarith [hsource, htarget, hderiv, hsecond]

/-- The unrestricted form of naturality of covariant differentiation along a curve under a
Riemannian isometry. -/
theorem mfderiv_alongCurve (Φ : RiemannianIsometry I J M N)
    {γ : ℝ → M} {V : ∀ r, TangentSpace I (γ r)} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t) :
    mfderiv I J Φ (γ t) (alongCurve (leviCivitaConnection I M) γ V t) =
      alongCurve (leviCivitaConnection J N) (Φ ∘ γ)
        (fun r ↦ mfderiv I J Φ (γ r) (V r)) t := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ]
  exact Φ.mfderiv_alongCurveWithin uniqueDiffWithinAt_univ hγ.mdifferentiableWithinAt
    hV.differentiableWithinAt

end TauCeti.RiemannianIsometry

end
