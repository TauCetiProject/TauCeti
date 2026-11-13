/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
import TauCeti.Geometry.Manifold.Riemannian.Isometry.LeviCivita

/-!
# Isometry naturality of O'Neill's fundamental tensors

The tensors `A` and `T` of a Riemannian submersion commute with local Riemannian
isometries of its source. A local isometry of the base leaves both tensors unchanged.
More generally, local isometries intertwining two submersions near a point transport
both tensors at that point, without any submersion assumption on the diagonal composite.
In particular the formulas apply to restrictions to open submanifolds.

The tensors use the actual Levi-Civita connection and horizontal/vertical projections.
The proof combines their field formulas with the existing isometry transport of those
projections and of the Levi-Civita connection. Neither completeness nor global
injectivity or surjectivity of the local isometries is needed. In the composition special
cases, the composite maps retain their Riemannian-submersion hypotheses, including their
boundary normal forms.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13
  (1966), 459–469, §1 (the intrinsic fundamental tensors).
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Proposition 5.13
  (naturality of the Levi-Civita connection).
-/

public section

open Bundle Manifold VectorField
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {K : ModelWithCorners ℝ E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold K ∞ P]
  [RiemannianBundle (fun z : P ↦ TangentSpace K z)]
  [IsContMDiffRiemannianBundle K ∞ E' (fun z : P ↦ TangentSpace K z)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)

include h

section Intertwining

variable
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {G' : Type*} [TopologicalSpace G'] {L : ModelWithCorners ℝ F' G'}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace G' Q] [IsManifold L ∞ Q]
  [RiemannianBundle (fun y : Q ↦ TangentSpace L y)]
  [IsContMDiffRiemannianBundle L ∞ F' (fun y : Q ↦ TangentSpace L y)]
  {f' : P → Q} (h' : IsRiemannianSubmersion K L f')
  {φ : P → M} (hφ : IsLocalRiemannianIsometry K I φ)
  {ψ : Q → N} (hψ : IsLocalRiemannianIsometry L J ψ)

include h' hφ hψ

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ F] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle K ∞ E' (fun z : P ↦ TangentSpace K z)]
  [FiniteDimensional ℝ F'] [IsManifold L ∞ Q]
  [IsContMDiffRiemannianBundle L ∞ F' (fun y : Q ↦ TangentSpace L y)] in
/-- The two orthogonal projections are transported by a locally commuting square. -/
private theorem mfderiv_projections_of_eventuallyEq {x : P}
    (hcomm : f ∘ φ =ᶠ[𝓝 x] ψ ∘ f') (v : TangentSpace K x) :
    (mfderiv K I φ x ((mfderiv K L f' x).kerᗮ.starProjection v) =
      (mfderiv I J f (φ x)).kerᗮ.starProjection (mfderiv K I φ x v)) ∧
    (mfderiv K I φ x ((mfderiv K L f' x).ker.starProjection v) =
      (mfderiv I J f (φ x)).ker.starProjection (mfderiv K I φ x v)) := by
  obtain ⟨e, he⟩ := hφ.exists_linearIsometryEquiv_eq_mfderiv x
  have hd (w : TangentSpace K x) :
      mfderiv I J f (φ x) (mfderiv K I φ x w) =
        tangentSpaceCast J (ψ (f' x)) (f (φ x))
          (mfderiv L J ψ (f' x) (mfderiv K L f' x w)) := by
    have hc := congrArg (fun A ↦ A w) (hcomm.mfderiv_eq (I := K) (I' := J))
    simpa only [mfderiv_comp x (h.isSubmersion.contMDiff.mdifferentiableAt (by simp))
        (hφ.mdifferentiableAt x),
      mfderiv_comp x (hψ.mdifferentiableAt (f' x))
        (h'.isSubmersion.contMDiff.mdifferentiableAt (by simp)),
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Function.comp_apply] using hc
  have hk : (mfderiv K L f' x).ker.map (e.toLinearIsometry : _ →ₗ[ℝ] _) =
      (mfderiv I J f (φ x)).ker := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      have hw0 : mfderiv K L f' x w = 0 := hw
      exact (congrArg (mfderiv I J f (φ x)) (he w)).trans
        ((hd w).trans (by simp only [hw0, map_zero]))
    · intro w hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      have hw0 : mfderiv I J f (φ x) w = 0 := hw
      have hzero : mfderiv K L f' x (e.symm w) = 0 := by
        apply hψ.mfderiv_injective (f' x)
        apply (tangentSpaceCast J (ψ (f' x)) (f (φ x))).injective
        simpa only [map_zero, ← hd, ← he, e.apply_symm_apply] using hw0
      exact hzero
  have hV : mfderiv K I φ x ((mfderiv K L f' x).ker.starProjection v) =
      (mfderiv I J f (φ x)).ker.starProjection (mfderiv K I φ x v) := by
    simpa only [LinearIsometryEquiv.coe_toLinearIsometry, hk, he] using
      e.toLinearIsometry.map_starProjection' (mfderiv K L f' x).ker v
  refine ⟨?_, hV⟩
  simp only [Submodule.starProjection_orthogonal, sub_apply,
    ContinuousLinearMap.id_apply, map_sub, hV]

/-- Transport of the differentiated horizontal and vertical parts of a pulled-back field.
This common step is used by both fundamental tensors, with different projected directions. -/
private theorem mfderiv_leviCivitaConnection_projections_of_eventuallyEq
    {Y : Π y : M, TangentSpace I y} {x : P}
    (hcomm : f ∘ φ =ᶠ[𝓝 x] ψ ∘ f') (hY : MDiffAt (T% Y) (φ x))
    (v : TangentSpace K x) :
    (mfderiv K I φ x (CovariantDerivative.leviCivitaConnection K P
        (fun z ↦ (mfderiv K L f' z).kerᗮ.starProjection
          (mpullback K I φ Y z)) x v) =
      CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) (φ x)
        (mfderiv K I φ x v)) ∧
    (mfderiv K I φ x (CovariantDerivative.leviCivitaConnection K P
        (fun z ↦ (mfderiv K L f' z).ker.starProjection
          (mpullback K I φ Y z)) x v) =
      CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) (φ x)
        (mfderiv K I φ x v)) := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let : IsManifold K (∞ + 1) P := by simpa using (inferInstance : IsManifold K ∞ P)
  have hH : ∀ᶠ z in 𝓝 x, (mfderiv K L f' z).kerᗮ.starProjection
      (mpullback K I φ Y z) =
      mpullback K I φ (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) z := by
    filter_upwards [hcomm.eventuallyEq_nhds] with z hz
    apply hφ.mfderiv_injective z
    simp only [(h.mfderiv_projections_of_eventuallyEq h' hφ hψ hz _).1,
      hφ.mfderiv_apply_mpullback]
  have hV : ∀ᶠ z in 𝓝 x, (mfderiv K L f' z).ker.starProjection
      (mpullback K I φ Y z) =
      mpullback K I φ (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) z := by
    filter_upwards [hcomm.eventuallyEq_nhds] with z hz
    apply hφ.mfderiv_injective z
    simp only [(h.mfderiv_projections_of_eventuallyEq h' hφ hψ hz _).2,
      hφ.mfderiv_apply_mpullback]
  have hHd := ((h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := φ x)).clm_bundle_apply hY
  have hVd := ((h.contMDiff_starProjection_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := φ x)).clm_bundle_apply hY
  have hHd' := ((h'.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := x)).clm_bundle_apply (hφ.mdifferentiableAt_mpullback hY)
  have hVd' := ((h'.contMDiff_starProjection_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := x)).clm_bundle_apply (hφ.mdifferentiableAt_mpullback hY)
  have hcov := (CovariantDerivative.leviCivitaConnection K P).isCovariantDerivativeOnUniv
  constructor
  · rw [hcov.congr_of_eventuallyEq hHd' (hφ.mdifferentiableAt_mpullback hHd)
        (by simp) hH, hφ.mfderiv_leviCivitaConnection_mpullback hHd]
  · rw [hcov.congr_of_eventuallyEq hVd' (hφ.mdifferentiableAt_mpullback hVd)
        (by simp) hV, hφ.mfderiv_leviCivitaConnection_mpullback hVd]

/-- Local isometries intertwining two submersions near `x` transport O'Neill's horizontal
tensor at `x`. No submersion hypothesis on either diagonal composite is needed. -/
theorem mfderiv_oneillA_of_eventuallyEq {x : P}
    (hcomm : f ∘ φ =ᶠ[𝓝 x] ψ ∘ f') (u v : TangentSpace K x) :
    mfderiv K I φ x (h'.oneillA x u v) =
      h.oneillA (φ x) (mfderiv K I φ x u) (mfderiv K I φ x v) := by
  let Y := FiberBundle.extend E (mfderiv K I φ x v)
  have hY : MDiffAt (T% Y) (φ x) := FiberBundle.mdifferentiableAt_extend I E _
  have hYx : mpullback K I φ Y x = v :=
    (hφ.mpullback_apply_eq_iff Y v).2 (FiberBundle.extend_apply_self E _)
  have ha := congrArg (mfderiv K I φ x)
    (h'.oneillA_apply (hφ.mdifferentiableAt_mpullback hY) u)
  simp only [map_add, (h.mfderiv_projections_of_eventuallyEq h' hφ hψ hcomm _).2,
    (h.mfderiv_projections_of_eventuallyEq h' hφ hψ hcomm _).1,
    (h.mfderiv_leviCivitaConnection_projections_of_eventuallyEq h' hφ hψ hcomm hY _).1,
    (h.mfderiv_leviCivitaConnection_projections_of_eventuallyEq h' hφ hψ hcomm hY _).2] at ha
  simpa only [hYx, Y, FiberBundle.extend_apply_self] using
    ha.trans (h.oneillA_apply hY (mfderiv K I φ x u)).symm

/-- Local isometries intertwining two submersions near `x` transport O'Neill's vertical
tensor at `x`. No submersion hypothesis on either diagonal composite is needed. -/
theorem mfderiv_oneillT_of_eventuallyEq {x : P}
    (hcomm : f ∘ φ =ᶠ[𝓝 x] ψ ∘ f') (u v : TangentSpace K x) :
    mfderiv K I φ x (h'.oneillT x u v) =
      h.oneillT (φ x) (mfderiv K I φ x u) (mfderiv K I φ x v) := by
  let Y := FiberBundle.extend E (mfderiv K I φ x v)
  have hY : MDiffAt (T% Y) (φ x) := FiberBundle.mdifferentiableAt_extend I E _
  have hYx : mpullback K I φ Y x = v :=
    (hφ.mpullback_apply_eq_iff Y v).2 (FiberBundle.extend_apply_self E _)
  have ht := congrArg (mfderiv K I φ x)
    (h'.oneillT_apply (hφ.mdifferentiableAt_mpullback hY) u)
  simp only [map_add, (h.mfderiv_projections_of_eventuallyEq h' hφ hψ hcomm _).1,
    (h.mfderiv_projections_of_eventuallyEq h' hφ hψ hcomm _).2,
    (h.mfderiv_leviCivitaConnection_projections_of_eventuallyEq h' hφ hψ hcomm hY _).2,
    (h.mfderiv_leviCivitaConnection_projections_of_eventuallyEq h' hφ hψ hcomm hY _).1] at ht
  simpa only [hYx, Y, FiberBundle.extend_apply_self] using
    ht.trans (h.oneillT_apply hY (mfderiv K I φ x u)).symm

end Intertwining

section Source

variable {φ : P → M} (hcomp : IsRiemannianSubmersion K J (f ∘ φ))
  (hφ : IsLocalRiemannianIsometry K I φ)

include hφ

/-- O'Neill's horizontal tensor commutes with a local Riemannian isometry of the source.
Both input vectors and the output are transported by its differential. -/
@[simp]
theorem mfderiv_oneillA_comp (x : P) (u v : TangentSpace K x) :
    mfderiv K I φ x (hcomp.oneillA x u v) =
      h.oneillA (φ x) (mfderiv K I φ x u) (mfderiv K I φ x v) :=
  h.mfderiv_oneillA_of_eventuallyEq hcomp hφ (IsLocalRiemannianIsometry.id J N)
    Filter.EventuallyEq.rfl u v

/-- O'Neill's vertical tensor commutes with a local Riemannian isometry of the source.
No total-geodesicity assumption on the fibres is imposed. -/
@[simp]
theorem mfderiv_oneillT_comp (x : P) (u v : TangentSpace K x) :
    mfderiv K I φ x (hcomp.oneillT x u v) =
      h.oneillT (φ x) (mfderiv K I φ x u) (mfderiv K I φ x v) :=
  h.mfderiv_oneillT_of_eventuallyEq hcomp hφ (IsLocalRiemannianIsometry.id J N)
    Filter.EventuallyEq.rfl u v

end Source

section Base

variable {ψ : N → P} (hcomp : IsRiemannianSubmersion I K (ψ ∘ f))
  (hψ : IsLocalRiemannianIsometry J K ψ)

include hψ

-- The intermediate base model cannot be inferred from the left-hand sides, so the base
-- identities are explicit rewrite lemmas rather than global simp rules.

/-- A local Riemannian isometry of the base leaves O'Neill's horizontal tensor unchanged. -/
theorem oneillA_comp (x : M) : hcomp.oneillA x = h.oneillA x := by
  ext u v
  simpa only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq] using
    (hcomp.mfderiv_oneillA_of_eventuallyEq h (IsLocalRiemannianIsometry.id I M) hψ
      Filter.EventuallyEq.rfl u v).symm

/-- A local Riemannian isometry of the base leaves O'Neill's vertical tensor unchanged. -/
theorem oneillT_comp (x : M) : hcomp.oneillT x = h.oneillT x := by
  ext u v
  simpa only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq] using
    (hcomp.mfderiv_oneillT_of_eventuallyEq h (IsLocalRiemannianIsometry.id I M) hψ
      Filter.EventuallyEq.rfl u v).symm

end Base

end TauCeti.IsRiemannianSubmersion
