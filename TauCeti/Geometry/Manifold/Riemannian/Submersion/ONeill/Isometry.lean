/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Isometry.LeviCivita

/-!
# Isometry naturality of O'Neill's fundamental tensors

The tensors `A` and `T` of a Riemannian submersion commute with local Riemannian
isometries of its source. A local isometry of the base leaves both tensors unchanged.
Together these statements give naturality under isometries intertwining submersions:
apply the source formula and then the base formula to the two factorizations of the
commuting square. In particular the formulas apply to restrictions to open submanifolds.

The tensors use the actual Levi-Civita connection and horizontal/vertical projections.
The proof combines their field formulas with the existing isometry transport of those
projections and of the Levi-Civita connection. Neither completeness nor global
injectivity or surjectivity of the local isometries is needed. The composite maps retain
their Riemannian-submersion hypotheses, including their boundary normal forms.

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

section Source

variable {φ : P → M} (hcomp : IsRiemannianSubmersion K J (f ∘ φ))
  (hφ : IsLocalRiemannianIsometry K I φ)

include hcomp hφ

/-- Transport of the differentiated horizontal and vertical parts of a pulled-back field.
This common step is used by both fundamental tensors, with different projected directions. -/
private theorem mfderiv_leviCivitaConnection_projections_comp
    {Y : Π y : M, TangentSpace I y} {x : P} (hY : MDiffAt (T% Y) (φ x))
    (v : TangentSpace K x) :
    (mfderiv K I φ x (CovariantDerivative.leviCivitaConnection K P
        (fun z ↦ (mfderiv K J (f ∘ φ) z).kerᗮ.starProjection
          (mpullback K I φ Y z)) x v) =
      CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) (φ x)
        (mfderiv K I φ x v)) ∧
    (mfderiv K I φ x (CovariantDerivative.leviCivitaConnection K P
        (fun z ↦ (mfderiv K J (f ∘ φ) z).ker.starProjection
          (mpullback K I φ Y z)) x v) =
      CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) (φ x)
        (mfderiv K I φ x v)) := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hH : (fun z ↦ (mfderiv K J (f ∘ φ) z).kerᗮ.starProjection
      (mpullback K I φ Y z)) =
      mpullback K I φ (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) := by
    funext z
    apply hφ.mfderiv_injective z
    simp only [h.mfderiv_starProjection_orthogonal_ker_comp hcomp hφ,
      hφ.mfderiv_apply_mpullback]
  have hV : (fun z ↦ (mfderiv K J (f ∘ φ) z).ker.starProjection
      (mpullback K I φ Y z)) =
      mpullback K I φ (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) := by
    funext z
    apply hφ.mfderiv_injective z
    simp only [h.mfderiv_starProjection_ker_comp hcomp hφ, hφ.mfderiv_apply_mpullback]
  have hHd := ((h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := φ x)).clm_bundle_apply hY
  have hVd := ((h.contMDiff_starProjection_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := φ x)).clm_bundle_apply hY
  constructor
  · rw [hH, hφ.mfderiv_leviCivitaConnection_mpullback hHd]
  · rw [hV, hφ.mfderiv_leviCivitaConnection_mpullback hVd]

/-- O'Neill's horizontal tensor commutes with a local Riemannian isometry of the source.
Both input vectors and the output are transported by its differential. -/
@[simp]
theorem mfderiv_oneillA_comp (x : P) (u v : TangentSpace K x) :
    mfderiv K I φ x (hcomp.oneillA x u v) =
      h.oneillA (φ x) (mfderiv K I φ x u) (mfderiv K I φ x v) := by
  let Y := FiberBundle.extend E (mfderiv K I φ x v)
  have hY : MDiffAt (T% Y) (φ x) := FiberBundle.mdifferentiableAt_extend I E _
  have hYx : mpullback K I φ Y x = v :=
    (hφ.mpullback_apply_eq_iff Y v).2 (FiberBundle.extend_apply_self E _)
  have ha := congrArg (mfderiv K I φ x)
    (hcomp.oneillA_apply (hφ.mdifferentiableAt_mpullback hY) u)
  simp only [map_add, h.mfderiv_starProjection_ker_comp hcomp hφ,
    h.mfderiv_starProjection_orthogonal_ker_comp hcomp hφ,
    (h.mfderiv_leviCivitaConnection_projections_comp hcomp hφ hY _).1,
    (h.mfderiv_leviCivitaConnection_projections_comp hcomp hφ hY _).2] at ha
  simpa only [hYx, Y, FiberBundle.extend_apply_self] using
    ha.trans (h.oneillA_apply hY (mfderiv K I φ x u)).symm

/-- O'Neill's vertical tensor commutes with a local Riemannian isometry of the source.
No total-geodesicity assumption on the fibres is imposed. -/
@[simp]
theorem mfderiv_oneillT_comp (x : P) (u v : TangentSpace K x) :
    mfderiv K I φ x (hcomp.oneillT x u v) =
      h.oneillT (φ x) (mfderiv K I φ x u) (mfderiv K I φ x v) := by
  let Y := FiberBundle.extend E (mfderiv K I φ x v)
  have hY : MDiffAt (T% Y) (φ x) := FiberBundle.mdifferentiableAt_extend I E _
  have hYx : mpullback K I φ Y x = v :=
    (hφ.mpullback_apply_eq_iff Y v).2 (FiberBundle.extend_apply_self E _)
  have ht := congrArg (mfderiv K I φ x)
    (hcomp.oneillT_apply (hφ.mdifferentiableAt_mpullback hY) u)
  simp only [map_add, h.mfderiv_starProjection_orthogonal_ker_comp hcomp hφ,
    h.mfderiv_starProjection_ker_comp hcomp hφ,
    (h.mfderiv_leviCivitaConnection_projections_comp hcomp hφ hY _).2,
    (h.mfderiv_leviCivitaConnection_projections_comp hcomp hφ hY _).1] at ht
  simpa only [hYx, Y, FiberBundle.extend_apply_self] using
    ht.trans (h.oneillT_apply hY (mfderiv K I φ x u)).symm

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
  have hY := FiberBundle.mdifferentiableAt_extend I E v
  have hc := hcomp.oneillA_apply hY u
  have hb := h.oneillA_apply hY u
  simp only [h.starProjection_ker_comp hcomp hψ,
    h.starProjection_orthogonal_ker_comp hcomp hψ, FiberBundle.extend_apply_self] at hc
  simpa only [FiberBundle.extend_apply_self] using hc.trans hb.symm

/-- A local Riemannian isometry of the base leaves O'Neill's vertical tensor unchanged. -/
theorem oneillT_comp (x : M) : hcomp.oneillT x = h.oneillT x := by
  ext u v
  have hY := FiberBundle.mdifferentiableAt_extend I E v
  have hc := hcomp.oneillT_apply hY u
  have hb := h.oneillT_apply hY u
  simp only [h.starProjection_ker_comp hcomp hψ,
    h.starProjection_orthogonal_ker_comp hcomp hψ, FiberBundle.extend_apply_self] at hc
  simpa only [FiberBundle.extend_apply_self] using hc.trans hb.symm

end Base

end TauCeti.IsRiemannianSubmersion
