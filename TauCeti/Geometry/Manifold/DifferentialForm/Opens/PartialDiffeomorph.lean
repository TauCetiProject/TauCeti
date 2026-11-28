/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Pullback along a partial diffeomorphism between its source and target

A partial diffeomorphism `Φ` from `M` to `M'` is a diffeomorphism between its source and its
target, as open subsets of `M` and `M'` (`PartialDiffeomorph.toDiffeomorphSourceTarget`).
Pulling the restriction of a form on `M'` to the target back along it gives, at each point of the
source, the pullback of the form along `Φ` (`TauCeti.mpullback_toDiffeomorphSourceTarget_apply`,
in `TauCeti.Geometry.Manifold.DifferentialForm.Opens`). Hence a partial diffeomorphism pulling one
form back to another on its source restricts to a diffeomorphism of open subsets pulling the
restricted forms back to each other
(`TauCeti.SmoothForm.mpullback_toDiffeomorphSourceTarget_eq_iff`), the form in which local
normal-form theorems for differential forms state their conclusion.

Because `Naturality` sits downstream of `Pullback.Smooth` and `Opens`, the corresponding exterior
derivative laws (`PartialDiffeomorph.mextDeriv_mpullback_toDiffeomorphSourceTarget_apply` and
`PartialDiffeomorph.mextDeriv_mpullback_toDiffeomorphSourceTarget_symm_apply`) live here rather
than in `Opens`.
-/

public section

open TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']

variable [IsManifold I ∞ M] [IsManifold I' ∞ M']

/-- **A partial diffeomorphism pulling `τ` back to `σ` is a diffeomorphism of open subsets doing
so.** The restriction `Φ.toDiffeomorphSourceTarget` of a smooth partial diffeomorphism `Φ` pulls
the restriction of `τ` to the target of `Φ` back to the restriction of `σ` to its source exactly
when `Φ` pulls `τ` back to `σ` at every point of its source. -/
theorem SmoothForm.mpullback_toDiffeomorphSourceTarget_eq_iff
    (Φ : PartialDiffeomorph I I' M M' ∞) {σ : SmoothForm I M F k} {τ : SmoothForm I' M' F k} :
    SmoothForm.mpullback Φ.toDiffeomorphSourceTarget Φ.toDiffeomorphSourceTarget.contMDiff
        (SmoothForm.mpullback (Subtype.val : (⟨Φ.target, Φ.open_target⟩ : Opens M') → M')
          contMDiff_subtypeVal τ) =
      SmoothForm.mpullback (Subtype.val : (⟨Φ.source, Φ.open_source⟩ : Opens M) → M)
        contMDiff_subtypeVal σ ↔
      ∀ x ∈ Φ.source, TauCeti.mpullback I I' Φ τ.val x = σ.val x := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ Subtype.ext (funext fun x ↦ ?_)⟩
  · have hx' := congrArg (fun β : SmoothForm I _ F k ↦ β.val ⟨x, hx⟩) h
    simp only [SmoothForm.coe_mpullback, mpullback_toDiffeomorphSourceTarget_apply Φ (by simp),
      mpullback_subtype_val_apply] at hx'
    -- The two sides live in the fibres at `⟨x, hx⟩` of the source and at `x` of `M`, which are
    -- both the model fibre.
    exact hx'
  · simp only [SmoothForm.coe_mpullback, mpullback_toDiffeomorphSourceTarget_apply Φ (by simp),
      mpullback_subtype_val_apply]
    exact h x x.property

/-- **Exterior derivative of a pullback along `Φ.toDiffeomorphSourceTarget`.** Pulling the
restriction of a smooth form on `M'` back along `Φ.toDiffeomorphSourceTarget` and differentiating
gives the exterior derivative of the form evaluated along the differential of `Φ`. -/
theorem _root_.PartialDiffeomorph.mextDeriv_mpullback_toDiffeomorphSourceTarget_apply
    (Φ : PartialDiffeomorph I I' M M' ∞) (β : SmoothForm I' M' F k)
    (x : (⟨Φ.source, Φ.open_source⟩ : Opens M)) (v : Fin (k + 1) → TangentSpace I x) :
    mextDeriv (SmoothForm.mpullback Φ.toDiffeomorphSourceTarget
        Φ.toDiffeomorphSourceTarget.contMDiff
        (SmoothForm.mpullback (Subtype.val : (⟨Φ.target, Φ.open_target⟩ : Opens M') → M')
          contMDiff_subtypeVal β)).val x v =
      mextDeriv β.val (Φ x.val) (fun i ↦ mfderiv I I' Φ x.val
        (Manifold.tangentSpaceOpenEquiv (I := I) x (v i))) := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I' 2 M' := IsManifold.of_le (n := ∞) (by simp)
  rw [← mextDerivₗ_apply, SmoothForm.mextDerivₗ_mpullback,
    SmoothForm.mextDerivₗ_mpullback, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback]
  refine (DFunLike.congr_fun
    (mpullback_toDiffeomorphSourceTarget_apply Φ (by simp) (mextDerivₗ I' k β).val x) v).trans ?_
  have hv : (fun i ↦ Manifold.tangentSpaceOpenEquiv (I := I) x (v i)) = v :=
    funext fun i ↦ Manifold.tangentSpaceOpenEquiv_apply x (v i)
  refine (DFunLike.congr_arg (mpullback (F := F) (k := k + 1) I I' Φ (mextDerivₗ I' k β).val x.val)
    hv.symm).trans ?_
  rw [TauCeti.mpullback_apply, mextDerivₗ_apply]

/-- **Exterior derivative of a pullback along `Φ.toDiffeomorphSourceTarget.symm`.** Pulling the
restriction of a smooth form on `M` back along `Φ.toDiffeomorphSourceTarget.symm` and
differentiating gives the exterior derivative of the form evaluated along the differential of
`Φ.symm`. -/
theorem _root_.PartialDiffeomorph.mextDeriv_mpullback_toDiffeomorphSourceTarget_symm_apply
    (Φ : PartialDiffeomorph I I' M M' ∞) (β : SmoothForm I M F k)
    (x : (⟨Φ.target, Φ.open_target⟩ : Opens M')) (v : Fin (k + 1) → TangentSpace I' x) :
    mextDeriv (SmoothForm.mpullback Φ.toDiffeomorphSourceTarget.symm
        Φ.toDiffeomorphSourceTarget.symm.contMDiff
        (SmoothForm.mpullback (Subtype.val : (⟨Φ.source, Φ.open_source⟩ : Opens M) → M)
          contMDiff_subtypeVal β)).val x v =
      mextDeriv β.val (Φ.symm x.val) (fun i ↦ mfderiv I' I Φ.symm x.val
        (Manifold.tangentSpaceOpenEquiv (I := I') x (v i))) := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I' 2 M' := IsManifold.of_le (n := ∞) (by simp)
  rw [← mextDerivₗ_apply, SmoothForm.mextDerivₗ_mpullback,
    SmoothForm.mextDerivₗ_mpullback, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback]
  refine (DFunLike.congr_fun
    (Φ.mpullback_toDiffeomorphSourceTarget_symm_apply (by simp) (mextDerivₗ I k β).val x) v).trans
    ?_
  have hv : (fun i ↦ Manifold.tangentSpaceOpenEquiv (I := I') x (v i)) = v :=
    funext fun i ↦ Manifold.tangentSpaceOpenEquiv_apply x (v i)
  refine (DFunLike.congr_arg
    (mpullback (F := F) (k := k + 1) I' I Φ.symm (mextDerivₗ I k β).val x.val) hv.symm).trans ?_
  rw [TauCeti.mpullback_apply, mextDerivₗ_apply]

end TauCeti
