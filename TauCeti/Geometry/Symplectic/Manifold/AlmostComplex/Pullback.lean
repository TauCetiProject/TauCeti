/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Tangent
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Pulling back almost complex structures along diffeomorphisms

A smooth diffeomorphism `h : M → N` pulls a smooth almost complex structure `J` on `N` back to
the almost complex structure

`(h^* J)_x = (dh_x)⁻¹ ∘ J_(h x) ∘ dh_x`

on `M` (`TauCeti.SmoothAlmostComplexStructure.pullback h J`). It is characterized by making every
differential of `h` complex linear, `dh_x ((h^* J)_x v) = J_(h x) (dh_x v)`
(`TauCeti.SmoothAlmostComplexStructure.mfderiv_pullback_apply`). Pulling back is contravariantly
functorial, and it carries structures tamed by, invariant under, or compatible with a two-form
`σ` on `N` to structures with the same relation to the pulled-back form `h^* σ`.

For a symplectomorphism `φ` of `(M, σ)` this gives the structure `φ^* J` that a time-dependent
family of almost complex structures on a mapping torus has to reach after one turn of the seam
`(t + 1, x) ∼ (t, φ x)`.

## Main definitions

* `TauCeti.SmoothAlmostComplexStructure.pullback h J`: the pullback `h^* J`.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.mfderiv_pullback_apply`: `dh ∘ h^* J = J ∘ dh`.
* `TauCeti.SmoothAlmostComplexStructure.eq_pullback_iff`: `h^* J` is the only structure on `M`
  making the differentials of `h` complex linear.
* `TauCeti.SmoothAlmostComplexStructure.pullback_refl`,
  `TauCeti.SmoothAlmostComplexStructure.pullback_trans`: functoriality.
* `TauCeti.SmoothAlmostComplexStructure.contMDiff_pullback_family`: pulling back a family of
  structures depending smoothly on a parameter gives a family depending smoothly on it.
* `TauCeti.SmoothTwoForm.Tames.pullback`, `TauCeti.SmoothTwoForm.Invariant.pullback`,
  `TauCeti.SmoothTwoForm.Compatible.pullback`: tameness, invariance and compatibility pass to
  the pullbacks of the form and of the structure.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 (the action `J ↦ φ^* J` of symplectomorphisms on compatible almost complex
  structures).
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M E' H' N E'' H'' P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold I'' ∞ P]

namespace SmoothAlmostComplexStructure

/-- The endomorphism `(dh_x)⁻¹ ∘ J_(h x) ∘ dh_x` of `T_x M`. -/
private def pullbackEndomorphism (h : M ≃ₘ⟮I, I'⟯ N) (J : SmoothAlmostComplexStructure I' N)
    (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x :=
  (mfderiv I I' h x).inverse ∘L J.toEndomorphism (h x) ∘L mfderiv I I' h x

section Family

variable {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {IQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]

/-- The pointwise pullbacks of a family of almost complex structures on `N` depending smoothly on
a parameter in `Q` depend smoothly on the parameter and the point. -/
private theorem contMDiff_pullbackEndomorphism_family (h : M ≃ₘ⟮I, I'⟯ N)
    {J : Q → SmoothAlmostComplexStructure I' N}
    (hJ : ContMDiff (IQ.prod I') (I'.prod 𝓘(ℝ, E' →L[ℝ] E')) ∞
      (fun q : Q × N ↦ TotalSpace.mk' (E' →L[ℝ] E')
        (E := fun y : N ↦ TangentSpace I' y →L[ℝ] TangentSpace I' y) q.2
        ((J q.1).toEndomorphism q.2))) :
    ContMDiff (IQ.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : Q × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        (pullbackEndomorphism h (J q.1) q.2)) := by
  rw [TauCeti.contMDiff_hom_bundle_prod_iff]
  -- On total spaces, the pullback is the conjugate of the family by the tangent lift of `h`.
  have hJ' := (TauCeti.contMDiff_hom_bundle_prod_iff _).1 hJ
  refine (h.tangent.symm.contMDiff.comp (hJ'.comp
    (contMDiff_fst.prodMk (h.tangent.contMDiff.comp contMDiff_snd)))).congr fun p ↦ ?_
  simp only [Function.comp_apply, Diffeomorph.coe_tangent]
  exact (h.tangent_symm_mk p.2.proj _).symm

end Family

private theorem contMDiff_pullbackEndomorphism (h : M ≃ₘ⟮I, I'⟯ N)
    (J : SmoothAlmostComplexStructure I' N) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x
        (pullbackEndomorphism h J x)) :=
  -- This is the case of the constant family, with parameter in `M` itself.
  (contMDiff_pullbackEndomorphism_family (IQ := I) h (J := fun _ : M ↦ J)
    (J.toEndomorphism.contMDiff.comp contMDiff_snd)).comp (contMDiff_id.prodMk contMDiff_id)

/-- The pullback `h^* J` of a smooth almost complex structure `J` on `N` along a smooth
diffeomorphism `h : M → N`: at `x` it is `(dh_x)⁻¹ ∘ J_(h x) ∘ dh_x`. -/
def pullback (h : M ≃ₘ⟮I, I'⟯ N) (J : SmoothAlmostComplexStructure I' N) :
    SmoothAlmostComplexStructure I M where
  toEndomorphism := ⟨pullbackEndomorphism h J, contMDiff_pullbackEndomorphism h J⟩
  square_neg x := by
    ext v
    have hinv := h.isInvertible_mfderiv (n := ∞) (x := x) (by simp)
    simp [pullbackEndomorphism, hinv.self_apply_inverse, hinv.inverse_apply_self]

variable (h : M ≃ₘ⟮I, I'⟯ N) (J : SmoothAlmostComplexStructure I' N)

/-- The pullback at `x` is `(dh_x)⁻¹ ∘ J_(h x) ∘ dh_x`. -/
theorem pullback_apply (x : M) (v : TangentSpace I x) :
    pullback h J x v = (mfderiv I I' h x).inverse (J (h x) (mfderiv I I' h x v)) :=
  (rfl)

/-- The endomorphism of `T_x M` underlying `h^* J` is the conjugate of `J_(h x)` by the
linear equivalence `dh_x`. -/
theorem pullback_toEndomorphism (x : M) :
    (pullback h J).toEndomorphism x =
      (h.mfderivToContinuousLinearEquiv (by simp) x).symm.conjContinuousAlgEquiv
        (J.toEndomorphism (h x)) := by
  have he : (h.mfderivToContinuousLinearEquiv (n := ∞) (by simp) x :
      TangentSpace I x →L[ℝ] TangentSpace I' (h x)) = mfderiv I I' h x :=
    Diffeomorph.mfderivToContinuousLinearEquiv_coe h _
  ext v
  simp only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
    ContinuousLinearEquiv.symm_symm]
  refine (pullback_apply h J x v).trans ?_
  rw [← he, ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_coe]

/-- The differentials of `h` are complex linear from `h^* J` to `J`. -/
@[simp]
theorem mfderiv_pullback_apply (x : M) (v : TangentSpace I x) :
    mfderiv I I' h x (pullback h J x v) = J (h x) (mfderiv I I' h x v) :=
  (h.isInvertible_mfderiv (by simp)).self_apply_inverse _

/-- Pulling back a family of smooth almost complex structures on `N`, depending smoothly on a
parameter in a manifold `Q`, along a diffeomorphism `h : M → N` gives a family of almost complex
structures on `M` depending smoothly on the parameter: `(q, x) ↦ (h^* J_q)_x` is a smooth section
of the tangent endomorphism bundle along the projection `Q × M → M`. -/
theorem contMDiff_pullback_family {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
    [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    {J : Q → SmoothAlmostComplexStructure I' N}
    (hJ : ContMDiff (IQ.prod I') (I'.prod 𝓘(ℝ, E' →L[ℝ] E')) ∞
      (fun q : Q × N ↦ TotalSpace.mk' (E' →L[ℝ] E')
        (E := fun y : N ↦ TangentSpace I' y →L[ℝ] TangentSpace I' y) q.2
        ((J q.1).toEndomorphism q.2))) :
    ContMDiff (IQ.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : Q × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        ((pullback h (J q.1)).toEndomorphism q.2)) :=
  contMDiff_pullbackEndomorphism_family h hJ

/-- The pullback `h^* J` is the only almost complex structure on `M` for which every
differential of `h` is complex linear into `J`. -/
theorem eq_pullback_iff {K : SmoothAlmostComplexStructure I M} :
    K = pullback h J ↔
      ∀ (x : M) (v : TangentSpace I x),
        mfderiv I I' h x (K x v) = J (h x) (mfderiv I I' h x v) := by
  refine ⟨fun hK x v ↦ hK ▸ mfderiv_pullback_apply h J x v, fun hK ↦ ?_⟩
  ext x v
  have hinv := h.isInvertible_mfderiv (n := ∞) (x := x) (by simp)
  rw [pullback_apply, ← hK, hinv.inverse_apply_self]

/-- Pulling back along the identity does nothing. -/
@[simp]
theorem pullback_refl (K : SmoothAlmostComplexStructure I M) :
    pullback (Diffeomorph.refl I M ∞) K = K := by
  refine ((eq_pullback_iff _ K).2 fun x v ↦ ?_).symm
  simp only [Diffeomorph.coe_refl, mfderiv_id]
  rfl

/-- Pulling back is contravariantly functorial: `(g ∘ h)^* J = h^* (g^* J)`. -/
theorem pullback_trans (g : N ≃ₘ⟮I', I''⟯ P) (J : SmoothAlmostComplexStructure I'' P) :
    pullback (h.trans g) J = pullback h (pullback g J) := by
  refine ((eq_pullback_iff _ J).2 fun x v ↦ ?_).symm
  have hchain (w : TangentSpace I x) :
      mfderiv I I'' (h.trans g) x w = mfderiv I' I'' g (h x) (mfderiv I I' h x w) :=
    mfderiv_comp_apply x (g.mdifferentiable (by simp) (h x)) (h.mdifferentiable (by simp) x) w
  rw [hchain, hchain, mfderiv_pullback_apply, mfderiv_pullback_apply]
  rfl

end SmoothAlmostComplexStructure

namespace SmoothTwoForm

variable {σ : SmoothTwoForm I' N} {J : SmoothAlmostComplexStructure I' N}

/-- If `σ` tames `J`, then `h^* σ` tames `h^* J`. -/
theorem Tames.pullback (hJ : σ.Tames J) (h : M ≃ₘ⟮I, I'⟯ N) :
    SmoothTwoForm.Tames (SmoothForm.mpullback h h.contMDiff σ) (J.pullback h) := by
  rw [tames_iff]
  intro x v hv
  rw [SmoothForm.eval₂_mpullback, SmoothAlmostComplexStructure.mfderiv_pullback_apply]
  refine tames_iff.1 hJ (h x) _ fun h0 ↦ hv ?_
  rw [← (h.isInvertible_mfderiv (n := ∞) (x := x) (by simp)).inverse_apply_self v, h0, map_zero]

/-- If `σ` is invariant under `J`, then `h^* σ` is invariant under `h^* J`. -/
theorem Invariant.pullback (hJ : σ.Invariant J) (h : M ≃ₘ⟮I, I'⟯ N) :
    SmoothTwoForm.Invariant (SmoothForm.mpullback h h.contMDiff σ) (J.pullback h) := by
  rw [invariant_iff]
  intro x v w
  simp only [SmoothForm.eval₂_mpullback, SmoothAlmostComplexStructure.mfderiv_pullback_apply]
  exact invariant_iff.1 hJ (h x) _ _

/-- If `σ` is compatible with `J`, then `h^* σ` is compatible with `h^* J`. -/
theorem Compatible.pullback (hJ : σ.Compatible J) (h : M ≃ₘ⟮I, I'⟯ N) :
    SmoothTwoForm.Compatible (SmoothForm.mpullback h h.contMDiff σ) (J.pullback h) :=
  ⟨hJ.invariant.pullback h, hJ.tames.pullback h⟩

end SmoothTwoForm

end TauCeti
