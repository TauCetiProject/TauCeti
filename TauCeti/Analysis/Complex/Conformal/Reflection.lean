/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Complex.Basic

/-!
# Conjugation and holomorphic domains

This file records the elementary conjugation API used by the conformal-mapping roadmap's
Schwarz-reflection layer.  Mathlib already proves the pointwise fact
`DifferentiableAt.conj_conj`: if `f` is complex differentiable at `conj z`, then
`z ↦ conj (f (conj z))` is complex differentiable at `z`.  The lemmas here package the
corresponding within-set statement for reflected images, which is the form needed before the
real-axis Schwarz reflection principle.  The private semilinear within-set helper adapts the
proof pattern of Mathlib's `HasFDerivAt.comp_semilinear`.
-/

public section

namespace TauCeti

open Complex Filter Set
open scoped ComplexConjugate

variable {f : ℂ → ℂ} {S : Set ℂ}

private lemma starRingEnd_eq_starL (z : ℂ) :
    (starRingEnd ℂ) z = (starL ℂ : ℂ ≃L⋆[ℂ] ℂ) z := by
  rw [starL_apply, starRingEnd_apply]

private lemma HasFDerivWithinAt.comp_semilinear_preimage
    {𝕜 V V' W W' : Type*} [NontriviallyNormedField 𝕜] {σ σ' : RingHom 𝕜 𝕜}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup V'] [NormedSpace 𝕜 V']
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [NormedAddCommGroup W'] [NormedSpace 𝕜 W']
    [RingHomIsometric σ] [RingHomInvPair σ σ']
    (L : W →SL[σ] W') (R : V' →SL[σ'] V)
    {g : V → W} {g' : V →L[𝕜] W} {T : Set V} {x : V'}
    (hg : HasFDerivWithinAt g g' T (R x)) :
    HasFDerivWithinAt (L ∘ g ∘ R) (L.comp (g'.comp R)) (R ⁻¹' T) x := by
  rw [hasFDerivWithinAt_iff_isLittleO] at ⊢ hg
  have : RingHomIsometric σ' := .inv σ
  have hR : Tendsto R (nhdsWithin x (R ⁻¹' T)) (nhdsWithin (R x) T) :=
    R.continuous.continuousAt.continuousWithinAt.tendsto_nhdsWithin (mapsTo_preimage R T)
  have hsmall := hg.comp_tendsto hR
  have hRsub : ((fun x' => x' - R x) ∘ R) =O[nhdsWithin x (R ⁻¹' T)] fun x' => x' - x := by
    simpa [Function.comp_def, map_sub] using R.isBigO_sub (nhdsWithin x (R ⁻¹' T)) x
  simpa [Function.comp_def, map_sub] using
    ((L.isBigO_comp _ _).trans_isLittleO hsmall).trans_isBigO hRsub

/--
Antiholomorphic-composition prerequisite for Schwarz reflection.

If `f` is holomorphic on `S`, then `z ↦ conj (f (conj z))` is holomorphic on the reflected
set `conj '' S`.
-/
lemma differentiableOn_conj_conj (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
      ((starRingEnd ℂ) '' S) := by
  intro z hz
  have hzS : (starRingEnd ℂ) z ∈ S :=
    (Set.mem_image_iff_of_inverse
      (Function.Involutive.leftInverse (starRingEnd_self_apply : Function.Involutive
        (starRingEnd ℂ)))
      (Function.Involutive.rightInverse (starRingEnd_self_apply : Function.Involutive
        (starRingEnd ℂ)))).mp hz
  rcases (hf ((starRingEnd ℂ) z) hzS) with ⟨f', hf'⟩
  have hstar :=
    HasFDerivWithinAt.comp_semilinear_preimage
      (starL ℂ).toContinuousLinearMap (starL ℂ).toContinuousLinearMap (x := z) hf'
  rw [Function.Involutive.image_eq_preimage_symm
    (starRingEnd_self_apply : Function.Involutive (starRingEnd ℂ))]
  have hfun :
      (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) =
        (⇑(starL ℂ).toContinuousLinearMap ∘ f ∘ ⇑(starL ℂ).toContinuousLinearMap) := by
    funext w
    dsimp [Function.comp_def]
    rw [starRingEnd_eq_starL, starRingEnd_eq_starL]
  have hset : (starRingEnd ℂ) ⁻¹' S = ⇑(starL ℂ).toContinuousLinearMap ⁻¹' S := by
    ext w
    -- Expose membership in the preimages before rewriting across the two conjugation coercions.
    change (starRingEnd ℂ) w ∈ S ↔ ((starL ℂ).toContinuousLinearMap : ℂ → ℂ) w ∈ S
    have hw : (starRingEnd ℂ) w = ((starL ℂ).toContinuousLinearMap : ℂ → ℂ) w := by
      rw [starRingEnd_eq_starL]
      rfl
    rw [hw]
  rw [hfun, hset]
  exact hstar.differentiableWithinAt

/--
Conjugating both source and target preserves holomorphicity on domains, in both directions.
-/
@[simp]
lemma differentiableOn_conj_conj_iff :
    DifferentiableOn ℂ (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
        ((starRingEnd ℂ) '' S) ↔
      DifferentiableOn ℂ f S := by
  constructor
  · intro h
    have htwice :=
      differentiableOn_conj_conj
        (S := (starRingEnd ℂ) '' S)
        (f := fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) h
    simpa [Function.Involutive.image_eq_preimage_symm
      (starRingEnd_self_apply : Function.Involutive (starRingEnd ℂ)), Set.preimage_preimage,
      Function.comp_def] using htwice
  · exact differentiableOn_conj_conj

end TauCeti
