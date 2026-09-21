/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Semilinear composition of derivatives within sets

Composing on both sides by continuous semilinear maps with inverse scalar homomorphisms
transports a Fréchet derivative, even at boundary points of a set. This includes conjugating
both the argument and value of a complex differentiable function.

`HasFDerivWithinAt.comp_semilinear` extends Mathlib's `HasFDerivAt.comp_semilinear` to
arbitrary source and target sets. The local `comp_semilinear_of_tendsto` form only requires
that `R` approaches the target set near the point under consideration. The corresponding
`DifferentiableWithinAt` lemmas transport differentiability without specifying a derivative.
-/

public section

open Asymptotics Filter Function Set Topology

variable
  {𝕜 𝕜' V V' W W' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  {σ : 𝕜 →+* 𝕜'} {σ' : 𝕜' →+* 𝕜}
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup V'] [NormedSpace 𝕜' V']
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]
  [SeminormedAddCommGroup W'] [NormedSpace 𝕜' W']
  [RingHomIsometric σ] [RingHomInvPair σ σ'] (L : W →SL[σ] W') (R : V' →SL[σ'] V)
  {f : V → W} {f' : V →L[𝕜] W} {s : Set V'} {t : Set V} {x : V'}

/-- If `L` and `R` are continuous semilinear maps with inverse scalar homomorphisms, and `R`
tends to `R x` within `t` as its argument tends to `x` within `s`, then a derivative of `f`
within `t` at `R x` transports to a derivative of `L ∘ f ∘ R` within `s` at `x`. The two
semilinear twists cancel in the resulting derivative. -/
lemma HasFDerivWithinAt.comp_semilinear_of_tendsto
    (hf : HasFDerivWithinAt f f' t (R x)) (hR : Tendsto R (𝓝[s] x) (𝓝[t] (R x))) :
    HasFDerivWithinAt (L ∘ f ∘ R) (L.comp (f'.comp R)) s x := by
  have : RingHomIsometric σ' := .inv σ
  rw [hasFDerivWithinAt_iff_isLittleO] at ⊢ hf
  have hsmall := hf.comp_tendsto hR
  have hRsub : ((fun y => y - R x) ∘ R) =O[𝓝[s] x] fun y => y - x := by
    simpa [Function.comp_def, map_sub] using R.isBigO_sub (𝓝[s] x) x
  simpa [Function.comp_def, map_sub] using
    ((L.isBigO_comp _ _).trans_isLittleO hsmall).trans_isBigO hRsub

/-- If `L` and `R` are continuous semilinear maps with inverse scalar homomorphisms, and `R`
maps `s` into `t`, then a derivative of `f` within `t` at `R x` transports to a derivative of
`L ∘ f ∘ R` within `s` at `x`. -/
lemma HasFDerivWithinAt.comp_semilinear
    (hf : HasFDerivWithinAt f f' t (R x)) (hR : MapsTo R s t) :
    HasFDerivWithinAt (L ∘ f ∘ R) (L.comp (f'.comp R)) s x :=
  hf.comp_semilinear_of_tendsto L R
    (R.continuous.continuousAt.continuousWithinAt.tendsto_nhdsWithin hR)

/-- Composing on both sides by continuous semilinear maps with inverse scalar homomorphisms
preserves differentiability within sets, provided the inner map tends to the target point
within the target set. -/
lemma DifferentiableWithinAt.comp_semilinear₂_of_tendsto
    (hf : DifferentiableWithinAt 𝕜 f t (R x)) (hR : Tendsto R (𝓝[s] x) (𝓝[t] (R x))) :
    DifferentiableWithinAt 𝕜' (L ∘ f ∘ R) s x :=
  (hf.hasFDerivWithinAt.comp_semilinear_of_tendsto L R hR).differentiableWithinAt

/-- Composing on both sides by continuous semilinear maps with inverse scalar homomorphisms
preserves differentiability within sets when the inner map carries the source set into the
target set. -/
lemma DifferentiableWithinAt.comp_semilinear₂
    (hf : DifferentiableWithinAt 𝕜 f t (R x)) (hR : MapsTo R s t) :
    DifferentiableWithinAt 𝕜' (L ∘ f ∘ R) s x :=
  (hf.hasFDerivWithinAt.comp_semilinear L R hR).differentiableWithinAt
