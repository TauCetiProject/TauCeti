/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Hadamard
public import TauCeti.Geometry.Manifold.ContMDiff.Prod
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic

/-!
# Linearizing an embedding at a fixed point

Let `f : E → F` be a `C^(n+1)` map between real normed spaces, with `F` complete, which is a
`C^n` smooth embedding, fixes the origin, and has a continuous linear equivalence `L` as its
derivative there. Rescaling `f` about the origin gives the embeddings `x ↦ t⁻¹ • f (t • x)` for
`0 < t ≤ 1`, which converge to `L` as `t → 0`. Hadamard's factorization `f y = A y y`, with `A y`
the derivative of `f` averaged along the segment from `0` to `y` (`hadamardFactor f 0`), writes the
rescaled map as `x ↦ A (t • x) x`. This formula still makes sense at `t = 0`, where it is `L`, and
is jointly `C^n` in `(t, x)`. The result is a smooth isotopy `TauCeti.linearizationIsotopy` from
`L` to `f` through embeddings, all of which fix the origin.

The isotopy supplies the vector-space linearization step in the proof of the disc theorem,
replacing an embedding of `ℝⁿ` fixing the origin by its derivative there. In this vector-space
case, connecting the derivatives uses the connectedness of the group of linear maps of positive
determinant. The general-manifold disc theorem says that two embeddings of `ℝⁿ` into a manifold,
sending `0` to the same point, whose derivatives at `0` differ by a linear map of positive
determinant, are isotopic rel `0`. That case also requires shrinking the embeddings into a common
chart and assembling the isotopy; these steps are not supplied by this construction.

## Main definitions and results

* `TauCeti.linearizationIsotopy`: the smooth isotopy from the derivative `L` at the origin to `f`.
* `TauCeti.linearizationIsotopy_apply_of_ne_zero`: at a nonzero time `t` the isotopy is the
  rescaling `x ↦ t⁻¹ • f (t • x)`; at time `0` it is `L` (`SmoothIsotopy.apply_zero`).
* `TauCeti.linearizationIsotopy_apply_mk_zero`: every stage of the isotopy fixes the origin.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, Theorem 6.6 (the disc
  theorem) and the isotopy of tubular neighbourhoods used in its proof.
* R. Palais, *Extending diffeomorphisms*, Proc. Amer. Math. Soc. 11 (1960), 274–277, for the disc
  theorem.
-/

public section

noncomputable section

open Manifold
open scoped ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {n : ℕ∞} {f : E → F}

/-- The rescaling `x ↦ t⁻¹ • f (t • x)` of `f` about the origin, written through Hadamard's
factorization so that it is defined at `t = 0` too, where it is the derivative of `f`. -/
private def linearizationMotion (f : E → F) (p : ℝ × E) : F :=
  hadamardFactor f 0 (p.1 • p.2) p.2

private theorem linearizationMotion_zero (f : E → F) (x : E) :
    linearizationMotion f (0, x) = fderiv ℝ f 0 x := by
  simp [linearizationMotion]

private theorem linearizationMotion_of_ne_zero (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) {t : ℝ}
    (ht : t ≠ 0) (x : E) : linearizationMotion f (t, x) = t⁻¹ • f (t • x) := by
  have h := ContDiff.sub_eq_hadamardFactor_apply f hf 0 (t • x)
  rw [hf0, sub_zero, sub_zero, map_smul] at h
  rw [linearizationMotion, h, smul_smul, inv_mul_cancel₀ ht, one_smul]

private theorem linearizationMotion_mk_zero (f : E → F) (t : ℝ) :
    linearizationMotion f (t, 0) = 0 := by
  simp [linearizationMotion]

private theorem contDiff_linearizationMotion (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (linearizationMotion f) :=
  ((ContDiff.contDiff_hadamardFactor_of_succ n f hf 0).comp
    (contDiff_fst.smul contDiff_snd)).clm_apply contDiff_snd

/-- Every stage `x ↦ t⁻¹ • f (t • x)`, `t ≠ 0`, of the rescaling of a smooth embedding `f` is a
smooth embedding: it is `f` conjugated by two dilations. -/
private theorem isSmoothEmbedding_linearizationMotion_of_ne_zero (hf : ContDiff ℝ 1 f)
    (hf0 : f 0 = 0) (hemb : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) n f) {t : ℝ} (ht : t ≠ 0) :
    IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) n (fun x => linearizationMotion f (t, x)) := by
  let dilate : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 t ht)
  -- Dilation by `t⁻¹` of the target, as a `C^n` diffeomorphism; Mathlib's
  -- `ContinuousLinearEquiv.toDiffeomorph` only provides the `C^∞` one.
  let shrink : F ≃ₘ^n⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ F :=
    { toEquiv := (ContinuousLinearEquiv.smulLeft (Units.mk0 t ht)⁻¹ : F ≃L[ℝ] F).toEquiv
      contMDiff_toFun := (ContinuousLinearEquiv.smulLeft (Units.mk0 t ht)⁻¹ :
        F ≃L[ℝ] F).contDiff.contMDiff
      contMDiff_invFun := (ContinuousLinearEquiv.smulLeft (Units.mk0 t ht)⁻¹ :
        F ≃L[ℝ] F).symm.contDiff.contMDiff }
  have h : (fun x => linearizationMotion f (t, x)) = shrink ∘ f ∘ dilate := by
    funext x
    simp [linearizationMotion_of_ne_zero hf hf0 ht, shrink, dilate, ← Diffeomorph.coe_toEquiv,
      Units.smul_def]
  rw [h]
  exact isSmoothEmbedding_diffeomorph_comp
    (isSmoothEmbedding_comp_continuousLinearEquiv dilate hemb) shrink

/-- **The linearization isotopy.** A smooth embedding `f : E → F` which is `C^(n+1)`, fixes the
origin, and has derivative a continuous linear equivalence `L` there, is smoothly isotopic to `L`.
At time `t ≠ 0` the isotopy is the rescaling `x ↦ t⁻¹ • f (t • x)`
(`linearizationIsotopy_apply_of_ne_zero`), at time `0` it is `L`, and it fixes the origin
throughout (`linearizationIsotopy_apply_mk_zero`). -/
def linearizationIsotopy (f : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) n E F) (L : E ≃L[ℝ] F)
    (hf : ContDiff ℝ (n + 1) f) (hL : HasFDerivAt f (L : E →L[ℝ] F) 0) (hf0 : f 0 = 0) :
    SmoothIsotopy (SmoothEmbedding.ofContinuousLinearEquiv L).toContMDiffMap f.toContMDiffMap where
  toContMDiffMap := ⟨fun p => linearizationMotion f ((p.1 : ℝ), p.2),
    (contMDiff_prod_modelWithCornersSelf_iff.2 (contDiff_linearizationMotion hf).contMDiff).comp
      ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk contMDiff_snd)⟩
  map_zero_left x := by simp [linearizationMotion_zero, hL.fderiv]
  map_one_left x := by
    simp [linearizationMotion_of_ne_zero (hf.of_le le_add_self) hf0 one_ne_zero]
  isSmoothEmbedding t := by
    simp only [ContMDiffMap.coeFn_mk]
    by_cases ht : (t : ℝ) = 0
    · have h : (fun x => linearizationMotion f ((t : ℝ), x)) = L := by
        funext x
        simp [ht, linearizationMotion_zero, hL.fderiv]
      rw [h]
      exact isSmoothEmbedding_continuousLinearEquiv L
    · exact isSmoothEmbedding_linearizationMotion_of_ne_zero (hf.of_le le_add_self) hf0
        f.isSmoothEmbedding ht

variable {g : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) n E F} {L : E ≃L[ℝ] F} {hg : ContDiff ℝ (n + 1) g}
  {hL : HasFDerivAt g (L : E →L[ℝ] F) 0} {hg0 : g 0 = 0}

/-- At a nonzero time `t`, the linearization isotopy is the rescaling `x ↦ t⁻¹ • g (t • x)`. -/
theorem linearizationIsotopy_apply_of_ne_zero {t : unitInterval} (ht : (t : ℝ) ≠ 0) (x : E) :
    linearizationIsotopy g L hg hL hg0 (t, x) = (t : ℝ)⁻¹ • g ((t : ℝ) • x) :=
  linearizationMotion_of_ne_zero (hg.of_le le_add_self) hg0 ht x

/-- Every stage of the linearization isotopy fixes the origin. -/
@[simp]
theorem linearizationIsotopy_apply_mk_zero (t : unitInterval) :
    linearizationIsotopy g L hg hL hg0 (t, 0) = 0 :=
  linearizationMotion_mk_zero g t

end TauCeti
