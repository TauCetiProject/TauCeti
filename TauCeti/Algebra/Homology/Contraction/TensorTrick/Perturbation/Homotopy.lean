/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.TensorTrick.Perturbation.Basic
public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoalgHom
import Mathlib.Tactic.LinearCombination

/-!
# The perturbed tensor-trick homotopy

The coalgebra perturbation lemma preserves not only the inclusion and projection, but also the
coderivation identity of the homotopy. If `i'`, `p'`, `h'` are the perturbed tensor-trick maps,
then `h'` is an odd coderivation along `id` and `i' p'`. This supplies the bar homotopy needed to
compare an A-infinity algebra with its transferred structure.

The perturbation need not lower tensor length here: invertibility of `1 + δ h` suffices.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* J. Huebschmann and T. Kadeishvili, *Small models for chain algebras*, Mathematische Zeitschrift
  207 (1991), 245--280.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti.LinearSpecialContraction

open ReducedTensorWords

universe uR uM uN

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN)
  {G : InternalGrading R M} {H : InternalGrading R N}
  (hdM : LinearMap.IsHomogeneous dM G.piece G.piece 1)
  (hh : LinearMap.IsHomogeneous c.homotopy G.piece G.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl H.piece G.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj G.piece H.piece 0)
  {δ : Module.End R (ReducedTensorWords R M)}
  (hsq : (gradedCoderiv G (dM ∘ₗ letter R M) 1 + δ) ∘ₗ
    (gradedCoderiv G (dM ∘ₗ letter R M) 1 + δ) =
      gradedCoderiv G (dM ∘ₗ letter R M) 1 ∘ₗ gradedCoderiv G (dM ∘ₗ letter R M) 1)
  (hU : IsUnit (1 + δ * (c.reducedTensorWords G H hdM hh hincl hproj).homotopy))

/-- The co-Leibniz rule for a perturbed homotopy `h'`, in terms of a comultiplication `D`,
from the corresponding rules for `h` and `δ` and the perturbation identities
`h' (1 + δ h) = h`, `i' + h' δ i = i`, `p' (1 + δ h) = p`. -/
private theorem comp_perturbed_homotopy_eq {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] {D : X →ₗ[R] X ⊗[R] X} {h h' δ τ : X →ₗ[R] X}
    {i i' : Y →ₗ[R] X} {p p' : X →ₗ[R] Y}
    (hfix : h' + h' ∘ₗ δ ∘ₗ h = h) (hih : i' + h' ∘ₗ δ ∘ₗ i = i)
    (hpfix : p' + p' ∘ₗ δ ∘ₗ h = p) (hp'h : p' ∘ₗ h = 0) (hp'π : p' ∘ₗ (i ∘ₗ p) = p)
    (hh'h : h' ∘ₗ h = 0) (hh'π : h' ∘ₗ (i ∘ₗ p) = 0) (hh'τh : h' ∘ₗ τ ∘ₗ h = 0)
    (hττ : τ ∘ₗ τ = LinearMap.id)
    (hΔh : D ∘ₗ h = (TensorProduct.map h (i ∘ₗ p) + TensorProduct.map τ h) ∘ₗ D)
    (hΔδ : D ∘ₗ δ = (TensorProduct.map δ LinearMap.id + TensorProduct.map τ δ) ∘ₗ D)
    (hsurj : Function.Surjective (1 + δ * h : Module.End R X)) :
    D ∘ₗ h' = (TensorProduct.map h' (i' ∘ₗ p') + TensorProduct.map τ h') ∘ₗ D := by
  -- Both sides agree after precomposition with the surjective map `1 + δ h`.
  set C := TensorProduct.map h' (i' ∘ₗ p') + TensorProduct.map τ h'
  have hΔδh : D ∘ₗ δ ∘ₗ h = ((TensorProduct.map δ LinearMap.id + TensorProduct.map τ δ) ∘ₗ
      (TensorProduct.map h (i ∘ₗ p) + TensorProduct.map τ h)) ∘ₗ D := by
    rw [← LinearMap.comp_assoc, hΔδ, LinearMap.comp_assoc, hΔh, LinearMap.comp_assoc]
  have h1 : D ∘ₗ h' + D ∘ₗ h' ∘ₗ δ ∘ₗ h =
      (TensorProduct.map h (i ∘ₗ p) + TensorProduct.map τ h) ∘ₗ D := by
    rw [← hΔh, ← LinearMap.comp_add, hfix]
  have h2 : C ∘ₗ D + C ∘ₗ D ∘ₗ δ ∘ₗ h =
      (TensorProduct.map h (i ∘ₗ p) + TensorProduct.map τ h) ∘ₗ D := by
    -- Of the eight tensor terms, four vanish by the side conditions. The remaining terms
    -- combine using the fixed-point equations for `h'`, `p'`, and `i'`.
    rw [hΔδh]
    simp only [C, LinearMap.add_comp, LinearMap.comp_add, ← LinearMap.comp_assoc,
      ← TensorProduct.map_comp, LinearMap.id_comp]
    simp only [LinearMap.comp_assoc, hp'π, hp'h, hh'π, hh'h, hh'τh,
      hττ, LinearMap.id_comp, LinearMap.comp_id,
      TensorProduct.map_zero_left, TensorProduct.map_zero_right, LinearMap.zero_comp,
      LinearMap.comp_zero, add_zero, zero_add]
    have hπ : i' ∘ₗ p + h' ∘ₗ δ ∘ₗ (i ∘ₗ p) = i ∘ₗ p := by
      simpa only [LinearMap.add_comp, LinearMap.comp_assoc] using congrArg (· ∘ₗ p) hih
    have e1 := congrArg (fun f ↦ TensorProduct.map h' (i' ∘ₗ f) ∘ₗ D) hpfix
    have e2 := congrArg (fun f ↦ TensorProduct.map f (i' ∘ₗ p) ∘ₗ D) hfix
    have e3 := congrArg (fun f ↦ TensorProduct.map τ f ∘ₗ D) hfix
    have e4 := congrArg (fun f ↦ TensorProduct.map h f ∘ₗ D) hπ
    simp only [LinearMap.comp_add, TensorProduct.map_add_left, TensorProduct.map_add_right,
      LinearMap.add_comp] at e1 e2 e3 e4
    linear_combination (norm := abel) e1 + e2 + e3 + e4
  have key (f : X →ₗ[R] X ⊗[R] X) : f ∘ₗ (1 + δ * h : Module.End R X) = f + f ∘ₗ δ ∘ₗ h := by
    rw [Module.End.mul_eq_comp, LinearMap.comp_add, Module.End.one_eq_id, LinearMap.comp_id]
  refine (LinearMap.cancel_right hsurj).mp ?_
  rw [key, key, LinearMap.comp_assoc, LinearMap.comp_assoc]
  exact h1.trans h2.symm

/-- The perturbed tensor-trick homotopy is an odd coderivation along `id` and the perturbed
inclusion followed by the perturbed projection. No length-lowering hypothesis is needed. -/
theorem isGradedCoderivationAlong_reducedTensorWords_perturb_homotopy
    (hδ : IsGradedCoderivation G 1 δ) :
    IsGradedCoderivationAlong G 1 LinearMap.id
      (((c.reducedTensorWords G H hdM hh hincl hproj).perturb δ hsq hU).incl ∘ₗ
        ((c.reducedTensorWords G H hdM hh hincl hproj).perturb δ hsq hU).proj)
      ((c.reducedTensorWords G H hdM hh hincl hproj).perturb δ hsq hU).homotopy := by
  classical
  -- Cache the additive instances before introducing abbreviations for the tensor-trick maps.
  let : AddCommGroup (ReducedTensorWords R M) := inferInstance
  let : AddCommGroup (ReducedTensorWords R M ⊗[R] ReducedTensorWords R M) := inferInstance
  -- Compare the two sides after precomposition with the surjective map `1 + δ h`.
  set T := c.reducedTensorWords G H hdM hh hincl hproj
  set i := T.incl
  set p := T.proj
  set h := T.homotopy
  set τ := ReducedTensorWords.map (R := R) (G.koszulTwist 1)
  set π := i ∘ₗ p
  set i' := (T.perturb δ hsq hU).incl
  set p' := (T.perturb δ hsq hU).proj
  set h' := (T.perturb δ hsq hU).homotopy
  -- Fixed-point equations and annihilation identities for the perturbed maps.
  have hfix : h' + h' ∘ₗ δ ∘ₗ h = h := by
    simpa only [Module.End.mul_eq_comp, LinearMap.comp_add, Module.End.one_eq_id,
      LinearMap.comp_id] using T.perturb_homotopy_comp_one_add_mul δ hsq hU
  have hih : i' + h' ∘ₗ δ ∘ₗ i = i := T.perturb_incl_add_homotopy_comp δ hsq hU
  have hp'h : p' ∘ₗ h = 0 := T.perturb_proj_comp_homotopy δ hsq hU
  have hp'π : p' ∘ₗ π = p := by
    rw [← LinearMap.comp_assoc, T.perturb_proj_comp_incl, LinearMap.id_comp]
  have hh'h : h' ∘ₗ h = 0 := by
    simp only [h', h, perturb_homotopy, LinearMap.sub_comp, LinearMap.comp_assoc,
      T.homotopy_comp_homotopy, LinearMap.comp_zero, sub_self]
  have hh'π : h' ∘ₗ π = 0 := by
    simp only [h', π, i, p, perturb_homotopy, LinearMap.sub_comp, LinearMap.comp_assoc,
      T.homotopy_comp_incl_assoc, LinearMap.comp_zero, sub_self]
  have hτh : τ ∘ₗ h = -(h ∘ₗ τ) := by
    simp only [h, T, reducedTensorWords_homotopy]
    exact c.map_koszulTwist_comp_reducedTensorWordsHomotopy G H hh hincl hproj
  have hh'τh : h' ∘ₗ τ ∘ₗ h = 0 := by
    rw [hτh, LinearMap.comp_neg, ← LinearMap.comp_assoc, hh'h, LinearMap.zero_comp]
    exact neg_zero
  have hττ : τ ∘ₗ τ = LinearMap.id := by
    rw [← ReducedTensorWords.map_comp, G.koszulTwist_comp_self, ReducedTensorWords.map_id]
  -- Expand deconcatenation using the two unperturbed co-Leibniz rules.
  have hΔh : deconcatenation R M ∘ₗ h =
      (TensorProduct.map h π + TensorProduct.map τ h) ∘ₗ deconcatenation R M := by
    simpa only [h, π, i, p, T, τ, reducedTensorWords_incl, reducedTensorWords_proj,
      reducedTensorWords_homotopy, ← ReducedTensorWords.map_comp] using
      c.deconcatenation_comp_reducedTensorWordsHomotopy G
  have hΔδ : deconcatenation R M ∘ₗ δ =
      (TensorProduct.map δ LinearMap.id + TensorProduct.map τ δ) ∘ₗ deconcatenation R M := by
    rw [isGradedCoderivation_iff.mp hδ, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_def, LinearMap.add_comp]
  have hpfix : p' + p' ∘ₗ δ ∘ₗ h = p := by
    simpa only [Module.End.mul_eq_comp, LinearMap.comp_add, Module.End.one_eq_id,
      LinearMap.comp_id] using T.perturb_proj_comp_one_add_mul δ hsq hU
  -- The co-Leibniz rule follows from the fixed-point equations and the side conditions.
  have heq := comp_perturbed_homotopy_eq hfix hih hpfix hp'h hp'π hh'h hh'π hh'τh hττ hΔh hΔδ
    ((Module.End.isUnit_iff _).mp hU).2
  rw [isGradedCoderivationAlong_iff, LinearMap.rTensor_def]
  simpa only [← LinearMap.comp_assoc, ← TensorProduct.map_comp,
    LinearMap.id_comp, LinearMap.comp_id, LinearMap.add_comp] using heq

end TauCeti.LinearSpecialContraction
