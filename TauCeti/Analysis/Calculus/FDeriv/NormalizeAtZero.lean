/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse

/-!
# Normalizing a map by its derivative at zero

Precomposing a map `g` with the inverse of its derivative at `0` gives a map with derivative the
identity at `0`. For a jointly smooth family `B q` this normalization costs one derivative, since
it involves the derivatives `J q` of the `B q` at `0`. This is how a family of maps `B q` with
`B q 0 = q` is turned into a local addition in the sense of Kriegl and Michor.

* `TauCeti.hasFDerivAt_comp_inverse_fderiv_zero`: the map `v ↦ g (J⁻¹ v)`, with `J` the
  derivative of `g` at `0`, has derivative the identity at `0` when `J` is invertible.
* `TauCeti.exists_isOpen_contDiffOn_comp_inverse_fderiv_zero`: the normalized family
  `(q, v) ↦ B q ((J q)⁻¹ v)` of a jointly `C^(n + 1)` family is jointly `C^n` near the points
  `(q, 0)` where `J q` is invertible.

## References

* A. Kriegl and P. W. Michor, *The Convenient Setting of Global Analysis*, Mathematical Surveys
  and Monographs 53, American Mathematical Society, 1997, Section 42.4 (local additions).
-/

public section

open Set Function

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F X : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Precomposing a map `g` with the inverse of its derivative at `0`, when that derivative is
invertible, gives a map with derivative the identity at `0`. -/
theorem hasFDerivAt_comp_inverse_fderiv_zero {g : E → F} (hinv : (fderiv 𝕜 g 0).IsInvertible) :
    HasFDerivAt (fun v ↦ g ((fderiv 𝕜 g 0).inverse v)) (ContinuousLinearMap.id 𝕜 F) 0 := by
  by_cases hg : DifferentiableAt 𝕜 g 0
  · have hg' : HasFDerivAt g (fderiv 𝕜 g 0) ((fderiv 𝕜 g 0).inverse 0) := by
      rw [map_zero]
      exact hg.hasFDerivAt
    have h := hg'.comp (0 : F) (fderiv 𝕜 g 0).inverse.hasFDerivAt
    rwa [hinv.self_comp_inverse] at h
  -- Otherwise the derivative is `0`, which is invertible only when `F` is trivial.
  · obtain ⟨e, he⟩ := hinv
    rw [fderiv_zero_of_not_differentiableAt hg] at he
    have : Subsingleton F := ⟨fun y y' ↦ by
      rw [← e.apply_symm_apply y, ← e.apply_symm_apply y', ← ContinuousLinearEquiv.coe_coe, he]
      simp⟩
    exact (hasFDerivAt_of_subsingleton _ _).congr_fderiv (Subsingleton.elim _ _)

/-- **Normalizing a family by its derivatives at zero.** Let `B` be jointly `C^(n + 1)` on an
open set `s`, and write `J q` for the derivative of `B q` at `0`. Then the normalized family
`(q, v) ↦ B q ((J q)⁻¹ v)` is jointly `C^n` on an open set `s'` containing every `(q, 0)` with
`(q, 0) ∈ s` and `J q` invertible, and `J q` is invertible for every `(q, v) ∈ s'`. -/
theorem exists_isOpen_contDiffOn_comp_inverse_fderiv_zero [CompleteSpace E] {n : WithTop ℕ∞}
    {B : X → E → F} {s : Set (X × E)} (hB : ContDiffOn 𝕜 (n + 1) (uncurry B) s)
    (hs : IsOpen s) :
    ∃ s' : Set (X × F), IsOpen s' ∧
      (∀ q, (q, 0) ∈ s → (fderiv 𝕜 (B q) 0).IsInvertible → (q, 0) ∈ s') ∧
      (∀ p ∈ s', (fderiv 𝕜 (B p.1) 0).IsInvertible) ∧
      ContDiffOn 𝕜 n (fun p : X × F ↦ B p.1 ((fderiv 𝕜 (B p.1) 0).inverse p.2)) s' := by
  set J : X → E →L[𝕜] F := fun q ↦ fderiv 𝕜 (B q) 0
  set S : Set X := {q | (q, 0) ∈ s}
  have hS : IsOpen S := hs.preimage (continuous_id.prodMk continuous_const)
  have hJ : ∀ q ∈ S, ContDiffAt 𝕜 n J q := fun q hq ↦
    (hB.contDiffAt (hs.mem_nhds hq)).fderiv contDiffAt_const le_rfl
  set S' : Set X := S ∩ J ⁻¹' {L | L.IsInvertible}
  have hS' : IsOpen S' := ContinuousOn.isOpen_inter_preimage
    (fun q hq ↦ (hJ q hq).continuousAt.continuousWithinAt) hS
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  -- The fibre change `(q, v) ↦ (q, (J q)⁻¹ v)` is `C^n` over `S'`.
  have hσ : ∀ p : X × F, p.1 ∈ S' →
      ContDiffAt 𝕜 n (fun p : X × F ↦ (p.1, (J p.1).inverse p.2)) p := fun p hp ↦
    contDiffAt_fst.prodMk
      ((((hJ p.1 hp.1).clm_inverse hp.2).comp p contDiffAt_fst).clm_apply contDiffAt_snd)
  refine ⟨(S' ×ˢ univ) ∩ (fun p : X × F ↦ (p.1, (J p.1).inverse p.2)) ⁻¹' s,
    ContinuousOn.isOpen_inter_preimage (fun p hp ↦ (hσ p hp.1).continuousAt.continuousWithinAt)
      (hS'.prod isOpen_univ) hs, fun q hq hJq ↦ ⟨⟨⟨hq, hJq⟩, mem_univ _⟩, by simpa using hq⟩,
    fun p hp ↦ hp.1.1.2, fun p hp ↦ ?_⟩
  exact ((hB.contDiffAt (hs.mem_nhds hp.2)).of_le le_self_add).comp p (hσ p hp.1.1)
    |>.contDiffWithinAt

end TauCeti
