/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Calculus.FDeriv.Comp
public import TauCeti.RepresentationTheory.Continuous.RightInverse
import TauCeti.Topology.OpenPartialHomeomorph.MulAction

/-!
# Equivariant straightening of invariant defining functions

Let a finite group act linearly on a Banach space, and let `r` be a smooth invariant map to a
finite-dimensional space, vanishing at the origin with surjective derivative `q`. There is a
smooth equivariant local coordinate change `e`, tangent to the identity, such that `q ∘ e = r`.
Both domains of the coordinate change are invariant. In particular, when the components of `r`
are labelled boundary defining functions, their inequalities and zero sets become the linear
inequalities and zero sets of the same labelled components of `q`.

Only invariance near the origin is required. Thus the construction can be applied after
linearizing a smooth finite action in a Bochner chart. The construction retains all group
elements, including ineffective ones.

The construction averages a right inverse `s` of `q` and applies the inverse function theorem
to `y ↦ y + s (r y - q y)`.

## References

* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46 (1945),
  372–381, for finite-group averaging in local coordinates.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 4.12, for submersion
  coordinates.
-/

public noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace ContRepresentation

variable {𝕜 G E F : Type*} [RCLike 𝕜] [Group G] [Finite G]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {n : WithTop ℕ∞}

/-- **Equivariant submersion coordinates.** A locally invariant `C^n` map vanishing at zero,
with surjective derivative `q`, can be straightened to `q` by an equivariant local coordinate
change tangent to the identity. Its source lies in the prescribed open set `U`, both source
and target are invariant, and both directions are `C^n` on their entire domains. -/
theorem exists_equivariant_straightening (ρ : ContRepresentation 𝕜 G E)
    {r : E → F} {q : E →L[𝕜] F} {U : Set E}
    (hr : ContDiffOn 𝕜 n r U) (hU : IsOpen U) (h0U : (0 : E) ∈ U)
    (hn : 1 ≤ n) (hr0 : r 0 = 0) (hd : HasFDerivAt r q 0)
    (hq : Function.Surjective q) (hinv : ∀ g : G, r ∘ ρ g =ᶠ[𝓝 0] r) :
    ∃ e : OpenPartialHomeomorph E E,
      (0 : E) ∈ e.source ∧ e 0 = 0 ∧ e.source ⊆ U ∧
      HasFDerivAt e (ContinuousLinearMap.id 𝕜 E) 0 ∧
      ContDiffOn 𝕜 n e e.source ∧ ContDiffOn 𝕜 n e.symm e.target ∧
      (∀ y ∈ e.source, q (e y) = r y) ∧
      (∀ z ∈ e.target, r (e.symm z) = q z) ∧
      (∀ (g : G) (y : E), y ∈ e.source →
        ρ g y ∈ e.source ∧ e (ρ g y) = ρ g (e y)) ∧
      ∀ (g : G) (z : E), z ∈ e.target →
        ρ g z ∈ e.target ∧ e.symm (ρ g z) = ρ g (e.symm z) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Fintype.card G : 𝕜) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hqi (g : G) : q.comp (ρ g) = q :=
    hd.comp_eq_of_eventuallyEq (ρ g).hasFDerivAt (map_zero _) (hinv g)
  obtain ⟨s, hqs, hsfix⟩ := ρ.exists_fixed_rightInverse q hq hqi
  let f : E → E := fun y ↦ y + s (r y - q y)
  have hf : ContDiffOn 𝕜 n f U :=
    contDiffOn_id.add (s.contDiff.comp_contDiffOn (hr.sub q.contDiff.contDiffOn))
  have hf0 : f 0 = 0 := by simp [f, hr0]
  have hdf : HasFDerivAt f (ContinuousLinearMap.id 𝕜 E) 0 := by
    have h : HasFDerivAt f
        (ContinuousLinearMap.id 𝕜 E + s.comp (q - q)) 0 :=
      (hasFDerivAt_id (𝕜 := 𝕜) (0 : E)).add
        (s.hasFDerivAt.comp (0 : E) (hd.sub q.hasFDerivAt))
    simpa only [sub_self, ContinuousLinearMap.comp_zero, add_zero] using h
  have hqf (y : E) : q (f y) = r y := by
    have h := DFunLike.congr_fun hqs (r y - q y)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
    simp only [f, map_add, h]
    exact add_sub_cancel _ _
  -- Choose a neighborhood on which every local invariance equation holds simultaneously.
  have hnear : ∀ᶠ y in 𝓝 (0 : E), y ∈ U ∧ ∀ g : G, r (ρ g y) = r y := by
    filter_upwards [hU.mem_nhds h0U, eventually_all.mpr hinv] with y hy hyi
    exact ⟨hy, hyi⟩
  obtain ⟨V, hVsub, hV, h0V⟩ := mem_nhds_iff.mp hnear
  obtain ⟨Θ, hΘ, h0Θ, hΘV, hΘsmooth⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph (hf.mono fun y hy ↦ (hVsub hy).1)
      hV h0V hn (e := ContinuousLinearEquiv.refl 𝕜 E) hdf.fderiv.symm
  -- Use the existing invariant restriction for the action underlying the representation.
  let : MulAction G E := MulAction.compHom E ρ.toRepresentation
  have hsmul (g : G) (y : E) : g • y = ρ g y := by
    simp [MulAction.compHom_smul_def, Module.End.smul_def, toMonoidHom_apply]
  let : ContinuousConstSMul G E := ⟨fun g ↦ by
    simpa only [hsmul] using (ρ g).continuous⟩
  have hfeq (g : G) {y : E} (hy : y ∈ Θ.source) : f (ρ g y) = ρ g (f y) := by
    have hri := (hVsub (hΘV hy)).2 g
    have hqg := DFunLike.congr_fun (hqi g) y
    simp only [ContinuousLinearMap.comp_apply] at hqg
    simp [f, hri, hqg, map_add, hsfix]
  let e := Θ.restrInvariant G
  have he : (e : E → E) = f := by simpa [e] using hΘ
  have heinv : (e.symm : E → E) = Θ.symm := by simp [e]
  have htarget : e.target ⊆ Θ.target := Θ.restrInvariant_target_subset
  have hsourceΘ : e.source ⊆ Θ.source := Θ.restrInvariant_source_subset
  have h0e : (0 : E) ∈ e.source :=
    Θ.mem_restrInvariant_source_of_forall_smul_eq (fun g ↦ by simp [hsmul]) h0Θ
  have hequiv (g : G) {y : E} (hy : y ∈ e.source) :
      ρ g y ∈ e.source ∧ e (ρ g y) = ρ g (e y) := by
    refine ⟨?_, ?_⟩
    · simpa only [hsmul] using Θ.smul_mem_restrInvariant_source hy g
    · rw [he]
      exact hfeq g (hsourceΘ hy)
  refine ⟨e, h0e, ?_, fun y hy ↦ (hVsub (hΘV (hsourceΘ hy))).1, ?_, ?_, ?_,
    ?_, ?_, fun g y hy ↦ hequiv g hy, ?_⟩
  · rw [he, hf0]
  · rw [he]
    exact hdf
  · rw [he]
    exact hf.mono fun y hy ↦ (hVsub (hΘV (hsourceΘ hy))).1
  · rw [heinv]
    exact hΘsmooth.mono htarget
  · intro y _
    rw [he]
    exact hqf y
  · intro z hz
    rw [← hqf (e.symm z), ← he, e.right_inv hz]
  · intro g z hz
    simpa only [hsmul] using e.symm_map_smul_of_map_smul
      (fun g y hy ↦ by simpa only [hsmul] using hequiv g hy) g z hz

end ContRepresentation
