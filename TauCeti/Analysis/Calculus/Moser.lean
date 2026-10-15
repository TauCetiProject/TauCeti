/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The local contraction equation for Moser deformation

Let `B` be a family of bilinear forms which agrees at `x₀` with a fixed invertible
bilinear form `L`. The contraction maps of `(1 - t) • L + t • B x` are invertible on a
single spatial neighbourhood of `x₀`, for every `t ∈ [0, 1]`. In fact, the time
interval can also be enlarged to an open neighbourhood.

For smooth `B` and a smooth one-form `α`, construct the jointly smooth vector field
`X(t, x)` uniquely determined by

`((1 - t) • L + t • B x) (X(t, x)) = -α x`.

This is the local algebraic step in Moser's argument and in the proof of Darboux's
theorem. Alternation and closedness of `B` are not needed for this step and are
not imposed here. No flow, pullback identity, or Darboux chart is asserted.

The argument follows McDuff--Salamon, *Introduction to Symplectic Topology*,
Section 3.2, and uses Mathlib's smooth inverse for continuous linear maps and
its generalized tube lemma.
-/

public section

open Set
open scoped Topology

noncomputable section

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {W : Set V} {x₀ : V} {B : V → V →L[ℝ] V →L[ℝ] ℝ}
  {L : V →L[ℝ] V →L[ℝ] ℝ}

/-- A straight-line family agreeing with an invertible bilinear form at one point has invertible
contraction maps on one neighbourhood, uniformly for all times in `[0, 1]`.
The returned time neighbourhood is open, so subsequent smoothness is ordinary local
smoothness, including at the endpoints. -/
theorem exists_isOpen_isInvertible_sub_smul_add_smul (hL : L.IsInvertible)
    (hW : IsOpen W) (hx₀ : x₀ ∈ W) (hB : ContinuousOn B W)
    (hB₀ : B x₀ = L) :
    ∃ (T : Set ℝ) (U : Set V), IsOpen T ∧ IsOpen U ∧ Icc 0 1 ⊆ T ∧
      x₀ ∈ U ∧ U ⊆ W ∧
      ∀ p ∈ T ×ˢ U,
        ((1 - p.1) • L + p.1 • B p.2).IsInvertible := by
  -- Supply the existing topological instance for the nested operator space explicitly.
  let : ContinuousAdd (V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousLinearMap.isTopologicalAddGroup.toContinuousAdd
  let A : ℝ × V → V →L[ℝ] V →L[ℝ] ℝ :=
    fun p ↦ (1 - p.1) • L + p.1 • B p.2
  let N := {p : ℝ × V | p.2 ∈ W ∧ (A p).IsInvertible}
  have hN : IsOpen N := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hBp : ContinuousAt B p.2 := hB.continuousAt (hW.mem_nhds hp.1)
    have hAp : ContinuousAt A p := by
      exact ((continuousAt_const.sub continuous_fst.continuousAt).smul
        continuousAt_const).add (continuous_fst.continuousAt.smul
          (hBp.comp continuous_snd.continuousAt))
    exact Filter.inter_mem ((hW.preimage continuous_snd).mem_nhds hp.1)
      (hAp (ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds hp.2))
  have hline : Icc (0 : ℝ) 1 ×ˢ {x₀} ⊆ N := by
    rintro ⟨t, x⟩ ⟨-, rfl⟩
    refine ⟨hx₀, ?_⟩
    have hA : A (t, x) = L := by
      dsimp only [A]
      rw [hB₀, ← add_smul (1 - t) t L, sub_add_cancel, one_smul]
    rw [hA]
    exact hL
  obtain ⟨T, U, hT, hU, hIT, hxU, hTU⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hN hline
  refine ⟨T, U ∩ W, hT, hU.inter hW, hIT,
    ⟨hxU (mem_singleton x₀), hx₀⟩, inter_subset_right, ?_⟩
  intro p hp
  exact (hTU ⟨hp.1, hp.2.1⟩).2

/-- Solve the local straight-line Moser contraction equation by a jointly `C^n` vector
field, on an open time neighbourhood of `[0, 1]` and one spatial neighbourhood of `x₀`.
The displayed equivalence characterizes the solution uniquely without unfolding it.
Closedness and alternation of the varying bilinear form are separate geometric hypotheses. -/
theorem exists_contDiffOn_moserField (hL : L.IsInvertible) {n : WithTop ℕ∞}
    (hW : IsOpen W) (hx₀ : x₀ ∈ W) (hB : ContDiffOn ℝ n B W)
    (hB₀ : B x₀ = L)
    {α : V → V →L[ℝ] ℝ} (hα : ContDiffOn ℝ n α W) :
    ∃ (T : Set ℝ) (U : Set V) (X : ℝ × V → V),
      IsOpen T ∧ IsOpen U ∧ Icc 0 1 ⊆ T ∧ x₀ ∈ U ∧ U ⊆ W ∧
      ContDiffOn ℝ n X (T ×ˢ U) ∧
      ∀ p ∈ T ×ˢ U, ∀ v : V,
        (∀ w : V,
          ((1 - p.1) • L + p.1 • B p.2) v w =
            -α p.2 w) ↔ v = X p := by
  -- Use Mathlib's operator-norm scalar-action instance, without exporting another instance.
  let : IsBoundedSMul ℝ (V →L[ℝ] V →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := V →L[ℝ] V →L[ℝ] ℝ)
  obtain ⟨T, U, hT, hU, hIT, hxU, hUW, hA⟩ :=
    exists_isOpen_isInvertible_sub_smul_add_smul hL hW hx₀ hB.continuousOn hB₀
  let A : ℝ × V → V →L[ℝ] V →L[ℝ] ℝ :=
    fun p ↦ (1 - p.1) • L + p.1 • B p.2
  let X : ℝ × V → V := fun p ↦ (A p).inverse (-α p.2)
  have hBs : ContDiffOn ℝ n (fun p : ℝ × V ↦ B p.2) (T ×ˢ U) :=
    hB.comp contDiffOn_snd (fun p hp ↦ hUW hp.2)
  have hAs : ContDiffOn ℝ n A (T ×ˢ U) :=
    ((contDiffOn_const.sub contDiffOn_fst).smul contDiffOn_const).add
      (contDiffOn_fst.smul hBs)
  -- Inversion is smooth at every contraction map on the uniform tube.
  have hinv : ContDiffOn ℝ n (fun p ↦ (A p).inverse) (T ×ˢ U) := by
    intro p hp
    exact (hA p hp).contDiffAt_map_inverse.comp_contDiffWithinAt p (hAs p hp)
  have hXs : ContDiffOn ℝ n X (T ×ˢ U) :=
    hinv.clm_apply (hα.comp contDiffOn_snd (fun p (hp : p ∈ T ×ˢ U) ↦ hUW hp.2)).neg
  refine ⟨T, U, X, hT, hU, hIT, hxU, hUW, hXs, ?_⟩
  intro p hp v
  simp only [A, X, ← neg_apply]
  rw [← ContinuousLinearMap.ext_iff]
  exact eq_comm.trans ((hA p hp).inverse_apply_eq.symm.trans eq_comm)

end TauCeti
