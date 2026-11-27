/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.PathSpace.Moore.Comparison.Between
public import TauCeti.Topology.PathSpace.Moore.Comparison.Trans

/-!
# Homotopy classes of reparametrized Moore paths between two points

A Moore path from `a` to `b` is reparametrized to a path on the unit interval from `a` to `b`
(`TauCeti.MoorePathBetween.toPath`, in `TauCeti.Topology.PathSpace.Moore.Comparison.Between`),
continuously in the Moore path. This file records how the homotopy class of the reparametrized
path depends on the Moore path, which is what the fundamental groupoid sees of the Moore paths:

* reparametrization commutes with concatenation up to homotopy
  (`TauCeti.MoorePathBetween.homotopic_toPath_trans`), hence also with the actions of the Moore
  loops at both ends by concatenation (`TauCeti.MoorePathBetween.homotopic_toPath_leftAct`,
  `TauCeti.MoorePathBetween.homotopic_toPath_rightAct`);
* Moore paths joined by a path in the space of Moore paths from `a` to `b` have homotopic
  reparametrizations (`TauCeti.MoorePathBetween.homotopic_toPath_of_joined`). Closing both up with
  the reversal of one of them reduces this to loops, where joined loops are homotopic
  (`Path.joined_iff_homotopic`).

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public noncomputable section

open unitInterval

namespace TauCeti.MoorePathBetween

variable {X : Type*} [TopologicalSpace X] {a b c : X}

/-- **Reparametrization commutes with concatenation up to homotopy**: the reparametrization of
`γ.trans δ` is homotopic to the concatenation on the unit interval of those of `γ` and `δ`. The
homotopy reads `γ.trans δ` along reparametrizations of the unit interval fixing both ends
(`TauCeti.MoorePath.toUnitPathTransHomotopy`). -/
theorem homotopic_toPath_trans (γ : MoorePathBetween X a b) (δ : MoorePathBetween X b c) :
    (γ.trans δ).toPath.Homotopic (γ.toPath.trans δ.toPath) := by
  let q : {q : MoorePath X × MoorePath X // q.1.target = q.2.source} :=
    ⟨(γ.toMoorePath, δ.toMoorePath), by simp⟩
  refine Path.Homotopic.symm ⟨
    { toFun := fun x ↦ MoorePath.toUnitPathTransHomotopy (x.1, q) x.2
      continuous_toFun := continuous_eval.comp
        ((MoorePath.toUnitPathTransHomotopy.continuous.comp
          (continuous_fst.prodMk continuous_const)).prodMk continuous_snd)
      map_zero_left := fun s ↦ ?_
      map_one_left := fun s ↦ ?_
      prop' := fun τ s hs ↦ ?_ }⟩
  · simp only [ContinuousMap.Homotopy.apply_zero, MoorePath.transToUnitPath_apply,
      Path.coe_toContinuousMap, Path.trans_apply, Path.cast_coe, MoorePath.toPath_apply,
      toPath_apply, q]
  · simp only [ContinuousMap.Homotopy.apply_one, MoorePath.toUnitPathTrans_apply,
      MoorePath.toUnitPath_apply, Path.coe_toContinuousMap, toPath_apply, toMoorePath_trans, q]
  · -- Every stage runs from `a` to `c`, so it agrees with the concatenation at both ends.
    rcases hs with rfl | rfl
    · simpa using (MoorePath.toUnitPathTransHomotopy_apply_zero_right τ q).trans γ.source
    · simpa using (MoorePath.toUnitPathTransHomotopy_apply_one_right τ q).trans δ.target

/-- Concatenating a Moore loop in front of a Moore path reparametrizes, up to homotopy, to the
concatenation of their reparametrizations. -/
theorem homotopic_toPath_leftAct (ω : MooreLoopSpace X a) (γ : MoorePathBetween X a b) :
    (leftAct ω γ).toPath.Homotopic (ω.toPath.trans γ.toPath) := by
  have h : leftAct ω γ = (loopHomeomorph a ω).trans γ := ext (by simp)
  simpa [h] using homotopic_toPath_trans (loopHomeomorph a ω) γ

/-- Concatenating a Moore loop behind a Moore path reparametrizes, up to homotopy, to the
concatenation of their reparametrizations. -/
theorem homotopic_toPath_rightAct (γ : MoorePathBetween X a b) (ω : MooreLoopSpace X b) :
    (rightAct γ ω).toPath.Homotopic (γ.toPath.trans ω.toPath) := by
  have h : rightAct γ ω = γ.trans (loopHomeomorph b ω) := ext (by simp)
  simpa [h] using homotopic_toPath_trans γ (loopHomeomorph b ω)

/-- **Moore paths in one path component have homotopic reparametrizations**: Moore paths from `a`
to `b` joined by a path in the space of such Moore paths reparametrize to homotopic paths. -/
theorem homotopic_toPath_of_joined {γ δ : MoorePathBetween X a b} (h : Joined γ δ) :
    γ.toPath.Homotopic δ.toPath := by
  -- Close both paths up with the reversal of `δ`: the resulting loops at `a` are joined in the
  -- loop space, hence homotopic, and the reversal of `δ` then cancels.
  let f : MoorePathBetween X a b → MooreLoopSpace X a :=
    fun η ↦ (loopHomeomorph a).symm (η.trans δ.symm)
  have hf : Continuous f := (loopHomeomorph a).symm.continuous.comp
    (continuous_trans.comp (continuous_id.prodMk continuous_const) :
      Continuous fun η : MoorePathBetween X a b ↦ η.trans δ.symm)
  have hloop (η : MoorePathBetween X a b) :
      ((loopHomeomorph a).symm (η.trans δ.symm)).toPath.Homotopic
        (η.toPath.trans δ.toPath.symm) := by
    have h' := toPath_loopHomeomorph ((loopHomeomorph a).symm (η.trans δ.symm))
    rw [Homeomorph.apply_symm_apply] at h'
    rw [← h', ← toPath_symm]
    exact homotopic_toPath_trans η δ.symm
  have hjoined := Path.joined_iff_homotopic.1 ((h.map hf).map MooreLoopSpace.continuous_toPath)
  have hq := Path.Homotopic.Quotient.eq.2 (((hloop γ).symm.trans hjoined).trans (hloop δ))
  rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans] at hq
  have hq' := congrArg (fun q ↦ q.trans (Path.Homotopic.Quotient.mk δ.toPath)) hq
  simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl] at hq'
  exact Path.Homotopic.Quotient.eq.1 hq'

end TauCeti.MoorePathBetween
