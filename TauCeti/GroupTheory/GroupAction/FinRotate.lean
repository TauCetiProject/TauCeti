/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Jordan
public import Mathlib.GroupTheory.Perm.Fin
import TauCeti.GroupTheory.Perm.MultipleTransitivity

/-!
# Transitivity from cyclic rotation

A permutation subgroup containing cyclic rotation acts transitively on the finite ordinal.
This gives a transitivity criterion for groups specified by generators, including the empty
and singleton ordinals. Conversely, a permutation generating a transitive group is conjugate to
cyclic rotation (`TauCeti.isPretransitive_zpowers_iff_isConj_finRotate`).
-/

public section

namespace TauCeti

open Equiv Equiv.Perm MulAction

/-- A permutation subgroup containing cyclic rotation acts transitively. -/
theorem isPretransitive_of_finRotate_mem {n : ℕ}
    {G : Subgroup (Perm (Fin n))} (hg : finRotate n ∈ G) : IsPretransitive G (Fin n) := by
  rcases n with _ | _ | n
  · infer_instance
  · refine ⟨fun x y ↦ ⟨1, ?_⟩⟩
    exact Fin.ext (by omega)
  · exact isPretransitive_of_isCycle_mem_of_support_eq_univ isCycle_finRotate hg support_finRotate

/-- **A permutation generates a transitive group exactly when it is conjugate to cyclic
rotation**, that is, when it is a single cycle through every point of the finite ordinal. -/
theorem isPretransitive_zpowers_iff_isConj_finRotate {n : ℕ} {σ : Perm (Fin n)} :
    IsPretransitive (Subgroup.zpowers σ) (Fin n) ↔ IsConj σ (finRotate n) := by
  refine ⟨fun hσ => ?_, fun h => ?_⟩
  · rcases lt_or_ge n 2 with hn | hn
    · have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.2 (by omega)
      rw [Subsingleton.elim σ (finRotate n)]
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
    have hc : σ.IsCycleOn Set.univ := ⟨σ.bijective.bijOn_univ, fun x _ y _ => by
      obtain ⟨⟨g, hg⟩, hxy⟩ := hσ.exists_smul_eq x y
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact ⟨k, by simpa [Subgroup.smul_def] using hxy⟩⟩
    have hsupp : σ.support = Finset.univ := Finset.eq_univ_of_forall fun x =>
      mem_support.2 (hc.apply_ne Set.nontrivial_univ (Set.mem_univ x))
    exact (isCycle_iff_exists_isCycleOn.2 ⟨_, Set.nontrivial_univ, hc, fun _ _ => Set.mem_univ _⟩
      ).isConj (isCycle_finRotate_of_le hn) (by rw [hsupp, support_finRotate_of_le hn])
  · -- Transport the transitivity of the powers of rotation along a conjugation.
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    have := isPretransitive_of_finRotate_mem (Subgroup.mem_zpowers (finRotate n))
    refine ⟨fun x y => ?_⟩
    obtain ⟨⟨g, hg⟩, hxy⟩ := this.exists_smul_eq (c x) (c y)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨⟨σ ^ k, Subgroup.zpow_mem_zpowers σ k⟩, c.injective ?_⟩
    have hxy' : (finRotate n ^ k) (c x) = c y := by simpa [Subgroup.smul_def] using hxy
    rw [← hc, conj_zpow] at hxy'
    simpa [Subgroup.smul_def, Perm.mul_apply] using hxy'

end TauCeti
