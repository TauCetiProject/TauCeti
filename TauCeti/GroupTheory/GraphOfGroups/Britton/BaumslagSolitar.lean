/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.Britton
public import TauCeti.GroupTheory.GraphOfGroups.Cyclic
import TauCeti.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Britton's lemma in the Baumslag–Solitar group `⟨a, t ∣ t a² t⁻¹ = a⟩`

The Baumslag–Solitar group `⟨a, t ∣ t a² t⁻¹ = a⟩` is the fundamental group of the loop
`baumslagSolitar 1 2` of infinite cyclic groups, with `α = id` and `ω = (· ^ 2)` on its dart
`t = ((), true)` (`π₁Tree.baumslagSolitarEquiv`). Through `π₁Tree.equivHNNExtension` it is the
HNN extension of `ℤ` in which the dart `((), true)` is the inverse of the stable letter, so in the
notation of `loopPath` the path `1, t, a, t⁻¹, 1` is `loopPath 1 [(-1, a), (1, 1)]`.

This path is reduced, because `a ∉ ω(ℤ) = ⟨a²⟩`, so `t a t⁻¹ ∉ ⟨a⟩` by Britton's lemma for the
loop (`baumslagSolitarRelator_one_two_conj_notMem_zpowers`). The examples check that the path is
reduced, and that the path `1, t, a², t⁻¹, 1` is not reduced, in accordance with `t a² t⁻¹ = a`.

## Main results

* `TauCeti.GraphOfGroups.baumslagSolitarRelator_one_two_conj_notMem_zpowers`: `t a t⁻¹ ∉ ⟨a⟩`
  in `⟨a, t ∣ t a² t⁻¹ = a⟩`.

## References

* G. Baumslag, D. Solitar, *Some two-generator one-relator non-Hopfian groups*,
  Bull. Amer. Math. Soc. 68 (1962).
* J. L. Britton, *The word problem*, Ann. of Math. 77 (1963).
-/

public section

namespace TauCeti

namespace GraphOfGroups

open Multiplicative

/-- In the Baumslag–Solitar group `⟨a, t ∣ t a² t⁻¹ = a⟩` the path `1, t, a, t⁻¹, 1` is reduced,
because `a ∉ ω(ℤ) = ⟨a²⟩`. -/
example {v : (SerreGraph.rose Unit).V} :
    (loopPath (zpowGroupHom (α := Multiplicative ℤ) 1) (zpowGroupHom 2)
      (zpow_left_injective one_ne_zero) (zpow_left_injective two_ne_zero) 1
      [(-1, ofAdd 1), (1, 1)] :
        (baumslagSolitar 1 2 one_ne_zero two_ne_zero).AlternatingPath v v).IsReduced :=
  (isReduced_loopPath_iff _ _).2
    (List.isChain_pair.2 fun h => absurd (Int.mem_range_zpowGroupHom_iff.1 h) (by decide))

/-- In the Baumslag–Solitar group `⟨a, t ∣ t a² t⁻¹ = a⟩` the conjugate `t a t⁻¹` does not lie in
`⟨a⟩`: the path `1, t, a, t⁻¹, 1` of the loop is reduced, because `a ∉ ω(ℤ) = ⟨a²⟩`, so this is
Britton's lemma for the loop. -/
theorem baumslagSolitarRelator_one_two_conj_notMem_zpowers :
    (PresentedGroup.of true * PresentedGroup.of false * (PresentedGroup.of true)⁻¹ :
      PresentedGroup {baumslagSolitarRelator 1 2}) ∉
      Subgroup.zpowers (PresentedGroup.of false) := by
  rintro ⟨k, hk⟩
  have hf : Function.Injective (zpowGroupHom (α := Multiplicative ℤ) 1) :=
    zpow_left_injective one_ne_zero
  have hg : Function.Injective (zpowGroupHom (α := Multiplicative ℤ) 2) :=
    zpow_left_injective two_ne_zero
  -- Through `⟨a, t ∣ t a² t⁻¹ = a⟩ ≃* π₁(𝔸, ∅) ≃* HNNExtension`, `t` is sent to `t⁻¹`.
  let e := (π₁Tree.baumslagSolitarEquiv 1 2 one_ne_zero two_ne_zero).symm.trans
    (π₁Tree.equivHNNExtension _ _ hf hg)
  have et : e (PresentedGroup.of true) = HNNExtension.t⁻¹ :=
    (congrArg (π₁Tree.equivHNNExtension _ _ hf hg)
      (π₁Tree.baumslagSolitarEquiv_symm_of_true ..)).trans
      (π₁Tree.equivHNNExtension_edge_true ..)
  have ea : e (PresentedGroup.of false) = HNNExtension.of (ofAdd 1) :=
    (congrArg (π₁Tree.equivHNNExtension _ _ hf hg)
      (π₁Tree.baumslagSolitarEquiv_symm_of_false ..)).trans
      (π₁Tree.equivHNNExtension_of ..)
  have h := congrArg e hk
  simp only [map_mul, map_inv, map_zpow, et, ea, inv_inv] at h
  -- Read `t a t⁻¹` at the vertex `v` of the loop: a reduced path of length two.
  suffices ∀ _ : (SerreGraph.rose Unit).V, False from this ()
  intro v
  have hP : (loopPath _ _ hf hg 1 [(-1, ofAdd 1), (1, 1)] :
      (loop _ _ hf hg).AlternatingPath v v).IsReduced :=
    (isReduced_loopPath_iff _ _).2
      (List.isChain_pair.2 fun h => absurd (Int.mem_range_zpowGroupHom_iff.1 h) (by decide))
  have := hP.equivHNNExtension_toπ₁Tree_toPath_mem_range_of_iff.1 ⟨ofAdd 1 ^ k, ?_⟩
  · simp at this
  · simp [← h]

/-- In `⟨a, t ∣ t a² t⁻¹ = a⟩` the path `1, t, a², t⁻¹, 1` is not reduced, because
`a² ∈ ω(ℤ)`. -/
example {v : (SerreGraph.rose Unit).V} :
    ¬ (loopPath (zpowGroupHom (α := Multiplicative ℤ) 1) (zpowGroupHom 2)
      (zpow_left_injective one_ne_zero) (zpow_left_injective two_ne_zero) 1
      [(-1, ofAdd 2), (1, 1)] :
        (baumslagSolitar 1 2 one_ne_zero two_ne_zero).AlternatingPath v v).IsReduced := fun h =>
  absurd (List.isChain_pair.1 ((isReduced_loopPath_iff _ _).1 h) ⟨ofAdd 1, rfl⟩) (by decide)

/-- In `⟨a, t ∣ t a² t⁻¹ = a⟩` the element `t a² t⁻¹` equals `a`. -/
example : (PresentedGroup.of true * PresentedGroup.of false ^ 2 * (PresentedGroup.of true)⁻¹ :
    PresentedGroup {baumslagSolitarRelator 1 2}) = PresentedGroup.of false := by
  simpa using baumslagSolitarRelator_relation 1 2

end GraphOfGroups

end TauCeti
