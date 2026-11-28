/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import TauCeti.NumberTheory.Padics.Coupling.SelectedExponents

/-!
# Theta couplings from short orbit steps

Suppose no point of a set can reach the set at two distinct short positive times under
iteration of a group element. At the target of a selected short coupling, its step is the
unique shortest admissible one from the selected sources. This is the hypothesis that
isolates the lowest source degree at a given partner degree.

This is the orbit argument in `New.Data.isCouplingFamily_of_isNearPair` in
`grh/src/New/Derivatives/Sharpness/Cases.lean` of [grh-lean](https://github.com/lsernau/grh-lean)
at commit `72fead1`.
-/

public section

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X]

/-- If each point of `B` has at most one positive return time below `L` to `B`, a chosen
step from each source in `A ⊆ B` to a target in `B` is the unique shortest admissible step
from `A` to that target. The step lengths are taken from a set of positive integers. -/
theorem isCouplingFamily_of_short_returns {B A : Set X} {L : ℕ} (g : G) {S : Set ℕ}
    (hS : 0 ∉ S) (e : A → ℕ) (hA : A ⊆ B) (he : ∀ x, e x ∈ S)
    (hlt : ∀ x, e x < L) (hend : ∀ x, g ^ e x • (x : X) ∈ B)
    (hsparse : ∀ x ∈ B, ∀ ⦃i j : ℕ⦄, 0 < i → i < j → j < L →
      g ^ i • x ∈ B → g ^ j • x ∉ B) :
    IsCouplingFamily S (fun k (x : A) ↦ g ^ k • (x : X)) e := by
  refine ⟨he, ?_⟩
  intro x y k hk hkle hsame
  rcases hkle.eq_or_lt with rfl | hklt
  · exact Prod.ext (Subtype.ext (smul_left_cancel _ hsame)) rfl
  · have hkpos : 0 < k := Nat.pos_of_ne_zero (fun h ↦ hS (h ▸ hk))
    have hstep : g ^ (e x - k) • (x : X) = y := by
      apply smul_left_cancel (g ^ k)
      rw [← mul_smul, ← pow_add, Nat.add_sub_of_le hkle]
      exact hsame.symm
    exact (hsparse x (hA x.property) (by omega : 0 < e x - k) (by omega : e x - k < e x)
      (hlt x) (hstep.symm ▸ hA y.property) (hend x)).elim

end TauCeti
