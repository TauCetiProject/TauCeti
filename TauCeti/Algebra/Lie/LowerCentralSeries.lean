/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Nilpotent
public import TauCeti.LinearAlgebra.Basis.Filtration

/-!
# Lower-central weights and adapted bases

Write `C k = LieModule.lowerCentralSeries R L L k`, so `C 0 = L` and `C 1 = [L,L]`.
The bracket satisfies `[C m, C n] ≤ C (m + n + 1)`. Thus a vector in `C (w - 1)` has
lower-central weight at least `w`, and brackets add these positive weights.

For a finite-dimensional nilpotent Lie algebra, `exists_basis_weight_lowerCentralSeries` supplies
a finite ordered basis with positive bounded weights, describing every term of the lower central
series by coordinate vanishing. In particular, a bracket of basis vectors has no coordinate of
weight less than the sum of their weights. This is the weight bound needed to straighten PBW
monomials without lowering weight, and to construct finite weighted enveloping-algebra quotients.
No characteristic or algebraic-closure hypothesis is used.

## References

* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapters II and V, for the lower central
  series, nilpotent Lie algebras and universal enveloping algebras.
-/

public section

namespace TauCeti

open LieModule Module

section Bracket

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Brackets add lower-central weights. The zero-indexed convention `C 0 = L` accounts for
the extra `1` in the index on the right. -/
theorem lie_lowerCentralSeries_le (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M] (m n : ℕ) :
    ⁅lowerCentralSeries R L L m, lowerCentralSeries R L M n⁆ ≤
      lowerCentralSeries R L M (m + n + 1) := by
  induction m generalizing n with
  | zero => simp [lowerCentralSeries_succ]
  | succ m ih =>
    rw [LieSubmodule.lie_le_iff]
    intro x hx y hy
    rw [lowerCentralSeries_succ, ← LieSubmodule.mem_toSubmodule,
      LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
    refine Submodule.span_induction (p := fun x _ ↦
      ⁅x, y⁆ ∈ lowerCentralSeries R L M (m + 1 + n + 1)) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, -, b, hb, rfl⟩
      rw [lie_lie]
      apply (lowerCentralSeries R L M _).sub_mem
      · have hby := ih n (LieSubmodule.lie_mem_lie hb hy)
        have ha : ⁅a, ⁅b, y⁆⁆ ∈ lowerCentralSeries R L M ((m + n + 1) + 1) := by
          rw [lowerCentralSeries_succ]
          exact LieSubmodule.lie_mem_lie trivial hby
        simpa only [LieSubmodule.mem_toSubmodule, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using ha
      · have hay : ⁅a, y⁆ ∈ lowerCentralSeries R L M (n + 1) := by
          rw [lowerCentralSeries_succ]
          exact LieSubmodule.lie_mem_lie trivial hy
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (n + 1) (LieSubmodule.lie_mem_lie hb hay)
    · simp
    · intro a b _ _ ha hb
      simpa [add_lie] using (lowerCentralSeries R L M _).add_mem ha hb
    · intro r a _ ha
      simpa [smul_lie] using (lowerCentralSeries R L M _).smul_mem r ha

/-- A bracket has zero coordinates below the sum of the weights of its two inputs in a
basis adapted to the lower central series. -/
theorem _root_.Module.Basis.repr_lie_eq_zero_of_weight_lt {ι : Type*}
    (b : Basis ι R L) (w : ι → ℕ) (hpos : ∀ i, 0 < w i)
    (hmem : ∀ k x, x ∈ lowerCentralSeries R L L k ↔
      ∀ i, w i ≤ k → b.repr x i = 0) (i j k : ι) (hk : w k < w i + w j) :
    b.repr ⁅b i, b j⁆ k = 0 := by
  have hb (a : ι) : b a ∈ lowerCentralSeries R L L (w a - 1) := by
    rw [hmem]
    intro c hc
    have hca : c ≠ a := by intro h; subst c; have := hpos a; omega
    simp [hca]
  have hbracket := lie_lowerCentralSeries_le L (w i - 1) (w j - 1)
    (LieSubmodule.lie_mem_lie (hb i) (hb j))
  apply (hmem _ _).mp hbracket k
  have := hpos i
  have := hpos j
  omega

end Bracket

section Basis

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieRing.IsNilpotent L]

/-- Every finite-dimensional nilpotent Lie algebra has a finite ordered basis with positive
bounded lower-central weights. Each central-series term is described exactly by coordinate
vanishing, and brackets of basis vectors have no coordinates below the sum of their weights. -/
theorem exists_basis_weight_lowerCentralSeries :
    ∃ (N : ℕ) (b : Basis (Fin (Module.finrank K L)) K L)
      (w : Fin (Module.finrank K L) → ℕ),
      (∀ i, 0 < w i ∧ w i ≤ N) ∧
      (∀ k x, x ∈ lowerCentralSeries K L L k ↔ ∀ i, w i ≤ k → b.repr x i = 0) ∧
      ∀ i j k, w k < w i + w j → b.repr ⁅b i, b j⁆ k = 0 := by
  classical
  obtain ⟨N, hN⟩ := LieModule.IsNilpotent.nilpotent K L L
  obtain ⟨ι, _, b, w, hweight, hmem⟩ := exists_basis_weight_of_antitone
    (fun k ↦ (lowerCentralSeries K L L k).toSubmodule)
    (fun _ _ h ↦ antitone_lowerCentralSeries K L L h)
    (by simp) N (by simp [hN])
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  let b' := b.reindex e
  let w' := w ∘ e.symm
  have hweight' : ∀ i, 0 < w' i ∧ w' i ≤ N := fun i ↦ hweight (e.symm i)
  have hmem' : ∀ k x, x ∈ lowerCentralSeries K L L k ↔
      ∀ i, w' i ≤ k → b'.repr x i = 0 := by
    intro k x
    rw [← LieSubmodule.mem_toSubmodule, hmem]
    simpa [b', w', Basis.repr_reindex_apply] using
      e.forall_congr_left (p := fun i ↦ w i ≤ k → b.repr x i = 0)
  exact ⟨N, b', w', hweight', hmem',
    b'.repr_lie_eq_zero_of_weight_lt w' (fun i ↦ (hweight' i).1) hmem'⟩

end Basis

end TauCeti
