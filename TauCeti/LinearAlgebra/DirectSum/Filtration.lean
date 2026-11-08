/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module

/-!
# Direct sums of maps compatible with an exhaustive filtration

Let `N 0 ≤ N 1 ≤ ⋯` be an increasing sequence of submodules of `M`, and `f j : Q j → M` linear
maps with values in `N (j + 1)`. The sum `DirectSum.toModule R ℕ M f` out of `⨁ j, Q j` is
injective when `f j q ∈ N j` forces `q = 0`, and surjective when `N 0 = ⊥`, the filtration is
exhaustive, and every element of `N (J + 1)` is congruent modulo `N J` to a value of `f J`.

## Main declarations

* `DirectSum.toModule_injective_of_filtration`
* `DirectSum.toModule_surjective_of_filtration`
-/

public section

open DirectSum

namespace DirectSum

variable {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M] {Q : ℕ → Type*}
  [∀ j, AddCommGroup (Q j)] [∀ j, Module R (Q j)]

/-- The sum of maps `f j : Q j → M` out of the pieces of a direct sum is injective when `f j`
lands in the `(j + 1)`-st step of an increasing filtration of `M` and `f j q ∈ N j` implies
`q = 0`; this forces each `f j` to be injective with image meeting `N j` only in `0`. -/
theorem toModule_injective_of_filtration (N : ℕ → Submodule R M) (hN : Monotone N)
    (f : ∀ j, Q j →ₗ[R] M) (hmem : ∀ j q, f j q ∈ N (j + 1))
    (hzero : ∀ j q, f j q ∈ N j → q = 0) :
    Function.Injective (DirectSum.toModule R ℕ M f) := by
  classical
  have key (J : ℕ) : ∀ d : ⨁ j, Q j, (∀ j ∈ d.support, j < J) →
      DirectSum.toModule R ℕ M f d ∈ N J ∧ (DirectSum.toModule R ℕ M f d = 0 → d = 0) := by
    induction J with
    | zero =>
      intro d hd
      have : d = 0 := DFinsupp.support_eq_empty.mp <|
        Finset.eq_empty_of_forall_notMem fun j hj ↦ Nat.not_lt_zero _ (hd j hj)
      subst this
      simp
    | succ J ih =>
      intro d hd
      have hd' : ∀ j ∈ (d.erase J).support, j < J := by
        intro j hj
        rw [DFinsupp.support_erase, Finset.mem_erase] at hj
        exact lt_of_le_of_ne (Nat.lt_succ_iff.mp (hd j hj.2)) hj.1
      obtain ⟨hmemJ, hzeroJ⟩ := ih _ hd'
      have hd_eq : d = d.erase J + DFinsupp.single J (d J) := (DFinsupp.erase_add_single J d).symm
      have hψd : DirectSum.toModule R ℕ M f d =
          DirectSum.toModule R ℕ M f (d.erase J) + f J (d J) := by
        have hsingle : DirectSum.toModule R ℕ M f (DFinsupp.single J (d J)) = f J (d J) :=
          DirectSum.toModule_lof R J (d J)
        rw [hd_eq, map_add, hsingle, DFinsupp.erase_add_single]
      refine ⟨hψd ▸ add_mem (hN J.le_succ hmemJ) (hmem J (d J)), fun h ↦ ?_⟩
      have hJ : d J = 0 := by
        refine hzero J (d J) ?_
        have : f J (d J) = -DirectSum.toModule R ℕ M f (d.erase J) :=
          eq_neg_of_add_eq_zero_right (hψd.symm.trans h)
        -- Negate in the additive group `⨁ j, Q j`, since `N J` need not be closed under negation
        -- when `R` is only a semiring.
        have hneg := (ih (-(d.erase J)) (by simpa only [DFinsupp.support_neg] using hd')).1
        rw [map_neg] at hneg
        exact this ▸ hneg
      have herase : d.erase J = 0 := hzeroJ (by simpa [hJ] using hψd.symm.trans h)
      rw [hd_eq, herase, hJ, zero_add, DFinsupp.single_zero]
  rw [injective_iff_map_eq_zero]
  intro d hd
  refine (key (d.support.sup id + 1) d fun j hj ↦ ?_).2 hd
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)

/-- The sum of maps `f j : Q j → M` out of the pieces of a direct sum is surjective when the
filtration `N` of `M` starts at `⊥`, is exhaustive, and every element of `N (J + 1)` is congruent
modulo `N J` to a value of `f J`. -/
theorem toModule_surjective_of_filtration (N : ℕ → Submodule R M) (h0 : N 0 = ⊥)
    (htop : ⨆ j, N j = ⊤) (f : ∀ j, Q j →ₗ[R] M)
    (hsplit : ∀ J, ∀ x ∈ N (J + 1), ∃ q, x - f J q ∈ N J) :
    Function.Surjective (DirectSum.toModule R ℕ M f) := by
  classical
  rw [← LinearMap.range_eq_top, eq_top_iff, ← htop, iSup_le_iff]
  intro J
  induction J with
  | zero => simp [h0]
  | succ J ih =>
    intro x hx
    obtain ⟨q, hq⟩ := hsplit J x hx
    obtain ⟨d, hd⟩ := ih hq
    refine ⟨d + DirectSum.of Q J q, ?_⟩
    have hof : DirectSum.toModule R ℕ M f (DirectSum.of Q J q) = f J q :=
      DirectSum.toModule_lof R J q
    rw [map_add, hd, hof, sub_add_cancel]

end DirectSum
