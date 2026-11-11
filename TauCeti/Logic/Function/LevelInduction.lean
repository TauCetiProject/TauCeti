/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Finite.Range

/-!
# Construction of a family indexed by pairs by induction on a level

Let `P` be a finite type and `F x y` types, one for each pair of elements of `P`, with levels
`ℓ x y : ℕ`. A family `f : ∀ x y, F x y` satisfying a condition at every pair can be built by
induction on the level, choosing the value at each pair once the values at all pairs of smaller
level have been chosen (`TauCeti.exists_forall_of_forall_level_lt`).
-/

public section

namespace TauCeti

variable {P : Type*}

/-- **Construction of a family by induction on a level.** Let `F x y` be types, one for each
pair of elements of `P`, with levels `ℓ x y`, admissible elements `adm x y` and a condition
`good f x y` on families `f`. Suppose that an admissible family exists, and that for every
admissible family `f` satisfying the condition at the pairs of smaller level than `(x, y)` some
admissible `a` satisfies the condition at `(x, y)` for every admissible family which agrees with
`f` at the pairs of smaller level and takes the value `a` at `(x, y)`. Then some admissible family
satisfies the condition at every pair.

Twisting chain systems representing prescribed classes
(`TauCeti.TwistingChainSystem.exists_isRepresenting`) and the homotopies between them are
constructed in this way, with the level `(ind x - ind y).toNat`. -/
theorem exists_forall_of_forall_level_lt [Finite P] {F : P → P → Type*} (ℓ : P → P → ℕ)
    (adm : ∀ x y, F x y → Prop) (good : (∀ x y, F x y) → P → P → Prop)
    (h₀ : ∃ f : ∀ x y, F x y, ∀ x y, adm x y (f x y))
    (hstep : ∀ f : ∀ x y, F x y, (∀ x y, adm x y (f x y)) → ∀ x y,
      (∀ x' y', ℓ x' y' < ℓ x y → good f x' y') →
      ∃ a, adm x y a ∧ ∀ f' : ∀ x y, F x y, (∀ x y, adm x y (f' x y)) →
        (∀ x' y', ℓ x' y' < ℓ x y → f' x' y' = f x' y') → f' x y = a → good f' x y) :
    ∃ f : ∀ x y, F x y, (∀ x y, adm x y (f x y)) ∧ ∀ x y, good f x y := by
  -- Induction on the level below which the condition holds, for every admissible family agreeing
  -- with the constructed one there.
  have key (d : ℕ) : ∃ f : ∀ x y, F x y, (∀ x y, adm x y (f x y)) ∧
      ∀ f' : ∀ x y, F x y, (∀ x y, adm x y (f' x y)) →
        (∀ x y, ℓ x y < d → f' x y = f x y) → ∀ x y, ℓ x y < d → good f' x y := by
    induction d with
    | zero =>
      obtain ⟨f, hf⟩ := h₀
      exact ⟨f, hf, fun _ _ _ _ _ h ↦ absurd h (Nat.not_lt_zero _)⟩
    | succ d ih =>
      obtain ⟨f, hf, hd⟩ := ih
      have hnew (x y : P) (hxy : ℓ x y = d) :=
        hstep f hf x y fun x' y' h ↦ hd f hf (fun _ _ _ ↦ rfl) x' y' (hxy ▸ h)
      classical
      -- The new family only changes the values at the pairs of level `d`.
      let g : ∀ x y, F x y := fun x y ↦
        if hxy : ℓ x y = d then (hnew x y hxy).choose else f x y
      have hg (x y : P) : adm x y (g x y) := by
        by_cases hxy : ℓ x y = d
        · simpa only [g, hxy, ↓reduceDIte] using (hnew x y hxy).choose_spec.1
        · simpa only [g, hxy, ↓reduceDIte] using hf x y
      refine ⟨g, hg, fun f' hf' hfg x y hxy ↦ ?_⟩
      have hlt (x' y' : P) (h : ℓ x' y' < d) : f' x' y' = f x' y' := by
        simpa only [g, h.ne, ↓reduceDIte] using hfg x' y' (Nat.lt_succ_of_lt h)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hxy with hxy | hxy
      · exact hd f' hf' hlt x y hxy
      · refine (hnew x y hxy).choose_spec.2 f' hf' (fun x' y' h ↦ hlt x' y' (hxy ▸ h)) ?_
        simpa only [g, hxy, ↓reduceDIte] using hfg x y (Nat.lt_succ_of_le hxy.le)
  -- The levels of the finitely many pairs are bounded.
  obtain ⟨N, hN⟩ := (Set.finite_range fun p : P × P ↦ ℓ p.1 p.2).bddAbove
  obtain ⟨f, hf, hgood⟩ := key (N + 1)
  exact ⟨f, hf, fun x y ↦ hgood f hf (fun _ _ _ ↦ rfl) x y
    (Nat.lt_succ_of_le (hN (Set.mem_range_self (x, y))))⟩

end TauCeti
