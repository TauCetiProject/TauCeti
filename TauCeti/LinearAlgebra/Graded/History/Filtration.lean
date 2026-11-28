/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.LinearAlgebra.Graded.History.Basic

/-!
# Filtration bounds for homogeneous histories

When each projected arrow transfer raises an additive filtration by one, a history
along `p` sends an input in step `k` into step `k + p.length`. It vanishes
if that step is zero. For exclusive cutoffs `r ≤ s`, the sums over `j < s` and
`j < r` agree if the step reached by each discarded path `p j` is zero.
For a decreasing filtration it suffices that step `k + r` is zero and that
`r ≤ (p j).length` for every `r ≤ j < s`. The stages need only be additive submonoids.

Adapted from `Mei/LinearAlgebra/GradedModule/History/Filtration.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public section

open Quiver TauCeti

section

variable {Q : Type*} [Quiver Q] {a b : Q} {R : Type*} [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  (T : ∀ {q q' : Q}, (q ⟶ q') → M q →ₗ[R] M q')
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)] (ℳ : ∀ q, ι q → Submodule R (M q))
  [∀ q, DirectSum.Decomposition (ℳ q)]
  {F : ∀ q, ℕ → AddSubmonoid (M q)}

namespace Quiver.Path

/-- If every component of an arrow raises filtration by one, a whole history
raises it by the path length. -/
theorem homogeneousHistory_mem_of_components_raise
    (hF : ∀ {q q' : Q} (e : q ⟶ q') (i : ι q') (k : ℕ) {y : M q},
      y ∈ F q k → homogeneousComponent (ℳ q') i (T e y) ∈ F q' (k + 1))
    (p : Path a b) (d : p.Degrees ι) {k : ℕ} {x : M a} (hx : x ∈ F a k) :
    p.homogeneousHistory T ℳ d x ∈ F b (k + p.length) := by
  induction p with
  | nil => simpa only [length_nil, Nat.add_zero, homogeneousHistory_nil, LinearMap.id_apply]
      using hx
  | cons p e ih =>
    obtain ⟨d, i⟩ := d
    simpa only [length_cons, ← Nat.add_assoc, homogeneousHistory_cons, LinearMap.comp_apply]
      using hF e i (k + p.length) (ih d)

/-- A history vanishes when the filtration step reached by its path is zero. -/
theorem homogeneousHistory_eq_zero_of_eq_bot
    (hF : ∀ {q q' : Q} (e : q ⟶ q') (i : ι q') (k : ℕ) {y : M q},
      y ∈ F q k → homogeneousComponent (ℳ q') i (T e y) ∈ F q' (k + 1))
    (p : Path a b) (d : p.Degrees ι) {k : ℕ} (hp : F b (k + p.length) = ⊥)
    {x : M a} (hx : x ∈ F a k) :
    p.homogeneousHistory T ℳ d x = 0 := by
  have hmem := p.homogeneousHistory_mem_of_components_raise T ℳ hF d hx
  rwa [hp, AddSubmonoid.mem_bot] at hmem

end Quiver.Path

namespace TauCeti

open Classical in
/-- For exclusive cutoffs `r ≤ s`, selected history sums agree when every
discarded path reaches a zero step of the filtration. -/
theorem sum_range_sum_homogeneousHistory_eq_of_eq_bot
    (hF : ∀ {q q' : Q} (e : q ⟶ q') (i : ι q') (l : ℕ) {y : M q},
      y ∈ F q l → homogeneousComponent (ℳ q') i (T e y) ∈ F q' (l + 1))
    (p : ℕ → Path a b) {k r s : ℕ}
    (hp : ∀ j, r ≤ j → j < s → F b (k + (p j).length) = ⊥) (hrs : r ≤ s)
    {x : M a} (hx : x ∈ F a k) (S : (j : ℕ) → Finset ((p j).Degrees ι)) :
    (∑ j ∈ Finset.range s, ∑ d ∈ S j, (p j).homogeneousHistory T ℳ d x) =
      ∑ j ∈ Finset.range r, ∑ d ∈ S j, (p j).homogeneousHistory T ℳ d x := by
  symm
  apply Finset.sum_subset (Finset.range_mono hrs)
  intro j hjs hj
  have hjr : r ≤ j := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
  apply Finset.sum_eq_zero
  intro d _
  exact (p j).homogeneousHistory_eq_zero_of_eq_bot T ℳ hF d
    (hp j hjr (Finset.mem_range.mp hjs)) hx

end TauCeti

end
