/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.LinearAlgebra.Graded.History.Basic

/-!
# Filtration bounds for homogeneous histories

When each arrow raises a filtration after selecting any homogeneous component,
every history advances at least one filtration step per arrow. If the filtration
vanishes at a fixed order, sufficiently long histories vanish individually.

Adapted from `Mei/LinearAlgebra/GradedModule/History/Filtration.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public section

open TauCeti

namespace Quiver.Path

variable {Q : Type*} [Quiver Q] {a b : Q} {R : Type*} [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  (T : ∀ {q q' : Q}, (q ⟶ q') → M q →ₗ[R] M q')
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)] (ℳ : ∀ q, ι q → Submodule R (M q))
  [∀ q, DirectSum.Decomposition (ℳ q)]
  {F : ∀ q, ℕ → Submodule R (M q)}

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

/-- A history that reaches a zero step of a decreasing filtration vanishes,
whether or not other histories are included in the sum. -/
theorem homogeneousHistory_eq_zero_of_le_length
    (hF : ∀ {q q' : Q} (e : q ⟶ q') (i : ι q') (k : ℕ) {y : M q},
      y ∈ F q k → homogeneousComponent (ℳ q') i (T e y) ∈ F q' (k + 1))
    (p : Path a b) (d : p.Degrees ι) {k r : ℕ} (hanti : Antitone (F b)) (hr : F b r = ⊥)
    (hp : r ≤ k + p.length) {x : M a} (hx : x ∈ F a k) :
    p.homogeneousHistory T ℳ d x = 0 := by
  have hmem := hanti hp (p.homogeneousHistory_mem_of_components_raise T ℳ hF d hx)
  rwa [hr, Submodule.mem_bot] at hmem

end Quiver.Path
