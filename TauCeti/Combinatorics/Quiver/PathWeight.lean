/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Combinatorics.Quiver.Path.Weight

/-!
# Path weights

Mathlib's `Quiver.Path.addWeight w p` sums the weights `w e` of the arrows along a path `p`. This
file records its evaluation at a constant weight: a constant weight `c` sums to `p.length • c`.
This identifies the path-length grading of a path algebra as the grading by the constant weight
one. It also records that pushing a path along a prefunctor computes the pulled-back arrow weight,
for both additive and multiplicative weights, and that a monoid homomorphism commutes with
multiplicative weights.
For natural-number arrow weights bounded by one, every weight up to a path's weight is attained
by a prefix.

## Main results

* `Quiver.Path.addWeight_const`: the constant weight `c` gives a path the weight `p.length • c`.
* `Prefunctor.addWeight_mapPath`: the weight of a pushed path is the pulled-back weight of the
  original path.
* `Prefunctor.weight_mapPath`: the multiplicative analogue for monoid-valued weights.
* `Quiver.Path.weight_ofAdd`: a weight valued in `Multiplicative M` is the additive weight.
* `Quiver.Path.map_weight`: a monoid homomorphism applied to a weight is the weight of the
  composed arrow weight.
* `Quiver.Path.exists_eq_comp_of_le_addWeight`: a natural-number weight bounded by one attains
  every intermediate value along a prefix.
-/

public section

universe u v

variable {V : Type u} [Quiver.{v} V] {M : Type*} [AddMonoid M]

namespace Quiver.Path

/-- **A constant weight counts arrows**: with every arrow of weight `c`, a path has weight
`p.length • c`. -/
@[simp]
theorem addWeight_const (c : M) {a b : V} (p : Quiver.Path a b) :
    p.addWeight (fun _ => c) = p.length • c := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih, succ_nsmul]

/-- For natural-number arrow weights bounded by one, a path whose weight is at least `n` has
a prefix of weight exactly `n`. -/
theorem exists_eq_comp_of_le_addWeight {i j : V} (p : Path i j)
    (wt : ∀ {a b : V}, (a ⟶ b) → ℕ) (hwt : ∀ {a b : V} (e : a ⟶ b), wt e ≤ 1)
    {n : ℕ} (hn : n ≤ p.addWeight wt) :
    ∃ (l : V) (p₁ : Path i l) (p₂ : Path l j),
      p = p₁.comp p₂ ∧ p₁.addWeight wt = n := by
  induction p with
  | nil =>
    have hn' : n = 0 := by simpa only [Path.addWeight_nil, Nat.le_zero] using hn
    exact ⟨_, Path.nil, Path.nil, rfl, (Path.addWeight_nil _ _).trans hn'.symm⟩
  | cons p a ih =>
    by_cases hp : n ≤ p.addWeight wt
    · obtain ⟨l, p₁, p₂, he, hn'⟩ := ih hp
      exact ⟨l, p₁, p₂.cons a, by simp only [Path.comp_cons, ← he], hn'⟩
    · have hn' : (p.cons a).addWeight wt = n := by
        have ha := hwt a
        rw [Path.addWeight_cons] at hn ⊢
        omega
      exact ⟨_, p.cons a, Path.nil, (Path.comp_nil _).symm, hn'⟩

/-- A monoid homomorphism sends the weight of a path to its weight for the composed arrow
weight. -/
theorem map_weight {N P F : Type*} [Monoid N] [Monoid P] [FunLike F N P] [MonoidHomClass F N P]
    (f : F) (wt : ∀ {a b : V}, (a ⟶ b) → N) {a b : V} (p : Quiver.Path a b) :
    f (p.weight wt) = p.weight fun e => f (wt e) := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih]

end Quiver.Path

namespace Prefunctor

variable {W : Type*} [Quiver W]

/-- **Pushing a path pulls back its arrow weight**: the weight of the image path is the sum of the
image-arrow weights along the original path. -/
@[simp]
theorem addWeight_mapPath (φ : V ⥤q W)
    (wt : ∀ {a b : W}, (a ⟶ b) → M) {a b : V} (p : Quiver.Path a b) :
    (φ.mapPath p).addWeight wt = p.addWeight fun e => wt (φ.map e) := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih]

/-- The multiplicative weight of a pushed path is its pulled-back arrow weight. -/
@[simp]
theorem weight_mapPath {N : Type*} [Monoid N] (φ : V ⥤q W)
    (wt : ∀ {a b : W}, (a ⟶ b) → N) {a b : V} (p : Quiver.Path a b) :
    (φ.mapPath p).weight wt = p.weight fun e => wt (φ.map e) := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih]

end Prefunctor

namespace Quiver.Path

/-- A multiplicative weight valued in `Multiplicative M` is the additive weight of the underlying
additive arrow weights. -/
theorem weight_ofAdd (w : ∀ {a b : V}, (a ⟶ b) → M) {a b : V} (p : Quiver.Path a b) :
    p.weight (fun e => Multiplicative.ofAdd (w e)) = Multiplicative.ofAdd (p.addWeight w) := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih]

end Quiver.Path
