/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Category.TopCat.Limits.Konig
public import TauCeti.Algebra.Category.ModuleCat.Tower.ProZero
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Towers of compact Hausdorff modules have vanishing `lim¹`

Let `A₀ ← A₁ ← A₂ ← ⋯` be a tower of modules whose terms carry compact Hausdorff topologies with
continuous addition, and whose transitions `φₙ : Aₙ₊₁ → Aₙ` are continuous. Then the shift map
`∏ₙ Aₙ → ∏ₙ Aₙ`, `(xₙ) ↦ (xₙ - φₙ(xₙ₊₁))`, is surjective, so `lim¹ A = 0`. No surjectivity of the
transitions is assumed. For a family `(bₙ)`, the solutions of `xₙ - φₙ(xₙ₊₁) = bₙ` are the points
of the inverse limit of the spaces `Aₙ` along the continuous maps `y ↦ bₙ + φₙ(y)`, and an
inverse limit of nonempty compact Hausdorff spaces is nonempty
(`TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`). Equivalently: the first `N`
equations are solved backwards from `x_N = 0`, and compactness of `∏ₙ Aₙ` lets `N` go to infinity.

This is a statement about the underlying abelian groups: the topology only serves to produce
solutions. Compactness cannot be dropped: over `ℤ`, the tower `ℤ ← ℤ ← ⋯` with transitions
multiplication by a prime `p` has `lim¹ ≃ ℤ_[p] ⧸ ℤ ≠ 0`
(`TauCeti.ModuleTower.nontrivial_limOne_multiplicationTower`), whereas over `ℤ_[p]`, which is
compact, the tower `ℤ_[p] ← ℤ_[p] ← ⋯` with the same transitions has `lim¹ = 0`
(`TauCeti.ModuleTower.subsingleton_limOne_multiplicationTower_of_compactSpace`).

Together with `TauCeti.ModuleTower.subsingleton_limOne_of_exact`, this also gives `lim¹ = 0` for a
levelwise extension of a tower with surjective transitions by a compact tower, such as a tower of
completed representation rings split into a rank part and compact completed augmentation ideals.
This is how the `lim¹` terms of Milnor sequences for sequential colimits of spaces are killed.

## Main results

* `TauCeti.ModuleTower.shift_surjective_of_compactSpace`: the shift map of a tower of compact
  Hausdorff modules with continuous transitions is surjective.
* `TauCeti.ModuleTower.subsingleton_limOne_of_compactSpace`: such a tower has `lim¹ A = 0`.
* `TauCeti.ModuleTower.subsingleton_limOne_multiplicationTower_of_compactSpace`: for a compact
  Hausdorff topological ring `R` and `a : R`, the tower `R ← R ← ⋯` with transitions
  multiplication by `a` has `lim¹ = 0`.

## References

* M. F. Atiyah, G. B. Segal, *Equivariant K-theory and completion*, J. Differential Geom. 3
  (1969), 1–18, Proposition 4.2.
* C. A. Weibel, *An introduction to homological algebra*, §3.5.
-/

public section

noncomputable section

namespace TauCeti

namespace ModuleTower

open CategoryTheory Opposite

universe v u

variable {R : Type u} [Ring R]

section CompactSpace

variable (F : ModuleTower.{v} R) [∀ n, TopologicalSpace (F.obj (op n))]
  [∀ n, CompactSpace (F.obj (op n))] [∀ n, T2Space (F.obj (op n))]
  [∀ n, ContinuousAdd (F.obj (op n))]

/-- **The shift map of a tower of compact Hausdorff modules is surjective.** If the terms `Aₙ` of
a tower are compact Hausdorff with continuous addition and the transitions `φₙ` are continuous,
then every family `(bₙ)` is of the form `(xₙ - φₙ(xₙ₊₁))`. The transitions need not be
surjective. -/
theorem shift_surjective_of_compactSpace (hF : ∀ n, Continuous (F.transition n)) :
    Function.Surjective F.shift := by
  intro b
  -- The tower of compact Hausdorff spaces `Aₙ` along the continuous maps `y ↦ bₙ + φₙ(y)`; a
  -- point of its inverse limit is a preimage of `b` under the shift map.
  let G : ℕᵒᵖ ⥤ TopCat.{v} := Functor.ofOpSequence (X := fun n ↦ TopCat.of (F.obj (op n)))
    fun n ↦ TopCat.ofHom ⟨fun y ↦ b n + F.transition n y, continuous_const.add (hF n)⟩
  -- The terms of `G` are the spaces `Aₙ`, by definition of `Functor.ofOpSequence`.
  have hobj (n : ℕ) : G.obj (op n) = TopCat.of (F.obj (op n)) := rfl
  have : ∀ j, Nonempty (G.obj j) := fun ⟨n⟩ ↦ hobj n ▸ ⟨(0 : F.obj (op n))⟩
  have : ∀ j, CompactSpace (G.obj j) := fun ⟨n⟩ ↦
    hobj n ▸ inferInstanceAs (CompactSpace (F.obj (op n)))
  have : ∀ j, T2Space (G.obj j) := fun ⟨n⟩ ↦ hobj n ▸ inferInstanceAs (T2Space (F.obj (op n)))
  obtain ⟨⟨x, hx⟩⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system G
  -- The point `x` of the inverse limit, read in `∏ₙ Aₙ` through `hobj`.
  refine ⟨(fun n ↦ x (op n) : F.Product), funext fun n ↦ ?_⟩
  have h := hx (homOfLE (Nat.le_add_right n 1)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  -- `h` says `bₙ + φₙ(xₙ₊₁) = xₙ`, after evaluating the continuous map `TopCat.ofHom ⟨_, _⟩`.
  exact (F.shift_apply _ n).trans (sub_eq_of_eq_add h.symm)

/-- **Towers of compact Hausdorff modules have vanishing `lim¹`.** If the terms `Aₙ` of a tower are
compact Hausdorff with continuous addition and the transitions are continuous, then
`lim¹ A = 0`, whether or not the transitions are surjective. -/
theorem subsingleton_limOne_of_compactSpace (hF : ∀ n, Continuous (F.transition n)) :
    Subsingleton F.limOne :=
  F.subsingleton_limOne_iff.2 (F.shift_surjective_of_compactSpace hF)

end CompactSpace

/-- For a compact Hausdorff topological ring `R` and `a : R`, the tower `R ← R ← ⋯` whose
transitions are multiplication by `a` has `lim¹ = 0`. For instance this holds for `R = ℤ_[p]` and
`a = p`, although the same tower over `ℤ` has nonzero `lim¹`
(`TauCeti.ModuleTower.nontrivial_limOne_multiplicationTower`). -/
theorem subsingleton_limOne_multiplicationTower_of_compactSpace [TopologicalSpace R]
    [CompactSpace R] [T2Space R] [ContinuousAdd R] [ContinuousMul R] (a : R) :
    Subsingleton (multiplicationTower a).limOne := by
  -- The terms of `multiplicationTower a` are `R` (`multiplicationTower_obj`), with its topology.
  let (n : ℕ) : TopologicalSpace ((multiplicationTower a).obj (op n)) :=
    inferInstanceAs (TopologicalSpace R)
  have (n : ℕ) : CompactSpace ((multiplicationTower a).obj (op n)) :=
    inferInstanceAs (CompactSpace R)
  have (n : ℕ) : T2Space ((multiplicationTower a).obj (op n)) := inferInstanceAs (T2Space R)
  have (n : ℕ) : ContinuousAdd ((multiplicationTower a).obj (op n)) :=
    inferInstanceAs (ContinuousAdd R)
  refine subsingleton_limOne_of_compactSpace _ fun n ↦ ?_
  rw [multiplicationTower_transition]
  -- `toSpanSingleton R R a` is `x ↦ x • a = x * a` on the carrier `R` of the terms.
  exact (continuous_id.mul continuous_const : Continuous fun x : R ↦ x * a)

/-- The tower `ℤ_[p] ← ℤ_[p] ← ⋯` with transitions multiplication by `p`, which are not surjective,
has `lim¹ = 0` since `ℤ_[p]` is compact. -/
example (p : ℕ) [Fact p.Prime] : Subsingleton (multiplicationTower (p : ℤ_[p])).limOne :=
  subsingleton_limOne_multiplicationTower_of_compactSpace _

end ModuleTower

end TauCeti
