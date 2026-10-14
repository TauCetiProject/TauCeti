/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.EdgeFactor
import Mathlib.Tactic.LinearCombination

/-!
# Five-component paths of minimal numerical types of genus one

This file classifies the numerical data on a minimal genus-one numerical type whose five
components form a path `a - b - c - d - e`. There are five possibilities up to reversing the
path. They are cases (17)--(21) in the Stacks Project classification. In two of them the only
edge joining components of different weights is the internal edge `c - d`, with weights
`(w, w, w, 2w, 2w)` or `(2w, 2w, 2w, w, w)`. In the other three both endpoint edges `a - b` and
`d - e` join components of different weights, with weights `(w, 2w, 2w, 2w, 4w)`,
`(w, 2w, 2w, 2w, w)` or `(2w, w, w, w, 2w)`.

The classification is stated first for five components of self-intersection `-2w` and then for a
minimal numerical type of arithmetic genus one, whose components satisfy those equations.

## References

* [Stacks Project, Lemma 55.6.2, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T),
  cases (17)--(21).
-/

public section

namespace TauCeti.NumericalType

open Finset

universe u

variable {T : NumericalType.{u}}

/-- The five unoriented path shapes among minimal numerical types of genus one with five
components. The arguments list the components consecutively along the path. -/
def IsGenusOneFivePathShape (T : NumericalType) (a b c d e : T.Component) : Prop :=
  ∃ w m : ℤ, 0 < w ∧ 0 < m ∧
    (((T.weight a : ℤ) = w ∧ T.weight b = w ∧ T.weight c = w ∧
        (T.weight d : ℤ) = 2 * w ∧ (T.weight e : ℤ) = 2 * w ∧
        (T.multiplicity a : ℤ) = m ∧ (T.multiplicity b : ℤ) = 2 * m ∧
        (T.multiplicity c : ℤ) = 3 * m ∧ (T.multiplicity d : ℤ) = 2 * m ∧
        (T.multiplicity e : ℤ) = m ∧ T.intersection a b = w ∧
        T.intersection b c = w ∧ T.intersection c d = 2 * w ∧
        T.intersection d e = 2 * w) ∨
      ((T.weight a : ℤ) = 2 * w ∧ (T.weight b : ℤ) = 2 * w ∧
        (T.weight c : ℤ) = 2 * w ∧ T.weight d = w ∧ T.weight e = w ∧
        (T.multiplicity a : ℤ) = m ∧ (T.multiplicity b : ℤ) = 2 * m ∧
        (T.multiplicity c : ℤ) = 3 * m ∧ (T.multiplicity d : ℤ) = 4 * m ∧
        (T.multiplicity e : ℤ) = 2 * m ∧ T.intersection a b = 2 * w ∧
        T.intersection b c = 2 * w ∧ T.intersection c d = 2 * w ∧
        T.intersection d e = w) ∨
      (T.weight a = w ∧ (T.weight b : ℤ) = 2 * w ∧
        (T.weight c : ℤ) = 2 * w ∧ (T.weight d : ℤ) = 2 * w ∧
        (T.weight e : ℤ) = 4 * w ∧ (T.multiplicity a : ℤ) = 2 * m ∧
        (T.multiplicity b : ℤ) = 2 * m ∧ (T.multiplicity c : ℤ) = 2 * m ∧
        (T.multiplicity d : ℤ) = 2 * m ∧ T.multiplicity e = m ∧
        T.intersection a b = 2 * w ∧ T.intersection b c = 2 * w ∧
        T.intersection c d = 2 * w ∧ T.intersection d e = 4 * w) ∨
      (T.weight a = w ∧ (T.weight b : ℤ) = 2 * w ∧
        (T.weight c : ℤ) = 2 * w ∧ (T.weight d : ℤ) = 2 * w ∧ T.weight e = w ∧
        (T.multiplicity a : ℤ) = m ∧ T.multiplicity b = m ∧
        T.multiplicity c = m ∧ T.multiplicity d = m ∧ T.multiplicity e = m ∧
        T.intersection a b = 2 * w ∧ T.intersection b c = 2 * w ∧
        T.intersection c d = 2 * w ∧ T.intersection d e = 2 * w) ∨
      ((T.weight a : ℤ) = 2 * w ∧ T.weight b = w ∧ T.weight c = w ∧
        T.weight d = w ∧ (T.weight e : ℤ) = 2 * w ∧
        (T.multiplicity a : ℤ) = m ∧ (T.multiplicity b : ℤ) = 2 * m ∧
        (T.multiplicity c : ℤ) = 2 * m ∧ (T.multiplicity d : ℤ) = 2 * m ∧
        T.multiplicity e = m ∧ T.intersection a b = 2 * w ∧
        T.intersection b c = w ∧ T.intersection c d = w ∧
        T.intersection d e = 2 * w))

/-- Unfold `IsGenusOneFivePathShape` into the five weight, multiplicity and intersection
patterns of cases (17)--(21) in the genus-one classification. -/
theorem isGenusOneFivePathShape_iff {a b c d e : T.Component} :
    T.IsGenusOneFivePathShape a b c d e ↔
      ∃ w m : ℤ, 0 < w ∧ 0 < m ∧
        (((T.weight a : ℤ) = w ∧ T.weight b = w ∧ T.weight c = w ∧
            (T.weight d : ℤ) = 2 * w ∧ (T.weight e : ℤ) = 2 * w ∧
            (T.multiplicity a : ℤ) = m ∧ (T.multiplicity b : ℤ) = 2 * m ∧
            (T.multiplicity c : ℤ) = 3 * m ∧ (T.multiplicity d : ℤ) = 2 * m ∧
            (T.multiplicity e : ℤ) = m ∧ T.intersection a b = w ∧
            T.intersection b c = w ∧ T.intersection c d = 2 * w ∧
            T.intersection d e = 2 * w) ∨
          ((T.weight a : ℤ) = 2 * w ∧ (T.weight b : ℤ) = 2 * w ∧
            (T.weight c : ℤ) = 2 * w ∧ T.weight d = w ∧ T.weight e = w ∧
            (T.multiplicity a : ℤ) = m ∧ (T.multiplicity b : ℤ) = 2 * m ∧
            (T.multiplicity c : ℤ) = 3 * m ∧ (T.multiplicity d : ℤ) = 4 * m ∧
            (T.multiplicity e : ℤ) = 2 * m ∧ T.intersection a b = 2 * w ∧
            T.intersection b c = 2 * w ∧ T.intersection c d = 2 * w ∧
            T.intersection d e = w) ∨
          (T.weight a = w ∧ (T.weight b : ℤ) = 2 * w ∧
            (T.weight c : ℤ) = 2 * w ∧ (T.weight d : ℤ) = 2 * w ∧
            (T.weight e : ℤ) = 4 * w ∧ (T.multiplicity a : ℤ) = 2 * m ∧
            (T.multiplicity b : ℤ) = 2 * m ∧ (T.multiplicity c : ℤ) = 2 * m ∧
            (T.multiplicity d : ℤ) = 2 * m ∧ T.multiplicity e = m ∧
            T.intersection a b = 2 * w ∧ T.intersection b c = 2 * w ∧
            T.intersection c d = 2 * w ∧ T.intersection d e = 4 * w) ∨
          (T.weight a = w ∧ (T.weight b : ℤ) = 2 * w ∧
            (T.weight c : ℤ) = 2 * w ∧ (T.weight d : ℤ) = 2 * w ∧ T.weight e = w ∧
            (T.multiplicity a : ℤ) = m ∧ T.multiplicity b = m ∧
            T.multiplicity c = m ∧ T.multiplicity d = m ∧ T.multiplicity e = m ∧
            T.intersection a b = 2 * w ∧ T.intersection b c = 2 * w ∧
            T.intersection c d = 2 * w ∧ T.intersection d e = 2 * w) ∨
          ((T.weight a : ℤ) = 2 * w ∧ T.weight b = w ∧ T.weight c = w ∧
            T.weight d = w ∧ (T.weight e : ℤ) = 2 * w ∧
            (T.multiplicity a : ℤ) = m ∧ (T.multiplicity b : ℤ) = 2 * m ∧
            (T.multiplicity c : ℤ) = 2 * m ∧ (T.multiplicity d : ℤ) = 2 * m ∧
            T.multiplicity e = m ∧ T.intersection a b = 2 * w ∧
            T.intersection b c = w ∧ T.intersection c d = w ∧
            T.intersection d e = 2 * w)) :=
  Iff.rfl

/-- The factor patterns when the first edge has factors `(1, 1)`. -/
private lemma fivePath_factor_cases_one_one
    {m₀ m₁ m₂ m₃ m₄ p₁ q₁ p₂ q₂ p₃ q₃ : ℤ}
    (hm₀ : 0 < m₀) (_hm₁ : 0 < m₁) (_hm₂ : 0 < m₂) (hm₃ : 0 < m₃) (hm₄ : 0 < m₄)
    (h₁ : IsGenusOneEdgeFactor p₁ q₁) (h₂ : IsGenusOneEdgeFactor p₂ q₂)
    (h₃ : IsGenusOneEdgeFactor p₃ q₃) (e₀ : m₁ = 2 * m₀)
    (e₁ : m₀ + m₂ * p₁ = 2 * m₁)
    (e₂ : m₁ * q₁ + m₃ * p₂ = 2 * m₂)
    (e₃ : m₂ * q₂ + m₄ * p₃ = 2 * m₃) (e₄ : m₃ * q₃ = 2 * m₄) :
    (p₁ = 1 ∧ q₁ = 1 ∧ p₂ = 2 ∧ q₂ = 1 ∧ p₃ = 1 ∧ q₃ = 1) ∨
    (p₁ = 1 ∧ q₁ = 1 ∧ p₂ = 1 ∧ q₂ = 2 ∧ p₃ = 1 ∧ q₃ = 1) ∨
    (p₁ = 1 ∧ q₁ = 2 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 1 ∧ q₃ = 1) ∨
    (p₁ = 2 ∧ q₁ = 1 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 1 ∧ q₃ = 1) := by
  rw [isGenusOneEdgeFactor_iff] at h₁ h₂ h₃
  rcases h₁ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    rcases h₂ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      rcases h₃ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        omega

/-- The factor patterns when the first edge has factors `(2, 1)`. -/
private lemma fivePath_factor_cases_two_one
    {m₀ m₁ m₂ m₃ m₄ p₁ q₁ p₂ q₂ p₃ q₃ : ℤ}
    (_hm₀ : 0 < m₀) (_hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hm₃ : 0 < m₃) (hm₄ : 0 < m₄)
    (h₁ : IsGenusOneEdgeFactor p₁ q₁) (h₂ : IsGenusOneEdgeFactor p₂ q₂)
    (h₃ : IsGenusOneEdgeFactor p₃ q₃) (e₀ : 2 * m₁ = 2 * m₀)
    (e₁ : m₀ + m₂ * p₁ = 2 * m₁) (e₂ : m₁ * q₁ + m₃ * p₂ = 2 * m₂)
    (e₃ : m₂ * q₂ + m₄ * p₃ = 2 * m₃) (e₄ : m₃ * q₃ = 2 * m₄) :
    (p₁ = 1 ∧ q₁ = 1 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 2 ∧ q₃ = 1) ∨
    (p₁ = 1 ∧ q₁ = 1 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 1 ∧ q₃ = 2) := by
  rw [isGenusOneEdgeFactor_iff] at h₁ h₂ h₃
  rcases h₁ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    rcases h₂ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      rcases h₃ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        omega

/-- Triple factors at the first edge are incompatible with a positive kernel vector. -/
private lemma fivePath_factor_cases_triple_false
    {m₀ m₁ m₂ m₃ m₄ p₁ q₁ p₂ q₂ p₃ q₃ r s : ℤ}
    (hm₀ : 0 < m₀) (_hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hm₃ : 0 < m₃) (hm₄ : 0 < m₄)
    (h₁ : IsGenusOneEdgeFactor p₁ q₁) (h₂ : IsGenusOneEdgeFactor p₂ q₂)
    (h₃ : IsGenusOneEdgeFactor p₃ q₃) (e₀ : s * m₁ = 2 * m₀)
    (e₁ : r * m₀ + m₂ * p₁ = 2 * m₁) (e₂ : m₁ * q₁ + m₃ * p₂ = 2 * m₂)
    (e₃ : m₂ * q₂ + m₄ * p₃ = 2 * m₃) (e₄ : m₃ * q₃ = 2 * m₄)
    (hsr : (s = 3 ∧ r = 1) ∨ (s = 1 ∧ r = 3)) : False := by
  rw [isGenusOneEdgeFactor_iff] at h₁ h₂ h₃
  rcases hsr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h₁ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      rcases h₂ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        rcases h₃ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
          omega

/-- The eight oriented endpoint-factor patterns compatible with the fibre relations along a
five-component path. Reversal identifies them with the five unoriented shapes. -/
private lemma fivePath_factor_cases
    {m₀ m₁ m₂ m₃ m₄ p₀ q₀ p₁ q₁ p₂ q₂ p₃ q₃ : ℤ}
    (hm₀ : 0 < m₀) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hm₃ : 0 < m₃) (hm₄ : 0 < m₄)
    (h₀ : IsGenusOneEdgeFactor p₀ q₀) (h₁ : IsGenusOneEdgeFactor p₁ q₁)
    (h₂ : IsGenusOneEdgeFactor p₂ q₂) (h₃ : IsGenusOneEdgeFactor p₃ q₃)
    (e₀ : m₁ * p₀ = 2 * m₀) (e₁ : m₀ * q₀ + m₂ * p₁ = 2 * m₁)
    (e₂ : m₁ * q₁ + m₃ * p₂ = 2 * m₂)
    (e₃ : m₂ * q₂ + m₄ * p₃ = 2 * m₃) (e₄ : m₃ * q₃ = 2 * m₄) :
    (p₀ = 1 ∧ q₀ = 1 ∧ p₁ = 1 ∧ q₁ = 1 ∧ p₂ = 2 ∧ q₂ = 1 ∧ p₃ = 1 ∧ q₃ = 1) ∨
    (p₀ = 1 ∧ q₀ = 1 ∧ p₁ = 1 ∧ q₁ = 1 ∧ p₂ = 1 ∧ q₂ = 2 ∧ p₃ = 1 ∧ q₃ = 1) ∨
    (p₀ = 2 ∧ q₀ = 1 ∧ p₁ = 1 ∧ q₁ = 1 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 2 ∧ q₃ = 1) ∨
    (p₀ = 2 ∧ q₀ = 1 ∧ p₁ = 1 ∧ q₁ = 1 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 1 ∧ q₃ = 2) ∨
    (p₀ = 1 ∧ q₀ = 2 ∧ p₁ = 1 ∧ q₁ = 1 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 2 ∧ q₃ = 1) ∨
    (p₀ = 1 ∧ q₀ = 1 ∧ p₁ = 1 ∧ q₁ = 2 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 1 ∧ q₃ = 1) ∨
    (p₀ = 1 ∧ q₀ = 1 ∧ p₁ = 2 ∧ q₁ = 1 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 1 ∧ q₃ = 1) ∨
    (p₀ = 1 ∧ q₀ = 2 ∧ p₁ = 1 ∧ q₁ = 1 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 1 ∧ q₃ = 2) := by
  rw [isGenusOneEdgeFactor_iff] at h₀
  rcases h₀ with h₀ | h₀ | h₀ | h₀ | h₀
  · rcases h₀ with ⟨rfl, rfl⟩
    obtain h | h | h | h := fivePath_factor_cases_one_one hm₀ hm₁ hm₂ hm₃ hm₄
      h₁ h₂ h₃ (by omega) (by omega) e₂ e₃ e₄ <;>
      rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;> omega
  · rcases h₀ with ⟨rfl, rfl⟩
    obtain h | h := fivePath_factor_cases_two_one hm₀ hm₁ hm₂ hm₃ hm₄
      h₁ h₂ h₃ (by omega) (by omega) e₂ e₃ e₄ <;>
      rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;> omega
  · rcases h₀ with ⟨rfl, rfl⟩
    obtain h | h := fivePath_factor_cases_two_one (m₀ := m₁) hm₁ hm₁ hm₂ hm₃ hm₄
      h₁ h₂ h₃ rfl (by omega) e₂ e₃ e₄ <;>
      rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;> omega
  · rcases h₀ with ⟨rfl, rfl⟩
    exact (fivePath_factor_cases_triple_false hm₀ hm₁ hm₂ hm₃ hm₄ h₁ h₂ h₃
      (by omega) (by omega) e₂ e₃ e₄ (Or.inl ⟨rfl, rfl⟩)).elim
  · rcases h₀ with ⟨rfl, rfl⟩
    exact (fivePath_factor_cases_triple_false hm₀ hm₁ hm₂ hm₃ hm₄ h₁ h₂ h₃
      (by omega) (by omega) e₂ e₃ e₄ (Or.inr ⟨rfl, rfl⟩)).elim

/-- The fibre relations at the five components of a path, after substituting the
self-intersections `-2w` and the vanishing intersections between nonadjacent components. -/
private lemma fivePath_fiber_equations
    (hcard : Fintype.card T.Component = 5) {a b c d e : T.Component}
    (haa : T.intersection a a = -(2 * (T.weight a : ℤ)))
    (hbb : T.intersection b b = -(2 * (T.weight b : ℤ)))
    (hcc : T.intersection c c = -(2 * (T.weight c : ℤ)))
    (hdd : T.intersection d d = -(2 * (T.weight d : ℤ)))
    (hee : T.intersection e e = -(2 * (T.weight e : ℤ)))
    (hac₀ : T.intersection a c = 0) (had₀ : T.intersection a d = 0)
    (hae₀ : T.intersection a e = 0) (hbd₀ : T.intersection b d = 0)
    (hbe₀ : T.intersection b e = 0) (hce₀ : T.intersection c e = 0)
    (hab₀ : 0 < T.intersection a b) (hbc₀ : 0 < T.intersection b c)
    (hcd₀ : 0 < T.intersection c d) (hde₀ : 0 < T.intersection d e) :
    (T.multiplicity b : ℤ) * T.intersection a b = 2 * T.weight a * T.multiplicity a ∧
    (T.multiplicity a : ℤ) * T.intersection a b + T.multiplicity c * T.intersection b c =
      2 * T.weight b * T.multiplicity b ∧
    (T.multiplicity b : ℤ) * T.intersection b c + T.multiplicity d * T.intersection c d =
      2 * T.weight c * T.multiplicity c ∧
    (T.multiplicity c : ℤ) * T.intersection c d + T.multiplicity e * T.intersection d e =
      2 * T.weight d * T.multiplicity d ∧
    (T.multiplicity d : ℤ) * T.intersection d e = 2 * T.weight e * T.multiplicity e := by
  have ne_of_nonneg {x y : T.Component}
      (hxx : T.intersection x x = -(2 * (T.weight x : ℤ)))
      (hxy : 0 ≤ T.intersection x y) : x ≠ y := by
    rintro rfl
    have := (T.weight x).pos
    omega
  have hab := ne_of_nonneg haa hab₀.le
  have hac := ne_of_nonneg haa hac₀.ge
  have had := ne_of_nonneg haa had₀.ge
  have hae := ne_of_nonneg haa hae₀.ge
  have hbc := ne_of_nonneg hbb hbc₀.le
  have hbd := ne_of_nonneg hbb hbd₀.ge
  have hbe := ne_of_nonneg hbb hbe₀.ge
  have hcd := ne_of_nonneg hcc hcd₀.le
  have hce := ne_of_nonneg hcc hce₀.ge
  have hde := ne_of_nonneg hdd hde₀.le
  -- The five distinct components exhaust the numerical type.
  have hu : (univ : Finset T.Component) = {a, b, c, d, e} :=
    (eq_univ_of_card _ (by simp [hcard, hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde])).symm
  have relation (r : T.Component) :
      (T.multiplicity a : ℤ) * T.intersection r a +
          T.multiplicity b * T.intersection r b + T.multiplicity c * T.intersection r c +
          T.multiplicity d * T.intersection r d + T.multiplicity e * T.intersection r e = 0 := by
    have hr := T.fiber_relation r
    rw [hu, sum_insert (by simp [hab, hac, had, hae]),
      sum_insert (by simp [hbc, hbd, hbe]), sum_insert (by simp [hcd, hce]),
      sum_pair hde, ← add_assoc, ← add_assoc, ← add_assoc] at hr
    exact hr
  have ra := relation a
  have rb := relation b
  have rc := relation c
  have rd := relation d
  have re := relation e
  rw [haa, hac₀, had₀, hae₀] at ra
  rw [T.intersection_comm b a, hbb, hbd₀, hbe₀] at rb
  rw [T.intersection_comm c a, hac₀, T.intersection_comm c b, hcc, hce₀] at rc
  rw [T.intersection_comm d a, had₀, T.intersection_comm d b, hbd₀,
    T.intersection_comm d c, hdd] at rd
  rw [T.intersection_comm e a, hae₀, T.intersection_comm e b, hbe₀,
    T.intersection_comm e c, hce₀, T.intersection_comm e d, hee] at re
  exact ⟨by linear_combination ra, by linear_combination rb, by linear_combination rc,
    by linear_combination rd, by linear_combination re⟩

/-- Five components forming a path and having self-intersection `-2w` have one of the five
genus-one path shapes, after possibly reversing the path. -/
theorem isGenusOneFivePathShape_or_isGenusOneFivePathShape
    (hcard : Fintype.card T.Component = 5) {a b c d e : T.Component}
    (haa : T.intersection a a = -(2 * (T.weight a : ℤ)))
    (hbb : T.intersection b b = -(2 * (T.weight b : ℤ)))
    (hcc : T.intersection c c = -(2 * (T.weight c : ℤ)))
    (hdd : T.intersection d d = -(2 * (T.weight d : ℤ)))
    (hee : T.intersection e e = -(2 * (T.weight e : ℤ)))
    (hac₀ : T.intersection a c = 0) (had₀ : T.intersection a d = 0)
    (hae₀ : T.intersection a e = 0) (hbd₀ : T.intersection b d = 0)
    (hbe₀ : T.intersection b e = 0) (hce₀ : T.intersection c e = 0)
    (hab₀ : 0 < T.intersection a b) (hbc₀ : 0 < T.intersection b c)
    (hcd₀ : 0 < T.intersection c d) (hde₀ : 0 < T.intersection d e) :
    T.IsGenusOneFivePathShape a b c d e ∨ T.IsGenusOneFivePathShape e d c b a := by
  obtain ⟨ra, rb, rc, rd, re⟩ := fivePath_fiber_equations hcard haa hbb hcc hdd hee
    hac₀ had₀ hae₀ hbd₀ hbe₀ hce₀ hab₀ hbc₀ hcd₀ hde₀
  -- Factor each edge's intersection number by the weights at its two endpoints.
  obtain ⟨p₀, q₀, hpq₀, hp₀, hq₀⟩ := T.exists_genusOneEdgeFactors (by omega) haa hbb hab₀
  obtain ⟨p₁, q₁, hpq₁, hp₁, hq₁⟩ := T.exists_genusOneEdgeFactors (by omega) hbb hcc hbc₀
  obtain ⟨p₂, q₂, hpq₂, hp₂, hq₂⟩ := T.exists_genusOneEdgeFactors (by omega) hcc hdd hcd₀
  obtain ⟨p₃, q₃, hpq₃, hp₃, hq₃⟩ := T.exists_genusOneEdgeFactors (by omega) hdd hee hde₀
  -- Dividing each fibre equation by the weight of its component leaves equations between the
  -- multiplicities and the edge factors.
  have cancelWeight {x : T.Component} {r s : ℤ}
      (h : (T.weight x : ℤ) * r = T.weight x * s) : r = s :=
    mul_left_cancel₀ (by simp) h
  have e₀ : (T.multiplicity b : ℤ) * p₀ = 2 * T.multiplicity a :=
    cancelWeight (x := a) (by rw [hp₀] at ra; linear_combination ra)
  have e₁ : (T.multiplicity a : ℤ) * q₀ + T.multiplicity c * p₁ =
      2 * T.multiplicity b :=
    cancelWeight (x := b) (by rw [hq₀, hp₁] at rb; linear_combination rb)
  have e₂ : (T.multiplicity b : ℤ) * q₁ + T.multiplicity d * p₂ =
      2 * T.multiplicity c :=
    cancelWeight (x := c) (by rw [hq₁, hp₂] at rc; linear_combination rc)
  have e₃ : (T.multiplicity c : ℤ) * q₂ + T.multiplicity e * p₃ =
      2 * T.multiplicity d :=
    cancelWeight (x := d) (by rw [hq₂, hp₃] at rd; linear_combination rd)
  have e₄ : (T.multiplicity d : ℤ) * q₃ = 2 * T.multiplicity e :=
    cancelWeight (x := e) (by rw [hq₃] at re; linear_combination re)
  have hba := T.intersection_comm a b
  have hcb := T.intersection_comm b c
  have hdc := T.intersection_comm c d
  have hed := T.intersection_comm d e
  -- Each of the eight oriented factor patterns is one of the five shapes, read along the path
  -- (the first five) or along its reversal (the last three).
  rcases fivePath_factor_cases (by simp) (by simp) (by simp) (by simp) (by simp)
    hpq₀ hpq₁ hpq₂ hpq₃ e₀ e₁ e₂ e₃ e₄ with
    h | h | h | h | h | h | h | h <;>
      rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
      rw [isGenusOneFivePathShape_iff, isGenusOneFivePathShape_iff]
  · left
    refine ⟨T.weight a, T.multiplicity a, by simp, by simp, ?_⟩
    left
    repeat' apply And.intro <;> omega
  · left
    refine ⟨T.weight d, T.multiplicity a, by simp, by simp, ?_⟩
    right; left
    repeat' apply And.intro <;> omega
  · left
    refine ⟨T.weight a, T.multiplicity e, by simp, by simp, ?_⟩
    right; right; left
    repeat' apply And.intro <;> omega
  · left
    refine ⟨T.weight a, T.multiplicity a, by simp, by simp, ?_⟩
    right; right; right; left
    repeat' apply And.intro <;> omega
  · left
    refine ⟨T.weight b, T.multiplicity a, by simp, by simp, ?_⟩
    right; right; right; right
    repeat' apply And.intro <;> omega
  · right
    refine ⟨T.weight e, T.multiplicity e, by simp, by simp, ?_⟩
    left
    repeat' apply And.intro <;> omega
  · right
    refine ⟨T.weight b, T.multiplicity e, by simp, by simp, ?_⟩
    right; left
    repeat' apply And.intro <;> omega
  · right
    refine ⟨T.weight e, T.multiplicity a, by simp, by simp, ?_⟩
    right; right; left
    repeat' apply And.intro <;> omega

/-- A minimal numerical type of genus one whose five components form the displayed path has one
of the path shapes in cases (17)--(21) of Stacks, Tag 0C8T. -/
theorem isGenusOneFivePathShape_or_isGenusOneFivePathShape_of_isMinimal_and_arithmeticGenus_eq_one
    (hcard : Fintype.card T.Component = 5) (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1)
    {a b c d e : T.Component} (hac₀ : T.intersection a c = 0)
    (had₀ : T.intersection a d = 0) (hae₀ : T.intersection a e = 0)
    (hbd₀ : T.intersection b d = 0) (hbe₀ : T.intersection b e = 0)
    (hce₀ : T.intersection c e = 0) (hab₀ : 0 < T.intersection a b)
    (hbc₀ : 0 < T.intersection b c) (hcd₀ : 0 < T.intersection c d)
    (hde₀ : 0 < T.intersection d e) :
    T.IsGenusOneFivePathShape a b c d e ∨ T.IsGenusOneFivePathShape e d c b a := by
  have h₂ := (T.isMinimal_and_arithmeticGenus_eq_one_iff (by omega)).mp ⟨hT, hg⟩
  exact T.isGenusOneFivePathShape_or_isGenusOneFivePathShape hcard
    (T.isMinusTwoIndex_iff.mp (h₂ a)).2 (T.isMinusTwoIndex_iff.mp (h₂ b)).2
    (T.isMinusTwoIndex_iff.mp (h₂ c)).2 (T.isMinusTwoIndex_iff.mp (h₂ d)).2
    (T.isMinusTwoIndex_iff.mp (h₂ e)).2 hac₀ had₀ hae₀ hbd₀ hbe₀ hce₀
    hab₀ hbc₀ hcd₀ hde₀

end TauCeti.NumericalType
