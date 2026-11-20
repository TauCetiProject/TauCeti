/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Genus
public import TauCeti.Analysis.Complex.RiemannSurface.Branch.EulerCharacteristic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The genus of a Riemann surface

The topological genus `TauCeti.RiemannSurface.genus X = ((2 - χ(X)) / 2).toNat` is defined in
the finite-CW Euler-characteristic library. This file connects it to the complex-analytic theory.

Given `χ = 2 - 2 · genus` on both sides, the branched-cover formula
`χ(X) = deg f · χ(Y) - R(f)` becomes the Riemann–Hurwitz formula in genus form
`2 genus X - 2 = deg f · (2 genus Y - 2) + R(f)`
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.two_mul_genus_sub_two_eq_of_eulerChar_eq`).

Since `deg f ≥ 1` and `R(f) ≥ 0`, this compares the genera of the two surfaces. A nonconstant
closed pseudoholomorphic curve `u` factors as `u = v ∘ f` through a simple curve `v` and a finite
holomorphic map `f` of some degree `d`; these comparisons bound the genus of `u` from below by
that of `v`, bound the covering degree `d` by the genera, and relate the virtual dimensions of
`u` and `v`:

* `deg f · (genus Y - 1) ≤ genus X - 1`, with equality exactly when `f` is unramified;
* `genus Y ≤ genus X`, with equality exactly when `deg f = 1`, or `genus Y = 1` and `f` is
  unramified, or `genus Y = 0` and `R(f) = 2 deg f - 2`;
* the unmarked virtual dimension `D = (m - 3)(2 - 2 g) + 2 c` of a curve of genus `g` and Chern
  number `c` in a target of complex dimension `m` satisfies `D(v ∘ f) = deg f · D(v) - (m - 3) R(f)`
  when the Chern number of `v ∘ f` is `deg f` times that of `v`.

## Main results

* `TauCeti.RiemannSurface.FiniteHolomorphicMap.two_mul_genus_sub_two_eq_of_eulerChar_eq`:
  Riemann–Hurwitz in genus form, for surfaces satisfying `χ = 2 - 2 · genus`.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.degree_mul_genus_sub_one_le`,
  `TauCeti.RiemannSurface.FiniteHolomorphicMap.degree_mul_genus_sub_one_eq_iff`: the bound
  `deg f · (genus Y - 1) ≤ genus X - 1` and its equality case.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.genus_le_genus`,
  `TauCeti.RiemannSurface.FiniteHolomorphicMap.genus_eq_genus_iff`: `genus Y ≤ genus X` and its
  equality case.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.index_eq_degree_mul_index_sub`: the virtual
  dimension of a multiple cover.

## Checks

* `TauCeti.RiemannSurface.genus_onePoint_complex`: the Riemann sphere has genus `0`.

The level-one modular curve has genus `0`: see
`TauCeti.ModularGroup.genus_compactifiedQuotient`.

## References

* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4.
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §17.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.5 (simple curves and multiple covers).
-/

public section

noncomputable section

open scoped Manifold

universe u

namespace TauCeti

namespace RiemannSurface

namespace FiniteHolomorphicMap

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
  [CompactSpace X] [T2Space X] [T2Space Y] [PreconnectedSpace Y]
  [FiniteCWType X] [FiniteCWType Y]
  (f : FiniteHolomorphicMap X Y) [FiniteCWType ↥f.branchValuesᶜ]

/-- **Riemann–Hurwitz in genus form**, for surfaces whose Euler numbers are `2 - 2 · genus`: if
`X`, `Y` and the complement of the branch values have finite CW type, and
`χ(X) = 2 - 2 · genus X` and `χ(Y) = 2 - 2 · genus Y`, then
`2 genus X - 2 = deg f · (2 genus Y - 2) + R(f)`, where `R(f)` is the ramification degree. The
two Euler-number hypotheses hold for every compact connected Riemann surface; they are explicit
here because they need Poincaré duality. -/
theorem two_mul_genus_sub_two_eq_of_eulerChar_eq (hX : eulerChar X = 2 - 2 * genus X)
    (hY : eulerChar Y = 2 - 2 * genus Y) :
    2 * (genus X : ℤ) - 2 = degree f * (2 * (genus Y : ℤ) - 2) + ramificationDegree f := by
  linear_combination -f.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree + hX -
    (degree f : ℤ) * hY

/-- **The multiplicity bound** of Riemann–Hurwitz: `deg f · (genus Y - 1) ≤ genus X - 1`, for
surfaces satisfying `χ = 2 - 2 · genus`. When `genus Y ≥ 2` this bounds the degree of a finite
holomorphic map out of `X` by `(genus X - 1) / (genus Y - 1)`. -/
theorem degree_mul_genus_sub_one_le (hX : eulerChar X = 2 - 2 * genus X)
    (hY : eulerChar Y = 2 - 2 * genus Y) :
    (degree f : ℤ) * (genus Y - 1) ≤ genus X - 1 := by
  linarith [f.two_mul_genus_sub_two_eq_of_eulerChar_eq hX hY]

/-- The multiplicity bound `deg f · (genus Y - 1) ≤ genus X - 1` is an equality exactly when `f`
is unramified. -/
theorem degree_mul_genus_sub_one_eq_iff (hX : eulerChar X = 2 - 2 * genus X)
    (hY : eulerChar Y = 2 - 2 * genus Y) :
    (degree f : ℤ) * (genus Y - 1) = genus X - 1 ↔ ramificationDegree f = 0 := by
  have := f.two_mul_genus_sub_two_eq_of_eulerChar_eq hX hY
  constructor <;> intro h <;> linarith

include f in
/-- **The genus does not increase under finite holomorphic maps**: if `f : X → Y` is a finite
holomorphic map of compact Riemann surfaces satisfying `χ = 2 - 2 · genus`, then
`genus Y ≤ genus X`. -/
theorem genus_le_genus (hX : eulerChar X = 2 - 2 * genus X)
    (hY : eulerChar Y = 2 - 2 * genus Y) : genus Y ≤ genus X := by
  have h := f.degree_mul_genus_sub_one_le hX hY
  have hd : (1 : ℤ) ≤ degree f := by exact_mod_cast degree_pos f
  rcases Nat.eq_zero_or_pos (genus Y) with h0 | h0
  · omega
  · have : (1 : ℤ) * (genus Y - 1) ≤ degree f * (genus Y - 1) :=
      mul_le_mul_of_nonneg_right hd (by omega)
    omega

/-- **The equality case of `genus Y ≤ genus X`.** A finite holomorphic map `f : X → Y` of compact
Riemann surfaces satisfying `χ = 2 - 2 · genus` preserves the genus exactly when it has degree
one, or `Y` has genus one and `f` is unramified, or `Y` has genus zero and the ramification
degree is `2 deg f - 2`. -/
theorem genus_eq_genus_iff (hX : eulerChar X = 2 - 2 * genus X)
    (hY : eulerChar Y = 2 - 2 * genus Y) :
    genus X = genus Y ↔ degree f = 1 ∨ genus Y = 1 ∧ ramificationDegree f = 0 ∨
      genus Y = 0 ∧ ramificationDegree f + 2 = 2 * degree f := by
  have h := f.two_mul_genus_sub_two_eq_of_eulerChar_eq hX hY
  have hd : (1 : ℤ) ≤ degree f := by exact_mod_cast degree_pos f
  constructor
  · intro hg
    rw [hg] at h
    rcases lt_trichotomy (genus Y) 1 with h0 | h1 | h2
    · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
      rw [show genus Y = 0 by omega] at h
      push_cast at h
      omega
    · refine Or.inr (Or.inl ⟨h1, ?_⟩)
      rw [h1] at h
      push_cast at h
      omega
    · refine Or.inl ?_
      -- `(deg f - 1) (2 genus Y - 2) + R = 0` with both summands nonnegative.
      have hpos : (0 : ℤ) < 2 * genus Y - 2 := by omega
      have : ((degree f : ℤ) - 1) * (2 * genus Y - 2) ≤ 0 := by linarith
      have : (degree f : ℤ) - 1 ≤ 0 := nonpos_of_mul_nonpos_left this hpos
      omega
  · rintro (h1 | ⟨h1, hR⟩ | ⟨h0, hR⟩)
    · rw [h1, ramificationDegree_eq_zero_of_degree_eq_one f h1] at h
      push_cast at h
      omega
    · rw [h1, hR] at h
      push_cast at h
      omega
    · rw [h0] at h ⊢
      have : (ramificationDegree f : ℤ) + 2 = 2 * degree f := by exact_mod_cast hR
      push_cast at h
      omega

/-- **The index of a multiple cover.** Let `f : X → Y` be a finite holomorphic map of compact
Riemann surfaces satisfying `χ = 2 - 2 · genus`, and write `D(g, c) = (m - 3) (2 - 2 g) + 2 c`
for the unmarked virtual dimension of a closed curve of genus `g` and first Chern number `c` in a
target of complex dimension `m`. Then
`D(genus X, deg f · c) = deg f · D(genus Y, c) - (m - 3) R(f)` for every integer `c`. For a
curve `v` on `Y` with Chern number `c` whose composite `v ∘ f` has Chern number `deg f · c`, this
is `D(v ∘ f) = deg f · D(v) - (m - 3) R(f)`. -/
theorem index_eq_degree_mul_index_sub (m c : ℤ) (hX : eulerChar X = 2 - 2 * genus X)
    (hY : eulerChar Y = 2 - 2 * genus Y) :
    (m - 3) * (2 - 2 * genus X) + 2 * (degree f * c) =
      degree f * ((m - 3) * (2 - 2 * genus Y) + 2 * c) - (m - 3) * ramificationDegree f := by
  linear_combination (3 - m) * f.two_mul_genus_sub_two_eq_of_eulerChar_eq hX hY

end FiniteHolomorphicMap

/-- **The Riemann sphere has genus `0`**: its Euler characteristic is `2`. -/
@[simp]
theorem genus_onePoint_complex : genus (OnePoint ℂ) = 0 :=
  genus_eq_of_eulerChar_eq (by rw [eulerChar_onePoint, Complex.finrank_real_complex]; norm_num)

end RiemannSurface

end TauCeti
