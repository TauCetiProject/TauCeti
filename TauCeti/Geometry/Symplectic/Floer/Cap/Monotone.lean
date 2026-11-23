/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The energy of capped coefficients is pinned by the index on monotone targets

A pair `(ω, c)` of an area and a first Chern number on spherical classes is *spherically
monotone* with constant `τ` if `ω = τ c` on spherical classes; it is *positively* monotone when
`τ > 0`. On the period group `Γ = PeriodGroup ω c` this reads `area = τ · chern`
(`TauCeti.Floer.PeriodGroup.area_eq_mul_chern`).

Let `a` and `m` be an action and a grading on the caps of an orbit, that is, functions on a torsor
`C` under `Γ` obeying the recapping laws `a (γ +ᵥ D) = area γ + a D` and
`m (γ +ᵥ D) = 2 chern γ + m D`. On a monotone target both change in proportion under recapping, so
`a D - (τ / 2) m D` is the same for every cap `D` of the orbit
(`TauCeti.Floer.sub_eq_div_two_mul_sub_of_area_eq_mul_chern`). In other words the action of a capped
orbit is `τ / 2` times its grading plus a constant depending only on the orbit
(`TauCeti.Floer.eq_div_two_mul_add_sub_of_area_eq_mul_chern`).

For a coefficient of the pair-of-pants product with input caps `D₁`, `D₂`, output cap `D₀` and
class `A` (`TauCeti.Floer.productClass`), the topological energy and the index are

`E(A) = a₁ D₁ + a₂ D₂ - a₀ D₀ + ω(A)` and `I(A) = m₁ D₁ + m₂ D₂ - m₀ D₀ + 2 c₁(A)`.

The energy identity of a Floer pair of pants `u` in class `A` says that its analytic energy is
`E(A)` minus the integrated curvature of the perturbation, and its Fredholm index is `I(A) - n`
on a target of dimension `2n`. On a monotone target the topological energy is determined by the
index and the three uncapped orbits:

`E(A) = (τ / 2) I(A) + (a₁ r₁ - (τ / 2) m₁ r₁) + (a₂ r₂ - (τ / 2) m₂ r₂) - (a₀ r₀ - (τ / 2) m₀ r₀)`

for any reference caps `rᵢ`
(`TauCeti.Floer.add_sub_add_area_eq_div_two_mul_add_of_area_eq_mul_chern`).
With finitely many orbits the difference `E(A) - (τ / 2) I(A)` is therefore bounded uniformly over
all caps and classes (`TauCeti.Floer.exists_forall_abs_sub_div_two_mul_le_of_area_eq_mul_chern`),
and on a positively monotone target the topological energy of every coefficient whose index is
at most a fixed budget `N` is bounded above by one constant
(`TauCeti.Floer.exists_forall_add_sub_add_area_le_of_area_eq_mul_chern`). Since the rigid counts
of the product and the one-dimensional moduli spaces of its chain-level identities live in a
bounded range of indices, this is the energy ceiling of the positively monotone branch: below it,
compactness and gluing are needed only up to one fixed energy. On a target where the first Chern
number vanishes on spheres instead, the index does not see the class at all, and no such ceiling
follows from the index.

These are statements about caps as torsors; the actual actions of cap classes on a closed
symplectic manifold, their gradings and the energy identity are not used.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the monotone case.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 12.1 (Floer homology of monotone symplectic manifolds).
-/

public section

namespace TauCeti.Floer

open PeriodGroup

variable {S : Type*} [AddGroup S] {ω : S →+ ℝ} {c : S →+ ℤ} {τ : ℝ}

section Torsor

variable {C : Type*} [AddTorsor (PeriodGroup ω c) C] {a : C → ℝ} {m : C → ℤ}

/-- **On a monotone target the action changes by `τ / 2` times the grading.** If the area of
every spherical class is `τ` times its first Chern number, an action `a` and a grading `m` obeying
the recapping laws for area and twice the first Chern number satisfy
`a D - a D' = (τ / 2) (m D - m D')` for any two caps `D`, `D'`. -/
theorem sub_eq_div_two_mul_sub_of_area_eq_mul_chern (h : ∀ s, ω s = τ * c s)
    (ha : ∀ (γ : PeriodGroup ω c) (D : C), a (γ +ᵥ D) = area ω c γ + a D)
    (hm : ∀ (γ : PeriodGroup ω c) (D : C), m (γ +ᵥ D) = 2 * chern ω c γ + m D) (D D' : C) :
    a D - a D' = τ / 2 * (m D - m D') := by
  have harea := ha (D -ᵥ D') D'
  have hchern := hm (D -ᵥ D') D'
  rw [vsub_vadd] at harea hchern
  rw [area_eq_mul_chern h] at harea
  have hchern' : (m D : ℝ) = 2 * chern ω c (D -ᵥ D') + m D' := by exact_mod_cast hchern
  linear_combination harea - τ / 2 * hchern'

/-- **On a monotone target the action is determined by the grading.** If the area of every
spherical class is `τ` times its first Chern number, then for an action `a` and a grading `m`
obeying the recapping laws, `a D = (τ / 2) m D + (a r - (τ / 2) m r)` for every cap `D` and any
reference cap `r`. -/
theorem eq_div_two_mul_add_sub_of_area_eq_mul_chern (h : ∀ s, ω s = τ * c s)
    (ha : ∀ (γ : PeriodGroup ω c) (D : C), a (γ +ᵥ D) = area ω c γ + a D)
    (hm : ∀ (γ : PeriodGroup ω c) (D : C), m (γ +ᵥ D) = 2 * chern ω c γ + m D) (D r : C) :
    a D = τ / 2 * m D + (a r - τ / 2 * m r) := by
  linear_combination sub_eq_div_two_mul_sub_of_area_eq_mul_chern h ha hm D r

end Torsor

section Product

variable {C₁ C₂ C₀ : Type*} [AddTorsor (PeriodGroup ω c) C₁] [AddTorsor (PeriodGroup ω c) C₂]
  [AddTorsor (PeriodGroup ω c) C₀] {a₁ : C₁ → ℝ} {a₂ : C₂ → ℝ} {a₀ : C₀ → ℝ}
  {m₁ : C₁ → ℤ} {m₂ : C₂ → ℤ} {m₀ : C₀ → ℤ}

/-- **On a monotone target the topological energy of a product coefficient is pinned by its
index.** If the area of every spherical class is `τ` times its first Chern number, and the
actions `aᵢ` and gradings `mᵢ` of the two inputs and the output obey the recapping laws, then for
caps `Dᵢ` and a class `γ`, such as the product class `productClass glue D₁ D₂ D₀`, the topological
energy `a₁ D₁ + a₂ D₂ - a₀ D₀ + ω(γ)` is `τ / 2` times the index
`m₁ D₁ + m₂ D₂ - m₀ D₀ + 2 c₁(γ)` plus a constant computed from any reference caps `rᵢ`. -/
theorem add_sub_add_area_eq_div_two_mul_add_of_area_eq_mul_chern (h : ∀ s, ω s = τ * c s)
    (ha₁ : ∀ (γ : PeriodGroup ω c) (D : C₁), a₁ (γ +ᵥ D) = area ω c γ + a₁ D)
    (hm₁ : ∀ (γ : PeriodGroup ω c) (D : C₁), m₁ (γ +ᵥ D) = 2 * chern ω c γ + m₁ D)
    (ha₂ : ∀ (γ : PeriodGroup ω c) (D : C₂), a₂ (γ +ᵥ D) = area ω c γ + a₂ D)
    (hm₂ : ∀ (γ : PeriodGroup ω c) (D : C₂), m₂ (γ +ᵥ D) = 2 * chern ω c γ + m₂ D)
    (ha₀ : ∀ (γ : PeriodGroup ω c) (D : C₀), a₀ (γ +ᵥ D) = area ω c γ + a₀ D)
    (hm₀ : ∀ (γ : PeriodGroup ω c) (D : C₀), m₀ (γ +ᵥ D) = 2 * chern ω c γ + m₀ D)
    (D₁ r₁ : C₁) (D₂ r₂ : C₂) (D₀ r₀ : C₀) (γ : PeriodGroup ω c) :
    a₁ D₁ + a₂ D₂ - a₀ D₀ + area ω c γ =
      τ / 2 * ((m₁ D₁ + m₂ D₂ - m₀ D₀ + 2 * chern ω c γ : ℤ) : ℝ) +
        ((a₁ r₁ - τ / 2 * m₁ r₁) + (a₂ r₂ - τ / 2 * m₂ r₂) - (a₀ r₀ - τ / 2 * m₀ r₀)) := by
  push_cast
  linear_combination eq_div_two_mul_add_sub_of_area_eq_mul_chern h ha₁ hm₁ D₁ r₁ +
    eq_div_two_mul_add_sub_of_area_eq_mul_chern h ha₂ hm₂ D₂ r₂ -
    eq_div_two_mul_add_sub_of_area_eq_mul_chern h ha₀ hm₀ D₀ r₀ + area_eq_mul_chern h γ

end Product

section Finite

variable {ι₁ ι₂ ι₀ : Type*} [Finite ι₁] [Finite ι₂] [Finite ι₀]
  {C₁ : ι₁ → Type*} {C₂ : ι₂ → Type*} {C₀ : ι₀ → Type*}
  [∀ i, AddTorsor (PeriodGroup ω c) (C₁ i)] [∀ j, AddTorsor (PeriodGroup ω c) (C₂ j)]
  [∀ k, AddTorsor (PeriodGroup ω c) (C₀ k)]
  {a₁ : ∀ i, C₁ i → ℝ} {a₂ : ∀ j, C₂ j → ℝ} {a₀ : ∀ k, C₀ k → ℝ}
  {m₁ : ∀ i, C₁ i → ℤ} {m₂ : ∀ j, C₂ j → ℤ} {m₀ : ∀ k, C₀ k → ℤ}

/-- **With finitely many orbits the energy is the index up to a uniform constant.** On a monotone
target with constant `τ`, let the caps of finitely many input orbits `i`, `j` and output orbits
`k` carry actions and gradings obeying the recapping laws. Then the topological energy
`a₁ D₁ + a₂ D₂ - a₀ D₀ + ω(γ)` of a capped triple and a class `γ` differs from `τ / 2` times its
index `m₁ D₁ + m₂ D₂ - m₀ D₀ + 2 c₁(γ)` by at most one constant `C`, for all orbits, caps and
classes. -/
theorem exists_forall_abs_sub_div_two_mul_le_of_area_eq_mul_chern (h : ∀ s, ω s = τ * c s)
    (ha₁ : ∀ i (γ : PeriodGroup ω c) (D : C₁ i), a₁ i (γ +ᵥ D) = area ω c γ + a₁ i D)
    (hm₁ : ∀ i (γ : PeriodGroup ω c) (D : C₁ i), m₁ i (γ +ᵥ D) = 2 * chern ω c γ + m₁ i D)
    (ha₂ : ∀ j (γ : PeriodGroup ω c) (D : C₂ j), a₂ j (γ +ᵥ D) = area ω c γ + a₂ j D)
    (hm₂ : ∀ j (γ : PeriodGroup ω c) (D : C₂ j), m₂ j (γ +ᵥ D) = 2 * chern ω c γ + m₂ j D)
    (ha₀ : ∀ k (γ : PeriodGroup ω c) (D : C₀ k), a₀ k (γ +ᵥ D) = area ω c γ + a₀ k D)
    (hm₀ : ∀ k (γ : PeriodGroup ω c) (D : C₀ k), m₀ k (γ +ᵥ D) = 2 * chern ω c γ + m₀ k D) :
    ∃ C : ℝ, ∀ i j k (D₁ : C₁ i) (D₂ : C₂ j) (D₀ : C₀ k) (γ : PeriodGroup ω c),
      |a₁ i D₁ + a₂ j D₂ - a₀ k D₀ + area ω c γ -
        τ / 2 * ((m₁ i D₁ + m₂ j D₂ - m₀ k D₀ + 2 * chern ω c γ : ℤ) : ℝ)| ≤ C := by
  -- Measure every orbit against one reference cap; the difference is a function of the orbits.
  let r₁ i : C₁ i := Classical.arbitrary _
  let r₂ j : C₂ j := Classical.arbitrary _
  let r₀ k : C₀ k := Classical.arbitrary _
  let g : ι₁ × ι₂ × ι₀ → ℝ := fun p ↦
    |(a₁ p.1 (r₁ p.1) - τ / 2 * m₁ p.1 (r₁ p.1)) +
      (a₂ p.2.1 (r₂ p.2.1) - τ / 2 * m₂ p.2.1 (r₂ p.2.1)) -
      (a₀ p.2.2 (r₀ p.2.2) - τ / 2 * m₀ p.2.2 (r₀ p.2.2))|
  obtain ⟨C, hC⟩ := (Set.finite_range g).bddAbove
  refine ⟨C, fun i j k D₁ D₂ D₀ γ ↦ ?_⟩
  rw [add_sub_add_area_eq_div_two_mul_add_of_area_eq_mul_chern h (ha₁ i) (hm₁ i) (ha₂ j) (hm₂ j)
    (ha₀ k) (hm₀ k) D₁ (r₁ i) D₂ (r₂ j) D₀ (r₀ k) γ, add_sub_cancel_left]
  exact hC ⟨(i, j, k), rfl⟩

/-- **The energy ceiling of a positively monotone target.** On a target with `ω = τ c` on
spherical classes and `τ ≥ 0`, let the caps of finitely many input orbits `i`, `j` and output
orbits `k` carry actions and gradings obeying the recapping laws. For every index budget `N` there
is one constant `C` bounding the topological energy `a₁ D₁ + a₂ D₂ - a₀ D₀ + ω(γ)` of every
capped triple and class `γ` whose index `m₁ D₁ + m₂ D₂ - m₀ D₀ + 2 c₁(γ)` is at most `N`. -/
theorem exists_forall_add_sub_add_area_le_of_area_eq_mul_chern (h : ∀ s, ω s = τ * c s)
    (hτ : 0 ≤ τ)
    (ha₁ : ∀ i (γ : PeriodGroup ω c) (D : C₁ i), a₁ i (γ +ᵥ D) = area ω c γ + a₁ i D)
    (hm₁ : ∀ i (γ : PeriodGroup ω c) (D : C₁ i), m₁ i (γ +ᵥ D) = 2 * chern ω c γ + m₁ i D)
    (ha₂ : ∀ j (γ : PeriodGroup ω c) (D : C₂ j), a₂ j (γ +ᵥ D) = area ω c γ + a₂ j D)
    (hm₂ : ∀ j (γ : PeriodGroup ω c) (D : C₂ j), m₂ j (γ +ᵥ D) = 2 * chern ω c γ + m₂ j D)
    (ha₀ : ∀ k (γ : PeriodGroup ω c) (D : C₀ k), a₀ k (γ +ᵥ D) = area ω c γ + a₀ k D)
    (hm₀ : ∀ k (γ : PeriodGroup ω c) (D : C₀ k), m₀ k (γ +ᵥ D) = 2 * chern ω c γ + m₀ k D)
    (N : ℤ) :
    ∃ C : ℝ, ∀ i j k (D₁ : C₁ i) (D₂ : C₂ j) (D₀ : C₀ k) (γ : PeriodGroup ω c),
      m₁ i D₁ + m₂ j D₂ - m₀ k D₀ + 2 * chern ω c γ ≤ N →
        a₁ i D₁ + a₂ j D₂ - a₀ k D₀ + area ω c γ ≤ C := by
  obtain ⟨C, hC⟩ := exists_forall_abs_sub_div_two_mul_le_of_area_eq_mul_chern h ha₁ hm₁ ha₂ hm₂
    ha₀ hm₀
  refine ⟨τ / 2 * N + C, fun i j k D₁ D₂ D₀ γ hN ↦ ?_⟩
  have hle := (le_abs_self _).trans (hC i j k D₁ D₂ D₀ γ)
  have hN' : ((m₁ i D₁ + m₂ j D₂ - m₀ k D₀ + 2 * chern ω c γ : ℤ) : ℝ) ≤ N := by exact_mod_cast hN
  linarith [mul_le_mul_of_nonneg_left hN' (div_nonneg hτ zero_le_two)]

end Finite

end TauCeti.Floer
