/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Basic
public import TauCeti.Algebra.Group.Hom.Int

/-!
# Homogeneous directed wall spaces

Wall spaces are homogeneous submodules indexed by a degree and an integral normal.
Their bracket has the normal obtained by contracting each input normal with the
other input's geometric direction. Nontangent spaces and spaces with zero normal
vanish. These conditions force commutation for proportional normals, for normals that
annihilate each other's geometric direction, and vanishing of brackets whose total direction
is annihilated by both normals.

The degree and tangent monoids are independent. No lattice basis, coefficient
characteristic or positivity assumption is needed for these algebraic identities.

The wall-space laws follow Definition 1.2 of Leung, Ma and Young,
*Refined scattering diagrams and theta functions from asymptotic analysis of
Maurer-Cartan equations*
([2019 preprint](https://archive.mpim-bonn.mpg.de/id/eprint/1320/1/preprint_2019_5.pdf#page=9)).
Here the complex vector spaces are generalized to submodules over any commutative
ring, with independent degree and tangent monoids related by `ρ`. We extend the
spaces by zero at nontangent indices. The definition retains the zero-normal,
rescaling and contracted-bracket laws, but omits the paper's condition (3) on an
action on a graded algebra: no such action is needed for these Lie identities.

## Attribution

Adapted from `Mei/Geometry/ScatteringDiagram/WallSpace/Basic.lean`
in Mei at commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`. Original copyright and author credit are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/7f1e4c7714fb020473694755ad8748c8f15d0e7f/Mei/Geometry/ScatteringDiagram/WallSpace/Basic.lean
-/

public section

namespace TauCeti

variable {Γ Λ R L : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The integral normal attached to a bracket of homogeneous wall elements. -/
def wallBracketNormal (ρ : Γ →+ Λ) (n n' : Γ) (m m' : Λ →+ ℤ) : Λ →+ ℤ :=
  m (ρ n') • m' - m' (ρ n) • m

/-- Evaluate the bracket normal on a tangent vector. -/
@[simp]
theorem wallBracketNormal_apply (ρ : Γ →+ Λ) (n n' : Γ) (m m' : Λ →+ ℤ) (v : Λ) :
    wallBracketNormal ρ n n' m m' v = m (ρ n') * m' v - m' (ρ n) * m v := (rfl)

/-- On integer multiples of two directions, the cross contractions scale by the
opposite multipliers. -/
@[simp]
theorem wallBracketNormal_zsmul {Γ Λ : Type*} [AddCommGroup Γ] [AddCommMonoid Λ]
    (ρ : Γ →+ Λ) (n n' : Γ) (m m' : Λ →+ ℤ) (a b : ℤ) :
    wallBracketNormal ρ (a • n) (b • n') m m' =
      (b * m (ρ n')) • m' - (a * m' (ρ n)) • m := by
  have hm : m (ρ (b • n')) = b * m (ρ n') := by
    simpa only [AddMonoidHom.comp_apply, zsmul_eq_mul, Int.cast_id] using (m.comp ρ).map_zsmul b n'
  have hm' : m' (ρ (a • n)) = a * m' (ρ n) := by
    simpa only [AddMonoidHom.comp_apply, zsmul_eq_mul, Int.cast_id] using (m'.comp ρ).map_zsmul a n
  simp only [wallBracketNormal, hm, hm']

/-- Homogeneous submodules with the normal and bracket laws of directed walls.
For a positive grading, containment in the homogeneous pieces automatically makes
all spaces outside the nonzero positive degrees vanish. -/
structure DirectedWallSpaces (ρ : Γ →+ Λ) (ℒ : Γ → Submodule R L) where
  /-- The submodule of wall elements of a given degree and normal. -/
  wall : Γ → (Λ →+ ℤ) → Submodule R L
  /-- Wall elements are homogeneous. -/
  wall_le_piece : ∀ n m, wall n m ≤ ℒ n
  /-- A zero normal carries no wall elements. -/
  zero_normal : ∀ n, wall n 0 = ⊥
  /-- A normal not annihilating the geometric degree carries no wall elements. -/
  nontangent : ∀ n m, m (ρ n) ≠ 0 → wall n m = ⊥
  /-- Nonzero integral rescaling leaves the wall submodule unchanged. -/
  rescale : ∀ n m (c : ℤ), c ≠ 0 → wall n (c • m) = wall n m
  /-- The bracket belongs to the space with summed degree and contracted normal. -/
  bracket_mem : ∀ {n n' m m' x y}, x ∈ wall n m → y ∈ wall n' m' →
    ⁅x, y⁆ ∈ wall (n + n') (wallBracketNormal ρ n n' m m')

attribute [simp] DirectedWallSpaces.zero_normal DirectedWallSpaces.nontangent

-- Remove integral scalars before negative scalar multiplication normalizes to negation.
attribute [simp↓] DirectedWallSpaces.rescale

namespace DirectedWallSpaces

variable {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)

/-- Integral normals with the same kernel define the same wall spaces.
In particular a change of coorientation preserves eligible coefficients. -/
theorem wall_eq_of_ker_eq {Λ : Type*} [AddCommGroup Λ]
    {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)
    (n : Γ) {m m' : Λ →+ ℤ} (hker : m.ker = m'.ker) :
    H.wall n m = H.wall n m' := by
  by_cases hm : m = 0
  · subst m
    have hm' : m' = 0 := by
      apply AddMonoidHom.ker_eq_top_iff.mp
      rw [← hker]
      simp
    rw [hm']
  · obtain ⟨c, e, hc, he, hme⟩ := m.exists_ne_zero_zsmul_eq_of_ker_eq m' hm hker
    rw [← H.rescale n m c hc, hme, H.rescale n m' e he]

/-- Directed wall spaces are determined by their wall submodules. -/
@[ext]
theorem ext {H K : DirectedWallSpaces ρ ℒ}
    (h : ∀ n m, H.wall n m = K.wall n m) : H = K := by
  have hw : H.wall = K.wall := funext fun n => funext fun m => h n m
  cases H
  cases K
  congr

/-- The normal of a nonzero wall element annihilates its geometric degree. -/
theorem normal_apply_eq_zero {n : Γ} {m : Λ →+ ℤ} {x : L}
    (hx : x ∈ H.wall n m) (hx0 : x ≠ 0) : m (ρ n) = 0 := by
  by_contra h
  rw [H.nontangent n m h, Submodule.mem_bot] at hx
  exact hx0 hx

/-- Wall elements commute if each normal annihilates the geometric degree of the other element,
`m(ρ(n')) = 0` and `m'(ρ(n)) = 0`: their bracket normal vanishes. The normals need not be
proportional. -/
theorem lie_eq_zero_of_apply_eq_zero {n n' : Γ} {m m' : Λ →+ ℤ} {x y : L}
    (hx : x ∈ H.wall n m) (hy : y ∈ H.wall n' m')
    (hm : m (ρ n') = 0) (hm' : m' (ρ n) = 0) : ⁅x, y⁆ = 0 := by
  have hnormal : wallBracketNormal ρ n n' m m' = 0 := by
    ext v
    simp [hm, hm']
  have h := H.bracket_mem hx hy
  rwa [hnormal, H.zero_normal, Submodule.mem_bot] at h

/-- A bracket vanishes if both input normals annihilate its total geometric degree. -/
theorem lie_eq_zero_of_normal_total_eq_zero {n n' : Γ} {m m' : Λ →+ ℤ} {x y : L}
    (hx : x ∈ H.wall n m) (hy : y ∈ H.wall n' m')
    (hm : m (ρ (n + n')) = 0) (hm' : m' (ρ (n + n')) = 0) : ⁅x, y⁆ = 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have hn := H.normal_apply_eq_zero hx hx0
  have hn' := H.normal_apply_eq_zero hy hy0
  exact H.lie_eq_zero_of_apply_eq_zero hx hy (by simpa [hn] using hm) (by simpa [hn'] using hm')

/-- Wall elements with the same normal commute, including nontangent degrees. -/
theorem lie_eq_zero_of_same_normal {n n' : Γ} {m : Λ →+ ℤ} {x y : L}
    (hx : x ∈ H.wall n m) (hy : y ∈ H.wall n' m) : ⁅x, y⁆ = 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have htotal : m (ρ (n + n')) = 0 := by
    simp [H.normal_apply_eq_zero hx hx0, H.normal_apply_eq_zero hy hy0]
  exact H.lie_eq_zero_of_normal_total_eq_zero hx hy htotal htotal

/-- Rationally proportional integral normals give commuting wall elements.
Proportionality is expressed by a common nonzero integral rescaling. -/
theorem lie_eq_zero_of_proportional {n n' : Γ} {m m' : Λ →+ ℤ} {x y : L}
    (hx : x ∈ H.wall n m) (hy : y ∈ H.wall n' m')
    {c d : ℤ} (hc : c ≠ 0) (hd : d ≠ 0) (h : c • m = d • m') : ⁅x, y⁆ = 0 := by
  apply H.lie_eq_zero_of_same_normal (n := n) (n' := n') (m := c • m)
  · simpa only [H.rescale n m c hc] using hx
  · simpa only [h, H.rescale n' m' d hd] using hy

end DirectedWallSpaces

end TauCeti
