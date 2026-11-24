/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.Algebra.PositiveDegrees.Scale
public import Mathlib.Tactic.Linarith

/-!
# Examples of cutoff moduli for positive degree data

Three computations show how the cutoff modulus of a `PositiveDegreeMap` behaves.

* On the wedge `{0} ∪ {(a, b) | 1 ≤ b ≤ a}` with degree `δ(a, b) = a`, the projection to the
  second coordinate preserves the allowed monoid and nonzero degrees and is bounded above by
  the source degree, but it admits no cutoff modulus: every `(j, 1)` is sent to degree one.
  An upper bound `δ'(T n) ≤ δ n` therefore does not give a positive degree map.
* On the nonnegative integers, the change of degree from `δ(a) = a` to `2 δ` has modulus
  `⌊k / 2⌋`, and the reverse change has modulus `2 k`.
* On the quadratic wedge `{(a, b) | 0 ≤ b ≤ a ≤ b²}`, the change of degree from `δ(a, b) = a`
  to `δ'(a, b) = b` has modulus `k²` and the reverse change has modulus `k`, so the two cutoff
  moduli of a change of degree can have different growth.

Adapted from `Mei/Algebra/PositiveDegrees/Examples.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`, released under Apache 2.0.
-/

public section

namespace TauCeti.PositiveDegrees.Examples

open PositiveDegrees

/-- The origin together with the integer points `1 ≤ b ≤ a`. -/
def wedgeMonoid : AddSubmonoid (ℤ × ℤ) where
  carrier := {n | n = 0 ∨ 1 ≤ n.2 ∧ n.2 ≤ n.1}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro x y (rfl | hx) (rfl | hy)
    · exact Or.inl (by simp)
    · simpa using Or.inr hy
    · simpa using Or.inr hx
    · exact Or.inr ⟨by dsimp; omega, by dsimp; omega⟩

/-- Membership in the wedge includes the origin as a separate case. -/
@[simp]
theorem mem_wedgeMonoid {n : ℤ × ℤ} :
    n ∈ wedgeMonoid ↔ n = 0 ∨ 1 ≤ n.2 ∧ n.2 ≤ n.1 := Iff.rfl

/-- The wedge with first-coordinate degree; each cutoff lies in a finite square. -/
def wedgeDegrees : PositiveDegrees (ℤ × ℤ) where
  monoid := wedgeMonoid
  degree := AddMonoidHom.fst ℤ ℤ
  degree_pos hn hne := by
    obtain h | h := mem_wedgeMonoid.mp hn
    · exact (hne h).elim
    · dsimp
      omega
  finite_le k := by
    apply ((Set.finite_Icc (a := (0 : ℤ)) (b := k)).prod
      (Set.finite_Icc (a := (0 : ℤ)) (b := k))).subset
    rintro ⟨a, b⟩ ⟨hn, hk⟩
    obtain h | h := mem_wedgeMonoid.mp hn
    · rw [h]
      exact ⟨⟨le_rfl, Int.natCast_nonneg k⟩, ⟨le_rfl, Int.natCast_nonneg k⟩⟩
    · exact ⟨⟨by omega, hk⟩, ⟨by omega, by dsimp at hk; omega⟩⟩

/-- The allowed wedge degrees. -/
@[simp]
theorem wedgeDegrees_monoid : wedgeDegrees.monoid = wedgeMonoid := (rfl)

/-- Wedge degree is the first coordinate. -/
@[simp]
theorem wedgeDegrees_degree (n : ℤ × ℤ) : wedgeDegrees.degree n = n.1 := (rfl)

/-- The projection to the second coordinate takes allowed wedge degrees to nonnegative
integers. -/
theorem snd_mem_nonnegIntegers_monoid {n : ℤ × ℤ} (hn : n ∈ wedgeDegrees.monoid) :
    AddMonoidHom.snd ℤ ℤ n ∈ nonnegIntegers.monoid := by
  obtain rfl | h := mem_wedgeMonoid.mp hn
  · simp
  · simpa using (zero_le_one.trans h.1)

/-- The projection to the second coordinate is nonzero on nonzero allowed wedge degrees. -/
theorem snd_ne_zero_of_mem_wedgeDegrees {n : ℤ × ℤ} (hn : n ∈ wedgeDegrees.monoid)
    (hne : n ≠ 0) : AddMonoidHom.snd ℤ ℤ n ≠ 0 := by
  obtain h | h := mem_wedgeMonoid.mp hn
  · exact (hne h).elim
  · simp only [AddMonoidHom.coe_snd]
    omega

/-- On allowed wedge degrees, the second coordinate is bounded above by the source degree. -/
theorem snd_le_degree_of_mem_wedgeDegrees {n : ℤ × ℤ} (hn : n ∈ wedgeDegrees.monoid) :
    nonnegIntegers.degree (AddMonoidHom.snd ℤ ℤ n) ≤ wedgeDegrees.degree n := by
  obtain rfl | h := mem_wedgeMonoid.mp hn
  · simp
  · simpa using h.2

/-- No cutoff function, even a nonmonotone one, bounds the source degrees of the allowed
wedge points whose projection to the second coordinate has degree at most one. -/
theorem exists_lt_degree_snd_le_one (μ : ℕ → ℕ) :
    ∃ n ∈ wedgeDegrees.monoid, (μ 1 : ℤ) < wedgeDegrees.degree n ∧
      nonnegIntegers.degree (AddMonoidHom.snd ℤ ℤ n) ≤ 1 := by
  refine ⟨((μ 1 : ℤ) + 1, 1), ?_, ?_, ?_⟩
  · simp only [wedgeDegrees_monoid, mem_wedgeMonoid]
    exact Or.inr ⟨by omega, by omega⟩
  · simp
  · simp

/-- The projection to the second coordinate, although it preserves allowed and nonzero
degrees and is bounded above by the source degree, is not the underlying map of any
`PositiveDegreeMap` from the wedge to `ℤ≥0`. -/
theorem not_exists_positiveDegreeMap_wedge_snd :
    ¬ ∃ T : PositiveDegreeMap wedgeDegrees nonnegIntegers, ∀ n, T n = n.2 := by
  rintro ⟨T, hT⟩
  obtain ⟨n, hn, hgt, hle⟩ := exists_lt_degree_snd_le_one T.modulus
  have h := T.degree_gt 1 hn hgt
  rw [hT] at h
  simp only [AddMonoidHom.coe_snd, nonnegIntegers_degree] at h hle
  omega

/-- On the nonnegative integers, the change of degree from `δ(a) = a` to `2 δ` has modulus
`⌊k / 2⌋`. -/
theorem changeDegree_nonnegIntegers_scale_two_modulus (k : ℕ) :
    (PositiveDegreeMap.changeDegree nonnegIntegers (nonnegIntegers.scale 2)
      (nonnegIntegers.scale_monoid 2).symm).modulus k = k / 2 :=
  PositiveDegreeMap.changeDegree_self_scale_modulus 2 (n := 1) (by simp) (by simp) k

/-- On the nonnegative integers, the change of degree from `2 δ` back to `δ(a) = a` has
modulus `2 k`. -/
theorem changeDegree_scale_two_nonnegIntegers_modulus (k : ℕ) :
    (PositiveDegreeMap.changeDegree (nonnegIntegers.scale 2) nonnegIntegers
      (nonnegIntegers.scale_monoid 2)).modulus k = 2 * k :=
  PositiveDegreeMap.changeDegree_scale_self_modulus 2 (n := 1) (by simp) (by simp) k

/-- The quadratic wedge of integer points `0 ≤ b ≤ a ≤ b²`. -/
def quadraticWedgeMonoid : AddSubmonoid (ℤ × ℤ) where
  carrier := {n | 0 ≤ n.2 ∧ n.2 ≤ n.1 ∧ n.1 ≤ n.2 ^ 2}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx0, hx1, hx2⟩ ⟨hy0, hy1, hy2⟩
    refine ⟨by dsimp; omega, by dsimp; omega, ?_⟩
    dsimp
    nlinarith [mul_nonneg hx0 hy0]

/-- Membership in the quadratic wedge. -/
@[simp]
theorem mem_quadraticWedgeMonoid {n : ℤ × ℤ} :
    n ∈ quadraticWedgeMonoid ↔ 0 ≤ n.2 ∧ n.2 ≤ n.1 ∧ n.1 ≤ n.2 ^ 2 := Iff.rfl

/-- A nonzero point of the quadratic wedge has second coordinate at least one. -/
theorem one_le_snd_of_mem_quadraticWedgeMonoid {n : ℤ × ℤ} (hn : n ∈ quadraticWedgeMonoid)
    (hne : n ≠ 0) : 1 ≤ n.2 := by
  obtain ⟨h0, h1, h2⟩ := hn
  by_contra h
  have hb : n.2 = 0 := by omega
  rw [hb] at h2
  exact hne (Prod.ext (by simp only [Prod.fst_zero]; nlinarith) hb)

/-- First-coordinate degree `δ(a, b) = a` on the quadratic wedge. -/
def quadraticWedgeFst : PositiveDegrees (ℤ × ℤ) where
  monoid := quadraticWedgeMonoid
  degree := AddMonoidHom.fst ℤ ℤ
  degree_pos hn hne := by
    have := one_le_snd_of_mem_quadraticWedgeMonoid hn hne
    have := (mem_quadraticWedgeMonoid.mp hn).2.1
    dsimp
    omega
  finite_le k := by
    apply ((Set.finite_Icc (a := (0 : ℤ)) (b := k)).prod
      (Set.finite_Icc (a := (0 : ℤ)) (b := k))).subset
    rintro ⟨a, b⟩ ⟨⟨h0, h1, _⟩, hk⟩
    dsimp at h0 h1 hk
    exact ⟨⟨by omega, hk⟩, ⟨h0, by omega⟩⟩

/-- Second-coordinate degree `δ'(a, b) = b` on the quadratic wedge. -/
def quadraticWedgeSnd : PositiveDegrees (ℤ × ℤ) where
  monoid := quadraticWedgeMonoid
  degree := AddMonoidHom.snd ℤ ℤ
  degree_pos hn hne := by
    have := one_le_snd_of_mem_quadraticWedgeMonoid hn hne
    dsimp
    omega
  finite_le k := by
    apply ((Set.finite_Icc (a := (0 : ℤ)) (b := (k : ℤ) ^ 2)).prod
      (Set.finite_Icc (a := (0 : ℤ)) (b := k))).subset
    rintro ⟨a, b⟩ ⟨⟨h0, h1, h2⟩, hk⟩
    dsimp at h0 h1 h2 hk
    exact ⟨⟨by omega, h2.trans (pow_le_pow_left₀ h0 hk 2)⟩, ⟨h0, hk⟩⟩

/-- The allowed points of the first-coordinate degree. -/
@[simp]
theorem quadraticWedgeFst_monoid : quadraticWedgeFst.monoid = quadraticWedgeMonoid := (rfl)

/-- The first-coordinate degree. -/
@[simp]
theorem quadraticWedgeFst_degree (n : ℤ × ℤ) : quadraticWedgeFst.degree n = n.1 := (rfl)

/-- The allowed points of the second-coordinate degree. -/
@[simp]
theorem quadraticWedgeSnd_monoid : quadraticWedgeSnd.monoid = quadraticWedgeMonoid := (rfl)

/-- The second-coordinate degree. -/
@[simp]
theorem quadraticWedgeSnd_degree (n : ℤ × ℤ) : quadraticWedgeSnd.degree n = n.2 := (rfl)

/-- Both coordinate degrees live on the quadratic wedge. -/
theorem quadraticWedgeFst_monoid_eq_quadraticWedgeSnd_monoid :
    quadraticWedgeFst.monoid = quadraticWedgeSnd.monoid := (rfl)

/-- The change of degree from `δ(a, b) = a` to `δ'(a, b) = b` on the quadratic wedge has
modulus `k²`, attained at `(k², k)`. -/
theorem changeDegree_quadraticWedgeFst_snd_modulus (k : ℕ) :
    (PositiveDegreeMap.changeDegree quadraticWedgeFst quadraticWedgeSnd
      quadraticWedgeFst_monoid_eq_quadraticWedgeSnd_monoid).modulus k = k ^ 2 := by
  apply le_antisymm
  · rw [PositiveDegreeMap.changeDegree_modulus_le_iff]
    rintro n ⟨h0, -, h2⟩ hk
    simp only [quadraticWedgeSnd_degree] at hk
    simp only [quadraticWedgeFst_degree, Nat.cast_pow]
    exact h2.trans (pow_le_pow_left₀ h0 hk 2)
  · have h := (PositiveDegreeMap.changeDegree quadraticWedgeFst quadraticWedgeSnd
      quadraticWedgeFst_monoid_eq_quadraticWedgeSnd_monoid).degree_le k (n := ((k : ℤ) ^ 2, k))
      ⟨by simp, by dsimp only; nlinarith, le_rfl⟩ (by simp)
    simp only [quadraticWedgeFst_degree] at h
    exact_mod_cast h

/-- The change of degree from `δ'(a, b) = b` to `δ(a, b) = a` on the quadratic wedge has
modulus `k`, attained at `(k, k)`. -/
theorem changeDegree_quadraticWedgeSnd_fst_modulus (k : ℕ) :
    (PositiveDegreeMap.changeDegree quadraticWedgeSnd quadraticWedgeFst
      quadraticWedgeFst_monoid_eq_quadraticWedgeSnd_monoid.symm).modulus k = k := by
  apply le_antisymm
  · rw [PositiveDegreeMap.changeDegree_modulus_le_iff]
    rintro n ⟨-, h1, -⟩ hk
    simp only [quadraticWedgeFst_degree] at hk
    simpa only [quadraticWedgeSnd_degree] using h1.trans hk
  · have h := (PositiveDegreeMap.changeDegree quadraticWedgeSnd quadraticWedgeFst
      quadraticWedgeFst_monoid_eq_quadraticWedgeSnd_monoid.symm).degree_le k (n := ((k : ℤ), k))
      ⟨by simp, le_rfl, by dsimp only; nlinarith⟩ (by simp)
    simp only [quadraticWedgeSnd_degree] at h
    exact_mod_cast h

end TauCeti.PositiveDegrees.Examples
