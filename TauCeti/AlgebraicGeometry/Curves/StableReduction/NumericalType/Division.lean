/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Topology
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Dividing the common factors of a numerical type

Dividing all multiplicities by a common positive divisor preserves the fibre relation.
Dividing all weights and intersection numbers by a common positive divisor preserves both
that relation and the weighted intersection matrix. These operations remove irrelevant common
factors before applying prime-torsion estimates to numerical types.

The numerical types and weighted relations are those of the Stacks Project, Tags 0C6Z and 0C7H.
-/

public section

namespace TauCeti.NumericalType

universe u

variable (T : NumericalType.{u}) (m w : ℕ+)
  (hm : ∀ i, (m : ℕ) ∣ T.multiplicity i) (hw : ∀ i, (w : ℕ) ∣ T.weight i)

/-- Divide the multiplicities by `m` and the weights and intersection numbers by `w`.
The component genera are unchanged. Both divisors must be positive and divide every
corresponding entry. The definition is exposed to identify its component type with the
original component type. -/
abbrev divide : NumericalType.{u} where
  Component := T.Component
  multiplicity i := ⟨T.multiplicity i / m,
    Nat.div_pos (Nat.le_of_dvd (T.multiplicity i).pos (hm i)) m.pos⟩
  weight i := ⟨T.weight i / w,
    Nat.div_pos (Nat.le_of_dvd (T.weight i).pos (hw i)) w.pos⟩
  intersection i j := T.intersection i j / w
  intersection_isSymm := Matrix.IsSymm.ext fun i j ↦ by rw [T.intersection_comm]
  offDiagonal_nonneg i j hij :=
    Int.ediv_nonneg (T.offDiagonal_nonneg i j hij) (Int.natCast_nonneg _)
  connected i j := by
    apply Relation.ReflTransGen.mono ?_ i j (T.connected i j)
    intro a b h
    refine ⟨h.1, Int.ediv_pos_of_pos_of_dvd h.2 (Int.natCast_nonneg _) ?_⟩
    exact dvd_trans (by exact_mod_cast hw a) (T.weight_dvd a b)
  fiber_relation i := by
    have hmi (j : T.Component) : (m : ℤ) * ((T.multiplicity j / m : ℕ) : ℤ) =
        T.multiplicity j := by
      exact_mod_cast Nat.mul_div_cancel' (hm j)
    have hwi (j : T.Component) : (w : ℤ) * (T.intersection i j / w) =
        T.intersection i j :=
      Int.mul_ediv_cancel' (dvd_trans (by exact_mod_cast hw i) (T.weight_dvd i j))
    apply mul_left_cancel₀ (a := (m : ℤ) * w)
      (mul_ne_zero (Int.natCast_pos.mpr m.pos).ne' (Int.natCast_pos.mpr w.pos).ne')
    rw [mul_zero, Finset.mul_sum]
    convert T.fiber_relation i using 1
    apply Finset.sum_congr rfl
    intro j _
    calc
      (m : ℤ) * w * (((T.multiplicity j / m : ℕ) : ℤ) * (T.intersection i j / w)) =
          ((m : ℤ) * ((T.multiplicity j / m : ℕ) : ℤ)) *
            ((w : ℤ) * (T.intersection i j / w)) := by ring
      _ = (T.multiplicity j : ℤ) * T.intersection i j := by rw [hmi, hwi]
  weight_dvd i j := by
    obtain ⟨a, ha⟩ := T.weight_dvd i j
    have hi : ((T.weight i / w : ℕ) : ℤ) * (w : ℤ) = T.weight i := by
      exact_mod_cast Nat.div_mul_cancel (hw i)
    refine ⟨a, ?_⟩
    rw [ha, ← hi]
    calc
      ((↑(T.weight i / w : ℕ) : ℤ) * w * a) / w =
          ((↑(T.weight i / w : ℕ) : ℤ) * a * w) / w := by
            congr 1
            ring
      _ = _ := by rw [Int.mul_ediv_cancel _ (Int.natCast_pos.mpr w.pos).ne']; rfl
  genus := T.genus

@[simp]
theorem divide_multiplicity (i : T.Component) :
    ((T.divide m w hm hw).multiplicity i : ℕ) = T.multiplicity i / m := (rfl)

@[simp]
theorem divide_weight (i : T.Component) :
    ((T.divide m w hm hw).weight i : ℕ) = T.weight i / w := (rfl)

@[simp]
theorem divide_intersection (i j : T.Component) :
    (T.divide m w hm hw).intersection i j = T.intersection i j / w := (rfl)

@[simp]
theorem divide_genus (i : T.Component) : (T.divide m w hm hw).genus i = T.genus i := (rfl)

/-- Clearing the division in a divided multiplicity. -/
theorem mul_divide_multiplicity (i : T.Component) :
    (m : ℤ) * ((T.divide m w hm hw).multiplicity i : ℤ) = T.multiplicity i := by
  simp only [← Int.natCast_mul]
  exact_mod_cast Nat.mul_div_cancel' (hm i)

/-- Clearing the division in a divided weight. -/
theorem mul_divide_weight (i : T.Component) :
    (w : ℤ) * ((T.divide m w hm hw).weight i : ℤ) = T.weight i := by
  simp only [← Int.natCast_mul]
  exact_mod_cast Nat.mul_div_cancel' (hw i)

/-- Clearing the division in a divided intersection number. -/
theorem mul_divide_intersection (i j : T.Component) :
    (w : ℤ) * (T.divide m w hm hw).intersection i j = T.intersection i j :=
  Int.mul_ediv_cancel' (dvd_trans (by exact_mod_cast hw i) (T.weight_dvd i j))

/-- Dividing common factors preserves adjacency of components. This is not a simp lemma:
`adj_iff` already expands its left-hand side to inequalities of intersection numbers. -/
theorem adj_divide_iff (i j : T.Component) :
    (T.divide m w hm hw).Adj i j ↔ T.Adj i j := by
  simp only [adj_iff]
  have h := T.mul_divide_intersection m w hm hw i j
  have hwpos : (0 : ℤ) < w := Int.natCast_pos.mpr w.pos
  constructor <;> rintro ⟨hne, hpos⟩ <;> exact ⟨hne, by nlinarith⟩

/-- Dividing common factors preserves the intersection graph. -/
@[simp]
theorem intersectionGraph_divide : (T.divide m w hm hw).intersectionGraph =
    T.intersectionGraph := by
  ext i j
  simp only [intersectionGraph_adj_iff, adj_divide_iff]

/-- Dividing common factors preserves the first Betti number of the intersection graph. -/
@[simp]
theorem topologicalGenus_divide : (T.divide m w hm hw).topologicalGenus =
    T.topologicalGenus := by
  rw [topologicalGenus_def, topologicalGenus_def, intersectionGraph_divide]

end TauCeti.NumericalType
