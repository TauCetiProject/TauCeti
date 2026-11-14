/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.Quaternion
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.Algebra.Quaternion.Steinberg
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.Algebra.Quaternion.SpecialLinear

/-!
# The Hurwitz quaternion order and its group of twenty-four units

A Hamilton quaternion `q ∈ ℍ[ℝ]` is a **Hurwitz integer** (`Quaternion.IsHurwitz`) when its four
coordinates in the standard basis `1, i, j, k` are either all integers or all half-odd-integers
`a + 1 / 2` (`a ∈ ℤ`). Equivalently, `q` lies in the `ℤ`-lattice spanned by `1, i, j` and
`ω = (1 + i + j + k) / 2` (`Quaternion.isHurwitz_iff_exists_zsmul`). Because `ω² = ω - 1` and
`star ω = 1 - ω`, the Hurwitz integers form a `ℤ`-subalgebra with involution of `ℍ[ℝ]`, packaged
here as `TauCeti.hurwitzQuaternions : StarSubalgebra ℤ ℍ[ℝ]`.

The norm-square of a Hurwitz quaternion is a natural number
(`Quaternion.IsHurwitz.exists_nat_normSq`), so a Hurwitz quaternion is invertible in the Hurwitz
order precisely when its norm-square is `1` (`TauCeti.hurwitzUnitaryEquivUnits`). Solving
`a² + b² + c² + d² = 1` on the integer and half-integer cosets classifies the unit group
`TauCeti.hurwitzUnitSubgroup ≤ unitary ℍ[ℝ]` into two disjoint families
(`TauCeti.mem_hurwitzUnitSubgroup_iff`):

* the `8` Lipschitz units `TauCeti.lipschitzUnit a ε`, having `ε = ±1` in coordinate `a` and `0`
  elsewhere — equivalently, the coordinate permutations of `(±1, 0, 0, 0)`
  (`TauCeti.exists_lipschitzUnit_iff_exists_perm`);
* the `16` half-integer units `TauCeti.halfHurwitzUnit δ = (±1 ± i ± j ± k) / 2` indexed by sign
  vectors `δ : Fin 4 → ℤˣ`.

Bundling the two families gives the explicit bijection
`TauCeti.hurwitzUnitParam : (Fin 4 × ℤˣ) ⊕ (Fin 4 → ℤˣ) ≃ hurwitzUnitSubgroup`, proving that the
`24` units are pairwise distinct and that `Nat.card hurwitzUnitSubgroup = 24`.

Since `2` is invertible modulo `3`, scaling the doubled integer coordinates `2 q` by `2 ≡ 2⁻¹` in
`ZMod 3` defines a star-algebra homomorphism `TauCeti.hurwitzModThree : hurwitzQuaternions →⋆ₐ[ℤ]
ℍ[ZMod 3]`. On `hurwitzUnitSubgroup` its kernel is trivial, and comparing cardinalities with
`SL₂(𝔽₃)` via the Steinberg splitting of `ℍ[𝔽₃]` yields the group equivalences
`TauCeti.hurwitzUnitEquivUnitaryZModThree` and `TauCeti.hurwitzUnitEquivSpecialLinear` with
`Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)`.

## Main definitions

* `Quaternion.IsHurwitz`: predicate that `q : ℍ[ℝ]` has all-integer or all-half-integer
  coordinates.
* `TauCeti.hurwitzQuaternions`: the Hurwitz order as a `StarSubalgebra ℤ ℍ[ℝ]`.
* `TauCeti.hurwitzUnitaryEquivUnits`: `unitary hurwitzQuaternions ≃* hurwitzQuaternionsˣ`.
* `TauCeti.lipschitzUnit`, `TauCeti.halfHurwitzUnit`: the `8` integer and `16` half-integer
  Hurwitz units in `ℍ[ℝ]`.
* `TauCeti.hurwitzUnitSubgroup`: the subgroup of `unitary ℍ[ℝ]` consisting of the Hurwitz units.
* `TauCeti.hurwitzUnitParam`: the coordinate bijection `(Fin 4 × ℤˣ) ⊕ (Fin 4 → ℤˣ) ≃
  hurwitzUnitSubgroup`.
* `TauCeti.hurwitzModThree`: reduction modulo `3`, `hurwitzQuaternions →⋆ₐ[ℤ] ℍ[ZMod 3]`.
* `TauCeti.hurwitzUnitEquivUnitaryZModThree` and `TauCeti.hurwitzUnitEquivSpecialLinear`:
  the multiplicative equivalences `hurwitzUnitSubgroup ≃* unitary ℍ[ZMod 3]` and
  `hurwitzUnitSubgroup ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)`.

## References

* A. Hurwitz, *Über die Zahlentheorie der Quaternionen*, Nachr. Ges. Wiss. Göttingen (1896),
  313–340.
* J. H. Conway and D. A. Smith, *On Quaternions and Octonions*, A K Peters, 2003, §§5.1–5.2.
-/

public section

open scoped Quaternion Matrix

namespace Quaternion

/-- A Hamilton quaternion `q : ℍ[ℝ]` is a **Hurwitz integer** if its four coordinates are either
all integers or all half-odd-integers `a + 1 / 2` (`a : ℤ`). -/
def IsHurwitz (q : ℍ[ℝ]) : Prop :=
  (∃ a b c d : ℤ, q = ⟨a, b, c, d⟩) ∨
    ∃ a b c d : ℤ, q = ⟨a + 1 / 2, b + 1 / 2, c + 1 / 2, d + 1 / 2⟩

/-- Unfolding lemma for `Quaternion.IsHurwitz`. -/
theorem isHurwitz_def (q : ℍ[ℝ]) :
    q.IsHurwitz ↔
      (∃ a b c d : ℤ, q = ⟨a, b, c, d⟩) ∨
        ∃ a b c d : ℤ, q = ⟨a + 1 / 2, b + 1 / 2, c + 1 / 2, d + 1 / 2⟩ :=
  Iff.rfl

/-- **Lattice basis of the Hurwitz order.** A real quaternion is Hurwitz if and only if it is a
`ℤ`-linear combination of `1, i, j` and `ω = (1 + i + j + k) / 2`. -/
theorem isHurwitz_iff_exists_zsmul {q : ℍ[ℝ]} :
    q.IsHurwitz ↔
      ∃ c₀ c₁ c₂ c₃ : ℤ, q = ⟨c₀, c₁, c₂, 0⟩ + c₃ • ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ := by
  constructor
  · rintro (⟨a, b, c, d, rfl⟩ | ⟨a, b, c, d, rfl⟩)
    · refine ⟨a - d, b - d, c - d, 2 * d, ?_⟩
      ext <;> simp <;> ring
    · refine ⟨a - d, b - d, c - d, 2 * d + 1, ?_⟩
      ext <;> simp <;> ring
  · rintro ⟨c₀, c₁, c₂, c₃, rfl⟩
    rcases Int.even_or_odd c₃ with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · refine Or.inl ⟨c₀ + k, c₁ + k, c₂ + k, k, ?_⟩
      ext <;> simp <;> ring
    · refine Or.inr ⟨c₀ + k, c₁ + k, c₂ + k, k, ?_⟩
      ext <;> simp <;> ring

/-- Zero is a Hurwitz integer. -/
@[simp]
theorem isHurwitz_zero : (0 : ℍ[ℝ]).IsHurwitz :=
  Or.inl ⟨0, 0, 0, 0, by ext <;> simp⟩

/-- One is a Hurwitz integer. -/
@[simp]
theorem isHurwitz_one : (1 : ℍ[ℝ]).IsHurwitz :=
  Or.inl ⟨1, 0, 0, 0, by ext <;> simp⟩

/-- Every rational integer embedded in `ℍ[ℝ]` is a Hurwitz integer. -/
@[simp]
theorem isHurwitz_intCast (n : ℤ) : (n : ℍ[ℝ]).IsHurwitz :=
  Or.inl ⟨n, 0, 0, 0, by ext <;> simp⟩

namespace IsHurwitz

/-- Hurwitz integers are closed under addition. -/
theorem add {p q : ℍ[ℝ]} (hp : p.IsHurwitz) (hq : q.IsHurwitz) : (p + q).IsHurwitz := by
  rw [isHurwitz_iff_exists_zsmul] at hp hq ⊢
  obtain ⟨a₁, b₁, c₁, d₁, rfl⟩ := hp
  obtain ⟨a₂, b₂, c₂, d₂, rfl⟩ := hq
  refine ⟨a₁ + a₂, b₁ + b₂, c₁ + c₂, d₁ + d₂, ?_⟩
  ext <;> simp <;> ring

/-- Hurwitz integers are closed under negation. -/
theorem neg {q : ℍ[ℝ]} (hq : q.IsHurwitz) : (-q).IsHurwitz := by
  rw [isHurwitz_iff_exists_zsmul] at hq ⊢
  obtain ⟨a, b, c, d, rfl⟩ := hq
  refine ⟨-a, -b, -c, -d, ?_⟩
  ext <;> simp <;> ring

/-- Hurwitz integers are closed under subtraction. -/
theorem sub {p q : ℍ[ℝ]} (hp : p.IsHurwitz) (hq : q.IsHurwitz) : (p - q).IsHurwitz := by
  simpa [sub_eq_add_neg] using hp.add hq.neg

/-- Hurwitz integers are closed under `ℤ`-scalar multiplication. -/
theorem zsmul (n : ℤ) {q : ℍ[ℝ]} (hq : q.IsHurwitz) : (n • q).IsHurwitz := by
  rw [isHurwitz_iff_exists_zsmul] at hq ⊢
  obtain ⟨a, b, c, d, rfl⟩ := hq
  refine ⟨n * a, n * b, n * c, n * d, ?_⟩
  ext <;> simp <;> ring

/-- Hurwitz integers are closed under quaternion multiplication. -/
theorem mul {p q : ℍ[ℝ]} (hp : p.IsHurwitz) (hq : q.IsHurwitz) : (p * q).IsHurwitz := by
  rw [isHurwitz_iff_exists_zsmul] at hp hq ⊢
  obtain ⟨a₁, b₁, c₁, d₁, rfl⟩ := hp
  obtain ⟨a₂, b₂, c₂, d₂, rfl⟩ := hq
  refine ⟨a₁ * a₂ - b₁ * b₂ - c₁ * c₂ - (b₁ * c₂ - c₁ * b₂) - b₁ * d₂ - d₁ * c₂ - d₁ * d₂,
    a₁ * b₂ + b₁ * a₂ - (b₁ * c₂ - c₁ * b₂) + d₁ * b₂ + c₁ * d₂ - d₁ * c₂,
    a₁ * c₂ + c₁ * a₂ - (b₁ * c₂ - c₁ * b₂) - b₁ * d₂ + d₁ * b₂ + c₁ * d₂,
    2 * (b₁ * c₂ - c₁ * b₂) + a₁ * d₂ + d₁ * a₂ + b₁ * d₂ + d₁ * c₂ - c₁ * d₂ - d₁ * b₂ +
      d₁ * d₂, ?_⟩
  ext <;> simp <;> ring

/-- Hurwitz integers are closed under quaternion conjugation. -/
theorem star {q : ℍ[ℝ]} (hq : q.IsHurwitz) : (Star.star q).IsHurwitz := by
  rw [isHurwitz_iff_exists_zsmul] at hq ⊢
  obtain ⟨a, b, c, d, rfl⟩ := hq
  refine ⟨a + d, -b, -c, -d, ?_⟩
  ext <;> simp <;> ring

/-- Doubling a Hurwitz quaternion produces integer coordinates. -/
theorem exists_int_two_mul {q : ℍ[ℝ]} (hq : q.IsHurwitz) :
    ∃ a b c d : ℤ, 2 * q.re = a ∧ 2 * q.imI = b ∧ 2 * q.imJ = c ∧ 2 * q.imK = d := by
  rw [isHurwitz_iff_exists_zsmul] at hq
  obtain ⟨c₀, c₁, c₂, c₃, rfl⟩ := hq
  refine ⟨2 * c₀ + c₃, 2 * c₁ + c₃, 2 * c₂ + c₃, c₃, ?_, ?_, ?_, ?_⟩ <;> simp <;> ring

/-- **The norm-square of a Hurwitz quaternion is a natural number.** -/
theorem exists_nat_normSq {q : ℍ[ℝ]} (hq : q.IsHurwitz) : ∃ n : ℕ, normSq q = n := by
  have hnonneg (m : ℤ) : 0 ≤ m ^ 2 + m := by
    rcases le_or_gt 0 m with h | h <;> nlinarith
  rcases hq with ⟨a, b, c, d, rfl⟩ | ⟨a, b, c, d, rfl⟩
  · refine ⟨a.natAbs ^ 2 + b.natAbs ^ 2 + c.natAbs ^ 2 + d.natAbs ^ 2, ?_⟩
    rw [normSq_def']
    push_cast
    simp [sq_abs]
  · set s : ℤ := (a ^ 2 + a) + (b ^ 2 + b) + (c ^ 2 + c) + (d ^ 2 + d) + 1
    have hs : 0 ≤ s := by
      have := hnonneg a; have := hnonneg b; have := hnonneg c; have := hnonneg d
      omega
    refine ⟨s.toNat, ?_⟩
    rw [normSq_def']
    calc
      ((a : ℝ) + 1 / 2) ^ 2 + ((b : ℝ) + 1 / 2) ^ 2 + ((c : ℝ) + 1 / 2) ^ 2 +
          ((d : ℝ) + 1 / 2) ^ 2 = (s : ℝ) := by
        dsimp [s]; push_cast; ring
      _ = (s.toNat : ℝ) := by exact_mod_cast (Int.toNat_of_nonneg hs).symm

end IsHurwitz

/-- Negation preserves `Quaternion.IsHurwitz`. -/
@[simp]
theorem isHurwitz_neg {q : ℍ[ℝ]} : (-q).IsHurwitz ↔ q.IsHurwitz :=
  ⟨fun h => neg_neg q ▸ h.neg, IsHurwitz.neg⟩

/-- Conjugation preserves `Quaternion.IsHurwitz`. -/
@[simp]
theorem isHurwitz_star {q : ℍ[ℝ]} : (star q).IsHurwitz ↔ q.IsHurwitz :=
  ⟨fun h => star_star q ▸ h.star, IsHurwitz.star⟩

end Quaternion

namespace TauCeti

/-! ### The Hurwitz star-subalgebra and its units -/

/-- **The Hurwitz quaternion order**, as a `ℤ`-star-subalgebra of `ℍ[ℝ]`. -/
def hurwitzQuaternions : StarSubalgebra ℤ ℍ[ℝ] where
  carrier := {q | q.IsHurwitz}
  mul_mem' hp hq := hp.mul hq
  one_mem' := Quaternion.isHurwitz_one
  add_mem' hp hq := hp.add hq
  zero_mem' := Quaternion.isHurwitz_zero
  algebraMap_mem' n := by simp
  star_mem' hq := hq.star

/-- Membership in `TauCeti.hurwitzQuaternions` is `Quaternion.IsHurwitz`. -/
@[simp]
theorem mem_hurwitzQuaternions {q : ℍ[ℝ]} : q ∈ hurwitzQuaternions ↔ q.IsHurwitz :=
  Iff.rfl

/-- **Every unit of the Hurwitz order is unitary**: because the norm-square of a Hurwitz quaternion
lies in `ℕ`, invertibility in `hurwitzQuaternions` forces norm-square `1`. -/
noncomputable def hurwitzUnitaryEquivUnits :
    unitary hurwitzQuaternions ≃* hurwitzQuaternionsˣ :=
  MulEquiv.ofBijective Unitary.toUnits
    ⟨Unitary.toUnits_injective, fun u => by
      obtain ⟨m, hm⟩ := (mem_hurwitzQuaternions.mp (u : hurwitzQuaternions).2).exists_nat_normSq
      obtain ⟨n, hn⟩ := (mem_hurwitzQuaternions.mp (↑u⁻¹ : hurwitzQuaternions).2).exists_nat_normSq
      have hmul : ((m * n : ℕ) : ℝ) = 1 := by
        push_cast
        rw [← hm, ← hn, ← map_mul]
        have hu1 : ((u : hurwitzQuaternions) : ℍ[ℝ]) * ((↑u⁻¹ : hurwitzQuaternions) : ℍ[ℝ]) = 1 :=
          congrArg Subtype.val u.mul_inv
        rw [hu1, map_one]
      have hm1 : m = 1 := Nat.eq_one_of_mul_eq_one_right (by exact_mod_cast hmul)
      have hnorm : Quaternion.normSq ((u : hurwitzQuaternions) : ℍ[ℝ]) = 1 := by
        simpa [hm1] using hm
      have hunitaryR : ((u : hurwitzQuaternions) : ℍ[ℝ]) ∈ unitary ℍ[ℝ] :=
        (Quaternion.mem_unitary_iff_normSq_eq_one _).mpr hnorm
      have hunitary : (u : hurwitzQuaternions) ∈ unitary hurwitzQuaternions := by
        rw [Unitary.mem_iff] at hunitaryR ⊢
        exact ⟨Subtype.ext hunitaryR.1, Subtype.ext hunitaryR.2⟩
      exact ⟨⟨(u : hurwitzQuaternions), hunitary⟩, Units.ext rfl⟩⟩

/-- `TauCeti.hurwitzUnitaryEquivUnits` preserves the underlying Hurwitz quaternion. -/
@[simp]
theorem coe_hurwitzUnitaryEquivUnits_apply (u : unitary hurwitzQuaternions) :
    ((hurwitzUnitaryEquivUnits u : hurwitzQuaternionsˣ) : hurwitzQuaternions) =
      (u : hurwitzQuaternions) :=
  (rfl)

/-- `TauCeti.hurwitzUnitaryEquivUnits.symm` preserves the underlying Hurwitz quaternion. -/
@[simp]
theorem coe_hurwitzUnitaryEquivUnits_symm_apply (u : hurwitzQuaternionsˣ) :
    (hurwitzUnitaryEquivUnits.symm u : hurwitzQuaternions) = (u : hurwitzQuaternions) := by
  rw [← coe_hurwitzUnitaryEquivUnits_apply, hurwitzUnitaryEquivUnits.apply_symm_apply]

/-! ### Coordinate constructors for the twenty-four Hurwitz units -/

/-- **The eight Lipschitz units** `±1, ±i, ±j, ±k` in `ℍ[ℝ]`, having `ε = ±1` at coordinate
`a : Fin 4` and `0` in the remaining three coordinates. -/
noncomputable def lipschitzUnit (a : Fin 4) (ε : ℤˣ) : ℍ[ℝ] :=
  (Quaternion.equivTuple ℝ).symm (Pi.single a ((ε : ℤ) : ℝ))

/-- Unfolding lemma for `TauCeti.lipschitzUnit`. -/
theorem lipschitzUnit_def (a : Fin 4) (ε : ℤˣ) :
    lipschitzUnit a ε = (Quaternion.equivTuple ℝ).symm (Pi.single a ((ε : ℤ) : ℝ)) :=
  (rfl)

/-- The coordinate tuple of `lipschitzUnit a ε` is `Pi.single a ε`. -/
theorem equivTuple_lipschitzUnit (a : Fin 4) (ε : ℤˣ) :
    Quaternion.equivTuple ℝ (lipschitzUnit a ε) = Pi.single a ((ε : ℤ) : ℝ) :=
  (Quaternion.equivTuple ℝ).apply_symm_apply _

/-- Coordinate `0` gives the real units `±1`. -/
theorem lipschitzUnit_zero (ε : ℤˣ) : lipschitzUnit 0 ε = ⟨(ε : ℤ), 0, 0, 0⟩ := by
  ext <;> simp [lipschitzUnit]

/-- Coordinate `1` gives `±i`. -/
theorem lipschitzUnit_one (ε : ℤˣ) : lipschitzUnit 1 ε = ⟨0, (ε : ℤ), 0, 0⟩ := by
  ext <;> simp [lipschitzUnit]

/-- Coordinate `2` gives `±j`. -/
theorem lipschitzUnit_two (ε : ℤˣ) : lipschitzUnit 2 ε = ⟨0, 0, (ε : ℤ), 0⟩ := by
  ext <;> simp [lipschitzUnit]

/-- Coordinate `3` gives `±k`. -/
theorem lipschitzUnit_three (ε : ℤˣ) : lipschitzUnit 3 ε = ⟨0, 0, 0, (ε : ℤ)⟩ := by
  ext <;> simp [lipschitzUnit]

/-- Every Lipschitz unit is a Hurwitz integer. -/
@[simp]
theorem isHurwitz_lipschitzUnit (a : Fin 4) (ε : ℤˣ) : (lipschitzUnit a ε).IsHurwitz := by
  fin_cases a
  · exact Or.inl ⟨ε, 0, 0, 0, by simpa using lipschitzUnit_zero ε⟩
  · exact Or.inl ⟨0, ε, 0, 0, by simpa using lipschitzUnit_one ε⟩
  · exact Or.inl ⟨0, 0, ε, 0, by simpa using lipschitzUnit_two ε⟩
  · exact Or.inl ⟨0, 0, 0, ε, by simpa using lipschitzUnit_three ε⟩

/-- Every Lipschitz unit has norm-square `1`. -/
@[simp]
theorem normSq_lipschitzUnit (a : Fin 4) (ε : ℤˣ) :
    Quaternion.normSq (lipschitzUnit a ε) = 1 := by
  have hsq : ((ε : ℤ) : ℝ) ^ 2 = 1 := by
    rw [← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq, Units.val_one, Int.cast_one]
  fin_cases a <;>
    simp [lipschitzUnit_zero, lipschitzUnit_one, lipschitzUnit_two, lipschitzUnit_three,
      Quaternion.normSq_def', hsq]

/-- Every Lipschitz unit lies in `unitary ℍ[ℝ]`. -/
theorem lipschitzUnit_mem_unitary (a : Fin 4) (ε : ℤˣ) :
    lipschitzUnit a ε ∈ unitary ℍ[ℝ] :=
  (Quaternion.mem_unitary_iff_normSq_eq_one _).mpr (normSq_lipschitzUnit a ε)

/-- Distinct index-sign pairs `(a, ε)` determine distinct Lipschitz units. -/
theorem lipschitzUnit_injective :
    Function.Injective (fun p : Fin 4 × ℤˣ => lipschitzUnit p.1 p.2) := by
  rintro ⟨a₁, ε₁⟩ ⟨a₂, ε₂⟩ h
  have htuple := congrArg (Quaternion.equivTuple ℝ) h
  rw [equivTuple_lipschitzUnit, equivTuple_lipschitzUnit] at htuple
  have ha : a₁ = a₂ := by
    by_contra hne
    have hval := congrFun htuple a₁
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at hval
    rcases Int.units_eq_one_or ε₁ with rfl | rfl <;> norm_num at hval
  subst ha
  have hval := congrFun htuple a₁
  rw [Pi.single_eq_same, Pi.single_eq_same] at hval
  exact Prod.ext rfl (Units.ext (Int.cast_injective hval))

/-- **The Lipschitz units are the coordinate permutations of `(±1, 0, 0, 0)`.** -/
theorem exists_lipschitzUnit_iff_exists_perm {q : ℍ[ℝ]} :
    (∃ (a : Fin 4) (ε : ℤˣ), q = lipschitzUnit a ε) ↔
      ∃ (σ : Equiv.Perm (Fin 4)) (ε : ℤˣ),
        Quaternion.equivTuple ℝ q = ![((ε : ℤ) : ℝ), 0, 0, 0] ∘ σ := by
  have hvec (ε : ℤˣ) : (![((ε : ℤ) : ℝ), 0, 0, 0] : Fin 4 → ℝ) = Pi.single 0 ((ε : ℤ) : ℝ) := by
    ext i
    fin_cases i <;> simp
  constructor
  · rintro ⟨a, ε, rfl⟩
    refine ⟨Equiv.swap 0 a, ε, ?_⟩
    rw [equivTuple_lipschitzUnit, hvec]
    ext i
    by_cases hi : i = a
    · subst hi
      simp
    · have hswap : Equiv.swap 0 a i ≠ 0 := by
        intro h0
        apply hi
        simpa using congrArg (Equiv.swap 0 a) h0
      simp [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hswap]
  · rintro ⟨σ, ε, hq⟩
    refine ⟨σ.symm 0, ε, (Quaternion.equivTuple ℝ).injective ?_⟩
    rw [hq, equivTuple_lipschitzUnit, hvec]
    ext i
    by_cases hi : i = σ.symm 0
    · subst hi
      simp
    · have hσ : σ i ≠ 0 := fun h0 => hi (by simpa using congrArg σ.symm h0)
      simp [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hσ]

/-- **The sixteen half-integer Hurwitz units** `(±1 ± i ± j ± k) / 2` in `ℍ[ℝ]`, indexed by sign
vectors `δ : Fin 4 → ℤˣ`. -/
noncomputable def halfHurwitzUnit (δ : Fin 4 → ℤˣ) : ℍ[ℝ] :=
  (Quaternion.equivTuple ℝ).symm (fun i => ((δ i : ℤ) : ℝ) / 2)

/-- Coordinate formula for `TauCeti.halfHurwitzUnit`. -/
theorem halfHurwitzUnit_def (δ : Fin 4 → ℤˣ) :
    halfHurwitzUnit δ =
      ⟨((δ 0 : ℤ) : ℝ) / 2, ((δ 1 : ℤ) : ℝ) / 2, ((δ 2 : ℤ) : ℝ) / 2, ((δ 3 : ℤ) : ℝ) / 2⟩ :=
  (rfl)

/-- The coordinate tuple of `halfHurwitzUnit δ` is `i ↦ δ i / 2`. -/
theorem equivTuple_halfHurwitzUnit (δ : Fin 4 → ℤˣ) :
    Quaternion.equivTuple ℝ (halfHurwitzUnit δ) = fun i => ((δ i : ℤ) : ℝ) / 2 :=
  (Quaternion.equivTuple ℝ).apply_symm_apply _

/-- Every half-integer unit `(±1 ± i ± j ± k) / 2` is a Hurwitz integer. -/
@[simp]
theorem isHurwitz_halfHurwitzUnit (δ : Fin 4 → ℤˣ) : (halfHurwitzUnit δ).IsHurwitz := by
  have hhalf (u : ℤˣ) : ∃ m : ℤ, ((u : ℤ) : ℝ) / 2 = (m : ℝ) + 1 / 2 := by
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨0, by norm_num⟩
    · exact ⟨-1, by norm_num⟩
  obtain ⟨a, ha⟩ := hhalf (δ 0)
  obtain ⟨b, hb⟩ := hhalf (δ 1)
  obtain ⟨c, hc⟩ := hhalf (δ 2)
  obtain ⟨d, hd⟩ := hhalf (δ 3)
  exact Or.inr ⟨a, b, c, d, by rw [halfHurwitzUnit_def, ha, hb, hc, hd]⟩

/-- Every half-integer Hurwitz unit has norm-square `1`. -/
@[simp]
theorem normSq_halfHurwitzUnit (δ : Fin 4 → ℤˣ) :
    Quaternion.normSq (halfHurwitzUnit δ) = 1 := by
  have hsq (u : ℤˣ) : ((u : ℤ) : ℝ) ^ 2 = 1 := by
    rw [← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq, Units.val_one, Int.cast_one]
  rw [halfHurwitzUnit_def, Quaternion.normSq_def']
  linear_combination (hsq (δ 0) + hsq (δ 1) + hsq (δ 2) + hsq (δ 3)) / 4

/-- Every half-integer Hurwitz unit lies in `unitary ℍ[ℝ]`. -/
theorem halfHurwitzUnit_mem_unitary (δ : Fin 4 → ℤˣ) :
    halfHurwitzUnit δ ∈ unitary ℍ[ℝ] :=
  (Quaternion.mem_unitary_iff_normSq_eq_one _).mpr (normSq_halfHurwitzUnit δ)

/-- Distinct sign vectors determine distinct half-integer Hurwitz units. -/
theorem halfHurwitzUnit_injective : Function.Injective halfHurwitzUnit := by
  intro δ₁ δ₂ h
  have htuple := congrArg (Quaternion.equivTuple ℝ) h
  rw [equivTuple_halfHurwitzUnit, equivTuple_halfHurwitzUnit] at htuple
  funext i
  have hi := congrFun htuple i
  have hcast : ((δ₁ i : ℤ) : ℝ) = ((δ₂ i : ℤ) : ℝ) := by linarith
  exact Units.ext (Int.cast_injective hcast)

/-- No Lipschitz unit equals any half-integer Hurwitz unit. -/
theorem lipschitzUnit_ne_halfHurwitzUnit (a : Fin 4) (ε : ℤˣ) (δ : Fin 4 → ℤˣ) :
    lipschitzUnit a ε ≠ halfHurwitzUnit δ := by
  intro h
  have hval := congrFun (congrArg (Quaternion.equivTuple ℝ) h) a
  rw [equivTuple_lipschitzUnit, Pi.single_eq_same, equivTuple_halfHurwitzUnit] at hval
  have hint : 2 * (ε : ℤ) = (δ a : ℤ) := by
    exact_mod_cast (by linarith : (2 : ℝ) * ((ε : ℤ) : ℝ) = ((δ a : ℤ) : ℝ))
  rcases Int.units_eq_one_or ε with rfl | rfl <;>
    rcases Int.units_eq_one_or (δ a) with hδ | hδ <;>
    simp [hδ] at hint

/-! ### The Hurwitz unit subgroup and its twenty-four elements -/

/-- The star-monoid embedding `hurwitzQuaternions →⋆* ℍ[ℝ]`. -/
private def hurwitzSubtypeStarHom : hurwitzQuaternions →⋆* ℍ[ℝ] :=
  StarMonoidHom.ofClass hurwitzQuaternions.subtype

/-- **The Hurwitz unit subgroup** of `unitary ℍ[ℝ]`: the image of `unitary hurwitzQuaternions`
under the inclusion `hurwitzQuaternions ↪ ℍ[ℝ]`. -/
def hurwitzUnitSubgroup : Subgroup (unitary ℍ[ℝ]) :=
  (Unitary.map hurwitzSubtypeStarHom).toMonoidHom.range

/-- A unit Hamilton quaternion lies in `TauCeti.hurwitzUnitSubgroup` precisely when its underlying
quaternion is a Hurwitz integer. -/
theorem mem_hurwitzUnitSubgroup_iff_isHurwitz {u : unitary ℍ[ℝ]} :
    u ∈ hurwitzUnitSubgroup ↔ (u : ℍ[ℝ]).IsHurwitz := by
  rw [hurwitzUnitSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    exact mem_hurwitzQuaternions.mp (v : hurwitzQuaternions).2
  · intro hu
    have hmemQ : (u : ℍ[ℝ]) ∈ hurwitzQuaternions := mem_hurwitzQuaternions.mpr hu
    have hunitary : (⟨(u : ℍ[ℝ]), hmemQ⟩ : hurwitzQuaternions) ∈ unitary hurwitzQuaternions := by
      have hmem := Unitary.mem_iff.mp u.2
      exact Unitary.mem_iff.mpr ⟨Subtype.ext hmem.1, Subtype.ext hmem.2⟩
    exact ⟨⟨⟨(u : ℍ[ℝ]), hmemQ⟩, hunitary⟩, Subtype.ext rfl⟩

/-- The unitary Hurwitz quaternions are multiplicatively equivalent to
`TauCeti.hurwitzUnitSubgroup`. -/
noncomputable def hurwitzUnitaryEquivUnitSubgroup :
    unitary hurwitzQuaternions ≃* hurwitzUnitSubgroup :=
  MonoidHom.ofInjective (f := (Unitary.map hurwitzSubtypeStarHom).toMonoidHom)
    (Unitary.map_injective Subtype.val_injective)

/-- `TauCeti.hurwitzUnitaryEquivUnitSubgroup` preserves the underlying real quaternion. -/
@[simp]
theorem coe_hurwitzUnitaryEquivUnitSubgroup_apply (u : unitary hurwitzQuaternions) :
    (((hurwitzUnitaryEquivUnitSubgroup u : hurwitzUnitSubgroup) : unitary ℍ[ℝ]) : ℍ[ℝ]) =
      ((u : hurwitzQuaternions) : ℍ[ℝ]) :=
  (rfl)

/-- The units of the Hurwitz order are multiplicatively equivalent to
`TauCeti.hurwitzUnitSubgroup`. -/
noncomputable def hurwitzUnitsEquivUnitSubgroup :
    hurwitzQuaternionsˣ ≃* hurwitzUnitSubgroup :=
  hurwitzUnitaryEquivUnits.symm.trans hurwitzUnitaryEquivUnitSubgroup

/-- Unfolding lemma for `TauCeti.hurwitzUnitsEquivUnitSubgroup`. -/
theorem hurwitzUnitsEquivUnitSubgroup_def :
    hurwitzUnitsEquivUnitSubgroup =
      hurwitzUnitaryEquivUnits.symm.trans hurwitzUnitaryEquivUnitSubgroup :=
  (rfl)

/-- `TauCeti.hurwitzUnitsEquivUnitSubgroup` preserves the underlying real quaternion. -/
@[simp]
theorem coe_hurwitzUnitsEquivUnitSubgroup_apply (u : hurwitzQuaternionsˣ) :
    (((hurwitzUnitsEquivUnitSubgroup u : hurwitzUnitSubgroup) : unitary ℍ[ℝ]) : ℍ[ℝ]) =
      ((u : hurwitzQuaternions) : ℍ[ℝ]) := by
  rw [hurwitzUnitsEquivUnitSubgroup_def, MulEquiv.trans_apply,
    coe_hurwitzUnitaryEquivUnitSubgroup_apply, coe_hurwitzUnitaryEquivUnits_symm_apply]

/-- **Classification of the Hurwitz units.** A unit Hamilton quaternion lies in
`TauCeti.hurwitzUnitSubgroup` if and only if it is one of the `8` Lipschitz units or one of the
`16` half-integer units `(±1 ± i ± j ± k) / 2`. -/
theorem mem_hurwitzUnitSubgroup_iff {u : unitary ℍ[ℝ]} :
    u ∈ hurwitzUnitSubgroup ↔
      (∃ (a : Fin 4) (ε : ℤˣ), (u : ℍ[ℝ]) = lipschitzUnit a ε) ∨
        ∃ δ : Fin 4 → ℤˣ, (u : ℍ[ℝ]) = halfHurwitzUnit δ := by
  rw [mem_hurwitzUnitSubgroup_iff_isHurwitz]
  constructor
  · intro hu
    have hnorm : Quaternion.normSq (u : ℍ[ℝ]) = 1 := Quaternion.normSq_coe_unitary_eq_one u
    rcases hu with ⟨a, b, c, d, hq⟩ | ⟨a, b, c, d, hq⟩
    · -- Integer coset: `a² + b² + c² + d² = 1` forces one `±1` coordinate and three zeros.
      let v : Fin 4 → ℤ := ![a, b, c, d]
      have hv : ∑ i : Fin 4, v i ^ 2 = 1 := by
        rw [hq, Quaternion.normSq_def'] at hnorm
        dsimp at hnorm
        rw [Fin.sum_univ_four]
        dsimp [v]
        exact_mod_cast hnorm
      have hex : ∃ idx : Fin 4, v idx ≠ 0 := by
        by_contra! hall
        simp [hall] at hv
      obtain ⟨idx, hidx⟩ := hex
      have hidx_pos : 0 < v idx ^ 2 := sq_pos_of_ne_zero hidx
      have hsplit := Finset.add_sum_erase Finset.univ (fun i => v i ^ 2) (Finset.mem_univ idx)
      rw [hv] at hsplit
      have herase_nonneg : 0 ≤ ∑ i ∈ Finset.univ.erase idx, v i ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg (v i)
      have hidx_sq : v idx ^ 2 = 1 := by omega
      have herase_zero : ∑ i ∈ Finset.univ.erase idx, v i ^ 2 = 0 := by omega
      obtain ⟨ε, hε⟩ := IsUnit.of_mul_eq_one (v idx) (by simpa [sq] using hidx_sq)
      refine Or.inl ⟨idx, ε, (Quaternion.equivTuple ℝ).injective ?_⟩
      rw [hq, equivTuple_lipschitzUnit]
      have hv_eq :
          ∀ i : Fin 4, ((v i : ℤ) : ℝ) = (Pi.single idx ((ε : ℤ) : ℝ) : Fin 4 → ℝ) i := by
        intro i
        by_cases hi : i = idx
        · subst hi
          simp [hε]
        · have hmem : i ∈ Finset.univ.erase idx := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
          have hle := Finset.single_le_sum (fun j _ => sq_nonneg (v j)) hmem
          have h0 : v i = 0 := sq_eq_zero_iff.mp (le_antisymm (herase_zero ▸ hle) (sq_nonneg (v i)))
          simp [Pi.single_eq_of_ne hi, h0]
      ext i
      have hi := hv_eq i
      fin_cases i <;> simpa [v] using hi
    · -- Half-integer coset: `∑ (mᵢ² + mᵢ) = 0` with `m² + m ≥ 0` forces `mᵢ ∈ {0, -1}`.
      rw [hq] at hnorm
      simp only [Quaternion.normSq_def'] at hnorm
      have hsum : (a ^ 2 + a) + (b ^ 2 + b) + (c ^ 2 + c) + (d ^ 2 + d) = 0 := by
        have hreal :
            (((a ^ 2 + a) + (b ^ 2 + b) + (c ^ 2 + c) + (d ^ 2 + d) : ℤ) : ℝ) = 0 := by
          push_cast
          linarith
        exact_mod_cast hreal
      have hnonneg (m : ℤ) : 0 ≤ m ^ 2 + m := by
        rcases le_or_gt 0 m with h | h <;> nlinarith
      have hunit_of_zero {m : ℤ} (hm : m ^ 2 + m = 0) :
          ∃ s : ℤˣ, (m : ℝ) + 1 / 2 = ((s : ℤ) : ℝ) / 2 := by
        have hfac : m * (m + 1) = 0 := by linear_combination hm
        rcases mul_eq_zero.mp hfac with rfl | hm1
        · exact ⟨1, by norm_num⟩
        · have hm' : m = -1 := by omega
          subst hm'
          exact ⟨-1, by norm_num⟩
      have := hnonneg a; have := hnonneg b; have := hnonneg c; have := hnonneg d
      obtain ⟨u₀, hu₀⟩ := hunit_of_zero (m := a) (by omega)
      obtain ⟨u₁, hu₁⟩ := hunit_of_zero (m := b) (by omega)
      obtain ⟨u₂, hu₂⟩ := hunit_of_zero (m := c) (by omega)
      obtain ⟨u₃, hu₃⟩ := hunit_of_zero (m := d) (by omega)
      refine Or.inr ⟨![u₀, u₁, u₂, u₃], ?_⟩
      rw [hq, halfHurwitzUnit_def, hu₀, hu₁, hu₂, hu₃]
      simp
  · rintro (⟨a, ε, hq⟩ | ⟨δ, hq⟩)
    · rw [hq]
      exact isHurwitz_lipschitzUnit a ε
    · rw [hq]
      exact isHurwitz_halfHurwitzUnit δ

/-- **Explicit coordinate parametrization of the twenty-four Hurwitz units**, bundling closure in
`hurwitzUnitSubgroup` and pairwise distinctness of the `8 + 16` points. -/
noncomputable def hurwitzUnitParam : (Fin 4 × ℤˣ) ⊕ (Fin 4 → ℤˣ) ≃ hurwitzUnitSubgroup :=
  Equiv.ofBijective
    (Sum.elim
      (fun p => ⟨⟨lipschitzUnit p.1 p.2, lipschitzUnit_mem_unitary p.1 p.2⟩,
        mem_hurwitzUnitSubgroup_iff_isHurwitz.mpr (isHurwitz_lipschitzUnit p.1 p.2)⟩)
      (fun δ => ⟨⟨halfHurwitzUnit δ, halfHurwitzUnit_mem_unitary δ⟩,
        mem_hurwitzUnitSubgroup_iff_isHurwitz.mpr (isHurwitz_halfHurwitzUnit δ)⟩))
    ⟨by
      let coeVal : hurwitzUnitSubgroup → ℍ[ℝ] := fun x => ((x : unitary ℍ[ℝ]) : ℍ[ℝ])
      rintro (p | δ₁) (q | δ₂) h
      · exact congrArg Sum.inl (lipschitzUnit_injective (congrArg coeVal h))
      · exact absurd (congrArg coeVal h) (lipschitzUnit_ne_halfHurwitzUnit p.1 p.2 δ₂)
      · exact absurd (congrArg coeVal h).symm (lipschitzUnit_ne_halfHurwitzUnit q.1 q.2 δ₁)
      · exact congrArg Sum.inr (halfHurwitzUnit_injective (congrArg coeVal h)),
    fun u => by
      rcases mem_hurwitzUnitSubgroup_iff.mp u.2 with ⟨a, ε, hq⟩ | ⟨δ, hq⟩
      · exact ⟨Sum.inl (a, ε), Subtype.ext (Subtype.ext hq.symm)⟩
      · exact ⟨Sum.inr δ, Subtype.ext (Subtype.ext hq.symm)⟩⟩

/-- On the left summand `hurwitzUnitParam` produces `lipschitzUnit`. -/
@[simp]
theorem coe_hurwitzUnitParam_inl (p : Fin 4 × ℤˣ) :
    (((hurwitzUnitParam (Sum.inl p) : hurwitzUnitSubgroup) : unitary ℍ[ℝ]) : ℍ[ℝ]) =
      lipschitzUnit p.1 p.2 :=
  (rfl)

/-- On the right summand `hurwitzUnitParam` produces `halfHurwitzUnit`. -/
@[simp]
theorem coe_hurwitzUnitParam_inr (δ : Fin 4 → ℤˣ) :
    (((hurwitzUnitParam (Sum.inr δ) : hurwitzUnitSubgroup) : unitary ℍ[ℝ]) : ℍ[ℝ]) =
      halfHurwitzUnit δ :=
  (rfl)

/-- `TauCeti.hurwitzUnitSubgroup` is finite. -/
instance : Finite hurwitzUnitSubgroup :=
  Finite.of_equiv _ hurwitzUnitParam

/-- **The Hurwitz unit group has order `24`.** -/
@[simp]
theorem natCard_hurwitzUnitSubgroup : Nat.card hurwitzUnitSubgroup = 24 := by
  rw [← Nat.card_congr hurwitzUnitParam, Nat.card_eq_fintype_card]
  simp [Fintype.card_units_int]

/-! ### Reduction modulo three and isomorphism with `SL₂(𝔽₃)` -/

private noncomputable def hurwitzModThreeFun (q : hurwitzQuaternions) : ℍ[ZMod 3] :=
  ⟨2 * (⌊2 * (q : ℍ[ℝ]).re⌋ : ZMod 3),
   2 * (⌊2 * (q : ℍ[ℝ]).imI⌋ : ZMod 3),
   2 * (⌊2 * (q : ℍ[ℝ]).imJ⌋ : ZMod 3),
   2 * (⌊2 * (q : ℍ[ℝ]).imK⌋ : ZMod 3)⟩

private theorem hurwitzModThreeFun_eq_of_two_mul {q : hurwitzQuaternions} {a b c d : ℤ}
    (ha : 2 * (q : ℍ[ℝ]).re = a) (hb : 2 * (q : ℍ[ℝ]).imI = b)
    (hc : 2 * (q : ℍ[ℝ]).imJ = c) (hd : 2 * (q : ℍ[ℝ]).imK = d) :
    hurwitzModThreeFun q =
      ⟨2 * (a : ZMod 3), 2 * (b : ZMod 3), 2 * (c : ZMod 3), 2 * (d : ZMod 3)⟩ := by
  dsimp [hurwitzModThreeFun]
  rw [ha, hb, hc, hd]
  simp

private theorem hurwitzModThreeFun_mul (p q : hurwitzQuaternions) :
    hurwitzModThreeFun (p * q) = hurwitzModThreeFun p * hurwitzModThreeFun q := by
  have h8 : ∀ x : ZMod 3, 2 * x = 4 * (2 * x) := by
    intro x
    rw [← mul_assoc]
    have h : (2 : ZMod 3) = 4 * 2 := by decide
    exact congrArg (· * x) h
  obtain ⟨a₁, b₁, c₁, d₁, ha₁, hb₁, hc₁, hd₁⟩ :=
    (mem_hurwitzQuaternions.mp p.2).exists_int_two_mul
  obtain ⟨a₂, b₂, c₂, d₂, ha₂, hb₂, hc₂, hd₂⟩ :=
    (mem_hurwitzQuaternions.mp q.2).exists_int_two_mul
  obtain ⟨a₃, b₃, c₃, d₃, ha₃, hb₃, hc₃, hd₃⟩ :=
    (mem_hurwitzQuaternions.mp (p * q).2).exists_int_two_mul
  have hre : 2 * a₃ = a₁ * a₂ - b₁ * b₂ - c₁ * c₂ - d₁ * d₂ := by
    apply Int.cast_injective (α := ℝ); push_cast
    rw [← ha₁, ← hb₁, ← hc₁, ← hd₁, ← ha₂, ← hb₂, ← hc₂, ← hd₂, ← ha₃]; simp; ring
  have himI : 2 * b₃ = a₁ * b₂ + b₁ * a₂ + c₁ * d₂ - d₁ * c₂ := by
    apply Int.cast_injective (α := ℝ); push_cast
    rw [← ha₁, ← hb₁, ← hc₁, ← hd₁, ← ha₂, ← hb₂, ← hc₂, ← hd₂, ← hb₃]; simp; ring
  have himJ : 2 * c₃ = a₁ * c₂ - b₁ * d₂ + c₁ * a₂ + d₁ * b₂ := by
    apply Int.cast_injective (α := ℝ); push_cast
    rw [← ha₁, ← hb₁, ← hc₁, ← hd₁, ← ha₂, ← hb₂, ← hc₂, ← hd₂, ← hc₃]; simp; ring
  have himK : 2 * d₃ = a₁ * d₂ + b₁ * c₂ - c₁ * b₂ + d₁ * a₂ := by
    apply Int.cast_injective (α := ℝ); push_cast
    rw [← ha₁, ← hb₁, ← hc₁, ← hd₁, ← ha₂, ← hb₂, ← hc₂, ← hd₂, ← hd₃]; simp; ring
  have hre3 := congrArg (Int.cast : ℤ → ZMod 3) hre
  have himI3 := congrArg (Int.cast : ℤ → ZMod 3) himI
  have himJ3 := congrArg (Int.cast : ℤ → ZMod 3) himJ
  have himK3 := congrArg (Int.cast : ℤ → ZMod 3) himK
  push_cast at hre3 himI3 himJ3 himK3
  rw [hurwitzModThreeFun_eq_of_two_mul ha₁ hb₁ hc₁ hd₁,
    hurwitzModThreeFun_eq_of_two_mul ha₂ hb₂ hc₂ hd₂,
    hurwitzModThreeFun_eq_of_two_mul ha₃ hb₃ hc₃ hd₃]
  ext
  · calc
      2 * (a₃ : ZMod 3) = 4 * (2 * (a₃ : ZMod 3)) := h8 _
      _ = 4 * ((a₁ : ZMod 3) * a₂ - b₁ * b₂ - c₁ * c₂ - d₁ * d₂) := by rw [hre3]
      _ = _ := by simp; ring
  · calc
      2 * (b₃ : ZMod 3) = 4 * (2 * (b₃ : ZMod 3)) := h8 _
      _ = 4 * ((a₁ : ZMod 3) * b₂ + b₁ * a₂ + c₁ * d₂ - d₁ * c₂) := by rw [himI3]
      _ = _ := by simp; ring
  · calc
      2 * (c₃ : ZMod 3) = 4 * (2 * (c₃ : ZMod 3)) := h8 _
      _ = 4 * ((a₁ : ZMod 3) * c₂ - b₁ * d₂ + c₁ * a₂ + d₁ * b₂) := by rw [himJ3]
      _ = _ := by simp; ring
  · calc
      2 * (d₃ : ZMod 3) = 4 * (2 * (d₃ : ZMod 3)) := h8 _
      _ = 4 * ((a₁ : ZMod 3) * d₂ + b₁ * c₂ - c₁ * b₂ + d₁ * a₂) := by rw [himK3]
      _ = _ := by simp; ring

/-- **Reduction of Hurwitz quaternions modulo `3`.** Because `2 • q` has integer coordinates and
`2⁻¹ = 2` in `ZMod 3`, sending each coordinate `x` to `2 * (⌊2 * x⌋ : ZMod 3)` is a `ℤ`-star-algebra
homomorphism `hurwitzQuaternions →⋆ₐ[ℤ] ℍ[ZMod 3]`. -/
noncomputable def hurwitzModThree : hurwitzQuaternions →⋆ₐ[ℤ] ℍ[ZMod 3] where
  toFun := hurwitzModThreeFun
  map_one' := by
    rw [hurwitzModThreeFun_eq_of_two_mul (a := 2) (b := 0) (c := 0) (d := 0)
      (by simp) (by simp) (by simp) (by simp)]
    ext
    · simp only [Int.cast_ofNat, QuaternionAlgebra.re_one]
      decide
    · simp
    · simp
    · simp
  map_mul' := hurwitzModThreeFun_mul
  map_zero' := by
    rw [hurwitzModThreeFun_eq_of_two_mul (a := 0) (b := 0) (c := 0) (d := 0)
      (by simp) (by simp) (by simp) (by simp)]
    ext <;> simp
  map_add' p q := by
    obtain ⟨a₁, b₁, c₁, d₁, ha₁, hb₁, hc₁, hd₁⟩ :=
      (mem_hurwitzQuaternions.mp p.2).exists_int_two_mul
    obtain ⟨a₂, b₂, c₂, d₂, ha₂, hb₂, hc₂, hd₂⟩ :=
      (mem_hurwitzQuaternions.mp q.2).exists_int_two_mul
    rw [hurwitzModThreeFun_eq_of_two_mul ha₁ hb₁ hc₁ hd₁,
      hurwitzModThreeFun_eq_of_two_mul ha₂ hb₂ hc₂ hd₂,
      hurwitzModThreeFun_eq_of_two_mul (a := a₁ + a₂) (b := b₁ + b₂) (c := c₁ + c₂) (d := d₁ + d₂)
        (by simp [mul_add, ha₁, ha₂]) (by simp [mul_add, hb₁, hb₂])
        (by simp [mul_add, hc₁, hc₂]) (by simp [mul_add, hd₁, hd₂])]
    ext <;> simp <;> ring
  commutes' n := by
    have h4 : (4 : ZMod 3) = 1 := by decide
    rw [hurwitzModThreeFun_eq_of_two_mul (a := 2 * n) (b := 0) (c := 0) (d := 0)
      (by simp) (by simp) (by simp) (by simp)]
    ext
    · calc
        2 * (((2 * n : ℤ) : ZMod 3)) = 4 * (n : ZMod 3) := by push_cast; ring
        _ = (algebraMap ℤ ℍ[ZMod 3] n).re := by simp [h4]
    · simp
    · simp
    · simp
  map_star' q := by
    obtain ⟨a, b, c, d, ha, hb, hc, hd⟩ :=
      (mem_hurwitzQuaternions.mp q.2).exists_int_two_mul
    rw [hurwitzModThreeFun_eq_of_two_mul ha hb hc hd,
      hurwitzModThreeFun_eq_of_two_mul (a := a) (b := -b) (c := -c) (d := -d)
        (by simpa using ha) (by simp [mul_neg, hb])
        (by simp [mul_neg, hc]) (by simp [mul_neg, hd])]
    ext <;> simp

/-- Coordinate formula for `TauCeti.hurwitzModThree`. -/
theorem hurwitzModThree_apply (q : hurwitzQuaternions) :
    hurwitzModThree q =
      ⟨2 * (⌊2 * (q : ℍ[ℝ]).re⌋ : ZMod 3),
       2 * (⌊2 * (q : ℍ[ℝ]).imI⌋ : ZMod 3),
       2 * (⌊2 * (q : ℍ[ℝ]).imJ⌋ : ZMod 3),
       2 * (⌊2 * (q : ℍ[ℝ]).imK⌋ : ZMod 3)⟩ :=
  (rfl)

/-- Evaluation of `TauCeti.hurwitzModThree` in terms of the doubled integer coordinates `2 q`. -/
theorem hurwitzModThree_eq_of_two_mul {q : hurwitzQuaternions} {a b c d : ℤ}
    (ha : 2 * (q : ℍ[ℝ]).re = a) (hb : 2 * (q : ℍ[ℝ]).imI = b)
    (hc : 2 * (q : ℍ[ℝ]).imJ = c) (hd : 2 * (q : ℍ[ℝ]).imK = d) :
    hurwitzModThree q =
      ⟨2 * (a : ZMod 3), 2 * (b : ZMod 3), 2 * (c : ZMod 3), 2 * (d : ZMod 3)⟩ :=
  hurwitzModThreeFun_eq_of_two_mul ha hb hc hd

/-- The group homomorphism `hurwitzUnitSubgroup →* unitary ℍ[ZMod 3]` induced by reduction modulo
`3`. -/
private noncomputable def hurwitzUnitToUnitaryZModThree :
    hurwitzUnitSubgroup →* unitary ℍ[ZMod 3] :=
  (Unitary.map (StarMonoidHom.ofClass hurwitzModThree)).toMonoidHom.comp
    hurwitzUnitaryEquivUnitSubgroup.symm.toMonoidHom

private theorem coe_hurwitzUnitToUnitaryZModThree_apply (u : hurwitzUnitSubgroup) :
    (hurwitzUnitToUnitaryZModThree u : ℍ[ZMod 3]) =
      hurwitzModThree ⟨((u : unitary ℍ[ℝ]) : ℍ[ℝ]),
        mem_hurwitzQuaternions.mpr (mem_hurwitzUnitSubgroup_iff_isHurwitz.mp u.2)⟩ := by
  have he : (((hurwitzUnitaryEquivUnitSubgroup.symm u : unitary hurwitzQuaternions) :
      hurwitzQuaternions) : ℍ[ℝ]) = ((u : unitary ℍ[ℝ]) : ℍ[ℝ]) :=
    congrArg (fun x : hurwitzUnitSubgroup => ((x : unitary ℍ[ℝ]) : ℍ[ℝ]))
      (hurwitzUnitaryEquivUnitSubgroup.apply_symm_apply u)
  exact congrArg hurwitzModThree (Subtype.ext he)

private theorem hurwitzUnitToUnitaryZModThree_injective :
    Function.Injective hurwitzUnitToUnitaryZModThree := by
  have hne (ε : ℤˣ) : (2 : ZMod 3) * ((2 * (ε : ℤ) : ℤ) : ZMod 3) ≠ 0 := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> decide
  rw [injective_iff_map_eq_one]
  intro u hu
  have hmod : hurwitzModThree ⟨((u : unitary ℍ[ℝ]) : ℍ[ℝ]),
      mem_hurwitzQuaternions.mpr (mem_hurwitzUnitSubgroup_iff_isHurwitz.mp u.2)⟩ = 1 := by
    rw [← coe_hurwitzUnitToUnitaryZModThree_apply, hu]
    rfl
  rcases mem_hurwitzUnitSubgroup_iff.mp u.2 with ⟨a, ε, hq⟩ | ⟨δ, hq⟩
  · fin_cases a <;> dsimp at hq
    · rcases Int.units_eq_one_or ε with rfl | rfl
      · refine Subtype.ext (Subtype.ext ?_)
        rw [hq, lipschitzUnit_zero]
        ext <;> simp
      · rw [hurwitzModThree_eq_of_two_mul (a := -2) (b := 0) (c := 0) (d := 0)
          (by rw [hq, lipschitzUnit_zero]; norm_num) (by rw [hq, lipschitzUnit_zero]; norm_num)
          (by rw [hq, lipschitzUnit_zero]; norm_num) (by rw [hq, lipschitzUnit_zero]; norm_num)]
          at hmod
        exact absurd (congrArg QuaternionAlgebra.re hmod) (by decide)
    · rw [hurwitzModThree_eq_of_two_mul (a := 0) (b := 2 * ε) (c := 0) (d := 0)
        (by rw [hq, lipschitzUnit_one]; simp) (by rw [hq, lipschitzUnit_one]; push_cast; ring)
        (by rw [hq, lipschitzUnit_one]; simp) (by rw [hq, lipschitzUnit_one]; simp)] at hmod
      exact absurd (congrArg QuaternionAlgebra.imI hmod) (hne ε)
    · rw [hurwitzModThree_eq_of_two_mul (a := 0) (b := 0) (c := 2 * ε) (d := 0)
        (by rw [hq, lipschitzUnit_two]; simp) (by rw [hq, lipschitzUnit_two]; simp)
        (by rw [hq, lipschitzUnit_two]; push_cast; ring) (by rw [hq, lipschitzUnit_two]; simp)]
        at hmod
      exact absurd (congrArg QuaternionAlgebra.imJ hmod) (hne ε)
    · rw [hurwitzModThree_eq_of_two_mul (a := 0) (b := 0) (c := 0) (d := 2 * ε)
        (by rw [hq, lipschitzUnit_three]; simp) (by rw [hq, lipschitzUnit_three]; simp)
        (by rw [hq, lipschitzUnit_three]; simp) (by rw [hq, lipschitzUnit_three]; push_cast; ring)]
        at hmod
      exact absurd (congrArg QuaternionAlgebra.imK hmod) (hne ε)
  · rw [hurwitzModThree_eq_of_two_mul (a := δ 0) (b := δ 1) (c := δ 2) (d := δ 3)
      (by rw [hq, halfHurwitzUnit_def]; ring) (by rw [hq, halfHurwitzUnit_def]; ring)
      (by rw [hq, halfHurwitzUnit_def]; ring) (by rw [hq, halfHurwitzUnit_def]; ring)] at hmod
    have himK := congrArg QuaternionAlgebra.imK hmod
    dsimp at himK
    rcases Int.units_eq_one_or (δ 3) with hδ | hδ <;>
      · rw [hδ] at himK; exact absurd himK (by decide)

private theorem hurwitzUnitToUnitaryZModThree_bijective :
    Function.Bijective hurwitzUnitToUnitaryZModThree := by
  let _ : Invertible (2 : ZMod 3) := ⟨2, by decide, by decide⟩
  let _ : Invertible (-1 : ZMod 3) := ⟨-1, by decide, by decide⟩
  let _ : Invertible (1 - (-1 : ZMod 3)) := ⟨2, by decide, by decide⟩
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  let eSL : unitary ℍ[ZMod 3] ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
    _root_.QuaternionAlgebra.unitaryEquivSpecialLinearOfAlgEquiv
      (TauCeti.QuaternionAlgebra.steinbergEquivMatrix (-1 : ZMod 3))
  have hcard : Nat.card (unitary ℍ[ZMod 3]) = 24 := by
    rw [Nat.card_congr eSL.toEquiv, Matrix.card_SL_field]
    simp [Fin.prod_univ_two]
  have : Finite (unitary ℍ[ZMod 3]) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  exact (Nat.bijective_iff_injective_and_card _).mpr
    ⟨hurwitzUnitToUnitaryZModThree_injective, by rw [natCard_hurwitzUnitSubgroup, hcard]⟩

/-- **Reduction modulo `3` identifies `hurwitzUnitSubgroup` with `unitary ℍ[ZMod 3]`.** -/
noncomputable def hurwitzUnitEquivUnitaryZModThree :
    hurwitzUnitSubgroup ≃* unitary ℍ[ZMod 3] :=
  MulEquiv.ofBijective hurwitzUnitToUnitaryZModThree hurwitzUnitToUnitaryZModThree_bijective

/-- `TauCeti.hurwitzUnitEquivUnitaryZModThree` evaluates `TauCeti.hurwitzModThree`. -/
@[simp]
theorem coe_hurwitzUnitEquivUnitaryZModThree_apply (u : hurwitzUnitSubgroup) :
    (hurwitzUnitEquivUnitaryZModThree u : ℍ[ZMod 3]) =
      hurwitzModThree ⟨((u : unitary ℍ[ℝ]) : ℍ[ℝ]),
        mem_hurwitzQuaternions.mpr (mem_hurwitzUnitSubgroup_iff_isHurwitz.mp u.2)⟩ :=
  coe_hurwitzUnitToUnitaryZModThree_apply u

/-- **The Hurwitz unit group is isomorphic to `SL₂(𝔽₃)`**, via reduction modulo `3` followed by the
Steinberg splitting of `ℍ[ZMod 3]`. -/
noncomputable def hurwitzUnitEquivSpecialLinear :
    hurwitzUnitSubgroup ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) := by
  letI : Invertible (2 : ZMod 3) := ⟨2, by decide, by decide⟩
  letI : Invertible (-1 : ZMod 3) := ⟨-1, by decide, by decide⟩
  letI : Invertible (1 - (-1 : ZMod 3)) := ⟨2, by decide, by decide⟩
  exact hurwitzUnitEquivUnitaryZModThree.trans
    (_root_.QuaternionAlgebra.unitaryEquivSpecialLinearOfAlgEquiv
      (TauCeti.QuaternionAlgebra.steinbergEquivMatrix (-1 : ZMod 3)))

/-- `TauCeti.hurwitzUnitEquivSpecialLinear` applies the Steinberg matrix representation at `-1` to
the modulo-`3` reduction of a Hurwitz unit. -/
@[simp]
theorem coe_hurwitzUnitEquivSpecialLinear_apply (u : hurwitzUnitSubgroup) :
    ((hurwitzUnitEquivSpecialLinear u : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
      Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      TauCeti.QuaternionAlgebra.steinbergToMatrix (-1 : ZMod 3)
        (hurwitzUnitEquivUnitaryZModThree u : ℍ[ZMod 3]) := by
  simp only [hurwitzUnitEquivSpecialLinear, MulEquiv.trans_apply,
    _root_.QuaternionAlgebra.coe_unitaryEquivSpecialLinearOfAlgEquiv_apply]
  exact @TauCeti.QuaternionAlgebra.steinbergEquivMatrix_apply (ZMod 3) _
    ⟨2, by decide, by decide⟩ (-1) ⟨-1, by decide, by decide⟩ ⟨2, by decide, by decide⟩ _

end TauCeti

end
