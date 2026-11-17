/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Data.ZMod.IntUnitsPower

/-!
# Tensor signs for cyclic chain complexes

For an even modulus `n`, parity descends to `ZMod n`. We equip
`ComplexShape.down (ZMod n)` with Mathlib's `TensorSigns`, so native totalization
and tensor products have differential `d(x ⊗ y) = dx ⊗ y + (-1)^p x ⊗ dy`
on bidegree `(p, q)`. The separate `TotalComplexShapeSymmetry` instance supplies
the Koszul interchange sign `(-1)^(p*q)`.

The sign on an integer representative is `Int.negOnePow`. Conversely, the
existence of tensor signs forces the modulus to be even. No positivity
hypothesis is needed: `ZMod 0` is the integer-graded case. In particular the
instances apply to gradings modulo four and eight.

The construction follows the additive tensor-sign and total-complex symmetry
interfaces of Joël Riou in `Mathlib.Algebra.Homology.ComplexShapeSigns`, using
Eric Wieser's power operation on integer units by `ZMod 2` rather than choosing
integer representatives.
-/

public section

namespace ComplexShape

/-- On a cyclic chain shape, any tensor-sign character takes the value
`(-1)^k` on the class of an integer `k`. -/
@[simp]
theorem ε_down_zmod_intCast (n : ℕ) [(down (ZMod n)).TensorSigns] (k : ℤ) :
    (down (ZMod n)).ε (k : ZMod n) = k.negOnePow := by
  have h₁ : (down (ZMod n)).ε 1 = -1 := by
    have h := (down (ZMod n)).ε_succ (p := 1) (q := 0) (by simp)
    simpa using (congrArg Neg.neg h).symm
  have hk : (down (ZMod n)).ε (k : ZMod n) =
      ((down (ZMod n)).ε 1) ^ k := by
    have h := (TensorSigns.ε' (down (ZMod n))).map_zpow
      (Multiplicative.ofAdd (1 : ZMod n)) k
    -- Convert between the type-tagged multiplicative power and the additive cast.
    convert h using 1
    · congr 1
      exact (congrArg Multiplicative.ofAdd (zsmul_one (R := ZMod n) k)).symm
    · rfl
  rw [hk, h₁, Int.negOnePow_def]

/-- A cyclic chain shape admits tensor signs only if its modulus is even. -/
theorem even_of_tensorSigns_down_zmod (n : ℕ) [(down (ZMod n)).TensorSigns] :
    Even n := by
  have h := ε_down_zmod_intCast n (n : ℤ)
  simp only [Int.cast_natCast, ZMod.natCast_self, ε_zero] at h
  exact_mod_cast (Int.negOnePow_eq_one_iff (n : ℤ)).mp h.symm

/-- Tensor signs for an even cyclic grading. The vertical sign is the sign of
the reduction of the first degree modulo two. -/
instance tensorSignsDownZMod (n : ℕ) [Fact (Even n)] :
    (down (ZMod n)).TensorSigns where
  ε' := MonoidHom.mk'
    (fun p : Multiplicative (ZMod n) =>
      (-1 : ℤˣ) ^ ZMod.castHom (even_iff_two_dvd.mp (Fact.out : Even n))
        (ZMod 2) p.toAdd)
    (by
      intro p q
      simp only [toAdd_mul, map_add, uzpow_add])
  rel_add p q r hpq :=
    (add_right_comm q r 1).trans (congrArg (· + r) hpq)
  add_rel p q r hpq := by
    simpa only [down_Rel, add_assoc] using congrArg (r + ·) hpq
  ε'_succ := by
    intro p q hpq
    -- The relation for a chain differential is q + 1 = p.
    obtain rfl : q + 1 = p := hpq
    -- The class coerces additive indices to a multiplicative type tag. Specify
    -- the untagged formula without unfolding castHom or its multiplicativity proof.
    change (-1 : ℤˣ) ^ ZMod.castHom
        (even_iff_two_dvd.mp (Fact.out : Even n)) (ZMod 2) q =
      -((-1 : ℤˣ) ^ ZMod.castHom
        (even_iff_two_dvd.mp (Fact.out : Even n)) (ZMod 2) (q + 1))
    simp only [map_add, map_one, uzpow_add, uzpow_one, mul_neg, mul_one, neg_neg]

/-- The cyclic tensor sign is computed by reducing the degree modulo two. -/
theorem ε_down_zmod (n : ℕ) [Fact (Even n)] (p : ZMod n) :
    (down (ZMod n)).ε p =
      (-1 : ℤˣ) ^ ZMod.castHom (even_iff_two_dvd.mp (Fact.out : Even n)) (ZMod 2) p :=
  (rfl)

/-- Evenness is exactly the obstruction to the standard additive tensor signs
on a cyclic chain shape. -/
theorem nonempty_tensorSigns_down_zmod_iff (n : ℕ) :
    Nonempty (down (ZMod n)).TensorSigns ↔ Even n := by
  constructor
  · rintro ⟨h⟩
    let := h
    exact even_of_tensorSigns_down_zmod n
  · intro h
    let : Fact (Even n) := ⟨h⟩
    exact ⟨inferInstance⟩

/-- Koszul interchange for even cyclic chain gradings. Its sign on bidegree
`(p, q)` is the tensor-sign character evaluated at `p*q`. -/
instance totalComplexShapeSymmetryDownZMod (n : ℕ) [Fact (Even n)] :
    TotalComplexShapeSymmetry (down (ZMod n)) (down (ZMod n)) (down (ZMod n)) where
  symm p q := add_comm q p
  σ p q := (down (ZMod n)).ε (p * q)
  σ_ε₁ := by
    intro p p' hp q
    obtain rfl : p' + 1 = p := hp
    simp only [ε₁_def, ε₂_def, mul_one, add_mul, one_mul, ε_add]
    ac_rfl
  σ_ε₂ := by
    intro p q q' hq
    obtain rfl : q' + 1 = q := hq
    simp only [ε₁_def, ε₂_def, one_mul, mul_add, mul_one, ε_add]
    rw [mul_assoc, Int.units_mul_self, mul_one]

/-- The cyclic interchange sign is the tensor-sign character at the product
of the degrees, not the character at the first degree alone. -/
@[simp]
theorem σ_down_zmod (n : ℕ) [Fact (Even n)] (p q : ZMod n) :
    σ (down (ZMod n)) (down (ZMod n)) (down (ZMod n)) p q =
      (down (ZMod n)).ε (p * q) :=
  (rfl)

/-- Interchanging twice uses the same Koszul sign in either order. -/
instance totalComplexShapeSymmetrySymmetryDownZMod (n : ℕ) [Fact (Even n)] :
    TotalComplexShapeSymmetrySymmetry
      (down (ZMod n)) (down (ZMod n)) (down (ZMod n)) where
  σ_symm p q := congrArg (down (ZMod n)).ε (mul_comm q p)

end ComplexShape
