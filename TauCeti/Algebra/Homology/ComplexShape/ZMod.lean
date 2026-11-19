/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.ZMod.Basic

/-!
# Tensor signs for cyclically graded complexes

Complexes graded by `ZMod n`, with differential `d : C_p ⟶ C_{p-1}` (`ComplexShape.down`) or
`d : C_p ⟶ C_{p+1}` (`ComplexShape.up`), have a tensor product with the Koszul differential
`d (x ⊗ y) = d x ⊗ y + (-1)^|x| x ⊗ d y` when `n` is even, and the sign `(-1)^|x|` is then well
defined. This file supplies the corresponding `ComplexShape.TensorSigns` datum, which Mathlib
provides only for `ComplexShape.down ℕ` and `ComplexShape.up ℤ`. Through Mathlib's
`TotalComplexShape` instance it gives the tensor product of cyclically graded complexes, Mathlib's
monoidal structure `HomologicalComplex.monoidalCategory` and the Künneth map
`HomologicalComplex.homologyKunneth` on these shapes; over a field the Künneth map is then an
isomorphism (`HomologicalComplex.isIso_homologyKunneth_of_isSplitMono_of_isSplitEpi`). Periodic
Floer complexes, graded by `ZMod 8` or `ZMod 4` once an absolute lift of their relative grading is
chosen, are the motivating examples.

The sign is forced. For every tensor sign datum on `ComplexShape.down (ZMod n)` or
`ComplexShape.up (ZMod n)`, the sign of the class of an integer `k` is `(-1)^k`, since the sign is
`1` in degree `0` and changes along each differential. Hence there is at most one such datum, and
none when `n` is odd: the class of `n` is `0`, whose sign is `1`, while `(-1)^n = -1`. For even `n`
the sign `(-1)^p` is well defined on `p : ZMod n`, and it is a tensor sign datum. So such a datum
exists exactly when `2 ∣ n`.

The `TotalComplexShapeSymmetry` instances carry the Koszul sign `(-1)^(p * q)` in bidegree
`(p, q)`, again well defined for even `n`, and are compatible with their own transposes
(`TotalComplexShapeSymmetrySymmetry`). They give Mathlib's isomorphisms
`HomologicalComplex₂.totalFlipIso` between the total complex of a bicomplex and that of its flip;
on the bicomplex of a tensor product this is `x ⊗ y ↦ (-1)^(|x| * |y|) y ⊗ x`. These are the
cyclic analogues of Mathlib's instance for `ComplexShape.up ℤ` and of
`HomologicalComplex₂.totalComplexShapeSymmetryDownNat`.

## Main definitions and results

* `ComplexShape.tensorSignsDownZMod`, `ComplexShape.tensorSignsUpZMod`: the tensor signs on the
  cyclic shapes, for `n` even.
* `ComplexShape.ε_down_zmod_intCast`, `ComplexShape.ε_up_zmod_intCast`: every tensor sign datum
  on a cyclic shape has sign `Int.negOnePow k` at the class of `k : ℤ`.
* `ComplexShape.two_dvd_of_tensorSigns_down_zmod`, `ComplexShape.two_dvd_of_tensorSigns_up_zmod`:
  no tensor sign datum exists on a cyclic shape of odd order.
* `ComplexShape.nonempty_tensorSigns_down_zmod_iff`, `ComplexShape.nonempty_tensorSigns_up_zmod_iff`
  and the `Subsingleton` instances: a tensor sign datum exists exactly when `2 ∣ n`, and it is
  unique.
* `ComplexShape.totalComplexShapeSymmetryDownZMod`, `ComplexShape.totalComplexShapeSymmetryUpZMod`:
  the Koszul symmetry signs, computed by `ComplexShape.σ_down_zmod_intCast` and
  `ComplexShape.σ_up_zmod_intCast`.
-/

public section

namespace ComplexShape

variable {n : ℕ}

/-- A sign function on `ZMod n` which is `1` at `0` and changes sign at each step `p ↦ p + 1` is
`Int.negOnePow k` at the class of `k`. -/
private lemma eq_negOnePow_of_add_one (e : ZMod n → ℤˣ) (h₀ : e 0 = 1)
    (h : ∀ p, e (p + 1) = -e p) (k : ℤ) : e k = k.negOnePow := by
  induction k using Int.induction_on with
  | zero => simpa using h₀
  | succ k ih => rw [Int.cast_add, Int.cast_one, h, ih, Int.negOnePow_succ]
  | pred k ih =>
    have hk := h ((-(k : ℤ) - 1 : ℤ) : ZMod n)
    rw [Int.cast_sub, Int.cast_one, sub_add_cancel, ← Int.cast_one, ← Int.cast_sub, ih] at hk
    rw [Int.negOnePow_sub, Int.negOnePow_one, mul_neg_one, hk, neg_neg]

section Down

variable [TensorSigns (down (ZMod n))]

/-- The sign of a tensor sign datum on `ComplexShape.down (ZMod n)` at the class of an integer
`k` is `(-1)^k`. -/
@[simp]
theorem ε_down_zmod_intCast (k : ℤ) : (down (ZMod n)).ε k = k.negOnePow :=
  eq_negOnePow_of_add_one _ (ε_zero _) (fun _ ↦ neg_eq_iff_eq_neg.mp (ε_succ _ rfl).symm) k

/-- The sign of a tensor sign datum on `ComplexShape.down (ZMod n)` at the class of a natural
number `k` is `(-1)^k`. -/
@[simp]
theorem ε_down_zmod_natCast (k : ℕ) : (down (ZMod n)).ε k = (-1) ^ k := by
  rw [← Int.cast_natCast, ε_down_zmod_intCast, Int.negOnePow_def, zpow_natCast]

/-- The sign of a tensor sign datum on `ComplexShape.down (ZMod n)` at a numeral `k` is
`(-1)^k`. -/
@[simp]
theorem ε_down_zmod_ofNat (k : ℕ) [k.AtLeastTwo] :
    (down (ZMod n)).ε (no_index (OfNat.ofNat k) : ZMod n) = (-1) ^ (OfNat.ofNat k : ℕ) := by
  have h := ε_down_zmod_natCast (n := n) (OfNat.ofNat k)
  rwa [Nat.cast_ofNat] at h

/-- The sign of a tensor sign datum on `ComplexShape.down (ZMod n)` at `1` is `-1`. -/
@[simp]
theorem ε_down_zmod_one : (down (ZMod n)).ε 1 = -1 := by
  simpa using ε_down_zmod_natCast (n := n) 1

/-- The sign of a tensor sign datum on `ComplexShape.down (ZMod n)` at `p` is `(-1)^k` for the
integer representative `k` of `p`. -/
theorem ε_down_zmod (p : ZMod n) : (down (ZMod n)).ε p = (p.cast : ℤ).negOnePow := by
  have h := ε_down_zmod_intCast (n := n) (p.cast : ℤ)
  rwa [ZMod.intCast_zmod_cast] at h

end Down

/-- **There are no tensor signs in odd order.** A tensor sign datum on
`ComplexShape.down (ZMod n)` forces `n` to be even. -/
theorem two_dvd_of_tensorSigns_down_zmod [TensorSigns (down (ZMod n))] : 2 ∣ n := by
  have h : (down (ZMod n)).ε (n : ℕ) = (-1) ^ n := ε_down_zmod_natCast n
  rw [ZMod.natCast_self, ε_zero, eq_comm, neg_one_pow_eq_one_iff_even (by decide)] at h
  exact h.two_dvd

/-- A tensor sign datum on `ComplexShape.down (ZMod n)` is unique. -/
instance : Subsingleton (TensorSigns (down (ZMod n))) where
  allEq s t := by
    have h (p : ZMod n) : s.ε' p = t.ε' p :=
      (@ε_down_zmod n s p).trans (@ε_down_zmod n t p).symm
    cases s; cases t
    congr
    exact MonoidHom.ext h

section Up

variable [TensorSigns (up (ZMod n))]

/-- The sign of a tensor sign datum on `ComplexShape.up (ZMod n)` at the class of an integer `k`
is `(-1)^k`. -/
@[simp]
theorem ε_up_zmod_intCast (k : ℤ) : (up (ZMod n)).ε k = k.negOnePow :=
  eq_negOnePow_of_add_one _ (ε_zero _) (fun _ ↦ ε_succ _ rfl) k

/-- The sign of a tensor sign datum on `ComplexShape.up (ZMod n)` at the class of a natural number
`k` is `(-1)^k`. -/
@[simp]
theorem ε_up_zmod_natCast (k : ℕ) : (up (ZMod n)).ε k = (-1) ^ k := by
  rw [← Int.cast_natCast, ε_up_zmod_intCast, Int.negOnePow_def, zpow_natCast]

/-- The sign of a tensor sign datum on `ComplexShape.up (ZMod n)` at a numeral `k` is
`(-1)^k`. -/
@[simp]
theorem ε_up_zmod_ofNat (k : ℕ) [k.AtLeastTwo] :
    (up (ZMod n)).ε (no_index (OfNat.ofNat k) : ZMod n) = (-1) ^ (OfNat.ofNat k : ℕ) := by
  have h := ε_up_zmod_natCast (n := n) (OfNat.ofNat k)
  rwa [Nat.cast_ofNat] at h

/-- The sign of a tensor sign datum on `ComplexShape.up (ZMod n)` at `1` is `-1`. -/
@[simp]
theorem ε_up_zmod_one : (up (ZMod n)).ε 1 = -1 := by
  simpa using ε_up_zmod_natCast (n := n) 1

/-- The sign of a tensor sign datum on `ComplexShape.up (ZMod n)` at `p` is `(-1)^k` for the
integer representative `k` of `p`. -/
theorem ε_up_zmod (p : ZMod n) : (up (ZMod n)).ε p = (p.cast : ℤ).negOnePow := by
  have h := ε_up_zmod_intCast (n := n) (p.cast : ℤ)
  rwa [ZMod.intCast_zmod_cast] at h

end Up

/-- **There are no tensor signs in odd order.** A tensor sign datum on `ComplexShape.up (ZMod n)`
forces `n` to be even. -/
theorem two_dvd_of_tensorSigns_up_zmod [TensorSigns (up (ZMod n))] : 2 ∣ n := by
  have h : (up (ZMod n)).ε (n : ℕ) = (-1) ^ n := ε_up_zmod_natCast n
  rw [ZMod.natCast_self, ε_zero, eq_comm, neg_one_pow_eq_one_iff_even (by decide)] at h
  exact h.two_dvd

/-- A tensor sign datum on `ComplexShape.up (ZMod n)` is unique. -/
instance : Subsingleton (TensorSigns (up (ZMod n))) where
  allEq s t := by
    have h (p : ZMod n) : s.ε' p = t.ε' p :=
      (@ε_up_zmod n s p).trans (@ε_up_zmod n t p).symm
    cases s; cases t
    congr
    exact MonoidHom.ext h

section Even

variable [Fact (2 ∣ n)]

/-- The sign `(-1)^p`, read through `ZMod n → ZMod 2`, changes at each step `p ↦ p + 1`. -/
private lemma uzpow_castHom_add_one (p : ZMod n) :
    (-1 : ℤˣ) ^ ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) (p + 1) =
      -(-1 : ℤˣ) ^ ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) p := by
  rw [map_add, map_one, uzpow_add, uzpow_one, mul_neg_one]

/-- The tensor signs on `ComplexShape.down (ZMod n)` for even `n`: the sign of `p` is `(-1)^p`,
read through the reduction `ZMod n → ZMod 2`. They are computed by
`ComplexShape.ε_down_zmod_intCast`. -/
instance tensorSignsDownZMod : TensorSigns (down (ZMod n)) where
  ε' := MonoidHom.mk' (fun p ↦ (-1 : ℤˣ) ^ ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) p.toAdd)
    (fun p q ↦ by simp only [toAdd_mul, map_add, uzpow_add])
  rel_add p q r (hpq : q + 1 = p) := by rw [down_Rel, ← hpq, add_right_comm]
  add_rel p q r (hpq : q + 1 = p) := by rw [down_Rel, ← hpq, add_assoc]
  ε'_succ := by
    rintro _ q rfl
    exact neg_eq_iff_eq_neg.mp (uzpow_castHom_add_one q).symm

/-- The tensor signs on `ComplexShape.up (ZMod n)` for even `n`: the sign of `p` is `(-1)^p`,
read through the reduction `ZMod n → ZMod 2`. They are computed by
`ComplexShape.ε_up_zmod_intCast`. -/
instance tensorSignsUpZMod : TensorSigns (up (ZMod n)) where
  ε' := MonoidHom.mk' (fun p ↦ (-1 : ℤˣ) ^ ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) p.toAdd)
    (fun p q ↦ by simp only [toAdd_mul, map_add, uzpow_add])
  rel_add p q r (hpq : p + 1 = q) := by rw [up_Rel, ← hpq, add_right_comm]
  add_rel p q r (hpq : p + 1 = q) := by rw [up_Rel, ← hpq, add_assoc]
  ε'_succ := by
    rintro p _ rfl
    exact uzpow_castHom_add_one p

/-- The Koszul sign `(-1)^(p * q)`, read through `ZMod n → ZMod 2`, changes by `(-1)^q` at each
step `p ↦ p + 1`. -/
private lemma uzpow_castHom_add_one_mul (p q : ZMod n) :
    (-1 : ℤˣ) ^ (ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) (p + 1) *
        ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) q) =
      (-1 : ℤˣ) ^ ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) q *
        (-1 : ℤˣ) ^ (ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) p *
          ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) q) := by
  rw [map_add, map_one, add_mul, one_mul, uzpow_add, mul_comm]

/-- The Koszul sign `(-1)^(p * q)`, read through `ZMod n → ZMod 2`, changes by `(-1)^p` at each
step `q ↦ q + 1`. -/
private lemma uzpow_mul_castHom_add_one_mul (p q : ZMod n) :
    (-1 : ℤˣ) ^ (ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) p *
        ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) (q + 1)) *
          (-1 : ℤˣ) ^ ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) p =
      (-1 : ℤˣ) ^ (ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) p *
        ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) q) := by
  rw [map_add, map_one, mul_add, mul_one, uzpow_add, mul_assoc, Int.units_mul_self, mul_one]

/-- `uzpow_castHom_add_one_mul`, solved for the sign at `(p, q)`. -/
private lemma uzpow_castHom_mul_eq (p q : ZMod n) :
    (-1 : ℤˣ) ^ (ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) p *
        ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) q) =
      (-1 : ℤˣ) ^ ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) q *
        (-1 : ℤˣ) ^ (ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) (p + 1) *
          ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) q) := by
  rw [uzpow_castHom_add_one_mul, ← mul_assoc, Int.units_mul_self, one_mul]

/-- `uzpow_mul_castHom_add_one_mul`, solved for the sign at `(p, q + 1)`. -/
private lemma uzpow_mul_castHom_mul_eq (p q : ZMod n) :
    (-1 : ℤˣ) ^ (ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) p *
        ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) q) *
          (-1 : ℤˣ) ^ ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) p =
      (-1 : ℤˣ) ^ (ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) p *
        ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) (q + 1)) := by
  rw [← uzpow_mul_castHom_add_one_mul, mul_assoc, Int.units_mul_self, mul_one]

/-- The Koszul symmetry of the total complex of a bicomplex graded by `ZMod n` with `n` even,
with differentials of `ComplexShape.down (ZMod n)`: the sign in bidegree `(p, q)` is
`(-1)^(p * q)` (`ComplexShape.σ_down_zmod_intCast`). -/
instance totalComplexShapeSymmetryDownZMod :
    TotalComplexShapeSymmetry (down (ZMod n)) (down (ZMod n)) (down (ZMod n)) where
  symm p q := add_comm q p
  σ p q := (-1 : ℤˣ) ^ (ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) p *
    ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) q)
  σ_ε₁ := by
    rintro _ p rfl q
    exact (mul_one _).trans (uzpow_castHom_add_one_mul p q)
  σ_ε₂ := by
    rintro p _ q rfl
    exact (uzpow_mul_castHom_add_one_mul p q).trans (one_mul _).symm

/-- The Koszul symmetry of the total complex of a bicomplex graded by `ZMod n` with `n` even,
with differentials of `ComplexShape.up (ZMod n)`: the sign in bidegree `(p, q)` is
`(-1)^(p * q)` (`ComplexShape.σ_up_zmod_intCast`). -/
instance totalComplexShapeSymmetryUpZMod :
    TotalComplexShapeSymmetry (up (ZMod n)) (up (ZMod n)) (up (ZMod n)) where
  symm p q := add_comm q p
  σ p q := (-1 : ℤˣ) ^ (ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) p *
    ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) q)
  σ_ε₁ := by
    rintro p _ rfl q
    exact (mul_one _).trans (uzpow_castHom_mul_eq p q)
  σ_ε₂ := by
    rintro p q _ rfl
    exact (uzpow_mul_castHom_mul_eq p q).trans (one_mul _).symm

/-- The Koszul symmetry signs on `ComplexShape.down (ZMod n)` are symmetric in the two
factors. -/
instance : TotalComplexShapeSymmetrySymmetry (down (ZMod n)) (down (ZMod n)) (down (ZMod n)) where
  σ_symm _ _ := congrArg ((-1 : ℤˣ) ^ ·) (mul_comm _ _)

/-- The Koszul symmetry signs on `ComplexShape.up (ZMod n)` are symmetric in the two factors. -/
instance : TotalComplexShapeSymmetrySymmetry (up (ZMod n)) (up (ZMod n)) (up (ZMod n)) where
  σ_symm _ _ := congrArg ((-1 : ℤˣ) ^ ·) (mul_comm _ _)

/-- The Koszul sign `(-1)^(p * q)`, read through `ZMod n → ZMod 2`, at the classes of two
integers. -/
private lemma uzpow_castHom_intCast_mul (k l : ℤ) :
    (-1 : ℤˣ) ^ (ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) k *
      ZMod.castHom (Fact.out : 2 ∣ n) (ZMod 2) l) = (k * l).negOnePow := by
  rw [map_intCast, map_intCast, ← Int.cast_mul, uzpow_intCast, Int.negOnePow_def]

/-- The Koszul symmetry sign on `ComplexShape.down (ZMod n)` at the classes of integers `k` and
`l` is `(-1)^(k * l)`. -/
@[simp]
theorem σ_down_zmod_intCast (k l : ℤ) :
    σ (down (ZMod n)) (down (ZMod n)) (down (ZMod n)) k l = (k * l).negOnePow :=
  uzpow_castHom_intCast_mul k l

/-- The Koszul symmetry sign on `ComplexShape.down (ZMod n)` at the classes of natural numbers `k`
and `l` is `(-1)^(k * l)`. -/
@[simp]
theorem σ_down_zmod_natCast (k l : ℕ) :
    σ (down (ZMod n)) (down (ZMod n)) (down (ZMod n)) k l = (-1) ^ (k * l) := by
  rw [← Int.cast_natCast, ← Int.cast_natCast (R := ZMod n) l, σ_down_zmod_intCast, ← Nat.cast_mul,
    Int.negOnePow_def, zpow_natCast]

/-- The Koszul symmetry sign on `ComplexShape.down (ZMod n)` at `(p, q)` is `(-1)^(k * l)` for the
integer representatives `k` and `l` of `p` and `q`. -/
theorem σ_down_zmod (p q : ZMod n) :
    σ (down (ZMod n)) (down (ZMod n)) (down (ZMod n)) p q =
      ((p.cast : ℤ) * (q.cast : ℤ)).negOnePow := by
  have h := σ_down_zmod_intCast (n := n) (p.cast : ℤ) (q.cast : ℤ)
  rwa [ZMod.intCast_zmod_cast, ZMod.intCast_zmod_cast] at h

/-- The Koszul symmetry sign on `ComplexShape.up (ZMod n)` at the classes of integers `k` and `l`
is `(-1)^(k * l)`. -/
@[simp]
theorem σ_up_zmod_intCast (k l : ℤ) :
    σ (up (ZMod n)) (up (ZMod n)) (up (ZMod n)) k l = (k * l).negOnePow :=
  uzpow_castHom_intCast_mul k l

/-- The Koszul symmetry sign on `ComplexShape.up (ZMod n)` at the classes of natural numbers `k`
and `l` is `(-1)^(k * l)`. -/
@[simp]
theorem σ_up_zmod_natCast (k l : ℕ) :
    σ (up (ZMod n)) (up (ZMod n)) (up (ZMod n)) k l = (-1) ^ (k * l) := by
  rw [← Int.cast_natCast, ← Int.cast_natCast (R := ZMod n) l, σ_up_zmod_intCast, ← Nat.cast_mul,
    Int.negOnePow_def, zpow_natCast]

/-- The Koszul symmetry sign on `ComplexShape.up (ZMod n)` at `(p, q)` is `(-1)^(k * l)` for the
integer representatives `k` and `l` of `p` and `q`. -/
theorem σ_up_zmod (p q : ZMod n) :
    σ (up (ZMod n)) (up (ZMod n)) (up (ZMod n)) p q =
      ((p.cast : ℤ) * (q.cast : ℤ)).negOnePow := by
  have h := σ_up_zmod_intCast (n := n) (p.cast : ℤ) (q.cast : ℤ)
  rwa [ZMod.intCast_zmod_cast, ZMod.intCast_zmod_cast] at h

end Even

/-- **Tensor signs on a cyclic shape exist exactly in even order.** -/
theorem nonempty_tensorSigns_down_zmod_iff : Nonempty (TensorSigns (down (ZMod n))) ↔ 2 ∣ n :=
  ⟨fun ⟨_⟩ ↦ two_dvd_of_tensorSigns_down_zmod, fun h ↦ have : Fact (2 ∣ n) := ⟨h⟩; ⟨inferInstance⟩⟩

/-- **Tensor signs on a cyclic shape exist exactly in even order.** -/
theorem nonempty_tensorSigns_up_zmod_iff : Nonempty (TensorSigns (up (ZMod n))) ↔ 2 ∣ n :=
  ⟨fun ⟨_⟩ ↦ two_dvd_of_tensorSigns_up_zmod, fun h ↦ have : Fact (2 ∣ n) := ⟨h⟩; ⟨inferInstance⟩⟩

end ComplexShape
