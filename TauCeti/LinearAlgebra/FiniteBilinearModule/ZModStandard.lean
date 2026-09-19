/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AddCircle
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Cyclic

/-!
# The standard finite bilinear and quadratic modules on `ℤ/m`

The cyclic group `ℤ/m` carries a canonical `ℚ/ℤ`-valued pairing

```text
b(x, y) = xy / m,
```

obtained from the injection `ZMod.toRatAddCircle` of `ℤ/m` onto the `m`-torsion of `ℚ/ℤ`.  It is
symmetric and nondegenerate, and it is the discriminant pairing of the rank-one lattice whose
Gram matrix is `(m)`.

When `m` is even this pairing is the polar form of the quadratic map

```text
q(x) = x² / (2m),
```

the half-norm of the same rank-one lattice.  Evenness is exactly the condition for `q` to be
well defined: replacing an integer lift `a` by `a + km` changes `a²` by `2akm + k²m²`, which
divided by `2m` is `ak + k²m/2`, an integer for all `a` and `k` precisely when `m` is even.  The
quadratic map is therefore constructed from the
cyclic presentation `TauCeti.FiniteQuadraticModule.cyclic`, whose two torsion hypotheses hold
for the generator value `1 / (2m)` exactly when `m` is even and `m ≠ 0`.

These are the alphabets in which a code over `ℤ/m` becomes a subgroup of a discriminant module:
the pairing of two words is the dot product of the words divided by `m`, and the quadratic value
of a word is the sum of the squares of its coordinate lifts divided by `2m`.

## Main declarations

* `TauCeti.FiniteBilinearModule.zmodStandard`: the pairing `xy / m` on `ℤ/m`.
* `TauCeti.FiniteBilinearModule.isNondegenerate_zmodStandard`: that pairing is nondegenerate.
* `TauCeti.FiniteQuadraticModule.zmodStandard`: for even `m`, the quadratic map `x² / (2m)`
  on `ℤ/m`, whose polar pairing is the standard one.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1 and
  §1.8, where these are the cyclic discriminant forms of the rank-one lattices.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3.
* W. Ebeling, *Lattices and Codes*, §§1.2–1.3.
-/

public section

namespace TauCeti

namespace FiniteBilinearModule

variable (m : ℕ) [NeZero m]

/-- **The standard finite bilinear module on `ℤ/m`**, with pairing `b(x, y) = xy / m`.

It is the discriminant form of the rank-one lattice with Gram matrix `(m)`, and the alphabet in
which an additive code over `ℤ/m` is a subgroup of a discriminant module.

Reducible, as `TauCeti.FiniteBilinearModule.coordinatePower` is, so that its carrier is the type
`ℤ/m` itself and additive codes are directly subgroups of its coordinate powers. -/
abbrev zmodStandard : FiniteBilinearModule where
  carrier := ZMod m
  pairing := LinearMap.toAddMonoidHom'.comp
    ((LinearMap.mul ℤ (ZMod m)).compr₂ (ZMod.toRatAddCircle m).toIntLinearMap).toAddMonoidHom
  pairing_comm x y := congrArg (ZMod.toRatAddCircle m) (mul_comm x y)

/-- The standard pairing of two residues is the image of their product under the injection of
`ℤ/m` into `ℚ/ℤ`. -/
@[simp]
theorem zmodStandard_pairing (x y : ZMod m) :
    (zmodStandard m).pairing x y = ZMod.toRatAddCircle m (x * y) := (rfl)

/-- The standard pairing of two residues, computed on integer lifts. -/
theorem zmodStandard_pairing_intCast (j k : ℤ) :
    (zmodStandard m).pairing (j : ZMod m) (k : ZMod m) =
      ((j * k / m : ℚ) : AddCircle (1 : ℚ)) := by
  have h : ((j * k : ℤ) : ℚ) / (m : ℚ) = (j : ℚ) * (k : ℚ) / (m : ℚ) := by push_cast; ring
  rw [zmodStandard_pairing, ← Int.cast_mul, ZMod.toRatAddCircle_intCast, h]

/-- The standard pairing of two residues, computed on canonical representatives. -/
theorem zmodStandard_pairing_val (x y : ZMod m) :
    (zmodStandard m).pairing x y = ((x.val * y.val / m : ℚ) : AddCircle (1 : ℚ)) := by
  have h : ((x.val * y.val : ℕ) : ℚ) / (m : ℚ) = (x.val : ℚ) * (y.val : ℚ) / (m : ℚ) := by
    push_cast; ring
  conv_lhs => rw [← ZMod.natCast_rightInverse x, ← ZMod.natCast_rightInverse y]
  rw [zmodStandard_pairing, ← Nat.cast_mul, ZMod.toRatAddCircle_natCast, h]

/-- Two residues are orthogonal for the standard pairing exactly when their product vanishes. -/
@[simp]
theorem zmodStandard_pairing_eq_zero_iff (x y : ZMod m) :
    (zmodStandard m).pairing x y = 0 ↔ x * y = 0 := by
  rw [zmodStandard_pairing, ZMod.toRatAddCircle_eq_zero_iff]

/-- The standard pairing on `ℤ/m` is nondegenerate: pairing with the generator `1` recovers the
residue. -/
theorem isNondegenerate_zmodStandard : (zmodStandard m).IsNondegenerate := by
  -- Pairing with the generator `1` is, by construction, the injection `ZMod.toRatAddCircle`.
  -- The auxiliary statement is phrased on `ZMod m`, which is the carrier of `zmodStandard m`.
  have key : ∀ x y : ZMod m, (zmodStandard m).pairing x = (zmodStandard m).pairing y → x = y := by
    intro x y hxy
    have h : ZMod.toRatAddCircle m (x * 1) = ZMod.toRatAddCircle m (y * 1) :=
      DFunLike.congr_fun hxy (1 : ZMod m)
    simpa using ZMod.toRatAddCircle_injective m h
  exact (zmodStandard m).isNondegenerate_of_injective key

end FiniteBilinearModule

namespace FiniteQuadraticModule

variable (m : ℕ) [NeZero m] (hm : Even m)

/-- The quadratic map `x ↦ x² / (2m)` on `ℤ/m`, defined for even `m`.

Evenness is exactly what makes the value of the generator well defined modulo `m`: the two
torsion conditions of the cyclic presentation ask that `m²/(2m) = m/2` and `2m/(2m) = 1` be
integers. -/
noncomputable def zmodStandardMap : QuadraticMap ℤ (ZMod m) (AddCircle (1 : ℚ)) :=
  cyclicMap m (((1 / (2 * m) : ℚ)) : AddCircle (1 : ℚ))
    (by
      have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
      obtain ⟨k, hk⟩ := hm
      have hk' : (m : ℚ) = (k : ℚ) + (k : ℚ) := by exact_mod_cast hk
      refine AddCircle.zsmul_coe_eq_zero (c := (k : ℤ)) ?_
      have key : ((((m : ℤ) * (m : ℤ) : ℤ)) : ℚ) * (1 / (2 * (m : ℚ))) = (m : ℚ) / 2 := by
        push_cast
        field_simp
      rw [key, hk']
      push_cast
      ring)
    (by
      have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
      refine AddCircle.zsmul_coe_eq_zero (c := 1) ?_
      push_cast
      field_simp)

/-- The standard quadratic value on the reduction of an integer. -/
@[simp]
theorem zmodStandardMap_intCast (k : ℤ) :
    zmodStandardMap m hm (k : ZMod m) = ((k ^ 2 / (2 * m) : ℚ) : AddCircle (1 : ℚ)) := by
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  unfold zmodStandardMap
  rw [cyclicMap_intCast, ← AddCircle.coe_zsmul]
  congr 1
  rw [zsmul_eq_mul]
  push_cast
  field_simp

/-- The standard quadratic value on the canonical representative of a residue. -/
theorem zmodStandardMap_val (x : ZMod m) :
    zmodStandardMap m hm x = ((x.val ^ 2 / (2 * m) : ℚ) : AddCircle (1 : ℚ)) := by
  have hcast : ((x.val : ℕ) : ZMod m) = ((x.val : ℤ) : ZMod m) := by push_cast; ring
  have h : (((x.val : ℤ) : ℚ)) ^ 2 / (2 * m) = ((x.val : ℚ)) ^ 2 / (2 * m) := by push_cast; ring
  conv_lhs => rw [← ZMod.natCast_rightInverse x, hcast]
  rw [zmodStandardMap_intCast, h]

/-- The polar form of `x² / (2m)` is the standard pairing `xy / m`. -/
theorem polar_zmodStandardMap (x y : ZMod m) :
    QuadraticMap.polar (zmodStandardMap m hm) x y =
      (FiniteBilinearModule.zmodStandard m).pairing x y := by
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective y
  unfold zmodStandardMap
  rw [polar_cyclicMap_intCast, FiniteBilinearModule.zmodStandard_pairing_intCast,
    ← AddCircle.coe_zsmul]
  congr 1
  rw [zsmul_eq_mul]
  push_cast
  field_simp

/-- **The standard finite quadratic module on `ℤ/m` for even `m`**, with quadratic map
`q(x) = x² / (2m)`.

Its underlying bilinear module is the standard one, so the pairing of residues is `xy / m`
whether or not `m` is even.  It is the discriminant form of the rank-one lattice with Gram
matrix `(m)` in the half-norm convention `q(x) = b(x, x) / 2`.

Reducible, as the bilinear alphabet and the coordinate powers are, so that its carrier is the
type `ℤ/m` itself. -/
noncomputable abbrev zmodStandard : FiniteQuadraticModule where
  toFiniteBilinearModule := FiniteBilinearModule.zmodStandard m
  quadratic := zmodStandardMap m hm
  polar_eq_pairing' := polar_zmodStandardMap m hm

/-- The quadratic map of the standard quadratic module is `x ↦ x² / (2m)`. -/
@[simp]
theorem zmodStandard_quadratic (x : ZMod m) :
    (zmodStandard m hm).quadratic x = zmodStandardMap m hm x := (rfl)

/-- The polar bilinear module of the standard quadratic module is the standard bilinear
module. -/
@[simp]
theorem zmodStandard_toFiniteBilinearModule :
    (zmodStandard m hm).toFiniteBilinearModule = FiniteBilinearModule.zmodStandard m := (rfl)

/-- The standard quadratic module on `ℤ/m` is nondegenerate. -/
theorem isNondegenerate_zmodStandard : (zmodStandard m hm).IsNondegenerate :=
  FiniteBilinearModule.isNondegenerate_zmodStandard m

end FiniteQuadraticModule

end TauCeti
