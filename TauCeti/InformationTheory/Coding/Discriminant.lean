/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Binary.Basic
public import TauCeti.InformationTheory.Coding.EuclideanDual
public import TauCeti.LinearAlgebra.FiniteBilinearModule.CoordinatePower
public import TauCeti.LinearAlgebra.FiniteBilinearModule.ZModStandard

/-!
# Codes over `ℤ/m` as subgroups of a discriminant module

Words over `ℤ/m` are elements of the coordinate power of the standard alphabet
`TauCeti.FiniteBilinearModule.zmodStandard`, whose pairing is `xy / m`.  Summing that pairing
over the coordinates gives

```text
b(x, y) = (x ⬝ᵥ y) / m,
```

so an additive code and the codes orthogonal to it for the `ℤ/m` dot product are literally a
subgroup of a finite bilinear module and its orthogonal complement.  In particular a code is
self-orthogonal exactly when it is isotropic, and self-dual exactly when it is Lagrangian.

When `m` is even the coordinate power of the quadratic alphabet adds the value

```text
q(x) = (∑ i, lift (xᵢ)²) / (2m),
```

independent of the chosen integer lifts because each coordinate value is.  At `m = 2` the square
of a lift is the lift, so `q(x)` is a quarter of the Hamming weight and quadratic isotropy of a
binary code is exactly double evenness.  These are the identifications through which a code
becomes an isotropic subgroup of the discriminant module of a lattice.

## Main declarations

* `TauCeti.coordinatePower_zmodStandard_pairing`: the coordinate pairing over `ℤ/m` is the dot
  product divided by `m`.
* `TauCeti.orthogonalComplement_coordinatePower_zmodStandard`: the orthogonal complement of a
  code is its Euclidean dual.
* `TauCeti.isIsotropic_coordinatePower_zmodStandard_iff_le_euclideanDual` and
  `TauCeti.isLagrangian_coordinatePower_zmodStandard_iff`: isotropy is self-orthogonality and
  the Lagrangian condition is self-duality.
* `TauCeti.coordinatePower_zmodStandard_quadratic`: the coordinate quadratic value over an even
  `ℤ/m` is the sum of the squares of the coordinate lifts divided by `2m`.
* `TauCeti.isIsotropic_coordinatePower_zmodStandard_two_iff_isDoublyEven`: over `ℤ/2` quadratic
  isotropy is double evenness.

## References

* W. Ebeling, *Lattices and Codes*, §§1.2–1.3, for binary codes, their weights, and the
  quadratic form `wt / 4` modulo `ℤ`.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3 and
  Chapter 7, §§8–9, for codes as glue groups in discriminant coordinates.
-/

public section

namespace TauCeti

open Matrix

variable {ι : Type*} [Fintype ι] (m : ℕ) [NeZero m]

/-! ## The bilinear coordinate power -/

/-- The pairing of two words over `ℤ/m` is their dot product, divided by `m`. -/
theorem coordinatePower_zmodStandard_pairing (x y : ι → ZMod m) :
    ((FiniteBilinearModule.zmodStandard m).coordinatePower ι).pairing x y =
      ZMod.toRatAddCircle m (x ⬝ᵥ y) := by
  rw [FiniteBilinearModule.coordinatePower_pairing, dotProduct, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ FiniteBilinearModule.zmodStandard_pairing m (x i) (y i)

/-- Two words over `ℤ/m` are orthogonal for the coordinate pairing exactly when their dot
product vanishes. -/
-- Not a `simp` lemma: the coordinate power and the alphabet are both reducible, so `simp` takes
-- the left-hand side apart into the summed coordinate pairings before this could fire.
theorem coordinatePower_zmodStandard_pairing_eq_zero_iff (x y : ι → ZMod m) :
    ((FiniteBilinearModule.zmodStandard m).coordinatePower ι).pairing x y = 0 ↔ x ⬝ᵥ y = 0 := by
  rw [coordinatePower_zmodStandard_pairing, ZMod.toRatAddCircle_eq_zero_iff]

/-- The orthogonal complement of an additive code over `ℤ/m` consists of the words with zero dot
product against every codeword. -/
theorem mem_orthogonalComplement_coordinatePower_zmodStandard_iff (C : AdditiveCode (ZMod m) ι)
    (x : ι → ZMod m) :
    x ∈ ((FiniteBilinearModule.zmodStandard m).coordinatePower ι).orthogonalComplement C ↔
      ∀ y ∈ C, x ⬝ᵥ y = 0 := by
  rw [FiniteBilinearModule.mem_orthogonalComplement_iff]
  exact forall₂_congr fun y _ ↦ coordinatePower_zmodStandard_pairing_eq_zero_iff m x y

/-- **The orthogonal complement of an additive code over `ℤ/m` is its Euclidean dual.** -/
theorem orthogonalComplement_coordinatePower_zmodStandard (C : AdditiveCode (ZMod m) ι) :
    ((FiniteBilinearModule.zmodStandard m).coordinatePower ι).orthogonalComplement C =
      (AddSubgroup.toZModSubmodule m C).euclideanDual.toAddSubgroup := by
  ext x
  rw [mem_orthogonalComplement_coordinatePower_zmodStandard_iff, Submodule.mem_toAddSubgroup,
    Submodule.mem_euclideanDual']
  exact ⟨fun h y hy ↦ (dotProduct_comm x y) ▸ h y hy,
    fun h y hy ↦ (dotProduct_comm y x) ▸ h y hy⟩

/-- An additive code over `ℤ/m` is isotropic exactly when any two of its words are
orthogonal. -/
theorem isIsotropic_coordinatePower_zmodStandard_iff (C : AdditiveCode (ZMod m) ι) :
    ((FiniteBilinearModule.zmodStandard m).coordinatePower ι).IsIsotropic C ↔
      ∀ x ∈ C, ∀ y ∈ C, x ⬝ᵥ y = 0 := by
  rw [FiniteBilinearModule.isIsotropic_def]
  exact forall₂_congr fun x _ ↦ forall₂_congr fun y _ ↦
    coordinatePower_zmodStandard_pairing_eq_zero_iff m x y

/-- **Isotropy of a code over `ℤ/m` is self-orthogonality.** -/
theorem isIsotropic_coordinatePower_zmodStandard_iff_le_euclideanDual
    (C : AdditiveCode (ZMod m) ι) :
    ((FiniteBilinearModule.zmodStandard m).coordinatePower ι).IsIsotropic C ↔
      AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual := by
  rw [FiniteBilinearModule.isIsotropic_iff_le_orthogonalComplement,
    orthogonalComplement_coordinatePower_zmodStandard]
  simp only [SetLike.le_def, Submodule.mem_toAddSubgroup, AddSubgroup.mem_toZModSubmodule]

/-- **The Lagrangian condition for a code over `ℤ/m` is self-duality.** -/
theorem isLagrangian_coordinatePower_zmodStandard_iff (C : AdditiveCode (ZMod m) ι) :
    ((FiniteBilinearModule.zmodStandard m).coordinatePower ι).IsLagrangian C ↔
      AddSubgroup.toZModSubmodule m C = (AddSubgroup.toZModSubmodule m C).euclideanDual := by
  rw [FiniteBilinearModule.isLagrangian_def, orthogonalComplement_coordinatePower_zmodStandard]
  constructor
  · intro h
    ext x
    rw [AddSubgroup.mem_toZModSubmodule]
    conv_lhs => rw [h]
    rw [Submodule.mem_toAddSubgroup]
  · intro h
    ext x
    rw [Submodule.mem_toAddSubgroup, ← h, AddSubgroup.mem_toZModSubmodule]

/-! ## The quadratic coordinate power for an even modulus -/

variable (hm : Even m)

/-- The quadratic value of a word over an even `ℤ/m` is the sum of the squares of its coordinate
representatives, divided by `2m`. -/
theorem coordinatePower_zmodStandard_quadratic (x : ι → ZMod m) :
    ((FiniteQuadraticModule.zmodStandard m hm).coordinatePower ι).quadratic x =
      (((∑ i, ((x i).val : ℚ) ^ 2) / (2 * m) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [FiniteQuadraticModule.coordinatePower_quadratic, Finset.sum_div, AddCircle.coe_sum]
  exact Finset.sum_congr rfl fun i _ ↦ FiniteQuadraticModule.zmodStandardMap_val m hm (x i)

/-- The quadratic value of a word over an even `ℤ/m` is computed by any coordinatewise integer
lift: the sum of the squares of the lifts, divided by `2m`. -/
theorem coordinatePower_zmodStandard_quadratic_intCast (z : ι → ℤ) :
    ((FiniteQuadraticModule.zmodStandard m hm).coordinatePower ι).quadratic
        (fun i ↦ ((z i : ZMod m))) =
      (((∑ i, (z i : ℚ) ^ 2) / (2 * m) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [FiniteQuadraticModule.coordinatePower_quadratic, Finset.sum_div, AddCircle.coe_sum]
  exact Finset.sum_congr rfl fun i _ ↦ FiniteQuadraticModule.zmodStandardMap_intCast m hm (z i)

/-- The quadratic value of a binary word is a quarter of its Hamming weight. -/
theorem coordinatePower_zmodStandard_two_quadratic (x : ι → ZMod 2) :
    ((FiniteQuadraticModule.zmodStandard 2 even_two).coordinatePower ι).quadratic x =
      (((hammingNorm x : ℚ) / 4 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [coordinatePower_zmodStandard_quadratic]
  have hval : ∀ a : ZMod 2, ((a.val : ℚ)) ^ 2 = if a ≠ 0 then (1 : ℚ) else 0 := by
    intro a
    -- a binary residue has representative `0` or `1`, and both are their own squares
    have hrep : a.val = if a ≠ 0 then 1 else 0 := by revert a; decide
    rw [hrep]
    split <;> norm_num
  have : ∑ i, ((x i).val : ℚ) ^ 2 = (hammingNorm x : ℚ) := by
    simp only [hval, Finset.sum_boole, hammingNorm]
  rw [this]
  norm_num

/-- **Quadratic isotropy of a binary code is double evenness of its Hamming weights.** -/
theorem isIsotropic_coordinatePower_zmodStandard_two_iff (C : AdditiveCode (ZMod 2) ι) :
    ((FiniteQuadraticModule.zmodStandard 2 even_two).coordinatePower ι).IsIsotropic C ↔
      ∀ x ∈ C, 4 ∣ hammingNorm x := by
  rw [FiniteQuadraticModule.isIsotropic_def]
  refine forall₂_congr fun x _ ↦ ?_
  rw [coordinatePower_zmodStandard_two_quadratic]
  have h4 : ((4 : ℕ) : ℚ) = (4 : ℚ) := by norm_num
  rw [← h4, ← Int.cast_natCast (hammingNorm x),
    AddCircle.coe_intCast_div_natCast_eq_zero_iff (by norm_num)]
  exact Int.natCast_dvd_natCast

/-- A binary linear code is quadratically isotropic in the standard coordinate discriminant
module exactly when it is doubly even. -/
theorem isIsotropic_coordinatePower_zmodStandard_two_iff_isDoublyEven
    (C : LinearCode (ZMod 2) ι) :
    ((FiniteQuadraticModule.zmodStandard 2 even_two).coordinatePower ι).IsIsotropic
        C.toAddSubgroup ↔ BinaryCode.IsDoublyEven C := by
  simp only [isIsotropic_coordinatePower_zmodStandard_two_iff, BinaryCode.isDoublyEven_iff,
    Submodule.mem_toAddSubgroup]

end TauCeti
