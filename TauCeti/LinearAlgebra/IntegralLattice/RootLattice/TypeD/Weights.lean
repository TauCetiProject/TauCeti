/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.Dynkin

/-!
# Spinor, vector and cospinor weights of `Dₙ` in simple-root coordinates

In the Conway--Sloane checkerboard model `Dₙ = {x ∈ ℤⁿ | ∑ xᵢ even}`, the three nonzero
discriminant classes are represented by their shortest vectors

```text
s = (1/2, …, 1/2),    v = (0, …, 0, 1),    c = (1/2, …, 1/2, -1/2),
```

corresponding to the glue labels `[1]`, `[2]` and `[3]`.  The uniform root lattice
`(D n).rootLattice ht` instead uses Bourbaki simple-root coordinates `Fin n → ℚ`, related to the
checkerboard model for `4 ≤ n` by `TauCeti.DynkinType.rootLatticeIsometryCheckerboard` (with
inverse coordinate formula `TauCeti.DynkinType.rootLatticeIsometryCheckerboard_symm_apply`).

This file defines the computable simple-root vectors `typeDSpinorWeight`, `typeDVectorWeight` and
`typeDCospinorWeight` on `Fin n → ℚ` that correspond to `s`, `v` and `c`:

* `typeDSpinorWeight n` is the Bourbaki spinor fundamental weight `ϖₙ`, with coordinates
  `(j + 1) / 2` along the chain (`j + 2 < n`), `(n - 2) / 4` at `n - 2`, and `n / 4` at `n - 1`;
* `typeDVectorWeight n` is `(-α_{n-2} + α_{n-1}) / 2`, which maps to `e_{n-1} = v`;
* `typeDCospinorWeight n = typeDSpinorWeight n - typeDVectorWeight n` is the Bourbaki cospinor
  fundamental weight `ϖ_{n-1}`, swapping the two fork coordinates of `ϖₙ`.

Under `rootLatticeIsometryCheckerboard`, these three vectors map literally to `checkerboardSpinor`,
`checkerboardVector` and `checkerboardCospinor`, so they inherit their dual-carrier memberships,
simple-root pairings, squared norms `n / 4`, `1`, `n / 4`, and discriminant classes.

## Main declarations

* `TauCeti.IntegralLattice.typeDSpinorWeight`, `typeDVectorWeight`, `typeDCospinorWeight`:
  computable simple-root vectors for the `[1]`, `[2]` and `[3]` cosets of `Dₙ`.
* `TauCeti.IntegralLattice.rootLatticeIsometryCheckerboard_typeDSpinorWeight`,
  `TauCeti.IntegralLattice.rootLatticeIsometryCheckerboard_typeDVectorWeight`,
  `TauCeti.IntegralLattice.rootLatticeIsometryCheckerboard_typeDCospinorWeight`: they map to `s`,
  `v` and `c`.
* `TauCeti.IntegralLattice.typeDSpinorWeightDual`, `typeDVectorWeightDual`,
  `typeDCospinorWeightDual`: the bundled dual-carrier elements of `((D n).rootLattice ht)`, together
  with their simple-root pairings, squared norms and discriminant classes.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §7.1 and Chapter 16 §1.
-/

public section

namespace TauCeti.IntegralLattice

open DynkinType

variable {n : ℕ}

/-! ## Computable simple-root coordinates of `s`, `v` and `c` -/

/-- **The spinor weight `ϖₙ` of `Dₙ` in Bourbaki simple-root coordinates**, corresponding to the
Conway--Sloane glue label `[1]` and the checkerboard spinor `(1/2, …, 1/2)`. -/
def typeDSpinorWeight (n : ℕ) : Fin n → ℚ :=
  fun j ↦
    if (j : ℕ) + 2 < n then ((j : ℕ) + 1 : ℚ) / 2
    else if (j : ℕ) + 1 < n then ((n : ℚ) - 2) / 4
    else (n : ℚ) / 4

/-- **The vector representative of `Dₙ` in Bourbaki simple-root coordinates**,
`(-α_{n-2} + α_{n-1}) / 2`, corresponding to the Conway--Sloane glue label `[2]` and the
checkerboard vector `(0, …, 0, 1)`. -/
def typeDVectorWeight (n : ℕ) : Fin n → ℚ :=
  fun j ↦
    if (j : ℕ) + 2 < n then 0
    else if (j : ℕ) + 1 < n then -(1 / 2)
    else 1 / 2

/-- **The cospinor weight `ϖ_{n-1}` of `Dₙ` in Bourbaki simple-root coordinates**, corresponding to
the Conway--Sloane glue label `[3]` and the checkerboard cospinor `(1/2, …, 1/2, -1/2)`. -/
def typeDCospinorWeight (n : ℕ) : Fin n → ℚ :=
  fun j ↦
    if (j : ℕ) + 2 < n then ((j : ℕ) + 1 : ℚ) / 2
    else if (j : ℕ) + 1 < n then (n : ℚ) / 4
    else ((n : ℚ) - 2) / 4

@[simp]
theorem typeDSpinorWeight_apply (n : ℕ) (j : Fin n) :
    typeDSpinorWeight n j =
      if (j : ℕ) + 2 < n then ((j : ℕ) + 1 : ℚ) / 2
      else if (j : ℕ) + 1 < n then ((n : ℚ) - 2) / 4
      else (n : ℚ) / 4 :=
  (rfl)

@[simp]
theorem typeDVectorWeight_apply (n : ℕ) (j : Fin n) :
    typeDVectorWeight n j =
      if (j : ℕ) + 2 < n then 0
      else if (j : ℕ) + 1 < n then -(1 / 2)
      else 1 / 2 :=
  (rfl)

@[simp]
theorem typeDCospinorWeight_apply (n : ℕ) (j : Fin n) :
    typeDCospinorWeight n j =
      if (j : ℕ) + 2 < n then ((j : ℕ) + 1 : ℚ) / 2
      else if (j : ℕ) + 1 < n then (n : ℚ) / 4
      else ((n : ℚ) - 2) / 4 :=
  (rfl)

/-- The cospinor weight is the difference of the spinor and vector weights. -/
theorem typeDCospinorWeight_eq_sub (n : ℕ) :
    typeDCospinorWeight n = typeDSpinorWeight n - typeDVectorWeight n := by
  ext j
  simp only [typeDCospinorWeight_apply, Pi.sub_apply, typeDSpinorWeight_apply,
    typeDVectorWeight_apply]
  split_ifs <;> ring

/-! ## Compatibility with `rootLatticeIsometryCheckerboard` -/

/-- **`rootLatticeIsometryCheckerboard` sends `typeDSpinorWeight n` to `checkerboardSpinor n`.** -/
-- Not a `simp` lemma: `rank_D` rewrites `(D n).rank` in the implicit `DFunLike` domain type on the
-- left-hand side, matching `rootLatticeIsometryCheckerboard_single`.
theorem rootLatticeIsometryCheckerboard_typeDSpinorWeight (hn : 4 ≤ n)
    (ht : (D n).IsSimplyLaced) :
    rootLatticeIsometryCheckerboard n hn ht (typeDSpinorWeight n) = checkerboardSpinor n := by
  have hsymm :
      (rootLatticeIsometryCheckerboard n hn ht).symm (checkerboardSpinor n) =
        typeDSpinorWeight n := by
    funext (k : Fin n)
    refine (rootLatticeIsometryCheckerboard_symm_apply n hn ht (checkerboardSpinor n) k).trans ?_
    rw [typeDSpinorWeight_apply, sum_checkerboardSpinor]
    split_ifs with h₁ h₂
    · simp only [checkerboardSpinor_apply, Finset.sum_const, Fin.card_Iic, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      ring
    · rw [checkerboardSpinor_apply]
      ring
    · ring
  exact (congrArg (rootLatticeIsometryCheckerboard n hn ht) hsymm.symm).trans
    ((rootLatticeIsometryCheckerboard n hn ht).apply_symm_apply _)

/-- **`rootLatticeIsometryCheckerboard` sends `typeDVectorWeight n` to `checkerboardVector n`.** -/
theorem rootLatticeIsometryCheckerboard_typeDVectorWeight (hn : 4 ≤ n)
    (ht : (D n).IsSimplyLaced) :
    letI : NeZero n := ⟨by omega⟩
    rootLatticeIsometryCheckerboard n hn ht (typeDVectorWeight n) = checkerboardVector n := by
  have : NeZero n := ⟨by omega⟩
  have hsymm :
      (rootLatticeIsometryCheckerboard n hn ht).symm (checkerboardVector n) =
        typeDVectorWeight n := by
    funext (k : Fin n)
    have hlast : (⟨n - 1, by omega⟩ : Fin n) = ⊤ := by
      ext
      simp [Fin.val_top]
    refine (rootLatticeIsometryCheckerboard_symm_apply n hn ht (checkerboardVector n) k).trans ?_
    rw [typeDVectorWeight_apply, sum_checkerboardVector, hlast, checkerboardVector_top]
    split_ifs with h₁ h₂
    · refine Finset.sum_eq_zero fun j hj ↦ ?_
      rw [Finset.mem_Iic, Fin.le_iff_val_le_val] at hj
      have hjtop : j ≠ ⊤ := by
        intro h
        rw [h, Fin.val_top] at hj
        omega
      rw [checkerboardVector_apply, ite_eq_right hjtop]
    · ring
    · ring
  exact (congrArg (rootLatticeIsometryCheckerboard n hn ht) hsymm.symm).trans
    ((rootLatticeIsometryCheckerboard n hn ht).apply_symm_apply _)

/-- **`rootLatticeIsometryCheckerboard` sends `typeDCospinorWeight n` to
`checkerboardCospinor n`.** -/
theorem rootLatticeIsometryCheckerboard_typeDCospinorWeight (hn : 4 ≤ n)
    (ht : (D n).IsSimplyLaced) :
    letI : NeZero n := ⟨by omega⟩
    rootLatticeIsometryCheckerboard n hn ht (typeDCospinorWeight n) = checkerboardCospinor n := by
  have : NeZero n := ⟨by omega⟩
  have hc : checkerboardCospinor n = checkerboardSpinor n - checkerboardVector n := by
    ext j
    rw [checkerboardCospinor_apply, Pi.sub_apply, checkerboardSpinor_apply,
      checkerboardVector_apply]
  refine (congrArg (rootLatticeIsometryCheckerboard n hn ht)
    (typeDCospinorWeight_eq_sub n)).trans ?_
  refine (map_sub (rootLatticeIsometryCheckerboard n hn ht)
    (typeDSpinorWeight n) (typeDVectorWeight n)).trans ?_
  exact (congrArg₂ (· - ·) (rootLatticeIsometryCheckerboard_typeDSpinorWeight hn ht)
    (rootLatticeIsometryCheckerboard_typeDVectorWeight hn ht)).trans hc.symm

/-! ## Dual-carrier membership, norms, pairings and discriminant classes -/

/-- `typeDSpinorWeight n` belongs to the dual carrier of `(D n).rootLattice ht` for `4 ≤ n`. -/
theorem typeDSpinorWeight_mem_dualCarrier (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) :
    typeDSpinorWeight n ∈ ((D n).rootLattice ht).dualCarrier :=
  ((rootLatticeIsometryCheckerboard n hn ht).apply_mem_dualCarrier_iff
    (x := typeDSpinorWeight n)).mp <| by
    rw [rootLatticeIsometryCheckerboard_typeDSpinorWeight]
    exact checkerboardSpinor_mem_dualCarrier

/-- `typeDVectorWeight n` belongs to the dual carrier of `(D n).rootLattice ht` for `4 ≤ n`. -/
theorem typeDVectorWeight_mem_dualCarrier (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) :
    typeDVectorWeight n ∈ ((D n).rootLattice ht).dualCarrier := by
  have : NeZero n := ⟨by omega⟩
  exact ((rootLatticeIsometryCheckerboard n hn ht).apply_mem_dualCarrier_iff
    (x := typeDVectorWeight n)).mp <| by
    rw [rootLatticeIsometryCheckerboard_typeDVectorWeight]
    exact checkerboardVector_mem_dualCarrier

/-- `typeDCospinorWeight n` belongs to the dual carrier of `(D n).rootLattice ht` for `4 ≤ n`. -/
theorem typeDCospinorWeight_mem_dualCarrier (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) :
    typeDCospinorWeight n ∈ ((D n).rootLattice ht).dualCarrier := by
  have : NeZero n := ⟨by omega⟩
  exact ((rootLatticeIsometryCheckerboard n hn ht).apply_mem_dualCarrier_iff
    (x := typeDCospinorWeight n)).mp <| by
    rw [rootLatticeIsometryCheckerboard_typeDCospinorWeight]
    exact checkerboardCospinor_mem_dualCarrier

/-- `typeDSpinorWeight n` bundled in `((D n).rootLattice ht).dualCarrier`. -/
noncomputable def typeDSpinorWeightDual (n : ℕ) (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) :
    ((D n).rootLattice ht).dualCarrier :=
  ⟨typeDSpinorWeight n, typeDSpinorWeight_mem_dualCarrier hn ht⟩

/-- `typeDVectorWeight n` bundled in `((D n).rootLattice ht).dualCarrier`. -/
noncomputable def typeDVectorWeightDual (n : ℕ) (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) :
    ((D n).rootLattice ht).dualCarrier :=
  ⟨typeDVectorWeight n, typeDVectorWeight_mem_dualCarrier hn ht⟩

/-- `typeDCospinorWeight n` bundled in `((D n).rootLattice ht).dualCarrier`. -/
noncomputable def typeDCospinorWeightDual (n : ℕ) (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) :
    ((D n).rootLattice ht).dualCarrier :=
  ⟨typeDCospinorWeight n, typeDCospinorWeight_mem_dualCarrier hn ht⟩

@[simp]
theorem coe_typeDSpinorWeightDual (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) :
    (typeDSpinorWeightDual n hn ht : Fin (D n).rank → ℚ) = typeDSpinorWeight n :=
  (rfl)

@[simp]
theorem coe_typeDVectorWeightDual (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) :
    (typeDVectorWeightDual n hn ht : Fin (D n).rank → ℚ) = typeDVectorWeight n :=
  (rfl)

@[simp]
theorem coe_typeDCospinorWeightDual (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) :
    (typeDCospinorWeightDual n hn ht : Fin (D n).rank → ℚ) = typeDCospinorWeight n :=
  (rfl)

/-- **Squared norm of `typeDSpinorWeight n`.** -/
theorem form_typeDSpinorWeight_self (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) :
    ((D n).rootLattice ht).form (typeDSpinorWeight n) (typeDSpinorWeight n) = (n : ℚ) / 4 :=
  ((rootLatticeIsometryCheckerboard n hn ht).map_app
    (typeDSpinorWeight n) (typeDSpinorWeight n)).symm.trans <| by
    rw [rootLatticeIsometryCheckerboard_typeDSpinorWeight,
      checkerboardLattice_form_checkerboardSpinor_self]

/-- **Squared norm of `typeDVectorWeight n`.** -/
theorem form_typeDVectorWeight_self (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) :
    ((D n).rootLattice ht).form (typeDVectorWeight n) (typeDVectorWeight n) = 1 := by
  have : NeZero n := ⟨by omega⟩
  exact ((rootLatticeIsometryCheckerboard n hn ht).map_app
    (typeDVectorWeight n) (typeDVectorWeight n)).symm.trans <| by
    rw [rootLatticeIsometryCheckerboard_typeDVectorWeight,
      checkerboardLattice_form_checkerboardVector_self]

/-- **Squared norm of `typeDCospinorWeight n`.** -/
theorem form_typeDCospinorWeight_self (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) :
    ((D n).rootLattice ht).form (typeDCospinorWeight n) (typeDCospinorWeight n) =
      (n : ℚ) / 4 := by
  have : NeZero n := ⟨by omega⟩
  exact ((rootLatticeIsometryCheckerboard n hn ht).map_app
    (typeDCospinorWeight n) (typeDCospinorWeight n)).symm.trans <| by
    rw [rootLatticeIsometryCheckerboard_typeDCospinorWeight,
      checkerboardLattice_form_checkerboardCospinor_self]

/-- **Pairings of `typeDSpinorWeight n` with the simple roots**: `ϖₙ` pairs to `1` with the last
simple root `α_{n-1}` and to `0` with all others. -/
theorem form_typeDSpinorWeight_single (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) (i : Fin n) :
    ((D n).rootLattice ht).form (typeDSpinorWeight n) (Pi.single i 1) =
      if (i : ℕ) + 1 = n then 1 else 0 := by
  refine ((rootLatticeIsometryCheckerboard n hn ht).map_app
    (typeDSpinorWeight n) (Pi.single i 1)).symm.trans ?_
  rw [rootLatticeIsometryCheckerboard_typeDSpinorWeight, rootLatticeIsometryCheckerboard_single,
    (checkerboardLattice n).isSymm.eq, checkerboardLattice_form_checkerboardSpinor]
  have hsum : ∑ j : Fin n, checkerboardSimpleRoot n hn i j =
      ((∑ j : Fin n, typeDSimpleRoot n hn i j : ℤ) : ℚ) := by
    simp only [checkerboardSimpleRoot_apply, Int.cast_sum]
  rw [hsum, sum_typeDSimpleRoot hn i]
  by_cases hi : (i : ℕ) + 1 < n
  · have hne : (i : ℕ) + 1 ≠ n := by omega
    simp [hi, hne]
  · have heq : (i : ℕ) + 1 = n := by omega
    simp [heq]

/-- **Pairings of `typeDVectorWeight n` with the simple roots**: it pairs to `-1` with `α_{n-2}`,
to `1` with `α_{n-1}`, and to `0` with all earlier simple roots. -/
theorem form_typeDVectorWeight_single (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) (i : Fin n) :
    ((D n).rootLattice ht).form (typeDVectorWeight n) (Pi.single i 1) =
      if (i : ℕ) + 2 < n then 0 else if (i : ℕ) + 1 < n then -1 else 1 := by
  have : NeZero n := ⟨by omega⟩
  refine ((rootLatticeIsometryCheckerboard n hn ht).map_app
    (typeDVectorWeight n) (Pi.single i 1)).symm.trans ?_
  rw [rootLatticeIsometryCheckerboard_typeDVectorWeight, rootLatticeIsometryCheckerboard_single,
    (checkerboardLattice n).isSymm.eq, checkerboardLattice_form_checkerboardVector,
    checkerboardSimpleRoot_apply]
  by_cases hi : (i : ℕ) + 1 < n
  · rw [typeDSimpleRoot_of_add_one_lt hn hi]
    simp only [Pi.sub_apply, Pi.single_apply, Fin.ext_iff, Fin.val_top]
    split_ifs <;> first | (exfalso; omega) | norm_num
  · rw [typeDSimpleRoot_of_not_add_one_lt hn hi]
    simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff, Fin.val_top]
    split_ifs <;> first | (exfalso; omega) | norm_num

/-- **Pairings of `typeDCospinorWeight n` with the simple roots**: `ϖ_{n-1}` pairs to `1` with
`α_{n-2}` and to `0` with all others. -/
theorem form_typeDCospinorWeight_single (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) (i : Fin n) :
    ((D n).rootLattice ht).form (typeDCospinorWeight n) (Pi.single i 1) =
      if (i : ℕ) + 2 = n then 1 else 0 := by
  have hsub : ((D n).rootLattice ht).form (typeDCospinorWeight n) (Pi.single i 1) =
      ((D n).rootLattice ht).form (typeDSpinorWeight n) (Pi.single i 1) -
        ((D n).rootLattice ht).form (typeDVectorWeight n) (Pi.single i 1) := by
    refine (congrArg (fun u ↦ ((D n).rootLattice ht).form u (Pi.single i 1))
      (typeDCospinorWeight_eq_sub n)).trans ?_
    exact LinearMap.map_sub₂ ((D n).rootLattice ht).form
      (typeDSpinorWeight n) (typeDVectorWeight n) (Pi.single i 1)
  rw [hsub, form_typeDSpinorWeight_single hn ht i, form_typeDVectorWeight_single hn ht i]
  split_ifs <;> first | (exfalso; omega) | ring

/-- `typeDSpinorWeightDual` represents the spinor class pulled back along
`rootLatticeIsometryCheckerboard`. -/
@[simp]
theorem mk_typeDSpinorWeightDual (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) :
    (Submodule.Quotient.mk (typeDSpinorWeightDual n hn ht) :
        ((D n).rootLattice ht).DiscriminantGroup) =
      (rootLatticeIsometryCheckerboard n hn ht).symm.discriminantGroupEquiv
        (checkerboardSpinorClass n) := by
  apply (rootLatticeIsometryCheckerboard n hn ht).discriminantGroupEquiv.injective
  rw [Isometry.discriminantGroupEquiv_mk, Isometry.discriminantGroupEquiv_symm,
    LinearEquiv.apply_symm_apply, mk_eq_checkerboardSpinorClass_iff,
    Isometry.coe_dualCarrierEquiv_apply, coe_typeDSpinorWeightDual,
    rootLatticeIsometryCheckerboard_typeDSpinorWeight, sub_self]
  exact (checkerboardCarrier n).zero_mem

/-- `typeDVectorWeightDual` represents the vector class pulled back along
`rootLatticeIsometryCheckerboard`. -/
@[simp]
theorem mk_typeDVectorWeightDual (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) :
    letI : NeZero n := ⟨by omega⟩
    (Submodule.Quotient.mk (typeDVectorWeightDual n hn ht) :
        ((D n).rootLattice ht).DiscriminantGroup) =
      (rootLatticeIsometryCheckerboard n hn ht).symm.discriminantGroupEquiv
        (checkerboardVectorClass n) := by
  have : NeZero n := ⟨by omega⟩
  apply (rootLatticeIsometryCheckerboard n hn ht).discriminantGroupEquiv.injective
  rw [Isometry.discriminantGroupEquiv_mk, Isometry.discriminantGroupEquiv_symm,
    LinearEquiv.apply_symm_apply, mk_eq_checkerboardVectorClass_iff,
    Isometry.coe_dualCarrierEquiv_apply, coe_typeDVectorWeightDual,
    rootLatticeIsometryCheckerboard_typeDVectorWeight, sub_self]
  exact (checkerboardCarrier n).zero_mem

/-- `typeDCospinorWeightDual` represents the cospinor class pulled back along
`rootLatticeIsometryCheckerboard`. -/
@[simp]
theorem mk_typeDCospinorWeightDual (hn : 4 ≤ n) (ht : (D n).IsSimplyLaced) :
    letI : NeZero n := ⟨by omega⟩
    (Submodule.Quotient.mk (typeDCospinorWeightDual n hn ht) :
        ((D n).rootLattice ht).DiscriminantGroup) =
      (rootLatticeIsometryCheckerboard n hn ht).symm.discriminantGroupEquiv
        (checkerboardCospinorClass n) := by
  have : NeZero n := ⟨by omega⟩
  apply (rootLatticeIsometryCheckerboard n hn ht).discriminantGroupEquiv.injective
  rw [Isometry.discriminantGroupEquiv_mk, Isometry.discriminantGroupEquiv_symm,
    LinearEquiv.apply_symm_apply, mk_eq_checkerboardCospinorClass_iff,
    Isometry.coe_dualCarrierEquiv_apply, coe_typeDCospinorWeightDual,
    rootLatticeIsometryCheckerboard_typeDCospinorWeight, sub_self]
  exact (checkerboardCarrier n).zero_mem

end TauCeti.IntegralLattice
