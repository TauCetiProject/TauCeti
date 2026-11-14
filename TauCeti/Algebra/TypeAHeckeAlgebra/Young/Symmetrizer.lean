/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.GroupAlgebra
public import TauCeti.Algebra.TypeAHeckeAlgebra.Symmetrizer.Basic
public import TauCeti.RepresentationTheory.Symmetric.YoungSubgroup.RowStandardTableau

/-!
# Young `q`-symmetrizers and `q`-antisymmetrizers in type-`A` Hecke algebras

For a partition `μ` of `n`, `TauCeti.youngParabolicSet μ` presents the Young subgroup
`TauCeti.youngSubgroup μ` as a standard parabolic subgroup of `permCoxeterSystem n`. Specializing
`TauCeti.TypeAHeckeAlgebra.parabolicEigenSum` to `youngParabolicSet μ` at the two roots `q` and
`-q⁻¹` of the Hecke quadratic relation defines:

* `TauCeti.TypeAHeckeAlgebra.youngRowSymmetrizer q μ`: the Young `q`-symmetrizer
  `x_μ = ∑_{w ∈ S_μ} q^{ℓ(w)} T_w`, and
* `TauCeti.TypeAHeckeAlgebra.youngAntisymmetrizer q μ`: the Young `q`-antisymmetrizer
  `y_μ = ∑_{w ∈ S_μ} (-q⁻¹)^{ℓ(w)} T_w` (summing over `S_μ`; column antisymmetrization for a
  Young diagram `D` uses the transpose shape `shapePartition D.transpose`).

Both elements are defined integrally over any commutative ring `R` and any unit `q : Rˣ`, with
identity PBW coefficient `1` and without inverting quantum factorials. Using the Young parabolic
Poincaré polynomial (`TauCeti.sum_pow_length_parabolic_youngParabolicSet`), this file proves their
quantum-factorial quasi-idempotence identities over arbitrary commutative rings (including at roots
of unity where the scalar vanishes), records the normalized idempotents when the quantum-factorial
product is a unit, evaluates the extreme partitions `(1ⁿ)` and `(n)`, and proves that at `q = 1`
`groupAlgebraEquiv` sends `youngRowSymmetrizer` to the classical row symmetrizer of the
row-superstandard tableau.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.youngRowSymmetrizer`: the Young `q`-symmetrizer `x_μ`.
* `TauCeti.TypeAHeckeAlgebra.youngAntisymmetrizer`: the Young `q`-antisymmetrizer `y_μ`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.Tw_mul_youngRowSymmetrizer`,
  `TauCeti.TypeAHeckeAlgebra.youngRowSymmetrizer_mul_Tw`,
  `TauCeti.TypeAHeckeAlgebra.Tw_mul_youngAntisymmetrizer`,
  `TauCeti.TypeAHeckeAlgebra.youngAntisymmetrizer_mul_Tw`: left and right absorption of PBW
  elements of `youngSubgroup μ`.
* `TauCeti.TypeAHeckeAlgebra.youngRowSymmetrizer_mul_self` and
  `TauCeti.TypeAHeckeAlgebra.youngAntisymmetrizer_mul_self`: quantum-factorial
  quasi-idempotence.
* `TauCeti.TypeAHeckeAlgebra.groupAlgebraEquiv_youngRowSymmetrizer_shapePartition`: classical
  `q = 1` specialization to `YoungTableau.rowSymmetrizer`.

## References

* R. Dipper and G. James, *Representations of Hecke algebras of general linear groups*,
  Proc. London Math. Soc. (3) 52 (1986), 20–52, Section 3.
* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999), Sections 3.1–3.2.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

section CommRing

variable {R : Type*} [CommRing R]

/-! ### Definitions, PBW coordinates, and subgroup sums -/

/-- **The Young `q`-symmetrizer** `x_μ = ∑_{w ∈ S_μ} q^{ℓ(w)} T_w` in `TypeAHeckeAlgebra R q n`. -/
noncomputable def youngRowSymmetrizer (q : Rˣ) {n : ℕ} (μ : n.Partition) :
    TypeAHeckeAlgebra R q n :=
  parabolicEigenSum (q := q) (permCoxeterSystem n) (youngParabolicSet μ) (q : R)

/-- Unfolding equation for `youngRowSymmetrizer` in terms of `parabolicEigenSum`. -/
theorem youngRowSymmetrizer_def (q : Rˣ) {n : ℕ} (μ : n.Partition) :
    youngRowSymmetrizer q μ =
      parabolicEigenSum (q := q) (permCoxeterSystem n) (youngParabolicSet μ) (q : R) :=
  (rfl)

/-- **The Young `q`-antisymmetrizer** `y_μ = ∑_{w ∈ S_μ} (-q⁻¹)^{ℓ(w)} T_w` in
`TypeAHeckeAlgebra R q n`. It sums over `youngSubgroup μ` (`S_μ`); column antisymmetrization for a
Young diagram `D` uses the transpose partition `shapePartition D.transpose`. -/
noncomputable def youngAntisymmetrizer (q : Rˣ) {n : ℕ} (μ : n.Partition) :
    TypeAHeckeAlgebra R q n :=
  parabolicEigenSum (q := q) (permCoxeterSystem n) (youngParabolicSet μ) (-(↑q⁻¹ : R))

/-- Unfolding equation for `youngAntisymmetrizer` in terms of `parabolicEigenSum`. -/
theorem youngAntisymmetrizer_def (q : Rˣ) {n : ℕ} (μ : n.Partition) :
    youngAntisymmetrizer q μ =
      parabolicEigenSum (q := q) (permCoxeterSystem n) (youngParabolicSet μ) (-(↑q⁻¹ : R)) :=
  (rfl)

/-- The Young `q`-symmetrizer belongs to the parabolic Hecke subalgebra of `youngParabolicSet μ`. -/
theorem youngRowSymmetrizer_mem_parabolic (q : Rˣ) {n : ℕ} (μ : n.Partition) :
    youngRowSymmetrizer q μ ∈ parabolic q (youngParabolicSet μ) :=
  parabolicEigenSum_mem_parabolic (permCoxeterSystem n) (youngParabolicSet μ) (q : R)

/-- The Young `q`-antisymmetrizer belongs to the parabolic Hecke subalgebra of
`youngParabolicSet μ`. -/
theorem youngAntisymmetrizer_mem_parabolic (q : Rˣ) {n : ℕ} (μ : n.Partition) :
    youngAntisymmetrizer q μ ∈ parabolic q (youngParabolicSet μ) :=
  parabolicEigenSum_mem_parabolic (permCoxeterSystem n) (youngParabolicSet μ) (-(↑q⁻¹ : R))

open scoped Classical in
/-- The PBW coefficient of `w` in `youngRowSymmetrizer q μ` is `q ^ ℓ(w)` on `youngSubgroup μ` and
`0` outside it. -/
@[simp]
theorem basisTw_repr_youngRowSymmetrizer (q : Rˣ) {n : ℕ} (μ : n.Partition)
    (w : Equiv.Perm (Fin n)) :
    (basisTw q (permCoxeterSystem n)).repr (youngRowSymmetrizer q μ) w =
      if w ∈ youngSubgroup μ then (q : R) ^ (permCoxeterSystem n).length w else 0 := by
  rw [youngRowSymmetrizer_def, basisTw_repr_parabolicEigenSum]
  simp only [parabolic_youngParabolicSet_eq_youngSubgroup]

open scoped Classical in
/-- The PBW coefficient of `w` in `youngAntisymmetrizer q μ` is `(-q⁻¹) ^ ℓ(w)` on
`youngSubgroup μ` and `0` outside it. -/
@[simp]
theorem basisTw_repr_youngAntisymmetrizer (q : Rˣ) {n : ℕ} (μ : n.Partition)
    (w : Equiv.Perm (Fin n)) :
    (basisTw q (permCoxeterSystem n)).repr (youngAntisymmetrizer q μ) w =
      if w ∈ youngSubgroup μ then (-(↑q⁻¹ : R)) ^ (permCoxeterSystem n).length w else 0 := by
  rw [youngAntisymmetrizer_def, basisTw_repr_parabolicEigenSum]
  simp only [parabolic_youngParabolicSet_eq_youngSubgroup]

/-- Sum expansion of `youngRowSymmetrizer q μ` directly over `youngSubgroup μ`. -/
theorem youngRowSymmetrizer_eq_sum (q : Rˣ) {n : ℕ} (μ : n.Partition)
    [Fintype (youngSubgroup μ)] :
    youngRowSymmetrizer q μ =
      ∑ w : youngSubgroup μ,
        (q : R) ^ (permCoxeterSystem n).length (w : Equiv.Perm (Fin n)) •
          Tw q (permCoxeterSystem n) w := by
  let _ := Fintype.ofFinite ((permCoxeterSystem n).parabolic (youngParabolicSet μ))
  let e : (permCoxeterSystem n).parabolic (youngParabolicSet μ) ≃ youngSubgroup μ :=
    Equiv.subtypeEquivRight fun w => by rw [parabolic_youngParabolicSet_eq_youngSubgroup]
  rw [youngRowSymmetrizer_def, parabolicEigenSum_eq_sum]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- Sum expansion of `youngAntisymmetrizer q μ` directly over `youngSubgroup μ`. -/
theorem youngAntisymmetrizer_eq_sum (q : Rˣ) {n : ℕ} (μ : n.Partition)
    [Fintype (youngSubgroup μ)] :
    youngAntisymmetrizer q μ =
      ∑ w : youngSubgroup μ,
        (-(↑q⁻¹ : R)) ^ (permCoxeterSystem n).length (w : Equiv.Perm (Fin n)) •
          Tw q (permCoxeterSystem n) w := by
  let _ := Fintype.ofFinite ((permCoxeterSystem n).parabolic (youngParabolicSet μ))
  let e : (permCoxeterSystem n).parabolic (youngParabolicSet μ) ≃ youngSubgroup μ :=
    Equiv.subtypeEquivRight fun w => by rw [parabolic_youngParabolicSet_eq_youngSubgroup]
  rw [youngAntisymmetrizer_def, parabolicEigenSum_eq_sum]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- Over any nontrivial commutative ring, `youngRowSymmetrizer q μ` is nonzero. -/
theorem youngRowSymmetrizer_ne_zero [Nontrivial R] (q : Rˣ) {n : ℕ} (μ : n.Partition) :
    youngRowSymmetrizer q μ ≠ 0 :=
  parabolicEigenSum_ne_zero (permCoxeterSystem n) (youngParabolicSet μ) (q : R)

/-- Over any nontrivial commutative ring, `youngAntisymmetrizer q μ` is nonzero. -/
theorem youngAntisymmetrizer_ne_zero [Nontrivial R] (q : Rˣ) {n : ℕ} (μ : n.Partition) :
    youngAntisymmetrizer q μ ≠ 0 :=
  parabolicEigenSum_ne_zero (permCoxeterSystem n) (youngParabolicSet μ) (-(↑q⁻¹ : R))

/-! ### Eigenvalue absorption on `youngParabolicSet μ` and `youngSubgroup μ` -/

/-- Left multiplication by `T q i` for `i ∈ youngParabolicSet μ` scales `youngRowSymmetrizer q μ`
by `q`. -/
theorem T_mul_youngRowSymmetrizer (q : Rˣ) {n : ℕ} (μ : n.Partition) {i : Fin (n - 1)}
    (hi : i ∈ youngParabolicSet μ) :
    T q i * youngRowSymmetrizer q μ = (q : R) • youngRowSymmetrizer q μ :=
  T_mul_parabolicEigenSum (permCoxeterSystem n) (youngParabolicSet μ) (by simp [sub_mul]) hi

/-- Right multiplication by `T q i` for `i ∈ youngParabolicSet μ` scales `youngRowSymmetrizer q μ`
by `q`. -/
theorem youngRowSymmetrizer_mul_T (q : Rˣ) {n : ℕ} (μ : n.Partition) {i : Fin (n - 1)}
    (hi : i ∈ youngParabolicSet μ) :
    youngRowSymmetrizer q μ * T q i = (q : R) • youngRowSymmetrizer q μ :=
  parabolicEigenSum_mul_T (permCoxeterSystem n) (youngParabolicSet μ) (by simp [sub_mul]) hi

/-- Left multiplication by `Tw q (permCoxeterSystem n) w` for `w ∈ youngSubgroup μ` scales
`youngRowSymmetrizer q μ` by `q ^ ℓ(w)`. -/
theorem Tw_mul_youngRowSymmetrizer (q : Rˣ) {n : ℕ} (μ : n.Partition) {w : Equiv.Perm (Fin n)}
    (hw : w ∈ youngSubgroup μ) :
    Tw q (permCoxeterSystem n) w * youngRowSymmetrizer q μ =
      (q : R) ^ (permCoxeterSystem n).length w • youngRowSymmetrizer q μ := by
  rw [← parabolic_youngParabolicSet_eq_youngSubgroup] at hw
  exact Tw_mul_parabolicEigenSum (permCoxeterSystem n) (youngParabolicSet μ) (by simp [sub_mul]) hw

/-- Right multiplication by `Tw q (permCoxeterSystem n) w` for `w ∈ youngSubgroup μ` scales
`youngRowSymmetrizer q μ` by `q ^ ℓ(w)`. -/
theorem youngRowSymmetrizer_mul_Tw (q : Rˣ) {n : ℕ} (μ : n.Partition) {w : Equiv.Perm (Fin n)}
    (hw : w ∈ youngSubgroup μ) :
    youngRowSymmetrizer q μ * Tw q (permCoxeterSystem n) w =
      (q : R) ^ (permCoxeterSystem n).length w • youngRowSymmetrizer q μ := by
  rw [← parabolic_youngParabolicSet_eq_youngSubgroup] at hw
  exact parabolicEigenSum_mul_Tw (permCoxeterSystem n) (youngParabolicSet μ) (by simp [sub_mul]) hw

/-- Left multiplication by `T q i` for `i ∈ youngParabolicSet μ` scales
`youngAntisymmetrizer q μ` by `-q⁻¹`. -/
theorem T_mul_youngAntisymmetrizer (q : Rˣ) {n : ℕ} (μ : n.Partition) {i : Fin (n - 1)}
    (hi : i ∈ youngParabolicSet μ) :
    T q i * youngAntisymmetrizer q μ = (-(↑q⁻¹ : R)) • youngAntisymmetrizer q μ :=
  T_mul_parabolicEigenSum (permCoxeterSystem n) (youngParabolicSet μ) (by simp [sub_mul]) hi

/-- Right multiplication by `T q i` for `i ∈ youngParabolicSet μ` scales
`youngAntisymmetrizer q μ` by `-q⁻¹`. -/
theorem youngAntisymmetrizer_mul_T (q : Rˣ) {n : ℕ} (μ : n.Partition) {i : Fin (n - 1)}
    (hi : i ∈ youngParabolicSet μ) :
    youngAntisymmetrizer q μ * T q i = (-(↑q⁻¹ : R)) • youngAntisymmetrizer q μ :=
  parabolicEigenSum_mul_T (permCoxeterSystem n) (youngParabolicSet μ) (by simp [sub_mul]) hi

/-- Left multiplication by `Tw q (permCoxeterSystem n) w` for `w ∈ youngSubgroup μ` scales
`youngAntisymmetrizer q μ` by `(-q⁻¹) ^ ℓ(w)`. -/
theorem Tw_mul_youngAntisymmetrizer (q : Rˣ) {n : ℕ} (μ : n.Partition) {w : Equiv.Perm (Fin n)}
    (hw : w ∈ youngSubgroup μ) :
    Tw q (permCoxeterSystem n) w * youngAntisymmetrizer q μ =
      (-(↑q⁻¹ : R)) ^ (permCoxeterSystem n).length w • youngAntisymmetrizer q μ := by
  rw [← parabolic_youngParabolicSet_eq_youngSubgroup] at hw
  exact Tw_mul_parabolicEigenSum (permCoxeterSystem n) (youngParabolicSet μ) (by simp [sub_mul]) hw

/-- Right multiplication by `Tw q (permCoxeterSystem n) w` for `w ∈ youngSubgroup μ` scales
`youngAntisymmetrizer q μ` by `(-q⁻¹) ^ ℓ(w)`. -/
theorem youngAntisymmetrizer_mul_Tw (q : Rˣ) {n : ℕ} (μ : n.Partition) {w : Equiv.Perm (Fin n)}
    (hw : w ∈ youngSubgroup μ) :
    youngAntisymmetrizer q μ * Tw q (permCoxeterSystem n) w =
      (-(↑q⁻¹ : R)) ^ (permCoxeterSystem n).length w • youngAntisymmetrizer q μ := by
  rw [← parabolic_youngParabolicSet_eq_youngSubgroup] at hw
  exact parabolicEigenSum_mul_Tw (permCoxeterSystem n) (youngParabolicSet μ) (by simp [sub_mul]) hw

/-! ### Quantum-factorial quasi-idempotence and unit-scalar idempotents -/

/-- **Quantum-factorial quasi-idempotence on `youngParabolicSet μ`.** At any root `a` of the Hecke
quadratic relation, the parabolic weighted sum on `youngParabolicSet μ` squares to the product of
the quantum factorials of the parts of `μ` at `a²` times itself, including when that scalar is
zero. -/
theorem parabolicEigenSum_youngParabolicSet_mul_self (q : Rˣ) {n : ℕ} (μ : n.Partition) {a : R}
    (ha : a * a = ((q : R) - ↑q⁻¹) * a + 1) :
    parabolicEigenSum (permCoxeterSystem n) (youngParabolicSet μ) a *
        parabolicEigenSum (permCoxeterSystem n) (youngParabolicSet μ) a =
      (μ.parts.map fun p => ∏ d ∈ Finset.Icc 1 p, ∑ j ∈ Finset.range d, a ^ (2 * j)).prod •
        parabolicEigenSum (q := q) (permCoxeterSystem n) (youngParabolicSet μ) a := by
  let _ := Fintype.ofFinite ((permCoxeterSystem n).parabolic (youngParabolicSet μ))
  rw [parabolicEigenSum_mul_self (permCoxeterSystem n) (youngParabolicSet μ) ha]
  congr 1
  simpa only [pow_mul] using sum_pow_length_parabolic_youngParabolicSet (a ^ 2) μ

/-- **Quantum-factorial quasi-idempotence of `youngRowSymmetrizer`:** `x_μ²` equals
`(∏_i [μ_i]_{q²}!) • x_μ` over every commutative ring `R`, without invertibility assumptions. -/
theorem youngRowSymmetrizer_mul_self (q : Rˣ) {n : ℕ} (μ : n.Partition) :
    youngRowSymmetrizer q μ * youngRowSymmetrizer q μ =
      (μ.parts.map fun p => ∏ d ∈ Finset.Icc 1 p, ∑ j ∈ Finset.range d, (q : R) ^ (2 * j)).prod •
        youngRowSymmetrizer q μ :=
  parabolicEigenSum_youngParabolicSet_mul_self q μ (by simp [sub_mul])

/-- **Quantum-factorial quasi-idempotence of `youngAntisymmetrizer`:** `y_μ²` equals
`(∏_i [μ_i]_{q⁻²}!) • y_μ` over every commutative ring `R`, without invertibility assumptions. -/
theorem youngAntisymmetrizer_mul_self (q : Rˣ) {n : ℕ} (μ : n.Partition) :
    youngAntisymmetrizer q μ * youngAntisymmetrizer q μ =
      (μ.parts.map fun p => ∏ d ∈ Finset.Icc 1 p, ∑ j ∈ Finset.range d, (↑q⁻¹ : R) ^ (2 * j)).prod •
        youngAntisymmetrizer q μ := by
  let _ := Fintype.ofFinite ((permCoxeterSystem n).parabolic (youngParabolicSet μ))
  rw [youngAntisymmetrizer_def,
    parabolicEigenSum_neg_inv_mul_self (permCoxeterSystem n) (youngParabolicSet μ)]
  congr 1
  simpa only [pow_mul] using sum_pow_length_parabolic_youngParabolicSet ((↑q⁻¹ : R) ^ 2) μ

/-- Dividing `youngRowSymmetrizer q μ` by a unit quantum-factorial product yields an idempotent. -/
theorem isIdempotentElem_smul_youngRowSymmetrizer (q : Rˣ) {n : ℕ} (μ : n.Partition)
    (h : IsUnit
      (μ.parts.map fun p => ∏ d ∈ Finset.Icc 1 p, ∑ j ∈ Finset.range d, (q : R) ^ (2 * j)).prod) :
    IsIdempotentElem ((↑h.unit⁻¹ : R) • youngRowSymmetrizer q μ) := by
  rw [IsIdempotentElem, smul_mul_assoc, mul_smul_comm, youngRowSymmetrizer_mul_self,
    smul_smul, smul_smul, mul_assoc, h.val_inv_mul, mul_one]

/-- Dividing `youngAntisymmetrizer q μ` by a unit quantum-factorial product yields an
idempotent. -/
theorem isIdempotentElem_smul_youngAntisymmetrizer (q : Rˣ) {n : ℕ} (μ : n.Partition)
    (h : IsUnit
      (μ.parts.map fun p =>
        ∏ d ∈ Finset.Icc 1 p, ∑ j ∈ Finset.range d, (↑q⁻¹ : R) ^ (2 * j)).prod) :
    IsIdempotentElem ((↑h.unit⁻¹ : R) • youngAntisymmetrizer q μ) := by
  rw [IsIdempotentElem, smul_mul_assoc, mul_smul_comm, youngAntisymmetrizer_mul_self,
    smul_smul, smul_smul, mul_assoc, h.val_inv_mul, mul_one]

/-! ### Extreme partitions and classical `q = 1` specialization -/

/-- On the single-column partition `(1ⁿ)`, the Young `q`-symmetrizer is `1`. -/
@[simp]
theorem youngRowSymmetrizer_ones (q : Rˣ) (n : ℕ) :
    youngRowSymmetrizer q (Nat.Partition.ones n) = 1 := by
  apply (basisTw q (permCoxeterSystem n)).repr.injective
  ext w
  rw [basisTw_repr_youngRowSymmetrizer, youngSubgroup_ones, Subgroup.mem_bot,
    ← Tw_one (permCoxeterSystem n), ← coe_basisTw, Module.Basis.repr_self_apply]
  by_cases hw : w = 1 <;> simp [hw, eq_comm]

/-- On the single-column partition `(1ⁿ)`, the Young `q`-antisymmetrizer is `1`. -/
@[simp]
theorem youngAntisymmetrizer_ones (q : Rˣ) (n : ℕ) :
    youngAntisymmetrizer q (Nat.Partition.ones n) = 1 := by
  apply (basisTw q (permCoxeterSystem n)).repr.injective
  ext w
  rw [basisTw_repr_youngAntisymmetrizer, youngSubgroup_ones, Subgroup.mem_bot,
    ← Tw_one (permCoxeterSystem n), ← coe_basisTw, Module.Basis.repr_self_apply]
  by_cases hw : w = 1 <;> simp [hw, eq_comm]

/-- On the single-row partition `(n)`, the Young `q`-symmetrizer is the full `S_n`
`q`-symmetrizer. -/
theorem youngRowSymmetrizer_indiscrete (q : Rˣ) (n : ℕ) :
    youngRowSymmetrizer q (Nat.Partition.indiscrete n) =
      parabolicEigenSum (q := q) (permCoxeterSystem n) Set.univ (q : R) := by
  apply (basisTw q (permCoxeterSystem n)).repr.injective
  ext w
  rw [basisTw_repr_youngRowSymmetrizer, basisTw_repr_parabolicEigenSum, youngSubgroup_indiscrete,
    CoxeterSystem.parabolic_univ]

/-- On the single-row partition `(n)`, the Young `q`-antisymmetrizer is the full `S_n`
`q`-antisymmetrizer. -/
theorem youngAntisymmetrizer_indiscrete (q : Rˣ) (n : ℕ) :
    youngAntisymmetrizer q (Nat.Partition.indiscrete n) =
      parabolicEigenSum (q := q) (permCoxeterSystem n) Set.univ (-(↑q⁻¹ : R)) := by
  apply (basisTw q (permCoxeterSystem n)).repr.injective
  ext w
  rw [basisTw_repr_youngAntisymmetrizer, basisTw_repr_parabolicEigenSum,
    youngSubgroup_indiscrete, CoxeterSystem.parabolic_univ]

/-- **Classical `q = 1` specialization:** `groupAlgebraEquiv` carries `youngRowSymmetrizer` of the
shape partition of `D` to the classical row symmetrizer `YoungTableau.rowSymmetrizer` of the
row-superstandard tableau of `D`. -/
theorem groupAlgebraEquiv_youngRowSymmetrizer_shapePartition (D : YoungDiagram) :
    groupAlgebraEquiv (permCoxeterSystem D.card) inv_one.symm
        (youngRowSymmetrizer (R := R) (1 : Rˣ) (shapePartition D)) =
      YoungTableau.rowSymmetrizer (R := R) (StandardYoungTableau.rowSuperstandard D).toTableau := by
  classical
  ext w
  rw [← (permCoxeterSystem D.card).basisTw_repr_eq_coeff_groupAlgebraEquiv inv_one.symm,
    basisTw_repr_youngRowSymmetrizer, YoungTableau.rowSymmetrizer_coeff]
  simp

end CommRing

end TauCeti.TypeAHeckeAlgebra
