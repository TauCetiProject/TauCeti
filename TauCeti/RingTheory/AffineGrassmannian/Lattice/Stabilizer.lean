/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.LinearAlgebra.Matrix.Block
public import TauCeti.RingTheory.AffineGrassmannian.Lattice.Filtration
import Mathlib.RingTheory.Jacobson.Ideal
import TauCeti.Algebra.Algebra.IsUnit
import TauCeti.LinearAlgebra.Matrix.Charpoly.Inverse
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.LinearAlgebra.Matrix.IdealEntries

/-!
# The stabilizer of the lattice of a diagonal cocharacter

Let `B` be a commutative ring and `ξ ∈ B`; the motivating case is `B = B⁺_dR` with `ξ` a
generator of the kernel of `θ`. For a cocharacter `μ = (k_i)` of the diagonal torus of `GLₙ`,
the positive loop group `GLₙ(B)` meets its conjugate `μ(ξ) GLₙ(B) μ(ξ)⁻¹` in the stabilizer of the
lattice `μ(ξ) Bⁿ`. This file computes that stabilizer: a matrix over `B` preserves `μ(ξ) Bⁿ`
exactly when its `(i, j)` entry is divisible by `ξ ^ (k i - k j)` whenever `k j < k i`.

The matrices with this divisibility form a subalgebra `TauCeti.diagonalLatticeSubalgebra k ξ` of
`Matrix n n B`, defined for every `ξ`, and its invertible elements form the subgroup
`TauCeti.diagonalLatticeStabilizer k ξ` of `GL n B`. When `B → K` is injective and `ξ` becomes a
unit in `K`, these are the matrices `A` with `μ(ξ)⁻¹ A μ(ξ)` integral, equivalently those with
`A μ(ξ) Bⁿ ⊆ μ(ξ) Bⁿ`; for `g ∈ GLₙ(B)` the inclusion `g μ(ξ) Bⁿ ⊆ μ(ξ) Bⁿ` is then an equality.

At `ξ = 0` the divisibility says that the entries with `k j < k i` vanish, i.e. that the matrix
is block triangular for `k` (`Matrix.BlockTriangular`); in `GLₙ` this is the parabolic `P⁻_μ`
of the nonpositive weights of `μ`. Reducing modulo `ξ` maps the stabilizer into `P⁻_μ(B ⧸ ξ)`,
and onto it when `ξ` lies in the Jacobson radical. More generally, for `ξ` regular, on the
congruence subgroup of level `m`, whose elements are `1 + ξ ^ m X`, the stabilizer is cut out by
`ξ ^ (k i - k j - m) ∣ X i j`; so, when moreover `ξ` lies in the Jacobson radical and `m ≥ 1`,
its image in the graded piece `X mod ξ` consists of the matrices supported on the weights
`k i - k j ≤ m` of `μ`.

## Main definitions

* `TauCeti.diagonalLatticeSubalgebra k ξ`: the matrices whose `(i, j)` entry is divisible by
  `ξ ^ (k i - k j)` whenever `k j < k i`.
* `TauCeti.diagonalLatticeStabilizer k ξ`: its group of units, a subgroup of `GL n B`.

## Main results

* `TauCeti.mem_diagonalLatticeSubalgebra_iff_map_le`: `A ∈ diagonalLatticeSubalgebra k ξ` iff
  `A μ(ξ) Bⁿ ⊆ μ(ξ) Bⁿ`.
* `TauCeti.mem_diagonalLatticeSubalgebra_iff_exists_map_mul_diagonal_eq`: the same condition says
  that `μ(ξ)⁻¹ A μ(ξ)` has entries in `B`.
* `TauCeti.mem_diagonalLatticeStabilizer_iff_map_eq`: `g ∈ GLₙ(B)` lies in the stabilizer iff
  `g μ(ξ) Bⁿ = μ(ξ) Bⁿ`.
* `TauCeti.diagonalLatticeSubalgebra_zero`: at `ξ = 0` the subalgebra is Mathlib's
  `Matrix.blockTriangularSubalgebra` of the block-triangular matrices.
* `TauCeti.map_diagonalLatticeStabilizer`: if `ξ` lies in the Jacobson radical, reduction modulo
  `ξ` maps the stabilizer onto the block-triangular subgroup of `GLₙ(B ⧸ ξ)`.
* `TauCeti.pow_smul_mem_diagonalLatticeSubalgebra_iff`: for `ξ` regular,
  `ξ ^ m X` lies in the subalgebra iff `ξ ^ (k i - k j - m) ∣ X i j` for all `i, j`.
* `TauCeti.exists_mem_diagonalLatticeStabilizer_eq_one_add_pow_smul_iff`: for `ξ` regular and in
  the Jacobson radical and `m ≥ 1`, the reductions modulo `ξ` of the `X` with `1 + ξ ^ m X` in the
  stabilizer are the matrices vanishing at the weights `k i - k j > m`.

## References

* L. Fargues, P. Scholze, *Geometrization of the local Langlands correspondence*, Proposition
  VI.2.4 and its proof.
* A. Caraiani, P. Scholze, *On the generic part of the cohomology of compact unitary Shimura
  varieties*, Ann. of Math. 186 (2017), proof of Proposition 3.4.3.
-/

public section

variable {B : Type*} [CommRing B] {n : Type*} [Fintype n] [DecidableEq n]

namespace TauCeti

open Matrix

/-- **The matrices preserving the lattice of a diagonal cocharacter.** For `k : n → ℤ` and
`ξ ∈ B`, the subalgebra of matrices `A` whose `(i, j)` entry is divisible by `ξ ^ (k i - k j)`
whenever `k j < k i`. When `B → K` is injective and `ξ` becomes a unit in `K`, these are the
matrices `A` with `μ(ξ)⁻¹ A μ(ξ)` integral, for `μ = (k_i)`, equivalently those preserving the
lattice `μ(ξ) Bⁿ` (`mem_diagonalLatticeSubalgebra_iff_map_le`). -/
def diagonalLatticeSubalgebra (k : n → ℤ) (ξ : B) : Subalgebra B (Matrix n n B) where
  carrier := {A | ∀ i j, ξ ^ (k i - k j).toNat ∣ A i j}
  mul_mem' {A A'} hA hA' i j := by
    rw [Matrix.mul_apply]
    -- `k i - k j ≤ (k i - k l)⁺ + (k l - k j)⁺` for every intermediate index `l`.
    exact Finset.dvd_sum fun l _ ↦ (pow_dvd_pow ξ (by omega)).trans
      ((pow_add ξ _ _).symm ▸ mul_dvd_mul (hA i l) (hA' l j))
  add_mem' hA hA' i j := dvd_add (hA i j) (hA' i j)
  algebraMap_mem' r i j := by
    rw [algebraMap_matrix_apply]
    split_ifs with h
    · simp [h]
    · exact dvd_zero _

/-- A matrix lies in the subalgebra iff `ξ ^ (k i - k j)⁺` divides its `(i, j)` entry for all
`i, j`. -/
@[simp]
theorem mem_diagonalLatticeSubalgebra {k : n → ℤ} {ξ : B} {A : Matrix n n B} :
    A ∈ diagonalLatticeSubalgebra k ξ ↔ ∀ i j, ξ ^ (k i - k j).toNat ∣ A i j :=
  Iff.rfl

/-- Only the entries with `k j < k i` are constrained: the others are divisible by
`ξ ^ 0 = 1`. -/
theorem mem_diagonalLatticeSubalgebra_iff_forall_lt {k : n → ℤ} {ξ : B} {A : Matrix n n B} :
    A ∈ diagonalLatticeSubalgebra k ξ ↔ ∀ i j, k j < k i → ξ ^ (k i - k j).toNat ∣ A i j := by
  refine ⟨fun hA i j _ ↦ hA i j, fun hA i j ↦ ?_⟩
  by_cases h : k j < k i
  · exact hA i j h
  · rw [show (k i - k j).toNat = 0 by omega, pow_zero]
    exact one_dvd _

/-- A ring map `φ` takes the subalgebra for `ξ` into the subalgebra for `φ ξ`. -/
theorem map_mem_diagonalLatticeSubalgebra {B' : Type*} [CommRing B'] (φ : B →+* B')
    {k : n → ℤ} {ξ : B} {A : Matrix n n B} (hA : A ∈ diagonalLatticeSubalgebra k ξ) :
    A.map φ ∈ diagonalLatticeSubalgebra k (φ ξ) :=
  mem_diagonalLatticeSubalgebra.2 fun i j ↦ by
    simpa only [map_apply, map_pow] using map_dvd φ (hA i j)

/-- **At `ξ = 0` the subalgebra consists of the block-triangular matrices**: those whose entries
with `k j < k i` vanish. -/
@[simp]
theorem diagonalLatticeSubalgebra_zero (k : n → ℤ) :
    diagonalLatticeSubalgebra k (0 : B) = blockTriangularSubalgebra B B k := by
  ext A
  rw [mem_diagonalLatticeSubalgebra_iff_forall_lt, mem_blockTriangularSubalgebra]
  refine ⟨fun hA i j h ↦ ?_, fun hA i j h ↦ by rw [hA h]; exact dvd_zero _⟩
  have := hA i j h
  rwa [zero_pow (by omega), zero_dvd_iff] at this

/-- **Reduction modulo `ξ` is block triangular.** A matrix in the subalgebra for `ξ` reduces
modulo `ξ` to a block-triangular matrix: its entries with `k j < k i` vanish. -/
theorem blockTriangular_map_mk_of_mem_diagonalLatticeSubalgebra {k : n → ℤ} {ξ : B}
    {A : Matrix n n B} (hA : A ∈ diagonalLatticeSubalgebra k ξ) :
    (A.map (Ideal.Quotient.mk (Ideal.span {ξ}))).BlockTriangular k := by
  rw [← mem_blockTriangularSubalgebra (R := B ⧸ Ideal.span {ξ}), ← diagonalLatticeSubalgebra_zero,
    ← Ideal.Quotient.mk_singleton_self ξ]
  exact map_mem_diagonalLatticeSubalgebra _ hA

/-- **Multiples of a power of a regular `ξ`.** If `ξ` is regular, `ξ ^ m X` lies in the
subalgebra exactly when `ξ ^ (k i - k j - m)` divides `X i j` for all `i, j`; so only the entries
at the weights `k i - k j > m` are constrained. -/
theorem pow_smul_mem_diagonalLatticeSubalgebra_iff {ξ : B} (hξ : IsLeftRegular ξ) (m : ℕ)
    {k : n → ℤ} {X : Matrix n n B} :
    ξ ^ m • X ∈ diagonalLatticeSubalgebra k ξ ↔ ∀ i j, ξ ^ (k i - k j - m).toNat ∣ X i j := by
  simp only [mem_diagonalLatticeSubalgebra, Matrix.smul_apply, smul_eq_mul]
  refine forall_congr' fun i ↦ forall_congr' fun j ↦ ?_
  rcases le_total (k i - k j) m with h | h
  · rw [show (k i - k j - m).toNat = 0 by omega, pow_zero]
    exact iff_of_true ((pow_dvd_pow ξ (by omega)).trans (dvd_mul_right _ _)) (one_dvd _)
  · rw [show (k i - k j).toNat = m + (k i - k j - m).toNat by omega, pow_add]
    exact (hξ.pow m).dvd_cancel_left

/-- **The stabilizer of the lattice of a diagonal cocharacter.** The units of
`diagonalLatticeSubalgebra k ξ`, as a subgroup of `GL n B`. When `B → K` is injective and `ξ`
becomes a unit in `K`, this is the stabilizer of `μ(ξ) Bⁿ` in `GLₙ(B)`
(`mem_diagonalLatticeStabilizer_iff_map_eq`), i.e. `GLₙ(B) ∩ μ(ξ) GLₙ(B) μ(ξ)⁻¹`. -/
def diagonalLatticeStabilizer (k : n → ℤ) (ξ : B) : Subgroup (GL n B) :=
  (diagonalLatticeSubalgebra k ξ).toSubmonoid.units

/-- An element of `GL n B` lies in `diagonalLatticeStabilizer k ξ` iff its matrix lies in
`diagonalLatticeSubalgebra k ξ`. -/
@[simp]
theorem mem_diagonalLatticeStabilizer {k : n → ℤ} {ξ : B} {g : GL n B} :
    g ∈ diagonalLatticeStabilizer k ξ ↔ (g : Matrix n n B) ∈ diagonalLatticeSubalgebra k ξ := by
  rw [diagonalLatticeStabilizer, Submonoid.mem_units_iff, coe_units_inv]
  exact ⟨And.left, fun h ↦ ⟨h, nonsing_inv_mem h⟩⟩

/-- **Reduction of the stabilizer modulo `ξ`.** If `ξ` lies in the Jacobson radical of `B`, the
reduction modulo `ξ` maps the stabilizer for `ξ` onto the block-triangular subgroup of
`GLₙ(B ⧸ ξ)`, the stabilizer for `0` (see `diagonalLatticeSubalgebra_zero`). -/
theorem map_diagonalLatticeStabilizer {ξ : B} (hξ : ξ ∈ Ring.jacobson B) (k : n → ℤ) :
    (diagonalLatticeStabilizer k ξ).map
        (GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {ξ}))) =
      diagonalLatticeStabilizer k 0 := by
  refine le_antisymm ?_ fun g hg ↦ ?_
  · rintro _ ⟨g, hg, rfl⟩
    rw [mem_diagonalLatticeStabilizer, ← Ideal.Quotient.mk_singleton_self ξ]
    exact map_mem_diagonalLatticeSubalgebra _ (mem_diagonalLatticeStabilizer.1 hg)
  · -- Lift `g` entrywise, choosing the lift `0` at the entries forced to vanish.
    rw [mem_diagonalLatticeStabilizer, diagonalLatticeSubalgebra_zero,
      mem_blockTriangularSubalgebra] at hg
    obtain ⟨A, hA, hA0⟩ := exists_map_eq_and_apply_eq_zero Ideal.Quotient.mk_surjective
      (g : Matrix n n (B ⧸ Ideal.span {ξ})) (fun i j ↦ k j < k i) fun i j h ↦ hg h
    have hAmem : A ∈ diagonalLatticeSubalgebra k ξ :=
      mem_diagonalLatticeSubalgebra_iff_forall_lt.2 fun i j h ↦ by
        rw [hA0 i j h]
        exact dvd_zero _
    -- The determinant of `A` is a unit modulo the Jacobson radical, hence a unit.
    have hdet : IsUnit A.det := by
      have := isLocalHom_of_le_jacobson ((Ideal.span_singleton_le_iff_mem _).2 hξ)
      refine IsUnit.of_map (Ideal.Quotient.mk (Ideal.span {ξ})) _ ?_
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hA]
      exact (g.isUnit).map detMonoidHom
    refine ⟨GeneralLinearGroup.mk'' A hdet, mem_diagonalLatticeStabilizer.2 hAmem, ?_⟩
    ext : 1
    simpa using hA

/-- **The graded pieces of the stabilizer.** Let `ξ` be regular and in the Jacobson radical, and
`1 ≤ m`. A matrix `Y` over `B ⧸ ξ` is `X mod ξ` for an element `1 + ξ ^ m X` of the stabilizer
iff `Y` vanishes at every entry of weight `k i - k j > m`. So the image of the intersection of the
stabilizer with the `m`-th congruence subgroup in the `m`-th graded piece consists of the
matrices supported on the weights `≤ m` of `μ`. -/
theorem exists_mem_diagonalLatticeStabilizer_eq_one_add_pow_smul_iff {ξ : B}
    (hreg : IsLeftRegular ξ) (hξ : ξ ∈ Ring.jacobson B) {m : ℕ} (hm : 1 ≤ m) (k : n → ℤ)
    {Y : Matrix n n (B ⧸ Ideal.span {ξ})} :
    (∃ g ∈ diagonalLatticeStabilizer k ξ, ∃ X : Matrix n n B,
      (g : Matrix n n B) = 1 + ξ ^ m • X ∧ X.map (Ideal.Quotient.mk (Ideal.span {ξ})) = Y) ↔
      ∀ i j, (m : ℤ) < k i - k j → Y i j = 0 := by
  constructor
  · rintro ⟨g, hg, X, hgX, rfl⟩ i j h
    -- `ξ ^ m X = g - 1` lies in the subalgebra, so `ξ ∣ ξ ^ (k i - k j - m) ∣ X i j`.
    have hX : ξ ^ m • X ∈ diagonalLatticeSubalgebra k ξ := by
      rw [← add_mem_cancel_left (one_mem _), ← hgX]
      exact mem_diagonalLatticeStabilizer.1 hg
    have := (pow_smul_mem_diagonalLatticeSubalgebra_iff hreg m).1 hX i j
    rw [map_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact (dvd_pow_self ξ (by omega)).trans this
  · intro hY
    -- Lift `Y` entrywise, choosing the lift `0` at the entries of weight `> m`.
    obtain ⟨X, hX, hX0⟩ := exists_map_eq_and_apply_eq_zero Ideal.Quotient.mk_surjective Y _ hY
    have hXmem : 1 + ξ ^ m • X ∈ diagonalLatticeSubalgebra k ξ := by
      refine add_mem (one_mem _) ((pow_smul_mem_diagonalLatticeSubalgebra_iff hreg m).2
        fun i j ↦ ?_)
      by_cases h : (m : ℤ) < k i - k j
      · rw [hX0 i j h]
        exact dvd_zero _
      · rw [show (k i - k j - m).toNat = 0 by omega, pow_zero]
        exact one_dvd _
    have hdet : IsUnit (1 + ξ ^ m • X).det :=
      isUnit_det_one_add_smul (Ideal.pow_mem_of_mem _ hξ m (by omega)) X
    exact ⟨GeneralLinearGroup.mk'' _ hdet, mem_diagonalLatticeStabilizer.2 hXmem, X, rfl, hX⟩

section Lattice

variable {K : Type*} [CommRing K] [Algebra B K] {ξ : B}

/-- Entrywise form of `μ(ξ)⁻¹ A μ(ξ)` being integral: `A i j ξ ^ (k j) = ξ ^ (k i) a` in `K`
for some `a ∈ B`. -/
private theorem mem_diagonalLatticeSubalgebra_iff_forall_exists
    (hinj : Function.Injective (algebraMap B K)) (hξ : IsUnit (algebraMap B K ξ)) {k : n → ℤ}
    {A : Matrix n n B} :
    A ∈ diagonalLatticeSubalgebra k ξ ↔ ∀ i j, ∃ a : B,
      algebraMap B K (A i j) * (hξ.unit ^ k j : Kˣ) = (hξ.unit ^ k i : Kˣ) * algebraMap B K a := by
  rw [mem_diagonalLatticeSubalgebra]
  refine ⟨fun hA i j ↦ ?_, fun h i j ↦ ?_⟩
  · obtain ⟨b, hb⟩ := hA i j
    rcases le_total (k j) (k i) with hle | hle
    · refine ⟨b, ?_⟩
      rw [hξ.val_unit_zpow_eq_mul_algebraMap_pow_of_le hle, hb, map_mul]
      ring
    · refine ⟨A i j * ξ ^ (k j - k i).toNat, ?_⟩
      rw [hξ.val_unit_zpow_eq_mul_algebraMap_pow_of_le hle, map_mul]
      ring
  · obtain ⟨a, ha⟩ := h i j
    rcases le_total (k j) (k i) with hle | hle
    · -- Cancel the unit `ξ ^ k j` in `A i j ξ ^ k j = ξ ^ k j ξ ^ (k i - k j) a`.
      refine ⟨a, hinj ((Units.mul_right_inj (hξ.unit ^ k j)).1 ?_)⟩
      rw [map_mul, ← mul_assoc, ← hξ.val_unit_zpow_eq_mul_algebraMap_pow_of_le hle, ← ha]
      exact mul_comm _ _
    · rw [show (k i - k j).toNat = 0 by omega, pow_zero]
      exact one_dvd _

/-- **The subalgebra is the intersection with the conjugate.** If `B → K` is injective and `ξ`
becomes a unit in `K`, a matrix `A` over `B` lies in `diagonalLatticeSubalgebra k ξ` iff
`μ(ξ)⁻¹ A μ(ξ)` has entries in `B`, i.e. `A μ(ξ) = μ(ξ) A'` for a matrix `A'` over `B`. -/
theorem mem_diagonalLatticeSubalgebra_iff_exists_map_mul_diagonal_eq
    (hinj : Function.Injective (algebraMap B K)) (hξ : IsUnit (algebraMap B K ξ)) {k : n → ℤ}
    {A : Matrix n n B} :
    A ∈ diagonalLatticeSubalgebra k ξ ↔ ∃ A' : Matrix n n B,
      A.map (algebraMap B K) * diagonal (fun i ↦ ((hξ.unit ^ k i : Kˣ) : K)) =
        diagonal (fun i ↦ ((hξ.unit ^ k i : Kˣ) : K)) * A'.map (algebraMap B K) := by
  rw [mem_diagonalLatticeSubalgebra_iff_forall_exists hinj hξ]
  constructor
  · intro h
    choose A' hA' using h
    exact ⟨of A', by ext i j; simp [mul_diagonal, diagonal_mul, hA']⟩
  · rintro ⟨A', hA'⟩ i j
    exact ⟨A' i j, by simpa [mul_diagonal, diagonal_mul] using congrFun (congrFun hA' i) j⟩

/-- **The subalgebra preserves the lattice.** If `B → K` is injective and `ξ` becomes a unit
in `K`, a matrix `A` over `B` lies in `diagonalLatticeSubalgebra k ξ` iff it maps the lattice
`μ(ξ) Bⁿ` of `μ = (k_i)` into itself. -/
theorem mem_diagonalLatticeSubalgebra_iff_map_le (hinj : Function.Injective (algebraMap B K))
    (hξ : IsUnit (algebraMap B K ξ)) {k : n → ℤ} {A : Matrix n n B} :
    A ∈ diagonalLatticeSubalgebra k ξ ↔
      (diagonalLattice k hξ).map ((A.map (algebraMap B K)).mulVecLin.restrictScalars B) ≤
        diagonalLattice k hξ := by
  rw [mem_diagonalLatticeSubalgebra_iff_forall_exists hinj hξ]
  constructor
  · intro h
    choose a ha using h
    rintro _ ⟨v, hv, rfl⟩
    choose c hc using mem_diagonalLattice.1 hv
    -- `(A v)_i = ∑ j, A i j ξ ^ k j c j = ξ ^ k i ∑ j, a i j c j`.
    refine mem_diagonalLattice.2 fun i ↦ ⟨∑ j, a i j * c j, ?_⟩
    simp only [LinearMap.restrictScalars_apply, mulVecLin_apply, mulVec, dotProduct, map_apply, hc,
      map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← mul_assoc, ha, mul_assoc]
  · intro h i j
    -- Test the inclusion on the basis vector `ξ ^ k j e_j` of the lattice.
    have hv : Pi.single j ((hξ.unit ^ k j : Kˣ) : K) ∈ diagonalLattice k hξ := by
      refine mem_diagonalLattice.2 fun i' ↦ ?_
      rcases eq_or_ne i' j with rfl | hne
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp [hne]⟩
    obtain ⟨b, hb⟩ := mem_diagonalLattice.1 (h (Submodule.mem_map_of_mem hv)) i
    exact ⟨b, by simpa [mulVec, dotProduct, Pi.single_apply] using hb⟩

/-- **The stabilizer of the lattice of a diagonal cocharacter.** If `B → K` is injective and `ξ`
becomes a unit in `K`, an element `g ∈ GLₙ(B)` lies in `diagonalLatticeStabilizer k ξ` iff
`g μ(ξ) Bⁿ = μ(ξ) Bⁿ`. -/
theorem mem_diagonalLatticeStabilizer_iff_map_eq (hinj : Function.Injective (algebraMap B K))
    (hξ : IsUnit (algebraMap B K ξ)) {k : n → ℤ} {g : GL n B} :
    g ∈ diagonalLatticeStabilizer k ξ ↔
      (diagonalLattice k hξ).map
        (((g : Matrix n n B).map (algebraMap B K)).mulVecLin.restrictScalars B) =
          diagonalLattice k hξ := by
  rw [mem_diagonalLatticeStabilizer]
  refine ⟨fun hg ↦ le_antisymm ((mem_diagonalLatticeSubalgebra_iff_map_le hinj hξ).1 hg) ?_,
    fun h ↦ (mem_diagonalLatticeSubalgebra_iff_map_le hinj hξ).2 h.le⟩
  -- The inverse matrix maps the lattice into itself, so `v = g (g⁻¹ v)` lies in `g μ(ξ) Bⁿ`.
  have hinv := (mem_diagonalLatticeSubalgebra_iff_map_le hinj hξ).1 (nonsing_inv_mem hg)
  intro v hv
  refine ⟨_, hinv (Submodule.mem_map_of_mem hv), ?_⟩
  simp [mulVec_mulVec, GeneralLinearGroup.coe_map_mul_map_inv]

end Lattice

end TauCeti
