/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Composition
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable

import TauCeti.Data.Matrix.Composition
import TauCeti.Logic.Equiv.Fin.Basic

/-!
# Morita invariance of algebraic `K₁`

An `m × m` matrix whose entries are `ι × ι` matrices over a ring `R` is the same as an
`(m × ι) × (m × ι)` matrix over `R`: Mathlib's `Matrix.compRingEquiv` flattens the blocks. On
invertible matrices this is the group isomorphism `TauCeti.compGL : GL m (Mι(R)) ≃* GL (m × ι) R`.

Flattening identifies the elementary subgroups as soon as `m` has two distinct indices. An
elementary matrix `eᵢⱼ(X)` over `Mι(R)` flattens to the product of the elementary matrices
`e₍ᵢ,ₐ₎₍ⱼ,ᵦ₎(X a b)` over `R`. Conversely an elementary matrix of `R` between two different block
rows `i ≠ j` is the flattening of `eᵢⱼ(r Eₐᵦ)`. One inside the block `i`, `e₍ᵢ,ₐ₎₍ᵢ,ᵦ₎(r)` with
`a ≠ b`, is not of this form, but for a second block index `k` it is the flattening of the
commutator `⁅eᵢₖ(r Eₐᵦ), eₖᵢ(Eᵦᵦ)⁆`, because `Eᵦᵦ · r Eₐᵦ = 0`. With a single block index there
is no room for this commutator: for `R ≠ 0`, `E₁(M₂(R))` is trivial while `E₂(R)` is not.

Flattening `k × k` block matrices to `Fin (k * n)`, where `n` is the number of elements of `ι`,
is compatible with the stabilizations `u ↦ u ⊕ 1`, so it induces a homomorphism
`K₁(Mι(R)) → K₁(R)`. It is surjective because flattening is bijective at each finite size, and
injective because, after stabilizing to at least two blocks, elementary matrices over `R` come
from elementary matrices over `Mι(R)`. This is the **Morita invariance of `K₁`**:

  `K₁(Mₙ(R)) ≃* K₁(R)` for `n ≥ 1`,

`TauCeti.AlgebraicK1.matrixEquiv`, natural in ring homomorphisms `R →+* S`. For `ι` empty,
`Mι(R)` is the zero ring and the statement fails, as `K₁(ℤ) = {±1}` is not trivial.

## Main definitions

* `TauCeti.compGL`: block flattening `GL m (Matrix ι ι R) ≃* GL (m × ι) R`.
* `TauCeti.flattenGL`: block flattening `GL (Fin k) (Matrix ι ι R) ≃* GL (Fin (k * n)) R`,
  with `n = Fintype.card ι`, compatible with stabilization.
* `TauCeti.AlgebraicK1.matrixEquiv`: the Morita isomorphism `K₁(Matrix ι ι R) ≃* K₁(R)` for
  nonempty `ι`.

## Main results

* `TauCeti.map_compGL_elementarySubgroup`: flattening maps `E m (Matrix ι ι R)` onto
  `E (m × ι) R` when `m` has two distinct elements.
* `TauCeti.flattenGL_stabilizeGL`: flattening commutes with stabilization.
* `TauCeti.AlgebraicK1.matrixEquiv_mk`, `TauCeti.AlgebraicK1.matrixEquiv_symm_mk`: the Morita
  isomorphism and its inverse on classes of invertible matrices.
* `TauCeti.AlgebraicK1.map_matrixEquiv`: naturality in ring homomorphisms.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §1 (Morita invariance of `K₁`).
-/

public section

noncomputable section

open Matrix

open scoped commutatorElement

namespace TauCeti

/-! ## Flattening block matrices -/

section Flatten

variable (m ι R : Type*) [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] [Semiring R]

/-- **Block flattening** of invertible matrices: an invertible `m × m` matrix with entries in the
`ι × ι` matrices over `R` is an invertible `(m × ι) × (m × ι)` matrix over `R`, through
`Matrix.compRingEquiv`. -/
def compGL : GL m (Matrix ι ι R) ≃* GL (m × ι) R :=
  Units.mapEquiv (compRingEquiv m ι R).toMulEquiv

variable {m ι R}

/-- The flattening of an invertible block matrix is `Matrix.comp` of its underlying matrix. -/
@[simp]
theorem coe_compGL (u : GL m (Matrix ι ι R)) :
    (compGL m ι R u : Matrix (m × ι) (m × ι) R) = comp m m ι ι R u :=
  (rfl)

/-- The inverse of flattening is `Matrix.comp` read backwards. -/
@[simp]
theorem coe_compGL_symm (u : GL (m × ι) R) :
    ((compGL m ι R).symm u : Matrix m m (Matrix ι ι R)) = (comp m m ι ι R).symm u :=
  (rfl)

variable (ι R) in
/-- **Block flattening at a finite stage**: an invertible `k × k` matrix with entries in the
`ι × ι` matrices over `R` is an invertible matrix of size `k * n` over `R`, where `n` is the
number of elements of `ι`. The block index `i` and the entry index `a` go to the index
`e a + n * i`, for the enumeration `e = Fintype.equivFin ι`, so the first `k * n` indices of a
larger stage are those of the first `k` blocks. -/
def flattenGL (k : ℕ) : GL (Fin k) (Matrix ι ι R) ≃* GL (Fin (k * Fintype.card ι)) R :=
  (compGL (Fin k) ι R).trans
    ((((Equiv.refl (Fin k)).prodCongr (Fintype.equivFin ι)).trans finProdFinEquiv).reindexGL R)

/-- The entries of a flattened block matrix: the entry of the block `(i, j)` at `(a, b)` sits at
the indices `e a + n * i` and `e b + n * j`. -/
@[simp]
theorem flattenGL_apply_finProdFinEquiv {k : ℕ} (u : GL (Fin k) (Matrix ι ι R)) (i j : Fin k)
    (a b : ι) :
    (flattenGL ι R k u : Matrix (Fin (k * Fintype.card ι)) (Fin (k * Fintype.card ι)) R)
        (finProdFinEquiv (i, Fintype.equivFin ι a)) (finProdFinEquiv (j, Fintype.equivFin ι b)) =
      (u : Matrix (Fin k) (Fin k) (Matrix ι ι R)) i j a b := by
  simp [flattenGL]

/-- The blocks of the inverse flattening: the entry at `(a, b)` of the block `(i, j)` is the entry
at the indices `e a + n * i` and `e b + n * j`. -/
@[simp]
theorem flattenGL_symm_apply {k : ℕ} (u : GL (Fin (k * Fintype.card ι)) R) (i j : Fin k)
    (a b : ι) :
    ((flattenGL ι R k).symm u : Matrix (Fin k) (Fin k) (Matrix ι ι R)) i j a b =
      (u : Matrix (Fin (k * Fintype.card ι)) (Fin (k * Fintype.card ι)) R)
        (finProdFinEquiv (i, Fintype.equivFin ι a))
        (finProdFinEquiv (j, Fintype.equivFin ι b)) := by
  rw [← flattenGL_apply_finProdFinEquiv, MulEquiv.apply_symm_apply]

/-- Flattening commutes with applying a ring homomorphism to the entries. -/
theorem unitsMap_mapMatrix_flattenGL {S : Type*} [Semiring S] (f : R →+* S) {k : ℕ}
    (u : GL (Fin k) (Matrix ι ι R)) :
    Units.map (f.mapMatrix (m := Fin (k * Fintype.card ι))).toMonoidHom (flattenGL ι R k u) =
      flattenGL ι S k (Units.map (f.mapMatrix.mapMatrix (m := Fin k)).toMonoidHom u) := by
  ext p q
  simp [flattenGL]

end Flatten

/-! ## Elementary matrices and stabilization -/

section Elementary

variable {m ι R : Type*} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] [Ring R]

/-- The flattening of the elementary matrix `eᵢⱼ(r Eₐᵦ)` over `Matrix ι ι R` is the elementary
matrix `e₍ᵢ,ₐ₎₍ⱼ,ᵦ₎(r)` over `R`. -/
@[simp]
theorem compGL_transvectionUnit_single {i j : m} (hij : i ≠ j) (a b : ι) (r : R) :
    compGL m ι R (transvectionUnit hij (single a b r)) =
      transvectionUnit (fun h ↦ hij (congrArg Prod.fst h) : (i, a) ≠ (j, b)) r := by
  ext : 1
  rw [coe_compGL, coe_transvectionUnit_eq_one_add_single, coe_transvectionUnit_eq_one_add_single,
    Matrix.comp_one_add_single_single]

/-- Flattening carries elementary matrices over `Matrix ι ι R` to elementary matrices over `R`:
`eᵢⱼ(X)` flattens to the product of the elementary matrices `e₍ᵢ,ₐ₎₍ⱼ,ᵦ₎(X a b)`. -/
theorem map_compGL_elementarySubgroup_le :
    (elementarySubgroup m (Matrix ι ι R)).map (compGL m ι R).toMonoidHom ≤
      elementarySubgroup (m × ι) R := by
  refine Subgroup.map_le_iff_le_comap.2 (elementarySubgroup_le_iff.2 fun i j hij X ↦ ?_)
  induction X using Matrix.induction_on' with
  | h_zero => simp
  | h_add X Y hX hY =>
    rw [transvectionUnit_add]
    exact mul_mem hX hY
  | h_std_basis a b r =>
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, compGL_transvectionUnit_single]
    exact transvectionUnit_mem_elementarySubgroup _ _

/-- With two distinct block indices, every elementary matrix over `R` of size `m × ι` is the
flattening of an elementary matrix over `Matrix ι ι R`. -/
theorem elementarySubgroup_le_map_compGL [Nontrivial m] :
    elementarySubgroup (m × ι) R ≤
      (elementarySubgroup m (Matrix ι ι R)).map (compGL m ι R).toMonoidHom := by
  refine elementarySubgroup_le_iff.2 fun ⟨i, a⟩ ⟨j, b⟩ hp r ↦ ?_
  rw [Subgroup.mem_map_equiv]
  rcases eq_or_ne i j with rfl | hij
  · have hab : a ≠ b := fun h ↦ hp (h ▸ rfl)
    obtain ⟨k, hki⟩ := exists_ne i
    have hik := hki.symm
    have h₁ := transvectionUnit_mem_elementarySubgroup hik (single a b r)
    have h₂ := transvectionUnit_mem_elementarySubgroup hik.symm (single b b (1 : R))
    have hmem : ⁅transvectionUnit hik (single a b r), transvectionUnit hik.symm (single b b 1)⁆ ∈
        elementarySubgroup m (Matrix ι ι R) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
    convert hmem using 1
    rw [MulEquiv.symm_apply_eq]
    ext : 1
    rw [coe_compGL, coe_commutatorElement_transvectionUnit_of_mul_eq_zero hik (by simp [hab.symm]),
      single_mul_single_same, mul_one, Matrix.comp_one_add_single_single,
      coe_transvectionUnit_eq_one_add_single]
  · convert transvectionUnit_mem_elementarySubgroup hij (single a b r) using 1
    rw [MulEquiv.symm_apply_eq, compGL_transvectionUnit_single]

/-- **Flattening identifies the elementary subgroups**: when `m` has two distinct elements, the
flattening of `E m (Matrix ι ι R)` is `E (m × ι) R`. -/
theorem map_compGL_elementarySubgroup [Nontrivial m] :
    (elementarySubgroup m (Matrix ι ι R)).map (compGL m ι R).toMonoidHom =
      elementarySubgroup (m × ι) R :=
  le_antisymm map_compGL_elementarySubgroup_le elementarySubgroup_le_map_compGL

/-- With two distinct block indices, an invertible block matrix is elementary exactly when its
flattening is. -/
@[simp]
theorem compGL_mem_elementarySubgroup_iff [Nontrivial m] {u : GL m (Matrix ι ι R)} :
    compGL m ι R u ∈ elementarySubgroup (m × ι) R ↔ u ∈ elementarySubgroup m (Matrix ι ι R) := by
  rw [← map_compGL_elementarySubgroup, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

/-- With at least two blocks, an invertible block matrix is elementary exactly when its flattening
is. -/
@[simp]
theorem flattenGL_mem_elementarySubgroup_iff {k : ℕ} (hk : 2 ≤ k) {u : GL (Fin k) (Matrix ι ι R)} :
    flattenGL ι R k u ∈ elementarySubgroup (Fin (k * Fintype.card ι)) R ↔
      u ∈ elementarySubgroup (Fin k) (Matrix ι ι R) := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 hk
  rw [flattenGL, MulEquiv.trans_apply, Equiv.reindexGL_mem_elementarySubgroup_iff,
    compGL_mem_elementarySubgroup_iff]

/-- **Flattening commutes with stabilization**: flattening `u ⊕ 1` is stabilizing the
flattening of `u`. -/
theorem flattenGL_stabilizeGL {k l : ℕ} (h : k ≤ l) (u : GL (Fin k) (Matrix ι ι R)) :
    flattenGL ι R l (stabilizeGL (Matrix ι ι R) h u) =
      stabilizeGL R (Nat.mul_le_mul_right _ h) (flattenGL ι R k u) := by
  ext p q
  obtain ⟨⟨i, c⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, d⟩, rfl⟩ := finProdFinEquiv.surjective q
  obtain ⟨a, rfl⟩ := (Fintype.equivFin ι).surjective c
  obtain ⟨b, rfl⟩ := (Fintype.equivFin ι).surjective d
  rw [flattenGL_apply_finProdFinEquiv, coe_stabilizeGL_apply, coe_stabilizeGL_apply]
  split_ifs with h₁ h₂ h₂
  · rw [mk_finProdFinEquiv _ h₁.1, mk_finProdFinEquiv _ h₁.2, flattenGL_apply_finProdFinEquiv]
  · exact absurd ⟨(finProdFinEquiv_lt_mul_iff _ _).2 h₁.1,
      (finProdFinEquiv_lt_mul_iff _ _).2 h₁.2⟩ h₂
  · exact absurd ⟨(finProdFinEquiv_lt_mul_iff _ _).1 h₂.1,
      (finProdFinEquiv_lt_mul_iff _ _).1 h₂.2⟩ h₁
  · rcases eq_or_ne i j with rfl | hij
    · rcases eq_or_ne a b with rfl | hab
      · simp
      · rw [one_apply_eq, one_apply_ne hab, one_apply_ne (by simpa using hab)]
    · simp [hij]

end Elementary

/-! ## Morita invariance of `K₁` -/

namespace AlgebraicK1

variable {R : Type*} [Ring R] (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The class of a flattened block matrix in `K₁(R)` does not change under stabilization. -/
private theorem mk_flattenGL_stabilizeGL {k l : ℕ} (h : k ≤ l) (u : GL (Fin k) (Matrix ι ι R)) :
    mk R (l * Fintype.card ι) (flattenGL ι R l (stabilizeGL (Matrix ι ι R) h u)) =
      mk R (k * Fintype.card ι) (flattenGL ι R k u) := by
  rw [flattenGL_stabilizeGL, mk_stabilizeGL]

variable (R) in
/-- Flattening block matrices induces `K₁(Matrix ι ι R) →* K₁(R)`. -/
private def flattenHom : AlgebraicK1 (Matrix ι ι R) →* AlgebraicK1 R :=
  lift (fun k ↦ (mk R (k * Fintype.card ι)).comp (flattenGL ι R k).toMonoidHom)
    fun _ _ h u ↦ mk_flattenGL_stabilizeGL ι h u

private theorem flattenHom_mk (k : ℕ) (u : GL (Fin k) (Matrix ι ι R)) :
    flattenHom R ι (mk _ k u) = mk R (k * Fintype.card ι) (flattenGL ι R k u) :=
  lift_mk ..

/-- Flattening is injective on `K₁`: a block matrix whose flattening is stably elementary is
itself stably elementary, after stabilizing to at least two blocks. -/
private theorem flattenHom_injective [Nonempty ι] : Function.Injective (flattenHom R ι) := by
  refine (injective_iff_map_eq_one _).2 fun x hx ↦ ?_
  obtain ⟨k, u, rfl⟩ := exists_mk x
  rw [flattenHom_mk, mk_eq_one_iff] at hx
  obtain ⟨N, hN, hNu⟩ := hx
  have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
  set l := max (max k N) 2
  have hkl : k ≤ l := le_max_of_le_left (le_max_left _ _)
  have hNl : N ≤ l * Fintype.card ι :=
    (le_max_of_le_left (le_max_right _ _) : N ≤ l).trans (Nat.le_mul_of_pos_right _ hn)
  rw [mk_eq_one_iff]
  refine ⟨l, hkl, ?_⟩
  have hflat := map_stabilizeGL_elementarySubgroup_le hNl ⟨_, hNu, rfl⟩
  rw [stabilizeGL_stabilizeGL, ← flattenGL_stabilizeGL hkl] at hflat
  exact (flattenGL_mem_elementarySubgroup_iff (le_max_right _ _)).1 hflat

/-- Flattening is surjective on `K₁`: every class of `R` is represented at a stage `k * n`, where
flattening is bijective. -/
private theorem flattenHom_surjective [Nonempty ι] : Function.Surjective (flattenHom R ι) := by
  intro x
  obtain ⟨k, u, rfl⟩ := exists_mk x
  have hk : k ≤ k * Fintype.card ι := Nat.le_mul_of_pos_right _ Fintype.card_pos
  refine ⟨mk _ k ((flattenGL ι R k).symm (stabilizeGL R hk u)), ?_⟩
  rw [flattenHom_mk, MulEquiv.apply_symm_apply, mk_stabilizeGL]

variable (R) [Nonempty ι]

/-- **Morita invariance of algebraic `K₁`**: for a nonempty finite index type `ι`, flattening
block matrices is an isomorphism `K₁(Matrix ι ι R) ≃* K₁(R)`. -/
def matrixEquiv : AlgebraicK1 (Matrix ι ι R) ≃* AlgebraicK1 R :=
  MulEquiv.ofBijective (flattenHom R ι) ⟨flattenHom_injective ι, flattenHom_surjective ι⟩

variable {R}

/-- The Morita isomorphism sends the class of an invertible `k × k` block matrix to the class of
its flattening, of size `k * n`. -/
@[simp]
theorem matrixEquiv_mk (k : ℕ) (u : GL (Fin k) (Matrix ι ι R)) :
    matrixEquiv R ι (mk _ k u) = mk R (k * Fintype.card ι) (flattenGL ι R k u) :=
  flattenHom_mk ι k u

/-- The inverse Morita isomorphism sends the class of an invertible matrix of size `k * n` to the
class of the `k × k` block matrix with the same entries. -/
@[simp]
theorem matrixEquiv_symm_mk (k : ℕ) (u : GL (Fin (k * Fintype.card ι)) R) :
    (matrixEquiv R ι).symm (mk R (k * Fintype.card ι) u) = mk _ k ((flattenGL ι R k).symm u) := by
  rw [MulEquiv.symm_apply_eq, matrixEquiv_mk, MulEquiv.apply_symm_apply]

/-- The Morita isomorphism is natural in ring homomorphisms `f : R →+* S`: it intertwines
`K₁(f)` with `K₁` of `f` applied to the entries of `ι × ι` matrices. -/
theorem map_matrixEquiv {S : Type*} [Ring S] (f : R →+* S) (x : AlgebraicK1 (Matrix ι ι R)) :
    map f (matrixEquiv R ι x) = matrixEquiv S ι (map f.mapMatrix x) := by
  obtain ⟨k, u, rfl⟩ := exists_mk x
  rw [matrixEquiv_mk, map_mk, map_mk, matrixEquiv_mk, unitsMap_mapMatrix_flattenGL]

end AlgebraicK1

end TauCeti
