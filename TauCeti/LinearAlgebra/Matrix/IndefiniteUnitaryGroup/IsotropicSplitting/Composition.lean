/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.IsotropicSplitting
import TauCeti.Algebra.Lie.Orthogonal.Basic
import TauCeti.LinearAlgebra.Matrix.Congruence

/-!
# Composing isotropic splittings, and removing hyperbolic planes

An isotropic splitting `D` of a hermitian Gram matrix `A` on `n` over a core `A₀` on `n₀` along
`p` (`TauCeti.IsotropicSplitting`) is a Witt decomposition `R^n = l R^p ⊕ ι R^{n₀} ⊕ k R^p`. This
file builds new splittings from old ones by block computations with the frames.

* `TauCeti.IsotropicSplitting.reindex`: the frames `k` and `l` reindexed along `e : p ≃ p'`.
* `TauCeti.IsotropicSplitting.comp`: a splitting `D₁` of `A` over `A₁` along `p` followed by a
  splitting `D₂` of `A₁` over `A₀` along `q` gives a splitting of `A` over `A₀` along `p ⊕ q`, with
  frames `(k₁, ι₁ k₂)`, `(l₁, ι₁ l₂)` and core embedding `ι₁ ι₂`. Its coordinates are computed in
  `TauCeti.IsotropicSplitting.kCoord_comp`, `lCoord_comp` and `ιCoord_comp`.
* `TauCeti.IsotropicSplitting.hyperbolic`: the hyperbolic space on `p ⊕ p`, with Gram matrix
  `LieAlgebra.Orthogonal.JD p R = (0 1; 1 0)`, splits over the empty core with `l` the first and
  `k` the second copy of `p`.
* `TauCeti.IsotropicSplitting.removePlanes`: the orthogonal sum `(0 1; 1 0) ⊕ A₀` of `q`
  hyperbolic planes and a core `A₀` splits over `A₀` along `q`; this splitting removes the planes.
* `TauCeti.IsotropicSplitting.splitOff`: a splitting `D` along `p ⊕ q` restricts to a splitting
  along `p` over the core `(0 1; 1 0) ⊕ A₀`, whose new core embedding is `(l|_q, k|_q, ι)`.

The main result, `TauCeti.IsotropicSplitting.splitOff_comp_removePlanes`, is that composing
`D.splitOff` with `removePlanes` gives back `D`: every splitting along `p ⊕ q` factors through the
splitting that removes the `q` hyperbolic planes. These factorisations are used to move between the
mixed models of the Weil representation along isotropic frames of different ranks.

## Provenance

The hyperbolic splitting, the splitting that removes the planes, the composite of two splittings
and the factorisation of a splitting through the splitting that removes the planes correspond to
`New.hyperbolicSplitting`, `New.Exchange.removePlanes` and
`New.Exchange.exists_isBaseAdapted_comp_removePlanes` (file
`grh/src/Lib/Weil/MixedModel/AdaptedSplitting.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), where they are
stated for hermitian spaces with adelic frames over a CM field, together with the condition that the
adelic frames be orthonormal at the infinite places and integral at the finite places. Here the
algebraic constructions are stated for an arbitrary hermitian Gram matrix over a commutative ring
with involution.

## References

* M.-A. Knus, *Quadratic and Hermitian forms over rings* (1991), the Witt decomposition of a
  hermitian space.
-/

public section

open Matrix

namespace TauCeti

namespace IsotropicSplitting

open LieAlgebra.Orthogonal

variable {R : Type*} [CommRing R] [StarRing R]
  {n n₀ n₁ p q : Type*} [Fintype n] [Fintype n₀] [Fintype n₁] [Fintype p] [Fintype q]
  [DecidableEq n₀] [DecidableEq n₁] [DecidableEq p] [DecidableEq q]
  {A : Matrix n n R} {A₀ : Matrix n₀ n₀ R} {A₁ : Matrix n₁ n₁ R}

/-! ### Reindexing the frames -/

variable {p' : Type*} [Fintype p'] [DecidableEq p']

/-- The splitting along `p'` obtained by reindexing the frames `k` and `l` along `e : p ≃ p'`,
with the same core embedding. -/
def reindex (D : IsotropicSplitting A A₀ p) (e : p ≃ p') : IsotropicSplitting A A₀ p' where
  k := D.k.submatrix id e.symm
  l := D.l.submatrix id e.symm
  ι := D.ι
  isHermitian := D.isHermitian
  isUnit_core := D.isUnit_core
  gram_kk := by
    rw [conjTranspose_submatrix, submatrix_mul_mul_submatrix, D.gram_kk]
    simp
  gram_ll := by
    rw [conjTranspose_submatrix, submatrix_mul_mul_submatrix, D.gram_ll]
    simp
  gram_lk := by
    rw [conjTranspose_submatrix, submatrix_mul_mul_submatrix, D.gram_lk, submatrix_one_equiv]
  gram_ιι := D.gram_ιι
  gram_ιk := by
    rw [← submatrix_id_id D.ι, conjTranspose_submatrix, submatrix_mul_mul_submatrix, D.gram_ιk]
    simp
  gram_ιl := by
    rw [← submatrix_id_id D.ι, conjTranspose_submatrix, submatrix_mul_mul_submatrix, D.gram_ιl]
    simp
  card_eq := by rw [D.card_eq, Fintype.card_congr e]

section Reindex

variable (D : IsotropicSplitting A A₀ p) (e : p ≃ p')

@[simp] theorem reindex_k : (D.reindex e).k = D.k.submatrix id e.symm := (rfl)

@[simp] theorem reindex_l : (D.reindex e).l = D.l.submatrix id e.symm := (rfl)

@[simp] theorem reindex_ι : (D.reindex e).ι = D.ι := (rfl)

@[simp]
theorem reindex_refl : D.reindex (Equiv.refl p) = D := by
  ext <;> simp

theorem reindex_reindex {p'' : Type*} [Fintype p''] [DecidableEq p''] (e' : p' ≃ p'') :
    (D.reindex e).reindex e' = D.reindex (e.trans e') := by
  ext <;> simp

end Reindex

/-! ### Composition -/

/-- The **composite** of a splitting `D₁` of `A` over `A₁` along `p` and a splitting `D₂` of `A₁`
over `A₀` along `q`: the splitting of `A` over `A₀` along `p ⊕ q` with frames `(k₁, ι₁ k₂)` and
`(l₁, ι₁ l₂)` and core embedding `ι₁ ι₂`. -/
def comp (D₁ : IsotropicSplitting A A₁ p) (D₂ : IsotropicSplitting A₁ A₀ q) :
    IsotropicSplitting A A₀ (p ⊕ q) where
  k := fromCols D₁.k (D₁.ι * D₂.k)
  l := fromCols D₁.l (D₁.ι * D₂.l)
  ι := D₁.ι * D₂.ι
  isHermitian := D₁.isHermitian
  isUnit_core := D₂.isUnit_core
  gram_kk := by
    simp [conjTranspose_fromCols_eq_fromRows_conjTranspose, conjTranspose_mul, Matrix.mul_assoc]
  gram_ll := by
    simp [conjTranspose_fromCols_eq_fromRows_conjTranspose, conjTranspose_mul, Matrix.mul_assoc]
  gram_lk := by
    simp [conjTranspose_fromCols_eq_fromRows_conjTranspose, conjTranspose_mul, Matrix.mul_assoc,
      ← fromBlocks_one]
  gram_ιι := by
    simp [conjTranspose_mul, Matrix.mul_assoc]
  gram_ιk := by
    simp [conjTranspose_mul, Matrix.mul_assoc]
  gram_ιl := by
    simp [conjTranspose_mul, Matrix.mul_assoc]
  card_eq := by
    rw [D₁.card_eq, D₂.card_eq, Fintype.card_sum]
    ring

section Comp

variable (D₁ : IsotropicSplitting A A₁ p) (D₂ : IsotropicSplitting A₁ A₀ q)

@[simp] theorem comp_k : (D₁.comp D₂).k = fromCols D₁.k (D₁.ι * D₂.k) := (rfl)

@[simp] theorem comp_l : (D₁.comp D₂).l = fromCols D₁.l (D₁.ι * D₂.l) := (rfl)

@[simp] theorem comp_ι : (D₁.comp D₂).ι = D₁.ι * D₂.ι := (rfl)

/-- The coordinate along `k` of the composite: the coordinate along `k₁`, followed by the
coordinate along `k₂` of the coordinate along the core `ι₁`. -/
@[simp]
theorem kCoord_comp :
    (D₁.comp D₂).kCoord = fromRows D₁.kCoord (D₂.kCoord * D₁.ιCoord) := by
  rw [kCoord_def]
  simp [conjTranspose_fromCols_eq_fromRows_conjTranspose, conjTranspose_mul, Matrix.mul_assoc,
    fromRows_mul]

/-- The coordinate along `l` of the composite: the coordinate along `l₁`, followed by the
coordinate along `l₂` of the coordinate along the core `ι₁`. -/
@[simp]
theorem lCoord_comp :
    (D₁.comp D₂).lCoord = fromRows D₁.lCoord (D₂.lCoord * D₁.ιCoord) := by
  rw [lCoord_def]
  simp [conjTranspose_fromCols_eq_fromRows_conjTranspose, conjTranspose_mul, Matrix.mul_assoc,
    fromRows_mul]

/-- The coordinate along the core of the composite is the composite of the coordinates along the
cores. -/
@[simp]
theorem ιCoord_comp : (D₁.comp D₂).ιCoord = D₂.ιCoord * D₁.ιCoord := by
  rw [ιCoord_def, D₂.ιCoord_mul, comp_ι, conjTranspose_mul, Matrix.mul_assoc,
    Matrix.mul_assoc D₂.ιᴴ, D₁.conjTranspose_ι_mul]
  simp only [Matrix.mul_assoc]

end Comp

/-! ### The hyperbolic splitting and the splitting that removes the planes -/

/-- The **hyperbolic splitting**: the hyperbolic space on `p ⊕ p`, with Gram matrix
`JD p R = (0 1; 1 0)`, splits over an empty core along `p`, with `l` the first and `k` the second
copy of `p`. -/
def hyperbolic (p : Type*) [Fintype p] [DecidableEq p] [IsEmpty n₀] (A₀ : Matrix n₀ n₀ R) :
    IsotropicSplitting (JD p R) A₀ p where
  k := fromRows 0 1
  l := fromRows 1 0
  ι := 0
  isHermitian := isHermitian_JD p R
  isUnit_core := isUnit_of_subsingleton A₀
  gram_kk := by
    simp [JD, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows]
  gram_ll := by
    simp [JD, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows]
  gram_lk := by
    simp [JD, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows]
  gram_ιι := Subsingleton.elim _ _
  gram_ιk := Subsingleton.elim _ _
  gram_ιl := Subsingleton.elim _ _
  card_eq := by
    rw [Fintype.card_sum, Fintype.card_eq_zero (α := n₀)]
    ring

section Hyperbolic

variable (p : Type*) [Fintype p] [DecidableEq p] [IsEmpty n₀] (A₀ : Matrix n₀ n₀ R)

@[simp] theorem hyperbolic_k : (hyperbolic p A₀).k = fromRows 0 1 := (rfl)

@[simp] theorem hyperbolic_l : (hyperbolic p A₀).l = fromRows 1 0 := (rfl)

@[simp] theorem hyperbolic_ι : (hyperbolic p A₀).ι = 0 := (rfl)

end Hyperbolic

/-- The splitting that **removes the planes**: the orthogonal sum `JD q R ⊕ A₀` of `q`
hyperbolic planes and a hermitian invertible core `A₀` splits over `A₀` along `q`, with `l` the
first and `k` the second copy of `q` in the hyperbolic summand, and `ι` the inclusion of the
second summand. -/
def removePlanes (q : Type*) [Fintype q] [DecidableEq q] (hA₀ : A₀.IsHermitian)
    (hu : IsUnit A₀) : IsotropicSplitting (fromBlocks (JD q R) 0 0 A₀) A₀ q where
  k := fromRows (fromRows 0 1) 0
  l := fromRows (fromRows 1 0) 0
  ι := fromRows 0 1
  isHermitian := by
    rw [IsHermitian, fromBlocks_conjTranspose, (isHermitian_JD q R).eq, hA₀.eq]
    simp
  isUnit_core := hu
  gram_kk := by
    simp [JD, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows]
  gram_ll := by
    simp [JD, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows]
  gram_lk := by
    simp [JD, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows]
  gram_ιι := by
    simp [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows]
  gram_ιk := by
    simp [JD, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows]
  gram_ιl := by
    simp [JD, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows]
  card_eq := by
    simp only [Fintype.card_sum]
    ring

section RemovePlanes

variable (q : Type*) [Fintype q] [DecidableEq q] (hA₀ : A₀.IsHermitian) (hu : IsUnit A₀)

@[simp]
theorem removePlanes_k : (removePlanes q hA₀ hu).k = fromRows (fromRows 0 1) 0 := (rfl)

@[simp]
theorem removePlanes_l : (removePlanes q hA₀ hu).l = fromRows (fromRows 1 0) 0 := (rfl)

@[simp] theorem removePlanes_ι : (removePlanes q hA₀ hu).ι = fromRows 0 1 := (rfl)

end RemovePlanes

/-! ### Splitting off hyperbolic planes -/

section SplitOff

variable (D : IsotropicSplitting A A₀ (p ⊕ q))

/-- A splitting `D` along `p ⊕ q` restricts to a splitting along `p` over the orthogonal sum
`JD q R ⊕ A₀` of `q` hyperbolic planes and the core of `D`: its frames are the columns of `k` and
`l` indexed by `p`, and its core embedding is `(l|_q, k|_q, ι)`. -/
def splitOff : IsotropicSplitting A (fromBlocks (JD q R) 0 0 A₀) p where
  k := D.k.submatrix id Sum.inl
  l := D.l.submatrix id Sum.inl
  ι := fromCols (fromCols (D.l.submatrix id Sum.inr) (D.k.submatrix id Sum.inr)) D.ι
  isHermitian := D.isHermitian
  isUnit_core := by
    rw [isUnit_fromBlocks_zero₂₁]
    exact ⟨isUnit_JD q R, D.isUnit_core⟩
  gram_kk := by
    rw [conjTranspose_submatrix, submatrix_mul_mul_submatrix, D.gram_kk]
    simp
  gram_ll := by
    rw [conjTranspose_submatrix, submatrix_mul_mul_submatrix, D.gram_ll]
    simp
  gram_lk := by
    rw [conjTranspose_submatrix, submatrix_mul_mul_submatrix, D.gram_lk]
    exact submatrix_one_embedding ⟨Sum.inl, Sum.inl_injective⟩
  gram_ιι := by
    rw [← submatrix_id_id D.ι]
    simp only [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, mul_fromCols,
      conjTranspose_submatrix, submatrix_mul_mul_submatrix, D.gram_ll, D.gram_kl, D.gram_lk,
      D.gram_kk, D.gram_lι, D.gram_kι, D.gram_ιl, D.gram_ιk, D.gram_ιι,
      submatrix_one _ Sum.inr_injective]
    ext ((i | i) | i) ((j | j) | j) <;> simp [JD]
  gram_ιk := by
    rw [← submatrix_id_id D.ι]
    simp only [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul,
      conjTranspose_submatrix, submatrix_mul_mul_submatrix, D.gram_lk, D.gram_kk, D.gram_ιk]
    ext ((_ | _) | _) _ <;> simp
  gram_ιl := by
    rw [← submatrix_id_id D.ι]
    simp only [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul,
      conjTranspose_submatrix, submatrix_mul_mul_submatrix, D.gram_ll, D.gram_kl, D.gram_ιl]
    ext ((_ | _) | _) _ <;> simp
  card_eq := by
    rw [D.card_eq]
    simp only [Fintype.card_sum]
    ring

@[simp] theorem splitOff_k : D.splitOff.k = D.k.submatrix id Sum.inl := (rfl)

@[simp] theorem splitOff_l : D.splitOff.l = D.l.submatrix id Sum.inl := (rfl)

@[simp]
theorem splitOff_ι :
    D.splitOff.ι = fromCols (fromCols (D.l.submatrix id Sum.inr) (D.k.submatrix id Sum.inr)) D.ι :=
  (rfl)

/-- **Every splitting along `p ⊕ q` factors through the splitting that removes the planes**:
the composite of `D.splitOff` (along `p`, over `JD q R ⊕ A₀`) with `removePlanes` (along `q`,
over `A₀`) is `D`. -/
theorem splitOff_comp_removePlanes :
    D.splitOff.comp (removePlanes q D.isHermitian_core D.isUnit_core) = D := by
  ext1
  · ext _ (_ | _) <;> simp [fromCols_mul_fromRows]
  · ext _ (_ | _) <;> simp [fromCols_mul_fromRows]
  · simp [fromCols_mul_fromRows]

end SplitOff

end IsotropicSplitting

end TauCeti
