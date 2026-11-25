/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.PerfectMatching.Crossing
public import TauCeti.Logic.Equiv.Fin.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.Action

import TauCeti.LinearAlgebra.Matrix.Congruence
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The symplectic Brauer boundary matrix and Pfaffian crossing-sign formula

Read the `2 * k` boundary points of a `k`-strand Brauer diagram `D` in counterclockwise order via
`TauCeti.finSumFinRevEquiv`: `0, …, k - 1` along the bottom from left to right, then
`k, …, 2k - 1` along the top from right to left. In this linear order `D` becomes a perfect
matching `M` of `Fin (k + k)` with a Pfaffian crossing sign `M.crossingSign ∈ ℤˣ` and a
skew-symmetric pair-weight product `M.weight` built from `Matrix.J ι R`. Their product defines the
computable **symplectic boundary matrix** `TauCeti.BrauerDiagram.symplecticBoundaryMatrix`
(Goodman–Wallach §10.1.1), without choosing an auxiliary permutation representative for `D`.

Using the Pfaffian sign-transformation law
`TauCeti.PerfectMatching.crossingSign_mul_weight_congr_perm_of_skew`, any boundary permutation `φ`
transporting `permToBrauer 1` to `D` computes the `(v, u)` entry of `symplecticBoundaryMatrix` as
`sign φ` times the product of `Matrix.J` along the `k` arcs
(`TauCeti.BrauerDiagram.symplecticBoundaryMatrix_apply_of_congr`). Dualizing the input slots on the
right by `(Matrix.J ι R).kroneckerPower (Fin k)` converts `Matrix.J` on each arc into
`TauCeti.BrauerDiagram.symplecticArcMatrix`, yielding the Pfaffian crossing-sign formula
`TauCeti.BrauerDiagram.symplecticActionMatrix_eq_symplecticBoundaryMatrix_mul_kroneckerPower` for
`TauCeti.BrauerDiagram.symplecticActionMatrix` and its inverse
`TauCeti.BrauerDiagram.symplecticBoundaryMatrix_eq_symplecticActionMatrix_mul_kroneckerPower`.

In addition, every matrix `A` satisfying `A * J * Aᵀ = J` leaves `symplecticBoundaryMatrix`
invariant under congruence by its Kronecker power
(`TauCeti.BrauerDiagram.kroneckerPower_mul_symplecticBoundaryMatrix_mul_transpose`), the matrix
counterpart of `Sp_{2n}`-invariance of the signed symplectic matching tensors, while transposing or
conjugate-transposing `symplecticBoundaryMatrix` reflects the diagram up to `(-1) ^ k`.

## Main definitions

* `TauCeti.BrauerDiagram.symplecticBoundaryMatrix`: the computable Pfaffian-signed boundary weight
  matrix of a Brauer diagram with pair weights given by `Matrix.J`.

## Main results

* `TauCeti.BrauerDiagram.symplecticBoundaryMatrix_permToBrauer_one_apply`: the boundary matrix of
  the identity diagram pairs each input label with the matching output label through `Matrix.J`.
* `TauCeti.BrauerDiagram.symplecticBoundaryMatrix_apply_of_congr`: boundary-permutation formula for
  `symplecticBoundaryMatrix`.
* `TauCeti.BrauerDiagram.symplecticBoundaryMatrix_relabel_apply`,
  `TauCeti.BrauerDiagram.map_symplecticBoundaryMatrix`, and
  `TauCeti.BrauerDiagram.reindex_symplecticBoundaryMatrix`: compatibility with boundary
  relabelling, coefficient maps, and coordinate reindexing.
* `TauCeti.BrauerDiagram.kroneckerPower_mul_symplecticBoundaryMatrix_mul_transpose_apply_of_congr`:
  bilinear Kronecker congruence of `symplecticBoundaryMatrix`, congruating `Matrix.J` on each arc.
* `TauCeti.BrauerDiagram.symplecticActionMatrix_eq_symplecticBoundaryMatrix_mul_kroneckerPower` and
  `TauCeti.BrauerDiagram.symplecticBoundaryMatrix_eq_symplecticActionMatrix_mul_kroneckerPower`:
  **the Pfaffian crossing-sign decomposition** relating `symplecticActionMatrix` and
  `symplecticBoundaryMatrix` via `(±Matrix.J ι R).kroneckerPower (Fin k)`.
* `TauCeti.BrauerDiagram.kroneckerPower_mul_symplecticBoundaryMatrix_mul_transpose`: congruence
  invariance of `symplecticBoundaryMatrix` under any matrix satisfying `A * J * Aᵀ = J`.
* `TauCeti.BrauerDiagram.transpose_symplecticBoundaryMatrix` and
  `TauCeti.BrauerDiagram.conjTranspose_symplecticBoundaryMatrix`: transposing or
  conjugate-transposing `symplecticBoundaryMatrix` gives `(-1) ^ k` times that of `D.flip`.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Dipper, S. Doty, and J. Hu, *Brauer algebras, symplectic Schur algebras and Schur-Weyl
  duality*, Transactions of the American Mathematical Society 360 (2008), 189-213, §1.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

open scoped Matrix

namespace TauCeti.BrauerDiagram

universe u

section BoundaryMatrix

variable (R : Type u) [CommRing R] (ι : Type*) [DecidableEq ι] {k : ℕ}

/-- **The symplectic boundary matrix of a Brauer diagram.** Numbering the `2 * k` boundary points
counterclockwise by `TauCeti.finSumFinRevEquiv` (bottom left-to-right, then top right-to-left),
the `(v, u)` entry is the Pfaffian crossing sign of the resulting perfect matching times the
product of `Matrix.J ι R` evaluated on the labels `Sum.elim u v` at the two endpoints of each arc
in increasing counterclockwise order. -/
def symplecticBoundaryMatrix (D : BrauerDiagram k) :
    Matrix (Fin k → ι ⊕ ι) (Fin k → ι ⊕ ι) R :=
  Matrix.of fun v u =>
    (((PerfectMatching.congr (finSumFinRevEquiv k k (k + k) rfl) D).crossingSign : ℤ) : R) *
      (PerfectMatching.congr (finSumFinRevEquiv k k (k + k) rfl) D).weight fun x y =>
        Matrix.J ι R
          (Sum.elim u v ((finSumFinRevEquiv k k (k + k) rfl).symm x))
          (Sum.elim u v ((finSumFinRevEquiv k k (k + k) rfl).symm y))

/-- Entrywise formula for `TauCeti.BrauerDiagram.symplecticBoundaryMatrix`. -/
theorem symplecticBoundaryMatrix_apply (D : BrauerDiagram k) (v u : Fin k → ι ⊕ ι) :
    D.symplecticBoundaryMatrix R ι v u =
      (((PerfectMatching.congr (finSumFinRevEquiv k k (k + k) rfl) D).crossingSign : ℤ) : R) *
        (PerfectMatching.congr (finSumFinRevEquiv k k (k + k) rfl) D).weight fun x y =>
          Matrix.J ι R
            (Sum.elim u v ((finSumFinRevEquiv k k (k + k) rfl).symm x))
            (Sum.elim u v ((finSumFinRevEquiv k k (k + k) rfl).symm y)) :=
  (rfl)

/-- The boundary matrix of the identity diagram pairs each input label with the matching output
label through `Matrix.J`. -/
@[simp]
theorem symplecticBoundaryMatrix_permToBrauer_one_apply (v u : Fin k → ι ⊕ ι) :
    (permToBrauer 1).symplecticBoundaryMatrix R ι v u =
      ∏ i : Fin k, Matrix.J ι R (u i) (v i) := by
  let e := finSumFinRevEquiv k k (k + k) rfl
  have hval_inl (i : Fin k) :
      (PerfectMatching.congr e (permToBrauer 1)).val (e (Sum.inl i)) = e (Sum.inr i) := by
    simp [Equiv.Perm.one_def]
  have hval_inr (j : Fin k) :
      (PerfectMatching.congr e (permToBrauer 1)).val (e (Sum.inr j)) = e (Sum.inl j) := by
    simp [Equiv.Perm.one_def]
  have hnc : (PerfectMatching.congr e (permToBrauer 1)).val.IsNoncrossingMatching := by
    rw [Equiv.Perm.isNoncrossingMatching_iff]
    intro a b hab hba hma
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    rcases x with i | i
    · rcases y with j | j
      · rw [hval_inl i, hval_inl j] at hma
        have hij : i < j := (finSumFinRevEquiv_inl_lt_inl_iff ..).mp hab
        have hji : j < i := (finSumFinRevEquiv_inr_lt_inr_iff ..).mp hma
        exact lt_asymm hij hji
      · rw [hval_inl i, hval_inr j] at hma
        exact not_finSumFinRevEquiv_inr_lt_inl k k (k + k) rfl j i hma
    · rw [hval_inr i] at hba
      exact not_lt_of_gt (lt_trans hab hba) (finSumFinRevEquiv_inl_lt_inr k k (k + k) rfl i i)
  rw [symplecticBoundaryMatrix_apply, PerfectMatching.crossingSign_of_isNoncrossingMatching hnc]
  simp only [Units.val_one, Int.cast_one, one_mul, PerfectMatching.weight_def]
  rw [← Equiv.prod_comp e, Fintype.prod_sum_type]
  refine (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => ?_)
    (Finset.prod_eq_one fun j _ => ?_)).trans (mul_one _) <;> simp [e]

variable {R ι} in
/-- **Boundary-permutation formula for `symplecticBoundaryMatrix`.** For any boundary permutation
`φ` transporting `permToBrauer 1` to `D`, the `(v, u)` entry of `D.symplecticBoundaryMatrix R ι` is
`sign φ` times the product of `Matrix.J` along the `k` arcs `(φ (Sum.inl i), φ (Sum.inr i))`. -/
theorem symplecticBoundaryMatrix_apply_of_congr {D : BrauerDiagram k}
    {φ : Equiv.Perm (Fin k ⊕ Fin k)}
    (hφ : PerfectMatching.congr φ (permToBrauer 1) = D) (v u : Fin k → ι ⊕ ι) :
    D.symplecticBoundaryMatrix R ι v u =
      ((Equiv.Perm.sign φ : ℤ) : R) *
        ∏ i : Fin k, Matrix.J ι R
          (Sum.elim u v (φ (Sum.inl i))) (Sum.elim u v (φ (Sum.inr i))) := by
  let e := finSumFinRevEquiv k k (k + k) rfl
  let ψ : Equiv.Perm (Fin (k + k)) := e.permCongr φ
  have heq : φ.trans e = e.trans ψ := Equiv.ext fun x => by simp [ψ]
  have hcongr : PerfectMatching.congr e D =
      PerfectMatching.congr ψ (PerfectMatching.congr e (permToBrauer 1)) := by
    rw [← hφ, PerfectMatching.congr_trans, PerfectMatching.congr_trans, heq]
  have hsign : Equiv.Perm.sign ψ = Equiv.Perm.sign φ := Equiv.Perm.sign_permCongr e φ
  let u' : Fin k → ι ⊕ ι := fun i => Sum.elim u v (φ (Sum.inl i))
  let v' : Fin k → ι ⊕ ι := fun i => Sum.elim u v (φ (Sum.inr i))
  have helim (x : Fin (k + k)) :
      Sum.elim u v (e.symm (ψ x)) = Sum.elim u' v' (e.symm x) := by
    simp only [ψ, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    rcases e.symm x with i | i <;> rfl
  have hw : (fun x y => Matrix.J ι R (Sum.elim u v (e.symm (ψ x)))
        (Sum.elim u v (e.symm (ψ y)))) =
      fun x y => Matrix.J ι R (Sum.elim u' v' (e.symm x)) (Sum.elim u' v' (e.symm y)) := by
    funext x y
    rw [helim, helim]
  rw [symplecticBoundaryMatrix_apply, hcongr,
    PerfectMatching.crossingSign_mul_weight_congr_perm_of_skew _ ψ
      (fun _ _ => Matrix.J_apply_swap ι R _ _),
    hsign, hw, ← symplecticBoundaryMatrix_apply R ι (permToBrauer 1) v' u',
    symplecticBoundaryMatrix_permToBrauer_one_apply]

/-- Relabelling the bottom boundary by `σ` and the top boundary by `τ` permutes the column and row
labellings of `symplecticBoundaryMatrix` and multiplies by `sign σ * sign τ`. -/
theorem symplecticBoundaryMatrix_relabel_apply (D : BrauerDiagram k) (σ τ : Equiv.Perm (Fin k))
    (v u : Fin k → ι ⊕ ι) :
    (D.relabel σ τ).symplecticBoundaryMatrix R ι v u =
      ((Equiv.Perm.sign σ * Equiv.Perm.sign τ : ℤ) : R) *
        D.symplecticBoundaryMatrix R ι (v ∘ τ) (u ∘ σ) := by
  obtain ⟨φ, hφ⟩ := D.exists_congr_permToBrauer_one
  have hrel : PerfectMatching.congr (Equiv.Perm.sumCongr σ τ * φ) (permToBrauer 1) =
      D.relabel σ τ := by
    rw [relabel_def, PerfectMatching.congr_mul, hφ]
  have helim (z : Fin k ⊕ Fin k) :
      Sum.elim u v (Sum.map σ τ z) = Sum.elim (u ∘ σ) (v ∘ τ) z := by
    cases z <;> rfl
  rw [symplecticBoundaryMatrix_apply_of_congr hrel, symplecticBoundaryMatrix_apply_of_congr hφ,
    Equiv.Perm.sign.map_mul, Equiv.Perm.sign_sumCongr]
  simp only [Units.val_mul, Int.cast_mul, Equiv.Perm.mul_apply, Equiv.Perm.sumCongr_apply, helim,
    mul_assoc]

private theorem map_ringHom_symplecticBoundaryMatrix {R₀ S : Type*} [CommRing R₀] [CommRing S]
    (f : R₀ →+* S) (D : BrauerDiagram k) :
    (D.symplecticBoundaryMatrix R₀ ι).map f = D.symplecticBoundaryMatrix S ι := by
  ext v u
  rw [Matrix.map_apply, symplecticBoundaryMatrix_apply, symplecticBoundaryMatrix_apply, map_mul,
    map_intCast, PerfectMatching.map_weight]
  congr 1
  refine PerfectMatching.weight_congr _ fun x _ => ?_
  simpa only [Matrix.map_apply] using congrFun (congrFun (Matrix.map_J ι f) _) _

variable {R} in
/-- **Functoriality in the coefficient ring**: applying an additive `1`-preserving map entrywise to
`symplecticBoundaryMatrix` gives the symplectic boundary matrix over the target ring, since every
entry lies in the prime subring. -/
@[simp]
theorem map_symplecticBoundaryMatrix {F S : Type*} [CommRing S] [FunLike F R S]
    [AddMonoidHomClass F R S] [OneHomClass F R S] (f : F) (D : BrauerDiagram k) :
    (D.symplecticBoundaryMatrix R ι).map f = D.symplecticBoundaryMatrix S ι := by
  rw [← map_ringHom_symplecticBoundaryMatrix ι (Int.castRingHom R) D,
    ← map_ringHom_symplecticBoundaryMatrix ι (Int.castRingHom S) D, Matrix.map_map]
  ext v u
  simpa only [Matrix.map_apply, Function.comp_apply, Int.coe_castRingHom] using
    map_intCast' f (map_one f) (D.symplecticBoundaryMatrix ℤ ι v u)

/-- **Coordinate-index functoriality**: reindexing the coordinate half-space along `e : ι₁ ≃ ι₂`
reindexes the rows and columns of `symplecticBoundaryMatrix` along the induced equivalence on
strand labellings. -/
theorem reindex_symplecticBoundaryMatrix {ι₁ ι₂ : Type*} [DecidableEq ι₁] [DecidableEq ι₂]
    (e : ι₁ ≃ ι₂) (D : BrauerDiagram k) :
    Matrix.reindex
        (Equiv.piCongrRight fun _ : Fin k => Equiv.sumCongr e e)
        (Equiv.piCongrRight fun _ : Fin k => Equiv.sumCongr e e)
        (D.symplecticBoundaryMatrix R ι₁) =
      D.symplecticBoundaryMatrix R ι₂ := by
  let eSum : ι₁ ⊕ ι₁ ≃ ι₂ ⊕ ι₂ := Equiv.sumCongr e e
  let eFun : (Fin k → ι₁ ⊕ ι₁) ≃ (Fin k → ι₂ ⊕ ι₂) := Equiv.piCongrRight fun _ => eSum
  have helim (v u : Fin k → ι₂ ⊕ ι₂) (z : Fin k ⊕ Fin k) :
      Sum.elim (eFun.symm u) (eFun.symm v) z = eSum.symm (Sum.elim u v z) := by
    cases z <;> rfl
  ext v u
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, symplecticBoundaryMatrix_apply,
    symplecticBoundaryMatrix_apply]
  congr 1
  refine PerfectMatching.weight_congr _ fun x _ => ?_
  rw [helim, helim]
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply] using
    congrFun (congrFun (Matrix.reindex_sumCongr_J R e) _) _

/-- **Transposing the symplectic boundary matrix reflects the diagram up to `(-1) ^ k`.** -/
@[simp]
theorem transpose_symplecticBoundaryMatrix (D : BrauerDiagram k) :
    (D.symplecticBoundaryMatrix R ι)ᵀ =
      (-1 : R) ^ k • D.flip.symplecticBoundaryMatrix R ι := by
  let e := finSumFinRevEquiv k k (k + k) rfl
  have hrev (x : Fin (k + k)) : e.symm (Fin.revPerm x) = (e.symm x).swap :=
    e.injective <| by
      rw [Equiv.apply_symm_apply, finSumFinRevEquiv_swap rfl, Equiv.apply_symm_apply,
        Fin.revPerm_apply]
  have hflip : PerfectMatching.congr e D.flip =
      PerfectMatching.congr Fin.revPerm (PerfectMatching.congr e D) := by
    have he : (Equiv.sumComm (Fin k) (Fin k)).trans e = e.trans Fin.revPerm :=
      Equiv.ext fun z => by
        rw [Equiv.trans_apply, Equiv.sumComm_apply, finSumFinRevEquiv_swap rfl,
          Equiv.trans_apply, Fin.revPerm_apply]
    rw [BrauerDiagram.flip_def, PerfectMatching.congr_trans, PerfectMatching.congr_trans, he]
  ext v u
  rw [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
    symplecticBoundaryMatrix_apply, symplecticBoundaryMatrix_apply, hflip,
    PerfectMatching.crossingSign_congr_revPerm,
    PerfectMatching.weight_congr_strictAnti_of_skew _ Fin.revPerm
      (fun _ _ h => Fin.rev_lt_rev.mpr h) (fun _ _ => Matrix.J_apply_swap ι R _ _)]
  have hcard : Fintype.card (Fin (k + k)) / 2 = k := by simp; omega
  have hw : (fun x y => Matrix.J ι R (Sum.elim u v (e.symm (Fin.revPerm x)))
        (Sum.elim u v (e.symm (Fin.revPerm y)))) =
      (fun x y => Matrix.J ι R (Sum.elim v u (e.symm x)) (Sum.elim v u (e.symm y))) := by
    funext x y
    rw [hrev x, hrev y]
    exact congrArg₂ (Matrix.J ι R)
      (congrFun (Sum.elim_swap (f := u) (g := v)) _)
      (congrFun (Sum.elim_swap (f := u) (g := v)) _)
  have hsign : (-1 : R) ^ k * (-1 : R) ^ k = 1 := by simp [← mul_pow]
  rw [hcard, hw, ← mul_assoc, ← mul_assoc, mul_right_comm ((-1 : R) ^ k), hsign, one_mul]

/-- **Conjugate-transposing the symplectic boundary matrix reflects the diagram up to
`(-1) ^ k`.** -/
@[simp]
theorem conjTranspose_symplecticBoundaryMatrix [StarRing R] (D : BrauerDiagram k) :
    (D.symplecticBoundaryMatrix R ι)ᴴ =
      (-1 : R) ^ k • D.flip.symplecticBoundaryMatrix R ι := by
  rw [← transpose_symplecticBoundaryMatrix,
    ← map_symplecticBoundaryMatrix ι (Int.castRingHom R) D]
  ext v u
  simp [Matrix.conjTranspose_apply]

end BoundaryMatrix

/-! ### Decomposition of `symplecticActionMatrix` and congruence invariance -/

section Fintype

variable (R : Type u) [CommRing R] (ι : Type*) [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- Reindexing equivalence sending a boundary labelling `ℓ : Fin k ⊕ Fin k → α` to the family of
endpoint label pairs `(ℓ (φ (Sum.inl i)), ℓ (φ (Sum.inr i)))` along the `k` arcs of `φ`. -/
private def arcLabellingEquiv {α : Type*} (φ : Equiv.Perm (Fin k ⊕ Fin k)) :
    (Fin k ⊕ Fin k → α) ≃ (Fin k → α × α) :=
  (Equiv.arrowCongr φ (Equiv.refl α)).symm.trans <|
    (Equiv.sumArrowEquivProdArrow (Fin k) (Fin k) α).trans
      (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => α) (fun _ => α)).symm

@[simp]
private theorem arcLabellingEquiv_apply_fst {α : Type*} (φ : Equiv.Perm (Fin k ⊕ Fin k))
    (ℓ : Fin k ⊕ Fin k → α) (i : Fin k) :
    (arcLabellingEquiv φ ℓ i).1 = ℓ (φ (Sum.inl i)) := by
  simp [arcLabellingEquiv, Equiv.arrowCongr, Equiv.sumArrowEquivProdArrow,
    Equiv.arrowProdEquivProdArrow]

@[simp]
private theorem arcLabellingEquiv_apply_snd {α : Type*} (φ : Equiv.Perm (Fin k ⊕ Fin k))
    (ℓ : Fin k ⊕ Fin k → α) (i : Fin k) :
    (arcLabellingEquiv φ ℓ i).2 = ℓ (φ (Sum.inr i)) := by
  simp [arcLabellingEquiv, Equiv.arrowCongr, Equiv.sumArrowEquivProdArrow,
    Equiv.arrowProdEquivProdArrow]

/-- Combining the double sum over top and bottom strand labellings `(w₁, w₂)` into a single sum
over boundary labellings `ℓ : Fin k ⊕ Fin k → ι ⊕ ι` via `Equiv.sumArrowEquivProdArrow`. -/
private theorem sum_kronecker_boundary_terms {R : Type*} [CommRing R]
    (φ : Equiv.Perm (Fin k ⊕ Fin k))
    (P : Fin k ⊕ Fin k → Matrix (ι ⊕ ι) (ι ⊕ ι) R) (u v : Fin k → ι ⊕ ι) :
    (∑ w₁ : Fin k → ι ⊕ ι, ∑ w₂ : Fin k → ι ⊕ ι,
        (∏ z : Fin k ⊕ Fin k, P z (Sum.elim u v z) (Sum.elim w₂ w₁ z)) *
          ∏ i : Fin k, Matrix.J ι R
            (Sum.elim w₂ w₁ (φ (Sum.inl i))) (Sum.elim w₂ w₁ (φ (Sum.inr i)))) =
      ∑ ℓ : Fin k ⊕ Fin k → ι ⊕ ι,
        (∏ z : Fin k ⊕ Fin k, P z (Sum.elim u v z) (ℓ z)) *
          ∏ i : Fin k, Matrix.J ι R (ℓ (φ (Sum.inl i))) (ℓ (φ (Sum.inr i))) := by
  let g (ℓ : Fin k ⊕ Fin k → ι ⊕ ι) : R :=
    (∏ z : Fin k ⊕ Fin k, P z (Sum.elim u v z) (ℓ z)) *
      ∏ i : Fin k, Matrix.J ι R (ℓ (φ (Sum.inl i))) (ℓ (φ (Sum.inr i)))
  have hsum_elim (ℓ : Fin k ⊕ Fin k → ι ⊕ ι) :
      Sum.elim (Equiv.sumArrowEquivProdArrow (Fin k) (Fin k) (ι ⊕ ι) ℓ).1
        (Equiv.sumArrowEquivProdArrow (Fin k) (Fin k) (ι ⊕ ι) ℓ).2 = ℓ := by
    ext (i | i) <;> simp
  rw [Finset.sum_comm, ← Fintype.sum_prod_type (f := fun p => g (Sum.elim p.1 p.2))]
  exact (Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow (Fin k) (Fin k) (ι ⊕ ι)) g
    (fun p => g (Sum.elim p.1 p.2)) fun ℓ => congrArg g (hsum_elim ℓ).symm).symm

omit [Fintype ι] in
/-- Grouping the `2 * k` boundary matrix factors with the `k` arc weights `Matrix.J` into one
factor per arc `(φ (Sum.inl i), φ (Sum.inr i))`. -/
private theorem prod_boundary_mul_prod_J {R : Type*} [CommRing R]
    (φ : Equiv.Perm (Fin k ⊕ Fin k))
    (P : Fin k ⊕ Fin k → Matrix (ι ⊕ ι) (ι ⊕ ι) R)
    (u v : Fin k → ι ⊕ ι) (ℓ : Fin k ⊕ Fin k → ι ⊕ ι) :
    (∏ z : Fin k ⊕ Fin k, P z (Sum.elim u v z) (ℓ z)) *
        (∏ i : Fin k, Matrix.J ι R (ℓ (φ (Sum.inl i))) (ℓ (φ (Sum.inr i)))) =
      ∏ i : Fin k, P (φ (Sum.inl i)) (Sum.elim u v (φ (Sum.inl i)))
          (arcLabellingEquiv φ ℓ i).1 *
        Matrix.J ι R (arcLabellingEquiv φ ℓ i).1 (arcLabellingEquiv φ ℓ i).2 *
        P (φ (Sum.inr i)) (Sum.elim u v (φ (Sum.inr i))) (arcLabellingEquiv φ ℓ i).2 := by
  rw [← Equiv.prod_comp φ (fun z => P z (Sum.elim u v z) (ℓ z)), Fintype.prod_sum_type,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [arcLabellingEquiv_apply_fst, arcLabellingEquiv_apply_snd]
  ring

variable {R ι} in
/-- **Bilinear Kronecker congruence of `symplecticBoundaryMatrix`.** Applying `M₂` to every top
slot and `M₁` to every bottom slot congruates the `Matrix.J` factor on each arc
`(φ (Sum.inl i), φ (Sum.inr i))` by the corresponding boundary matrices. -/
theorem kroneckerPower_mul_symplecticBoundaryMatrix_mul_transpose_apply_of_congr
    {D : BrauerDiagram k} {φ : Equiv.Perm (Fin k ⊕ Fin k)}
    (hφ : PerfectMatching.congr φ (permToBrauer 1) = D)
    (M₁ M₂ : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (v u : Fin k → ι ⊕ ι) :
    (M₂.kroneckerPower (Fin k) * D.symplecticBoundaryMatrix R ι *
        (M₁.kroneckerPower (Fin k))ᵀ) v u =
      ((Equiv.Perm.sign φ : ℤ) : R) *
        ∏ i : Fin k,
          (Sum.elim (fun _ => M₁) (fun _ => M₂) (φ (Sum.inl i)) * Matrix.J ι R *
              (Sum.elim (fun _ => M₁) (fun _ => M₂) (φ (Sum.inr i)))ᵀ)
            (Sum.elim u v (φ (Sum.inl i))) (Sum.elim u v (φ (Sum.inr i))) := by
  let P : Fin k ⊕ Fin k → Matrix (ι ⊕ ι) (ι ⊕ ι) R := Sum.elim (fun _ => M₁) (fun _ => M₂)
  -- Expand matrix congruence and factor `sign φ` out of the double sum over `(w₁, w₂)`.
  rw [Matrix.mul_mul_transpose_apply]
  have hterm (w₁ w₂ : Fin k → ι ⊕ ι) :
      (M₂.kroneckerPower (Fin k) v w₁ * D.symplecticBoundaryMatrix R ι w₁ w₂ *
          M₁.kroneckerPower (Fin k) u w₂) =
        ((Equiv.Perm.sign φ : ℤ) : R) *
          ((∏ z : Fin k ⊕ Fin k, P z (Sum.elim u v z) (Sum.elim w₂ w₁ z)) *
            ∏ i : Fin k, Matrix.J ι R
              (Sum.elim w₂ w₁ (φ (Sum.inl i))) (Sum.elim w₂ w₁ (φ (Sum.inr i)))) := by
    rw [Matrix.kroneckerPower_apply, Matrix.kroneckerPower_apply,
      symplecticBoundaryMatrix_apply_of_congr hφ, Fintype.prod_sum_type]
    simp only [P, Sum.elim_inl, Sum.elim_inr]
    ring
  rw [Finset.sum_congr rfl fun w₁ _ => Finset.sum_congr rfl fun w₂ _ => hterm w₁ w₂]
  simp_rw [← Finset.mul_sum]
  congr 1
  -- Swap the sums and combine `(w₂, w₁)` into a single boundary labelling `ℓ`.
  rw [sum_kronecker_boundary_terms ι φ P u v]
  -- Regroup factors per arc, reindex by `arcLabellingEquiv φ`, and interchange sum and product.
  rw [Finset.sum_congr rfl fun ℓ _ => prod_boundary_mul_prod_J ι φ P u v ℓ,
    Equiv.sum_comp (arcLabellingEquiv φ)
      (fun f => ∏ i : Fin k, P (φ (Sum.inl i)) (Sum.elim u v (φ (Sum.inl i))) (f i).1 *
        Matrix.J ι R (f i).1 (f i).2 *
        P (φ (Sum.inr i)) (Sum.elim u v (φ (Sum.inr i))) (f i).2),
    ← Fintype.prod_sum (fun (i : Fin k) (q : (ι ⊕ ι) × (ι ⊕ ι)) =>
      P (φ (Sum.inl i)) (Sum.elim u v (φ (Sum.inl i))) q.1 * Matrix.J ι R q.1 q.2 *
        P (φ (Sum.inr i)) (Sum.elim u v (φ (Sum.inr i))) q.2)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.mul_mul_transpose_apply, Fintype.sum_prod_type]

/-- **The Pfaffian crossing-sign formula for `symplecticActionMatrix`.** Multiplying the computable
Pfaffian-signed boundary matrix `D.symplecticBoundaryMatrix R ι` on the right by the Kronecker
power of `Matrix.J` yields `D.symplecticActionMatrix R ι`. -/
theorem symplecticActionMatrix_eq_symplecticBoundaryMatrix_mul_kroneckerPower
    (D : BrauerDiagram k) :
    D.symplecticActionMatrix R ι =
      D.symplecticBoundaryMatrix R ι * (Matrix.J ι R).kroneckerPower (Fin k) := by
  obtain ⟨φ, hφ⟩ := D.exists_congr_permToBrauer_one
  have harc (x y : Fin k ⊕ Fin k) :
      Sum.elim (fun _ => (Matrix.J ι R)ᵀ) (fun _ => (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) x *
          Matrix.J ι R *
          (Sum.elim (fun _ => (Matrix.J ι R)ᵀ) (fun _ => (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) y)ᵀ =
        symplecticArcMatrix R ι x y := by
    cases x <;> cases y <;> simp [Matrix.J_transpose, Matrix.J_squared]
  ext v u
  have h := kroneckerPower_mul_symplecticBoundaryMatrix_mul_transpose_apply_of_congr hφ
    (Matrix.J ι R)ᵀ 1 v u
  rw [Matrix.kroneckerPower_one, Matrix.one_mul, ← Matrix.transpose_kroneckerPower,
    Matrix.transpose_transpose] at h
  rw [symplecticActionMatrix_apply_of_congr hφ, h]
  exact congrArg (((Equiv.Perm.sign φ : ℤ) : R) * ·)
    (Finset.prod_congr rfl fun i _ => by rw [harc])

/-- **Recovering `symplecticBoundaryMatrix` from `symplecticActionMatrix`.** Multiplying
`D.symplecticActionMatrix R ι` on the right by the Kronecker power of `-Matrix.J ι R` (the inverse
of `Matrix.J ι R`) recovers `D.symplecticBoundaryMatrix R ι`. -/
theorem symplecticBoundaryMatrix_eq_symplecticActionMatrix_mul_kroneckerPower
    (D : BrauerDiagram k) :
    D.symplecticBoundaryMatrix R ι =
      D.symplecticActionMatrix R ι * (-Matrix.J ι R).kroneckerPower (Fin k) := by
  have hinv : Matrix.J ι R * -Matrix.J ι R = 1 := by
    rw [Matrix.mul_neg, Matrix.J_squared, neg_neg]
  rw [symplecticActionMatrix_eq_symplecticBoundaryMatrix_mul_kroneckerPower, Matrix.mul_assoc,
    ← Matrix.kroneckerPower_mul, hinv, Matrix.kroneckerPower_one, Matrix.mul_one]

/-- **Congruence invariance of the symplectic boundary matrix.** If `A * J * Aᵀ = J`, then
congruating the boundary matrix of `D` by the Kronecker power of `A` leaves it unchanged. -/
theorem kroneckerPower_mul_symplecticBoundaryMatrix_mul_transpose
    (D : BrauerDiagram k) {A : Matrix (ι ⊕ ι) (ι ⊕ ι) R}
    (hA : A * Matrix.J ι R * Aᵀ = Matrix.J ι R) :
    A.kroneckerPower (Fin k) * D.symplecticBoundaryMatrix R ι * (A.kroneckerPower (Fin k))ᵀ =
      D.symplecticBoundaryMatrix R ι := by
  obtain ⟨φ, hφ⟩ := D.exists_congr_permToBrauer_one
  have harc (z : Fin k ⊕ Fin k) : Sum.elim (fun _ => A) (fun _ => A) z = A := by
    rcases z with _ | _ <;> simp
  ext v u
  rw [kroneckerPower_mul_symplecticBoundaryMatrix_mul_transpose_apply_of_congr hφ A A v u,
    symplecticBoundaryMatrix_apply_of_congr hφ]
  exact congrArg (((Equiv.Perm.sign φ : ℤ) : R) * ·)
    (Finset.prod_congr rfl fun i _ => by rw [harc, harc, hA])

end Fintype

end TauCeti.BrauerDiagram
