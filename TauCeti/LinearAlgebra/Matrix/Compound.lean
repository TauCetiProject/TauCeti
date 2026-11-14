/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import TauCeti.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.LinearAlgebra.Matrix.Minor
public import TauCeti.Order.Hom.PowersetCard

import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Plucker
import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# Compound matrices and higher adjugates

For a matrix `A : Matrix ι κ R` over a commutative ring `R` with linearly ordered row and column
index types, the `r`-th compound matrix `A.compound r` is indexed by `r`-element subsets
`S : Set.powersetCard ι r` and `T : Set.powersetCard κ r`, with `(S, T)`-entry the `r × r` minor
on the rows `S` and columns `T` listed in increasing order via
`Set.powersetCard.ofFinEmbEquiv.symm`. When `ι` and `κ` are finite, `A.compound r` is the matrix
of the exterior-power map `exteriorPower.map r A.toLin'` in the exterior-power bases associated to
the standard bases.

For a square matrix `A : Matrix ι ι R` on a finite linearly ordered index type `ι`, the `r`-th
higher adjugate `A.higherAdjugate r` has `(T, S)`-entry equal to the signed complementary
`(#ι - r) × (#ι - r)` minor `(sign S * sign T) • det A[Sᶜ, Tᶜ]`. Over `ι = Fin m`, the sign
`sign S * sign T` is `(-1) ^ (∑ i ∈ S, i + ∑ j ∈ T, j)`.

## Main definitions

* `Matrix.compound`: the `r`-th compound matrix of `A`, indexed by `r`-subsets of the row and
  column index types.
* `Matrix.higherAdjugate`: the `r`-th higher adjugate of a square matrix `A` on a finite linearly
  ordered index type.

## Main results

* `Module.Basis.toMatrix_exteriorPower_map_eq_compound` and
  `Matrix.toMatrix_exteriorPower_map_toLin'`: `A.compound r` represents `exteriorPower.map r` in
  the exterior-power bases.
* `Matrix.compound_mul`: the Cauchy–Binet formula
  `(A * B).compound r = A.compound r * B.compound r`.
* `Matrix.compound_one`, `Matrix.compound_ofSingleton`, `Matrix.compound_two_eq_pairMinor`,
  `Matrix.compound_card_apply`: the unit rule and the cases `r = 0, 1, 2, #ι`.
* `Matrix.sum_sign_compound_mul_compound_compl`, `Matrix.sum_compound_mul_compound_compl`,
  `Matrix.det_eq_sum_compound_mul_compound_compl`,
  `Matrix.sum_compound_mul_compound_compl_eq_zero`: the generalised Laplace expansion along an
  `r`-element set of rows.
* `Matrix.compound_mul_higherAdjugate` and `Matrix.higherAdjugate_mul_compound`:
  `A.compound r * A.higherAdjugate r = A.det • 1` and
  `A.higherAdjugate r * A.compound r = A.det • 1`.
* `Matrix.higherAdjugate_smul` and `Matrix.higherAdjugate_mul_distrib`: scalar and multiplicative
  laws for `Matrix.higherAdjugate`.
* `Matrix.reindex_ofSingleton_higherAdjugate_one` and `Matrix.higherAdjugate_one_ofSingleton`:
  for `r = 1`, the higher adjugate agrees with `Matrix.adjugate` on any finite linearly ordered
  index type.
* `LinearMap.det_smul_mem_range_exteriorPower_map`: for an endomorphism `φ` of a finite free
  module `F`, `LinearMap.det φ` multiplies `⋀[R]^r F` into
  `LinearMap.range (exteriorPower.map r φ)`.

## Implementation notes

`Matrix.higherAdjugate` is defined for any finite linearly ordered index type `ι` and any `r : ℕ`,
without a cardinality side-condition `r ≤ Fintype.card ι`: every element `S : Set.powersetCard ι r`
carries the bound `r ≤ Fintype.card ι` (`Set.powersetCard.sub_add_eq_card`), while for
`r > Fintype.card ι` the index type is empty and the identity
`A.compound r * A.higherAdjugate r = A.det • 1` holds unconditionally.

## References

* [N. Bourbaki, *Algebra I*, Chapter III, §8][bourbaki1989]
* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. (2) 197 (2023), Lemma 3.9.
-/

public section

open Set.powersetCard

namespace Matrix

variable {R : Type*} [CommRing R]

section Compound

variable {ι κ ν : Type*} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]

/-- **The `r`-th compound matrix** of `A : Matrix ι κ R`, indexed by `r`-subsets of `ι` and `κ`,
whose `(S, T)`-entry is the `r × r` minor of `A` on the rows `S` and columns `T` listed in
increasing order. -/
noncomputable def compound (A : Matrix ι κ R) (r : ℕ) :
    Matrix (Set.powersetCard ι r) (Set.powersetCard κ r) R :=
  Matrix.of fun S T ↦
    (A.submatrix (ofFinEmbEquiv.symm S) (ofFinEmbEquiv.symm T)).det

/-- The `(S, T)`-entry of `A.compound r` is the `r × r` minor on the increasing enumerations of
`S` and `T`. -/
theorem compound_apply (A : Matrix ι κ R) (r : ℕ)
    (S : Set.powersetCard ι r) (T : Set.powersetCard κ r) :
    A.compound r S T = (A.submatrix (ofFinEmbEquiv.symm S) (ofFinEmbEquiv.symm T)).det := by
  rfl

/-- Compound matrices commute with transposition. -/
theorem compound_transpose (A : Matrix ι κ R) (r : ℕ) :
    (A.compound r)ᵀ = Aᵀ.compound r := by
  ext T S
  rw [transpose_apply, compound_apply, compound_apply, ← det_transpose]
  rfl

/-- Compound matrices commute with ring homomorphisms. -/
theorem compound_map {R' : Type*} [CommRing R'] (φ : R →+* R') (A : Matrix ι κ R) (r : ℕ) :
    (A.map φ).compound r = (A.compound r).map φ := by
  ext S T
  rw [compound_apply, map_apply, compound_apply, RingHom.map_det]
  rfl

/-- Submatrices along order embeddings commute with `Matrix.compound`. -/
theorem compound_submatrix_orderEmbedding {ι' κ' : Type*} [LinearOrder ι'] [LinearOrder κ']
    (e : ι' ↪o ι) (f : κ' ↪o κ) (A : Matrix ι κ R) (r : ℕ) :
    (A.submatrix e f).compound r =
      (A.compound r).submatrix (Set.powersetCard.map r e.toEmbedding)
        (Set.powersetCard.map r f.toEmbedding) := by
  ext S T
  simp [compound_apply, submatrix_submatrix, Function.comp_def]

/-- Scaling a matrix by `c` scales its `r`-th compound matrix by `c ^ r`. -/
@[simp]
theorem compound_smul (c : R) (A : Matrix ι κ R) (r : ℕ) :
    (c • A).compound r = c ^ r • A.compound r := by
  ext S T
  simp [compound_apply, submatrix_smul]

/-- **The Cauchy–Binet formula in compound-matrix form**: the `r`-th compound of a product is the
product of the `r`-th compounds. -/
theorem compound_mul [Fintype κ] (A : Matrix ι κ R) (B : Matrix κ ν R) (r : ℕ) :
    (A * B).compound r = A.compound r * B.compound r := by
  ext S U
  let x : Fin r → κ → R := fun i k ↦ A (ofFinEmbEquiv.symm S i) k
  let y : Fin r → κ → R := fun j k ↦ B k (ofFinEmbEquiv.symm U j)
  have hAB : (A * B).submatrix (ofFinEmbEquiv.symm S) (ofFinEmbEquiv.symm U) =
      Matrix.of x * (Matrix.of y)ᵀ := by
    ext i j
    simp [x, y, Matrix.mul_apply]
  have hx (T : Set.powersetCard κ r) : TauCeti.plucker x T = A.compound r S T := by
    rw [TauCeti.plucker_apply, compound_apply]
    rfl
  have hy (T : Set.powersetCard κ r) : TauCeti.plucker y T = B.compound r T U := by
    rw [TauCeti.plucker_apply, compound_apply, ← det_transpose]
    rfl
  rw [compound_apply, hAB, TauCeti.det_mul_transpose_eq_sum_plucker_mul, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun T _ ↦ by rw [hx, hy]

/-- The `r`-th compound of the identity matrix is the identity matrix. -/
@[simp]
theorem compound_one (r : ℕ) : (1 : Matrix ι ι R).compound r = 1 := by
  ext S T
  by_cases hST : S = T
  · subst hST
    have hsub : (1 : Matrix ι ι R).submatrix (ofFinEmbEquiv.symm S) (ofFinEmbEquiv.symm S) = 1 := by
      ext i j
      by_cases hij : i = j <;>
        simp [hij, Matrix.one_apply, (ofFinEmbEquiv.symm S).injective.eq_iff]
    simp [compound_apply, hsub]
  · simp only [compound_apply, one_apply_ne hST]
    -- Since `S ≠ T` have the same cardinality, some element of `S` does not belong to `T`,
    -- giving a zero row of the submatrix of `1`.
    have hnot : ¬ S.val ⊆ T.val := fun hsub ↦ hST (Set.powersetCard.eq_iff_subset.mpr hsub)
    obtain ⟨x, hxS, hxT⟩ := Finset.not_subset.mp hnot
    obtain ⟨a, rfl⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S x).mpr hxS
    refine det_eq_zero_of_row_eq_zero a fun b ↦ ?_
    have hne : ofFinEmbEquiv.symm S a ≠ ofFinEmbEquiv.symm T b := by
      intro heq
      exact hxT ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T _).mp ⟨b, heq.symm⟩)
    simp [one_apply_ne hne]

/-- Compound matrices commute with matrix powers. -/
@[simp]
theorem compound_pow [Fintype ι] (A : Matrix ι ι R) (r k : ℕ) :
    (A ^ k).compound r = A.compound r ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, compound_mul, ih, pow_succ]

/-- Every entry of the `0`-th compound matrix is `1`. -/
theorem compound_zero_apply (A : Matrix ι κ R)
    (S : Set.powersetCard ι 0) (T : Set.powersetCard κ 0) :
    A.compound 0 S T = 1 := by
  simp [compound_apply]

/-- The `0`-th compound of a square matrix is `1`. -/
@[simp]
theorem compound_zero (A : Matrix ι ι R) : A.compound 0 = 1 := by
  ext S T
  have hST : S = T := Subtype.ext <| by
    rw [Finset.card_eq_zero.mp (Set.powersetCard.mem_iff.mp S.prop),
      Finset.card_eq_zero.mp (Set.powersetCard.mem_iff.mp T.prop)]
  subst hST
  rw [compound_zero_apply, one_apply_eq]

/-- The first compound matrix evaluates on singletons `{i}` and `{k}` to `A i k`. -/
@[simp]
theorem compound_ofSingleton (A : Matrix ι κ R) (i : ι) (k : κ) :
    A.compound 1 (ofSingleton i) (ofSingleton k) = A i k := by
  simp [compound_apply]

/-- Reindexing the first compound matrix along `Set.powersetCard.ofSingleton` recovers `A`. -/
theorem reindex_ofSingleton_compound_one (A : Matrix ι κ R) :
    Matrix.reindex ofSingleton.symm ofSingleton.symm (A.compound 1) = A := by
  ext i k
  simp

/-- The second compound matrix evaluates on `{i, j}` (`i < j`) and `{k, l}` (`k < l`) to
`Matrix.pairMinor A (i, j) (k, l)`. -/
theorem compound_two_eq_pairMinor (A : Matrix ι κ R)
    {S : Set.powersetCard ι 2} {T : Set.powersetCard κ 2} {i j : ι} {k l : κ}
    (hij : i < j) (hkl : k < l) (hS : S.val = {i, j}) (hT : T.val = {k, l}) :
    A.compound 2 S T = A.pairMinor (i, j) (k, l) := by
  rw [compound_apply, coe_ofFinEmbEquiv_symm_pair hij hS, coe_ofFinEmbEquiv_symm_pair hkl hT,
    det_fin_two, pairMinor_eq]
  simp

/-- On a square matrix indexed by a finite type `ι`, the top compound `A.compound (Fintype.card ι)`
has sole entry `A.det`. -/
@[simp]
theorem compound_card_apply [Fintype ι] (A : Matrix ι ι R)
    (S T : Set.powersetCard ι (Fintype.card ι)) :
    A.compound (Fintype.card ι) S T = A.det := by
  have hST : S = T := by
    apply Subtype.ext
    rw [Finset.eq_univ_of_card S.val (Set.powersetCard.mem_iff.mp S.prop),
      Finset.eq_univ_of_card T.val (Set.powersetCard.mem_iff.mp T.prop)]
  subst hST
  have hbij : Function.Bijective (ofFinEmbEquiv.symm S) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨(ofFinEmbEquiv.symm S).injective, Fintype.card_fin _⟩
  let e : Fin (Fintype.card ι) ≃ ι := Equiv.ofBijective _ hbij
  exact det_submatrix_equiv_self e A

/-- When `d = Fintype.card ι`, every entry of `A.compound d` equals `A.det`. -/
theorem compound_eq_det_of_card_eq [Fintype ι] {d : ℕ} (hd : d = Fintype.card ι)
    (A : Matrix ι ι R) (S T : Set.powersetCard ι d) :
    A.compound d S T = A.det := by
  subst hd
  exact compound_card_apply A S T

/-- On `Fin m`, the `m`-th compound matrix has sole entry `A.det`. -/
@[simp]
theorem compound_self_fin_apply {m : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (S T : Set.powersetCard (Fin m) m) :
    A.compound m S T = A.det :=
  compound_eq_det_of_card_eq (Fintype.card_fin m).symm A S T

-- Check: `C_1(A)_{{i},{k}} = A i k` for a `2 × 3` matrix.
example (A : Matrix (Fin 2) (Fin 3) R) (i : Fin 2) (k : Fin 3) :
    A.compound 1 (ofSingleton i) (ofSingleton k) = A i k :=
  A.compound_ofSingleton i k

-- Check: `C_2` of `!![a, b; c, d]` has sole entry `a * d - b * c`.
example (a b c d : R) (S T : Set.powersetCard (Fin 2) 2) :
    (!![a, b; c, d]).compound 2 S T = a * d - b * c := by
  rw [compound_self_fin_apply, det_fin_two_of]

-- Check: for `r` larger than the number of rows, `Set.powersetCard (Fin 2) 3` is empty, so `C_3`
-- of a `2 × 3` matrix lives in a subsingleton matrix type.
example : IsEmpty (Set.powersetCard (Fin 2) 3) :=
  ⟨fun S ↦ Nat.not_succ_le_self 2 (Set.powersetCard.le_of_fin S)⟩

end Compound

end Matrix

namespace Module.Basis

/-- **Exterior-power maps have compound matrices**: the matrix of `exteriorPower.map r f` with
respect to `b.exteriorPower r` and `c.exteriorPower r` is the `r`-th compound of the matrix of `f`
with respect to `b` and `c`. -/
theorem toMatrix_exteriorPower_map_eq_compound {R M N ι κ : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [LinearOrder ι] [Finite ι] [LinearOrder κ] [Fintype κ]
    (b : Module.Basis κ R M) (c : Module.Basis ι R N) (r : ℕ) (f : M →ₗ[R] N) :
    LinearMap.toMatrix (b.exteriorPower r) (c.exteriorPower r) (exteriorPower.map r f) =
      (LinearMap.toMatrix b c f).compound r := by
  ext S T
  rw [toMatrix_exteriorPower_map, Matrix.compound_apply, ← Matrix.det_transpose]
  rfl

end Module.Basis

namespace Matrix

variable {R : Type*} [CommRing R]

/-- For `A : Matrix ι κ R`, the exterior-power map `exteriorPower.map r A.toLin'` has matrix
`A.compound r` in the exterior-power bases of the standard bases. -/
theorem toMatrix_exteriorPower_map_toLin' {ι κ : Type*} [LinearOrder ι] [Finite ι]
    [LinearOrder κ] [Fintype κ] (A : Matrix ι κ R) (r : ℕ) :
    LinearMap.toMatrix ((Pi.basisFun R κ).exteriorPower r) ((Pi.basisFun R ι).exteriorPower r)
        (exteriorPower.map r A.toLin') =
      A.compound r := by
  rw [Module.Basis.toMatrix_exteriorPower_map_eq_compound, ← toLin_eq_toLin',
    LinearMap.toMatrix_toLin]

section LaplaceAndHigherAdjugate

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- Expanding `exteriorPower.map d Aᵀ.toLin'` on the standard exterior-power basis vector at `X`
produces the `X`-th row of `A.compound d`. -/
private theorem exteriorPower_map_toLin'_transpose_apply (A : Matrix ι ι R) {d : ℕ}
    (X : Set.powersetCard ι d) :
    exteriorPower.map d Aᵀ.toLin' ((Pi.basisFun R ι).exteriorPower d X) =
      ∑ Y : Set.powersetCard ι d, A.compound d X Y • (Pi.basisFun R ι).exteriorPower d Y := by
  let b := Pi.basisFun R ι
  conv_lhs => rw [← (b.exteriorPower d).sum_repr (exteriorPower.map d Aᵀ.toLin' _)]
  refine Finset.sum_congr rfl fun Y _ ↦ ?_
  have hmat := congr_fun (congr_fun (toMatrix_exteriorPower_map_toLin' Aᵀ d) Y) X
  rw [LinearMap.toMatrix_apply, ← compound_transpose, transpose_apply] at hmat
  rw [hmat]

/-- **Generalised Laplace expansion (general index form).** For a square matrix `A : Matrix ι ι R`
on a finite linearly ordered index type `ι`, `k + r = Fintype.card ι`, and `r`-subsets `S, S'` of
`ι`, summing `(sign S' * sign T) • (det A[S, T] * det A[S'ᶜ, Tᶜ])` over all `r`-subsets `T` gives
`A.det` when `S = S'` and `0` when `S ≠ S'`. -/
theorem sum_sign_compound_mul_compound_compl (A : Matrix ι ι R) {k r : ℕ}
    (hk : k + r = Fintype.card ι) (S S' : Set.powersetCard ι r) :
    ∑ T : Set.powersetCard ι r,
      (Set.powersetCard.sign S' * Set.powersetCard.sign T) •
        (A.compound r S T * A.compound k (compl hk S') (compl hk T)) =
      if S = S' then A.det else 0 := by
  nontriviality R
  let b := Pi.basisFun R ι
  have hcard : Module.finrank R (ι → R) = Fintype.card ι := Module.finrank_eq_card_basis b
  have hkl : r + k = Module.finrank R (ι → R) := by omega
  let topIdx : Set.powersetCard ι (Module.finrank R (ι → R)) := ⟨Finset.univ, by simp [hcard]⟩
  have : Subsingleton (Set.powersetCard ι (Module.finrank R (ι → R))) :=
    ⟨fun s t ↦ Subtype.ext <| by
      rw [Finset.eq_univ_of_card s.val (by simp [hcard]),
        Finset.eq_univ_of_card t.val (by simp [hcard])]⟩
  let vol : ⋀[R]^(Module.finrank R (ι → R)) (ι → R) ≃ₗ[R] R :=
    (b.exteriorPower (Module.finrank R (ι → R))).repr.trans
      (Finsupp.uniqueLinearEquiv R R topIdx)
  let P := exteriorPower.wedgePairing vol hkl
  have hpair (T : Set.powersetCard ι r) (U : Set.powersetCard ι k) :
      P (b.exteriorPower r T) (b.exteriorPower k U) =
        if U = compl hk T then Set.powersetCard.sign T • (1 : R) else 0 := by
    have hvol : vol b.topVector = 1 := by
      rw [LinearEquiv.trans_apply, Finsupp.uniqueLinearEquiv_apply,
        ← b.topVector_eq_exteriorPower topIdx, Module.Basis.repr_self, Finsupp.single_eq_same]
    rw [exteriorPower.wedgePairing_exteriorPower_apply vol hkl b T U, hvol, one_smul]
    simp only [disjoint_comm.trans (Set.powersetCard.disjoint_iff_eq_compl hk)]
    split_ifs <;> simp
  have hlhs :
      P (exteriorPower.map r Aᵀ.toLin' (b.exteriorPower r S))
        (exteriorPower.map k Aᵀ.toLin' (b.exteriorPower k (compl hk S'))) =
        ∑ T : Set.powersetCard ι r,
          Set.powersetCard.sign T •
            (A.compound r S T * A.compound k (compl hk S') (compl hk T)) := by
    rw [exteriorPower_map_toLin'_transpose_apply, exteriorPower_map_toLin'_transpose_apply,
      map_sum P, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun T _ ↦ ?_
    rw [map_sum (P _), Finset.sum_eq_single (compl hk T)]
    · rw [map_smul, map_smul P, LinearMap.smul_apply, hpair, ite_eq_left rfl]
      simp only [Units.smul_def, zsmul_eq_mul, smul_eq_mul, mul_one]
      ring
    · intro U _ hU
      rw [map_smul, map_smul P, LinearMap.smul_apply, hpair, ite_eq_right hU, smul_zero, smul_zero]
    · exact fun hmem ↦ absurd (Finset.mem_univ _) hmem
  have hdet := LinearMap.congr_fun₂
    (exteriorPower.wedge_compr₂_compl₁₂_exteriorPower_map_eq_det_smul rfl hkl
      (vol : ⋀[R]^(Module.finrank R (ι → R)) (ι → R) →ₗ[R] R) Aᵀ.toLin')
    (b.exteriorPower r S) (b.exteriorPower k (compl hk S'))
  simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, LinearMap.det_toLin',
    det_transpose] at hdet
  -- Multiply `hdet` by `sign S'`, cancelling `(sign S') ^ 2 = 1` on the diagonal.
  have hmul := congrArg (Set.powersetCard.sign S' • ·) (hlhs.symm.trans hdet)
  rw [Finset.smul_sum, smul_comm _ A.det, hpair S (compl hk S')] at hmul
  simp only [smul_smul, (compl hk).injective.eq_iff, eq_comm (a := S')] at hmul
  split_ifs at hmul ⊢ with hSS'
  · subst hSS'
    simpa [smul_smul, Int.units_mul_self] using hmul
  · simpa using hmul

/-- **Generalised Laplace expansion.** For an `m × m` matrix `A` and `r`-subsets `S, S'` of
`Fin m`, summing `(-1) ^ (∑ i ∈ S', i + ∑ j ∈ T, j) * det A[S, T] * det A[S'ᶜ, Tᶜ]` over all
`r`-subsets `T` gives `A.det` when `S = S'` and `0` when `S ≠ S'`. -/
theorem sum_compound_mul_compound_compl {m k r : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (hk : k + r = Fintype.card (Fin m)) (S S' : Set.powersetCard (Fin m) r) :
    ∑ T : Set.powersetCard (Fin m) r,
      (-1 : R) ^ (∑ i ∈ (S' : Finset (Fin m)), (i : ℕ) + ∑ j ∈ (T : Finset (Fin m)), (j : ℕ)) *
        A.compound r S T * A.compound k (compl hk S') (compl hk T) =
      if S = S' then A.det else 0 := by
  rw [← sum_sign_compound_mul_compound_compl A hk S S']
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  rw [Set.powersetCard.sign_mul_sign_fin]
  simp [Units.smul_def, mul_assoc]

/-- **Generalised Laplace expansion along the rows `S`.** For an `r`-subset `S` of `Fin m` and
`k + r = Fintype.card (Fin m)`, `A.det` is the signed sum over `r`-subsets `T` of
`det A[S, T] * det A[Sᶜ, Tᶜ]`. -/
theorem det_eq_sum_compound_mul_compound_compl {m k r : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (hk : k + r = Fintype.card (Fin m)) (S : Set.powersetCard (Fin m) r) :
    A.det =
      ∑ T : Set.powersetCard (Fin m) r,
        (-1 : R) ^ (∑ i ∈ (S : Finset (Fin m)), (i : ℕ) + ∑ j ∈ (T : Finset (Fin m)), (j : ℕ)) *
          A.compound r S T * A.compound k (compl hk S) (compl hk T) := by
  simpa using (sum_compound_mul_compound_compl A hk S S).symm

/-- **Off-diagonal generalised Laplace expansion.** For distinct `r`-subsets `S ≠ S'` of `Fin m`,
the signed sum of `det A[S, T] * det A[S'ᶜ, Tᶜ]` over `r`-subsets `T` vanishes. -/
theorem sum_compound_mul_compound_compl_eq_zero {m k r : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (hk : k + r = Fintype.card (Fin m)) {S S' : Set.powersetCard (Fin m) r} (hSS' : S ≠ S') :
    ∑ T : Set.powersetCard (Fin m) r,
      (-1 : R) ^ (∑ i ∈ (S' : Finset (Fin m)), (i : ℕ) + ∑ j ∈ (T : Finset (Fin m)), (j : ℕ)) *
        A.compound r S T * A.compound k (compl hk S') (compl hk T) = 0 := by
  simpa [hSS'] using sum_compound_mul_compound_compl A hk S S'

/-- **The `r`-th higher adjugate** of a square matrix `A : Matrix ι ι R` on a finite linearly
ordered index type `ι`. Its `(T, S)`-entry is `(sign S * sign T) • det A[Sᶜ, Tᶜ]`; over
`ι = Fin m`, this is `(-1) ^ (∑ i ∈ S, i + ∑ j ∈ T, j) * det A[Sᶜ, Tᶜ]`
(`Matrix.higherAdjugate_fin_apply`). -/
noncomputable def higherAdjugate (A : Matrix ι ι R) (r : ℕ) :
    Matrix (Set.powersetCard ι r) (Set.powersetCard ι r) R :=
  Matrix.of fun T S ↦
    (Set.powersetCard.sign S * Set.powersetCard.sign T) •
      A.compound (Fintype.card ι - r)
        (compl (Set.powersetCard.sub_add_eq_card S) S)
        (compl (Set.powersetCard.sub_add_eq_card T) T)

/-- The `(T, S)`-entry of `A.higherAdjugate r` written with any proof
`hk : k + r = Fintype.card ι`. -/
theorem higherAdjugate_apply_of_add_eq (A : Matrix ι ι R) {k r : ℕ}
    (hk : k + r = Fintype.card ι) (T S : Set.powersetCard ι r) :
    A.higherAdjugate r T S =
      (Set.powersetCard.sign S * Set.powersetCard.sign T) •
        A.compound k (compl hk S) (compl hk T) := by
  obtain rfl : k = Fintype.card ι - r := by omega
  rfl

/-- The `(T, S)`-entry of `A.higherAdjugate r`. -/
theorem higherAdjugate_apply (A : Matrix ι ι R) (r : ℕ) (T S : Set.powersetCard ι r) :
    A.higherAdjugate r T S =
      (Set.powersetCard.sign S * Set.powersetCard.sign T) •
        A.compound (Fintype.card ι - r)
          (compl (Set.powersetCard.sub_add_eq_card S) S)
          (compl (Set.powersetCard.sub_add_eq_card T) T) := by
  rfl

/-- On `Fin m`, the `(T, S)`-entry of `A.higherAdjugate r` is
`(-1) ^ (∑ i ∈ S, i + ∑ j ∈ T, j) * det A[Sᶜ, Tᶜ]`. -/
theorem higherAdjugate_fin_apply {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (r : ℕ)
    (T S : Set.powersetCard (Fin m) r) :
    A.higherAdjugate r T S =
      (-1 : R) ^ (∑ i ∈ (S : Finset (Fin m)), (i : ℕ) + ∑ j ∈ (T : Finset (Fin m)), (j : ℕ)) *
        A.compound (m - r)
          (compl (Set.powersetCard.sub_add_eq_card_fin S) S)
          (compl (Set.powersetCard.sub_add_eq_card_fin T) T) := by
  rw [higherAdjugate_apply_of_add_eq A (Set.powersetCard.sub_add_eq_card_fin S) T S,
    Set.powersetCard.sign_mul_sign_fin]
  simp [Units.smul_def]

/-- Higher adjugates commute with transposition. -/
theorem higherAdjugate_transpose (A : Matrix ι ι R) (r : ℕ) :
    (A.higherAdjugate r)ᵀ = Aᵀ.higherAdjugate r := by
  ext S T
  rw [transpose_apply, higherAdjugate_apply, higherAdjugate_apply,
    mul_comm (Set.powersetCard.sign T), ← compound_transpose, transpose_apply]

/-- Higher adjugates commute with ring homomorphisms. -/
theorem higherAdjugate_map {R' : Type*} [CommRing R'] (φ : R →+* R') (A : Matrix ι ι R) (r : ℕ) :
    (A.map φ).higherAdjugate r = (A.higherAdjugate r).map φ := by
  ext T S
  simp [higherAdjugate_apply, compound_map, Units.smul_def]

/-- Reindexing a square matrix along an order isomorphism commutes with `Matrix.higherAdjugate`. -/
@[simp]
theorem higherAdjugate_submatrix_orderIso {ι' : Type*} [LinearOrder ι'] [Fintype ι']
    (e : ι' ≃o ι) (A : Matrix ι ι R) (r : ℕ) :
    (A.submatrix e e).higherAdjugate r =
      (A.higherAdjugate r).submatrix (Set.powersetCard.map r e.toEmbedding)
        (Set.powersetCard.map r e.toEmbedding) := by
  ext T S
  have hk' := Set.powersetCard.sub_add_eq_card S
  have hk : Fintype.card ι' - r + r = Fintype.card ι :=
    hk'.trans (Fintype.card_congr e.toEquiv)
  have hlhs :=
    congr_fun (congr_fun (compound_submatrix_orderEmbedding e.toOrderEmbedding
      e.toOrderEmbedding A (Fintype.card ι' - r)) (compl hk' S)) (compl hk' T)
  rw [higherAdjugate_apply_of_add_eq (A.submatrix e e) hk' T S, submatrix_apply,
    higherAdjugate_apply_of_add_eq A hk]
  simpa only [OrderIso.coe_toOrderEmbedding, submatrix_apply,
    show e.toOrderEmbedding.toEmbedding = e.toEquiv.toEmbedding from rfl,
    show e.toEmbedding = e.toEquiv.toEmbedding from rfl,
    Set.powersetCard.map_compl_equiv hk' e.toEquiv,
    ← show e.toEmbedding = e.toEquiv.toEmbedding from rfl,
    Set.powersetCard.sign_map_orderIso] using
    congrArg ((Set.powersetCard.sign S * Set.powersetCard.sign T) • ·) hlhs

/-- Scaling `A` by `c` scales `A.higherAdjugate r` by `c ^ (Fintype.card ι - r)`. -/
@[simp]
theorem higherAdjugate_smul (c : R) (A : Matrix ι ι R) (r : ℕ) :
    (c • A).higherAdjugate r = c ^ (Fintype.card ι - r) • A.higherAdjugate r := by
  ext T S
  simp [higherAdjugate_apply, mul_smul_comm]

/-- Higher adjugates reverse multiplication:
`(A * B).higherAdjugate r = B.higherAdjugate r * A.higherAdjugate r`. -/
theorem higherAdjugate_mul_distrib (A B : Matrix ι ι R) (r : ℕ) :
    (A * B).higherAdjugate r = B.higherAdjugate r * A.higherAdjugate r := by
  ext T S
  have hk := Set.powersetCard.sub_add_eq_card S
  rw [higherAdjugate_apply_of_add_eq (A * B) hk T S, compound_mul, Matrix.mul_apply,
    Matrix.mul_apply, ← (compl hk).sum_comp, Finset.smul_sum]
  refine Finset.sum_congr rfl fun U _ ↦ ?_
  rw [higherAdjugate_apply_of_add_eq B hk T U, higherAdjugate_apply_of_add_eq A hk U S]
  have hsign : (Set.powersetCard.sign U * Set.powersetCard.sign T) *
      (Set.powersetCard.sign S * Set.powersetCard.sign U) =
      Set.powersetCard.sign S * Set.powersetCard.sign T := by
    calc (Set.powersetCard.sign U * Set.powersetCard.sign T) *
          (Set.powersetCard.sign S * Set.powersetCard.sign U)
        = (Set.powersetCard.sign S * Set.powersetCard.sign T) *
            (Set.powersetCard.sign U * Set.powersetCard.sign U) := by ac_rfl
      _ = Set.powersetCard.sign S * Set.powersetCard.sign T := by
            rw [Int.units_mul_self, mul_one]
  rw [smul_mul_smul_comm, hsign, mul_comm (B.compound _ _ _)]

/-- **Cramer's rule for compound matrices (right)**:
`A.compound r * A.higherAdjugate r = A.det • 1`. -/
theorem compound_mul_higherAdjugate (A : Matrix ι ι R) (r : ℕ) :
    A.compound r * A.higherAdjugate r = A.det • (1 : Matrix _ _ R) := by
  ext S S'
  have hk := Set.powersetCard.sub_add_eq_card S
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_ite, smul_eq_mul, mul_one,
    smul_zero, ← sum_sign_compound_mul_compound_compl A hk S S']
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  rw [higherAdjugate_apply_of_add_eq A hk T S', mul_smul_comm]

/-- **Cramer's rule for compound matrices (left)**:
`A.higherAdjugate r * A.compound r = A.det • 1`. -/
theorem higherAdjugate_mul_compound (A : Matrix ι ι R) (r : ℕ) :
    A.higherAdjugate r * A.compound r = A.det • (1 : Matrix _ _ R) := by
  apply transpose_injective
  rw [transpose_mul, compound_transpose, higherAdjugate_transpose, compound_mul_higherAdjugate,
    det_transpose, transpose_smul, transpose_one]

/-- Every higher adjugate of the identity matrix is the identity matrix. -/
@[simp]
theorem higherAdjugate_one (r : ℕ) : (1 : Matrix ι ι R).higherAdjugate r = 1 := by
  simpa using compound_mul_higherAdjugate (1 : Matrix ι ι R) r

/-- Higher adjugates commute with matrix powers. -/
@[simp]
theorem higherAdjugate_pow (A : Matrix ι ι R) (r k : ℕ) :
    (A ^ k).higherAdjugate r = A.higherAdjugate r ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', higherAdjugate_mul_distrib, ih, pow_succ]

/-- The `0`-th higher adjugate of `A` is `A.det • 1`. -/
@[simp]
theorem higherAdjugate_zero (A : Matrix ι ι R) : A.higherAdjugate 0 = A.det • 1 := by
  simpa using compound_mul_higherAdjugate A 0

/-- The top higher adjugate `A.higherAdjugate (Fintype.card ι)` is the `1 × 1` identity matrix. -/
@[simp]
theorem higherAdjugate_card (A : Matrix ι ι R) :
    A.higherAdjugate (Fintype.card ι) = 1 := by
  ext T S
  have hTS : T = S := by
    apply Subtype.ext
    rw [Finset.eq_univ_of_card T.val (Set.powersetCard.mem_iff.mp T.prop),
      Finset.eq_univ_of_card S.val (Set.powersetCard.mem_iff.mp S.prop)]
  subst hTS
  rw [higherAdjugate_apply_of_add_eq A (Nat.zero_add (Fintype.card ι)) T T]
  simp [Int.units_mul_self]

/-- When `d = Fintype.card ι`, `A.higherAdjugate d` is the `1 × 1` identity matrix. -/
theorem higherAdjugate_eq_one_of_card_eq {d : ℕ} (hd : d = Fintype.card ι) (A : Matrix ι ι R) :
    A.higherAdjugate d = 1 := by
  subst hd
  exact higherAdjugate_card A

/-- On `Fin m`, the `m`-th higher adjugate `A.higherAdjugate m` is the `1 × 1` identity matrix. -/
@[simp]
theorem higherAdjugate_self_fin {m : ℕ} (A : Matrix (Fin m) (Fin m) R) :
    A.higherAdjugate m = 1 :=
  higherAdjugate_eq_one_of_card_eq (Fintype.card_fin m).symm A

private theorem higherAdjugate_one_ofSingleton_fin {m : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (i j : Fin m) :
    A.higherAdjugate 1 (ofSingleton i) (ofSingleton j) = A.adjugate i j := by
  cases m with
  | zero => exact i.elim0
  | succ n =>
    rw [higherAdjugate_fin_apply, compound_apply,
      Set.powersetCard.ofFinEmbEquiv_symm_compl_ofSingleton,
      Set.powersetCard.ofFinEmbEquiv_symm_compl_ofSingleton,
      adjugate_fin_succ_eq_det_submatrix]
    simp

/-- The first higher adjugate evaluated at singletons `{i}` and `{j}` agrees with
`Matrix.adjugate A i j`. -/
@[simp]
theorem higherAdjugate_one_ofSingleton (A : Matrix ι ι R) (i j : ι) :
    A.higherAdjugate 1 (ofSingleton i) (ofSingleton j) = A.adjugate i j := by
  let e : Fin (Fintype.card ι) ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
  have h := higherAdjugate_one_ofSingleton_fin (A.submatrix e e) (e.symm i) (e.symm j)
  have hadj : (A.submatrix e e).adjugate (e.symm i) (e.symm j) = A.adjugate i j := by
    simpa using congr_fun (congr_fun (adjugate_submatrix_equiv_self e.toEquiv A)
      (e.symm i)) (e.symm j)
  rw [higherAdjugate_submatrix_orderIso, submatrix_apply, Set.powersetCard.map_ofSingleton,
    Set.powersetCard.map_ofSingleton, hadj] at h
  simpa using h

/-- Reindexing the first higher adjugate of `A` along `Set.powersetCard.ofSingleton` recovers
`A.adjugate`. -/
theorem reindex_ofSingleton_higherAdjugate_one (A : Matrix ι ι R) :
    Matrix.reindex ofSingleton.symm ofSingleton.symm (A.higherAdjugate 1) = A.adjugate := by
  ext i j
  simp

-- Check: for a `3 × 3` matrix, `adj_1` agrees with `Matrix.adjugate`.
example (A : Matrix (Fin 3) (Fin 3) R) :
    Matrix.reindex ofSingleton.symm ofSingleton.symm (A.higherAdjugate 1) = A.adjugate :=
  A.reindex_ofSingleton_higherAdjugate_one

-- Check: for a `3 × 3` matrix, `adj_3(A) = 1`.
example (A : Matrix (Fin 3) (Fin 3) R) : A.higherAdjugate 3 = 1 :=
  A.higherAdjugate_self_fin

-- Check: `adj_r(1_3) = 1` for every `r ≤ 3`.
example (r : ℕ) (_hr : r ≤ 3) : (1 : Matrix (Fin 3) (Fin 3) R).higherAdjugate r = 1 :=
  higherAdjugate_one r

/-- For a square matrix `A` on a finite linearly ordered index type `ι`, `A.det` multiplies every
element of `⋀[R]^r (ι → R)` into the range of `exteriorPower.map r A.toLin'`. -/
theorem det_smul_mem_range_exteriorPower_map_toLin' (A : Matrix ι ι R) (r : ℕ)
    (z : ⋀[R]^r (ι → R)) :
    A.det • z ∈ LinearMap.range (exteriorPower.map r A.toLin') := by
  let br := (Pi.basisFun R ι).exteriorPower r
  refine ⟨Matrix.toLin br br (A.higherAdjugate r) z, ?_⟩
  have h := congr(Matrix.toLin br br $(A.compound_mul_higherAdjugate r) z)
  rw [Matrix.toLin_mul br br br, ← A.toMatrix_exteriorPower_map_toLin' r, Matrix.toLin_toMatrix,
    map_smul, Matrix.toLin_one] at h
  simpa using h

end LaplaceAndHigherAdjugate

end Matrix

namespace LinearMap

/-- **Determinant control of exterior-power ranges.** For an endomorphism `φ` of a finite free
module `F` over a commutative ring `R`, `LinearMap.det φ` multiplies every element of `⋀[R]^r F`
into the range of `exteriorPower.map r φ`. -/
theorem det_smul_mem_range_exteriorPower_map {R F : Type*} [CommRing R] [AddCommGroup F]
    [Module R F] [Module.Free R F] [Module.Finite R F] (φ : F →ₗ[R] F) (r : ℕ)
    (z : ⋀[R]^r F) :
    LinearMap.det φ • z ∈ LinearMap.range (exteriorPower.map r φ) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have := Module.subsingleton R (⋀[R]^r F)
    exact ⟨0, Subsingleton.elim _ _⟩
  · let b := Module.finBasis R F
    let br := b.exteriorPower r
    let adj := (LinearMap.toMatrix b b φ).higherAdjugate r
    refine ⟨Matrix.toLin br br adj z, ?_⟩
    have h :=
      congr(Matrix.toLin br br $((LinearMap.toMatrix b b φ).compound_mul_higherAdjugate r) z)
    rw [Matrix.toLin_mul br br br, ← b.toMatrix_exteriorPower_map_eq_compound b r φ,
      Matrix.toLin_toMatrix, map_smul, Matrix.toLin_one, LinearMap.det_toMatrix] at h
    simpa using h

end LinearMap
