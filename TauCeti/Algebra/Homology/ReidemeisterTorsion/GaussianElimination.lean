/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Homology.HomologicalComplex.Biprod
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.Algebra.Homology.ModuleCat.MatrixBaseChange
import TauCeti.Algebra.Homology.ReidemeisterTorsion.SquareMinor

/-!
# Gaussian elimination and Reidemeister torsion

Let `C` be a `ℤ`-graded chain complex of vector spaces over a field `F` with ordered bases, in
which the last basis vector `z⁺` of `Cᵢ₊₁` and the last basis vector `z⁻` of `Cᵢ` are joined by
an invertible matrix coefficient: in these bases the differential `d : Cᵢ₊₁ → Cᵢ` has the block
form `[[N, w], [v, a]]` with `a ≠ 0`, where `N` is the matrix between the remaining basis vectors,
`w` is the column of `z⁺` and `v` is the row of `z⁻`. *Gaussian elimination* cancels the pair:
let `D` be a based complex with the remaining basis vectors, whose differential `Dᵢ₊₁ → Dᵢ` has
the Schur complement `N - w a⁻¹ v` as matrix, and whose other differentials have the matrices of
`C` with the rows and columns of `z⁺` and `z⁻` deleted. Then
(`HomologicalComplex.reidemeisterTorsion_eq_mul_of_gaussianElimination`)

`τ(C) = (-1) ^ (dim Bᵢ₋₁(D)) · a ^ ((-1) ^ (i + 1)) · τ(D)`,

where `Bᵢ₋₁(D)` is the image of the differential `Dᵢ → Dᵢ₋₁`, and `C` is acyclic exactly when `D`
is (`HomologicalComplex.acyclic_iff_of_gaussianElimination`). For the elementary complex itself
(`D = 0`, with `C` concentrated in degrees `1` and `0` and `d` multiplication by `a`), this is the
normalization `τ = a⁻¹` of the torsion.

The proof changes the bases of `C`: the vectors `x ≠ z⁺` of `Cᵢ₊₁` are replaced by
`x - (v x / a) z⁺` and `z⁻` by `d z⁺`. In the new bases, of determinants `1` and `a` with respect
to the old ones, `C` has the matrices of the direct sum of `D` and of the elementary complex
`F → F` spanned by `z⁺` and `d z⁺`, whose torsion is `1`. This follows the plan of the
two-periodic cancellation `HomologicalComplex.parityTorsion_eq_of_cancel_one_zero` in
`ReidemeisterTorsion/Cancellation.lean`.

In Morse and Floer theory, `C` is the complex just before the death of a pair of critical points
or orbits of adjacent indices joined by a single connecting trajectory of coefficient `a`, and
`D` is the complex just after it; read from `D` to `C`, the same formula describes a birth.

## Main results

* `HomologicalComplex.reidemeisterTorsion_eq_mul_of_gaussianElimination`: the change of the torsion
  under Gaussian elimination.
* `HomologicalComplex.acyclic_iff_of_gaussianElimination`: Gaussian elimination preserves
  acyclicity.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* V. Turaev, *Introduction to Combinatorial Torsions*, Birkhäuser 2001, Chapter I.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  209–244, §3.
* M. Hutchings, Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and Seiberg–Witten
  invariants of 3-manifolds*, Topology 38 (1999), 861–888.
-/

public section

noncomputable section

open CategoryTheory Limits Module

namespace HomologicalComplex

universe u v

variable {F : Type u} [Field F]

/-! ### The elementary complex -/

section Pair

/-- The dimension of the elementary complex spanned by a cancelling pair in degrees `i + 1` and
`i`: `1` in these two degrees and `0` elsewhere. -/
private abbrev pairRank (i j : ℤ) : ℕ := if j = i + 1 ∨ j = i then 1 else 0

/-- The matrix of the differential of the elementary complex from degree `j + 1` to degree `j`:
all of its entries are `1` if `j = i`, and `0` otherwise. Between the one-dimensional terms in
degrees `i + 1` and `i` it is the identity. -/
private def pairMatrix (i j : ℤ) : Matrix (Fin (pairRank i j)) (Fin (pairRank i (j + 1))) F :=
  if j = i then .of fun _ _ ↦ 1 else 0

variable (F) in
/-- The elementary complex `F → F`, with identity differential, in degrees `i + 1` and `i`. -/
private def pairComplex (i : ℤ) : ChainComplex (ModuleCat.{u} F) ℤ :=
  ChainComplex.of (fun j ↦ ModuleCat.of F (Fin (pairRank i j) → F))
    (fun j ↦ ModuleCat.ofHom (Matrix.toLin' (pairMatrix i j))) fun j ↦ by
      ext1
      by_cases h : j = i <;> simp [pairMatrix, h]

/-- The standard basis of the elementary complex. -/
private def pairBasis (i j : ℤ) : Basis (Fin (pairRank i j)) F ((pairComplex F i).X j) :=
  Pi.basisFun F _

/-- The matrix of the differential of the elementary complex in its standard bases. -/
private theorem toMatrix_pairComplex_d (i j : ℤ) :
    LinearMap.toMatrix (pairBasis (F := F) i (j + 1)) (pairBasis i j)
      ((pairComplex F i).d (j + 1) j).hom = pairMatrix i j := by
  simp only [pairComplex, ChainComplex.of_d, ModuleCat.hom_ofHom]
  -- As in `HomologicalComplex.toMatrix_matrixBaseChange_d`: `pairBasis i j` is
  -- `Pi.basisFun F _` by definition, and `Matrix.toLin'` is `Matrix.toLin` in the standard bases;
  -- the module structure on `(pairComplex F i).X j` is that of `Fin _ → F` only after unfolding
  -- `ModuleCat.of`, so the lemma is applied with `exact` rather than rewritten with.
  exact LinearMap.toMatrix_toLin (Pi.basisFun F _) (Pi.basisFun F _) _

/-- The entries of the matrix of the differential of the elementary complex: `1` from degree
`i + 1` to degree `i`, and `0` elsewhere. -/
private theorem toMatrix_pairComplex_d_apply (i j : ℤ) (t' : Fin (pairRank i j))
    (t : Fin (pairRank i (j + 1))) :
    LinearMap.toMatrix (pairBasis (F := F) i (j + 1)) (pairBasis i j)
      ((pairComplex F i).d (j + 1) j).hom t' t = if j = i then 1 else 0 := by
  rw [toMatrix_pairComplex_d, pairMatrix]
  split_ifs <;> simp

private theorem pairRank_eq_add (i j : ℤ) :
    pairRank i j = (if j = i then 1 else 0) + if j = i + 1 then 1 else 0 := by
  unfold pairRank
  split_ifs <;> omega

private theorem pairRank_succ_eq (i j : ℤ) :
    (if j + 1 = i + 1 then 1 else 0) = if j = i then 1 else 0 := by
  simp

/-- The square minors of the elementary complex are identity matrices. -/
private theorem torsionMinor_pairBasis (i j : ℤ) :
    torsionMinor (pairBasis (F := F) i) (pairRank_eq_add i) (pairRank_succ_eq i) j = 1 := by
  ext r k
  by_cases hj : j = i
  · subst hj
    have hr := r.isLt
    have hk := k.isLt
    simp only [↓reduceIte] at hr hk
    have hrk : r = k := Fin.ext (by omega)
    subst hrk
    rw [torsionMinor_apply, ← LinearMap.toMatrix_apply, toMatrix_pairComplex_d_apply]
    simp
  · exact absurd r.isLt (by simp [hj])

private theorem finite_pairRank (i : ℤ) : {j | pairRank i j ≠ 0}.Finite :=
  (Set.toFinite {i + 1, i}).subset fun j hj ↦ by
    by_contra h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    exact hj (ite_eq_right h)

/-- The elementary complex has torsion `1` in its standard basis. -/
private theorem reidemeisterTorsion_pairComplex (i : ℤ) :
    (pairComplex F i).reidemeisterTorsion (pairBasis i) = 1 := by
  rw [reidemeisterTorsion_eq_finprod_det_torsionMinor (hn := pairRank_eq_add i)
    (hpq := pairRank_succ_eq i) (fun j ↦ by simp [torsionMinor_pairBasis]) (finite_pairRank i)]
  simp [torsionMinor_pairBasis]

/-- The elementary complex is acyclic. -/
private theorem acyclic_pairComplex (i : ℤ) : (pairComplex F i).Acyclic :=
  acyclic_of_det_torsionMinor_ne_zero (c := pairBasis i) (hn := pairRank_eq_add i)
    (hpq := pairRank_succ_eq i) fun j ↦ by simp [torsionMinor_pairBasis]

/-- The differential of the elementary complex has rank `1` from degree `i + 1` to degree `i`,
and rank `0` elsewhere. -/
private theorem finrank_range_pairComplex_d (i j : ℤ) :
    finrank F (LinearMap.range ((pairComplex F i).d (j + 1) j).hom) =
      if j = i then 1 else 0 := by
  have h := Matrix.rank_eq_finrank_range_toLin (pairMatrix (F := F) i j) (pairBasis i j)
    (pairBasis i (j + 1))
  rw [← toMatrix_pairComplex_d, Matrix.toLin_toMatrix] at h
  rw [← h, toMatrix_pairComplex_d, pairMatrix]
  split_ifs with hj
  · subst hj
    -- Between the one-dimensional terms, the matrix is the `1 × 1` identity matrix.
    have h₀ : 1 = pairRank j j := by simp
    have h₁ : 1 = pairRank j (j + 1) := by simp
    have hM : (Matrix.of fun _ _ ↦ 1 : Matrix (Fin (pairRank j j)) (Fin (pairRank j (j + 1))) F) =
        (1 : Matrix (Fin 1) (Fin 1) F).reindex (finCongr h₀) (finCongr h₁) := by
      ext r t
      simp [Matrix.one_apply, Subsingleton.elim (Fin.cast h₀.symm r) (Fin.cast h₁.symm t)]
    rw [hM, Matrix.rank_reindex, Matrix.rank_one, Fintype.card_fin]
  · exact Matrix.rank_zero

end Pair

/-! ### Gaussian elimination -/

section Elimination

variable {C : ChainComplex (ModuleCat F) ℤ} {D : ChainComplex (ModuleCat.{v} F) ℤ}
  {m : ℤ → ℕ} {i : ℤ}

variable (m i) in
/-- The last basis index in a degree `j ∈ {i + 1, i}` of the cancelling pair. -/
private def pairIdx (j : ℤ) (h : j = i + 1 ∨ j = i) : Fin (m j + pairRank i j) :=
  Fin.natAdd (m j) ⟨0, by simp [pairRank, h]⟩

private theorem natAdd_eq_pairIdx {j : ℤ} (h : j = i + 1 ∨ j = i) (t : Fin (pairRank i j)) :
    Fin.natAdd (m j) t = pairIdx m i j h :=
  Fin.ext (by have := t.isLt; simp only [pairRank, h, ite_true] at this; simp [pairIdx]; omega)

private theorem castAdd_ne_pairIdx {j : ℤ} (h : j = i + 1 ∨ j = i) (r : Fin (m j)) :
    Fin.castAdd (pairRank i j) r ≠ pairIdx m i j h :=
  fun hr ↦ by have := congrArg Fin.val hr; simp [pairIdx] at this; omega

private theorem le_pairIdx {j : ℤ} (h : j = i + 1 ∨ j = i) (k : Fin (m j + pairRank i j)) :
    k ≤ pairIdx m i j h := by
  have := k.isLt
  simp only [pairRank, h, ite_true] at this
  rw [Fin.le_def]
  simp [pairIdx]
  omega

/-- In a degree of the cancelling pair, the sum over the indices of the pair is its only term. -/
private theorem sum_natAdd_eq {M : Type*} [AddCommMonoid M] {j : ℤ} (h : j = i + 1 ∨ j = i)
    (g : Fin (m j + pairRank i j) → M) :
    ∑ t : Fin (pairRank i j), g (Fin.natAdd (m j) t) = g (pairIdx m i j h) := by
  rw [Fintype.sum_eq_single ⟨0, by simp [pairRank, h]⟩ fun t ht ↦ absurd (Fin.ext (by
    have := t.isLt; simp only [pairRank, h, ite_true] at this; simp; omega)) ht]
  rfl

/-- Outside the degrees of the cancelling pair, there are no indices of the pair. -/
private theorem sum_pairRank_eq_zero {M : Type*} [AddCommMonoid M] {j : ℤ}
    (h : ¬(j = i + 1 ∨ j = i)) (g : Fin (pairRank i j) → M) : ∑ t, g t = 0 :=
  Finset.sum_eq_zero fun t _ ↦ absurd t.isLt (by simp [pairRank, h])

variable (c : ∀ j, Basis (Fin (m j + if j = i + 1 ∨ j = i then 1 else 0)) F (C.X j))
  (e : ∀ j, Basis (Fin (m j)) F (D.X j))

/-- The differential of a basis vector, expanded along the basis vectors of `c` outside and
inside the cancelling pair. -/
private theorem d_basis_eq (j : ℤ) (l : Fin (m (j + 1) + pairRank i (j + 1))) :
    (C.d (j + 1) j).hom (c (j + 1) l) =
      ∑ r, LinearMap.toMatrix (c (j + 1)) (c j) (C.d (j + 1) j).hom (Fin.castAdd _ r) l •
          c j (Fin.castAdd _ r) +
        ∑ t, LinearMap.toMatrix (c (j + 1)) (c j) (C.d (j + 1) j).hom (Fin.natAdd _ t) l •
          c j (Fin.natAdd _ t) := by
  simp_rw [LinearMap.toMatrix_apply]
  rw [← Fin.sum_univ_add (f := fun k ↦ (c j).repr ((C.d (j + 1) j).hom (c (j + 1) l)) k • c j k),
    Basis.sum_repr]

/-- The matrix of the differential `Cᵢ₊₁ → Cᵢ`, whose entry at the cancelling pair is the pivot. -/
private abbrev pivotMatrix := LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom

/-- The basis of `Cᵢ₊₁` after the column operations of the elimination: the vector `z⁺` of the
pair, and the other vectors `x` corrected to `x - (v x / a) z⁺`, whose differentials have no
`z⁻`-coordinate. -/
private def upperFamily (l : Fin (m (i + 1) + pairRank i (i + 1))) : C.X (i + 1) :=
  if l = pairIdx m i (i + 1) (.inl rfl) then c (i + 1) l else
    c (i + 1) l - ((pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)))⁻¹ *
      pivotMatrix c (pairIdx m i i (.inr rfl)) l) • c (i + 1) (pairIdx m i (i + 1) (.inl rfl))

/-- The basis of `Cᵢ` after the elimination: the vector `z⁻` of the pair replaced by `d z⁺`. -/
private def lowerFamily : Fin (m i + pairRank i i) → C.X i :=
  Function.update (c i) (pairIdx m i i (.inr rfl))
    ((C.d (i + 1) i).hom (c (i + 1) (pairIdx m i (i + 1) (.inl rfl))))

/-- The bases of `C` after the elimination. -/
private def newFamily : ∀ j, Fin (m j + pairRank i j) → C.X j :=
  Function.update (Function.update (fun j ↦ ⇑(c j)) (i + 1) (upperFamily c)) i (lowerFamily c)

private theorem newFamily_self : newFamily c i = lowerFamily c :=
  Function.update_self ..

private theorem newFamily_succ : newFamily c (i + 1) = upperFamily c := by
  rw [newFamily, Function.update_of_ne (by omega), Function.update_self]

private theorem newFamily_of_ne {j : ℤ} (h₁ : j ≠ i + 1) (h₀ : j ≠ i) : newFamily c j = c j := by
  rw [newFamily, Function.update_of_ne h₀, Function.update_of_ne h₁]

/-- The column operations in degree `i + 1` are unitriangular. -/
private theorem det_upperFamily : (c (i + 1)).det (upperFamily c) = 1 := by
  rw [Basis.det_apply]
  refine (Matrix.det_of_isLowerTriangular _ fun k l hkl ↦ ?_).trans
    (Finset.prod_eq_one fun k _ ↦ ?_)
  · have hkl : k < l := OrderDual.toDual_lt_toDual.1 hkl
    have hk : k ≠ pairIdx m i (i + 1) (.inl rfl) := fun hk ↦
      (le_pairIdx (.inl rfl) l).not_gt (hk ▸ hkl)
    by_cases hl : l = pairIdx m i (i + 1) (.inl rfl) <;>
      simp [Basis.toMatrix_apply, upperFamily, hl, hk, hkl.ne']
  · by_cases hk : k = pairIdx m i (i + 1) (.inl rfl) <;>
      simp [Basis.toMatrix_apply, upperFamily, hk]

/-- Replacing `z⁻` by `d z⁺` in degree `i` multiplies the determinant by the pivot. -/
private theorem det_lowerFamily :
    (c i).det (lowerFamily c) =
      pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)) := by
  have h := Matrix.det_updateCol_sum (1 : Matrix _ _ F) (pairIdx m i i (.inr rfl))
    ((c i).repr ((C.d (i + 1) i).hom (c (i + 1) (pairIdx m i (i + 1) (.inl rfl)))))
  simp only [Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Matrix.det_one] at h
  rw [Basis.det_apply, lowerFamily, Basis.toMatrix_update, Basis.toMatrix_self, pivotMatrix,
    LinearMap.toMatrix_apply]
  exact h

private theorem det_newFamily (j : ℤ) :
    (c j).det (newFamily c j) = if j = i then
      pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)) else 1 := by
  by_cases h₀ : j = i
  · subst h₀
    simp only [↓reduceIte, newFamily_self, det_lowerFamily]
  simp only [h₀, ↓reduceIte]
  by_cases h₁ : j = i + 1
  · subst h₁
    rw [newFamily_succ, det_upperFamily]
  rw [newFamily_of_ne c h₁ h₀, Basis.det_self]

/-- The expansion of the differential of a basis vector into a degree `j` of the cancelling pair. -/
private theorem d_basis_eq_of_mem {j : ℤ} (h : j = i + 1 ∨ j = i)
    (l : Fin (m (j + 1) + pairRank i (j + 1))) :
    (C.d (j + 1) j).hom (c (j + 1) l) =
      ∑ r, LinearMap.toMatrix (c (j + 1)) (c j) (C.d (j + 1) j).hom (Fin.castAdd _ r) l •
          c j (Fin.castAdd _ r) +
        LinearMap.toMatrix (c (j + 1)) (c j) (C.d (j + 1) j).hom (pairIdx m i j h) l •
          c j (pairIdx m i j h) := by
  rw [d_basis_eq]
  congr 1
  exact sum_natAdd_eq h fun k ↦ LinearMap.toMatrix (c (j + 1)) (c j) (C.d (j + 1) j).hom k l • c j k

/-- The expansion of the differential of a basis vector into a degree outside the cancelling
pair. -/
private theorem d_basis_eq_of_not_mem {j : ℤ} (h : ¬(j = i + 1 ∨ j = i))
    (l : Fin (m (j + 1) + pairRank i (j + 1))) :
    (C.d (j + 1) j).hom (c (j + 1) l) =
      ∑ r, LinearMap.toMatrix (c (j + 1)) (c j) (C.d (j + 1) j).hom (Fin.castAdd _ r) l •
          c j (Fin.castAdd _ r) := by
  rw [d_basis_eq, sum_pairRank_eq_zero h, add_zero]

/-- The matrices of `D` are those of `C` after the elimination: the Schur complement
`N - w a⁻¹ v` from degree `i + 1` to degree `i`, and the matrices of `C` with the rows and columns
of `z⁺` and `z⁻` deleted elsewhere. -/
private def IsGaussianElimination : Prop :=
  (∀ r s, LinearMap.toMatrix (e (i + 1)) (e i) (D.d (i + 1) i).hom r s =
      pivotMatrix c (Fin.castAdd _ r) (Fin.castAdd _ s) -
        pivotMatrix c (Fin.castAdd _ r) (pairIdx m i (i + 1) (.inl rfl)) *
          (pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)))⁻¹ *
          pivotMatrix c (pairIdx m i i (.inr rfl)) (Fin.castAdd _ s)) ∧
    ∀ j, j ≠ i → ∀ r s, LinearMap.toMatrix (e (j + 1)) (e j) (D.d (j + 1) j).hom r s =
      LinearMap.toMatrix (c (j + 1)) (c j) (C.d (j + 1) j).hom (Fin.castAdd _ r) (Fin.castAdd _ s)

variable {c}

/-- The differential of the corrected vectors `x - (v x / a) z⁺` of `Cᵢ₊₁` has no
`z⁻`-coordinate, and its other coordinates form the Schur complement `N - w a⁻¹ v`. -/
private theorem d_upperFamily_castAdd
    (ha : pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)) ≠ 0)
    (s : Fin (m (i + 1))) :
    (C.d (i + 1) i).hom (upperFamily c (Fin.castAdd _ s)) =
      ∑ r, (pivotMatrix c (Fin.castAdd _ r) (Fin.castAdd _ s) -
        pivotMatrix c (Fin.castAdd _ r) (pairIdx m i (i + 1) (.inl rfl)) *
          (pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)))⁻¹ *
          pivotMatrix c (pairIdx m i i (.inr rfl)) (Fin.castAdd _ s)) • c i (Fin.castAdd _ r) := by
  simp only [upperFamily, castAdd_ne_pairIdx, ↓reduceIte, map_sub, map_smul]
  rw [d_basis_eq_of_mem c (.inr rfl), d_basis_eq_of_mem c (.inr rfl)]
  set a := pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl))
  simp only [smul_add, Finset.smul_sum, smul_smul, sub_smul, Finset.sum_sub_distrib]
  rw [mul_right_comm, inv_mul_cancel₀ ha, one_mul]
  have hcoef (r : Fin (m i)) :
      a⁻¹ * pivotMatrix c (pairIdx m i i (.inr rfl)) (Fin.castAdd _ s) *
          pivotMatrix c (Fin.castAdd _ r) (pairIdx m i (i + 1) (.inl rfl)) =
        pivotMatrix c (Fin.castAdd _ r) (pairIdx m i (i + 1) (.inl rfl)) * a⁻¹ *
          pivotMatrix c (pairIdx m i i (.inr rfl)) (Fin.castAdd _ s) := by
    ring
  simp only [hcoef]
  abel

/-- Since `d ∘ d = 0`, the `z⁻`-row of the matrix of `d : Cᵢ₊₁ → Cᵢ` annihilates the columns of
the matrix of `d : Cᵢ₊₂ → Cᵢ₊₁`. -/
private theorem sum_pivotMatrix_mul_eq_zero (l : Fin (m (i + 1 + 1) + pairRank i (i + 1 + 1))) :
    ∑ r, pivotMatrix c (pairIdx m i i (.inr rfl)) (Fin.castAdd _ r) *
        LinearMap.toMatrix (c (i + 1 + 1)) (c (i + 1)) (C.d (i + 1 + 1) (i + 1)).hom
          (Fin.castAdd _ r) l +
      pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)) *
        LinearMap.toMatrix (c (i + 1 + 1)) (c (i + 1)) (C.d (i + 1 + 1) (i + 1)).hom
          (pairIdx m i (i + 1) (.inl rfl)) l = 0 := by
  have hpair := sum_natAdd_eq (.inl rfl) fun k ↦ pivotMatrix c (pairIdx m i i (.inr rfl)) k *
    LinearMap.toMatrix (c (i + 1 + 1)) (c (i + 1)) (C.d (i + 1 + 1) (i + 1)).hom k l
  beta_reduce at hpair
  have := congrFun (congrFun (toMatrix_d_mul_toMatrix_d C c (i + 1 + 1) (i + 1) i)
    (pairIdx m i i (.inr rfl))) l
  rw [Matrix.mul_apply, Fin.sum_univ_add, hpair] at this
  exact this

/-- The differential `Cᵢ₊₂ → Cᵢ₊₁`, written in the corrected basis of `Cᵢ₊₁`, has no
`z⁺`-coordinate. -/
private theorem d_basis_castAdd_eq_sum_upperFamily
    (ha : pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)) ≠ 0)
    (s : Fin (m (i + 1 + 1))) :
    (C.d (i + 1 + 1) (i + 1)).hom (c (i + 1 + 1) (Fin.castAdd _ s)) =
      ∑ r, LinearMap.toMatrix (c (i + 1 + 1)) (c (i + 1)) (C.d (i + 1 + 1) (i + 1)).hom
        (Fin.castAdd _ r) (Fin.castAdd _ s) • upperFamily c (Fin.castAdd _ r) := by
  have key := sum_pivotMatrix_mul_eq_zero (c := c) (Fin.castAdd _ s)
  rw [d_basis_eq_of_mem c (.inl rfl)]
  simp only [upperFamily, castAdd_ne_pairIdx, ↓reduceIte, smul_sub, smul_smul,
    Finset.sum_sub_distrib]
  rw [← Finset.sum_smul, sub_eq_add_neg, ← neg_smul]
  congr 2
  set a := pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl))
  rw [eq_neg_iff_add_eq_zero, ← mul_right_inj' ha, mul_zero, ← key, mul_add, Finset.mul_sum,
    add_comm]
  congr 1
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  field_simp

/-- Away from `z⁺`, the new bases agree with `c` on the vectors outside the pair. -/
private theorem newFamily_castAdd_of_ne {j : ℤ} (h : j ≠ i + 1) (r : Fin (m j)) :
    newFamily c j (Fin.castAdd _ r) = c j (Fin.castAdd _ r) := by
  by_cases h₀ : j = i
  · subst h₀
    simp [newFamily_self, lowerFamily, castAdd_ne_pairIdx]
  rw [newFamily_of_ne c h h₀]

/-- The differentials of the vectors outside the pair in the new bases of `C` have the matrices of
`D`: the Schur complement from degree `i + 1` to degree `i`, and the submatrices of the matrices of
`C` elsewhere. -/
private theorem d_newFamily_castAdd
    (ha : pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)) ≠ 0)
    (he : IsGaussianElimination c e)
    (j : ℤ) (s : Fin (m (j + 1))) :
    (C.d (j + 1) j).hom (newFamily c (j + 1) (Fin.castAdd _ s)) =
      ∑ r, LinearMap.toMatrix (e (j + 1)) (e j) (D.d (j + 1) j).hom r s •
        newFamily c j (Fin.castAdd _ r) := by
  by_cases h₀ : j = i
  · subst h₀
    rw [newFamily_succ, d_upperFamily_castAdd ha]
    have hj : j ≠ j + 1 := by omega
    simp only [he.1, newFamily_castAdd_of_ne hj]
  by_cases h₁ : j = i + 1
  · subst h₁
    rw [newFamily_of_ne c (by omega) (by omega), d_basis_castAdd_eq_sum_upperFamily ha,
      newFamily_succ]
    simp only [he.2 (i + 1) (by omega)]
  rw [newFamily_castAdd_of_ne (by omega), newFamily_of_ne c h₁ h₀,
    d_basis_eq_of_not_mem c (by omega)]
  simp only [he.2 j h₀]

/-- The differentials of the vectors of the pair in the new bases of `C` have the matrix of the
elementary complex: `d z⁺` is the new vector of `Cᵢ`, whose differential vanishes. -/
private theorem d_newFamily_natAdd (j : ℤ) (t : Fin (pairRank i (j + 1))) :
    (C.d (j + 1) j).hom (newFamily c (j + 1) (Fin.natAdd _ t)) =
      ∑ t' : Fin (pairRank i j), (if j = i then (1 : F) else 0) •
        newFamily c j (Fin.natAdd _ t') := by
  by_cases h₀ : j = i
  · subst h₀
    have hpair := sum_natAdd_eq (.inr rfl) fun k ↦ (if j = j then (1 : F) else 0) • newFamily c j k
    beta_reduce at hpair
    rw [hpair, newFamily_succ, newFamily_self, natAdd_eq_pairIdx (.inl rfl)]
    simp [upperFamily, lowerFamily]
  have h₁ : j + 1 = i := by
    have := t.isLt
    simp only [pairRank] at this
    split_ifs at this with h
    · omega
    · omega
  subst h₁
  rw [newFamily_self, natAdd_eq_pairIdx (.inr rfl)]
  simp [lowerFamily, h₀, d_comp_d_apply]

private theorem isUnit_det_newFamily
    (ha : pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)) ≠ 0)
    (j : ℤ) : IsUnit ((c j).det (newFamily c j)) := by
  rw [det_newFamily]
  split_ifs <;> simp [ha]

/-- The bases of `C` after the elimination: `C` is the direct sum of the span of the vectors
outside the pair, with the matrices of `D`, and of the span of `z⁺` and `d z⁺`. -/
private def newBasis
    (ha : pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)) ≠ 0)
    (j : ℤ) : Basis (Fin (m j + pairRank i j)) F (C.X j) :=
  .mk ((Basis.is_basis_iff_det (c j)).2 (isUnit_det_newFamily ha j)).1
    ((Basis.is_basis_iff_det (c j)).2 (isUnit_det_newFamily ha j)).2.ge

private theorem coe_newBasis
    (ha : pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)) ≠ 0)
    (j : ℤ) : ⇑(newBasis ha j) = newFamily c j :=
  Basis.coe_mk _ _

variable (i) in
/-- The direct sum of the coordinate copy of `D` and the elementary complex. -/
private abbrev sumComplex : ChainComplex (ModuleCat.{u} F) ℤ :=
  D.matrixBaseChange e (RingHom.id F) ⊞ pairComplex F i

variable (i) in
/-- The bases of the direct sum of `D` and the elementary complex: those of `D` followed by the
standard basis of the elementary complex. -/
private def sumBasis (j : ℤ) : Basis (Fin (m j + pairRank i j)) F ((sumComplex i e).X j) :=
  (biprodXBasis (D.matrixBaseChangeBasis e (RingHom.id F) j) (pairBasis i j)).reindex
    finSumFinEquiv

/-- The torsion of the direct sum of `D` and the elementary complex. -/
private theorem reidemeisterTorsion_sumBasis :
    (sumComplex i e).reidemeisterTorsion (sumBasis i e) =
      (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range
          ((pairComplex F i).d (j + 1 + 1) (j + 1)).hom) *
        finrank F (LinearMap.range (D.d (j + 1) j).hom))) * D.reidemeisterTorsion e := by
  have hrk (j : ℤ) :
      finrank F (LinearMap.range ((D.matrixBaseChange e (RingHom.id F)).d (j + 1) j).hom) =
        finrank F (LinearMap.range (D.d (j + 1) j).hom) :=
    finrank_range_d_eq_of_toMatrix_eq (RingHom.id F) (toMatrix_matrixBaseChange_d D e _ (j + 1) j)
  have h := reidemeisterTorsion_biprod (D.matrixBaseChangeBasis e (RingHom.id F)) (pairBasis i)
  rw [reidemeisterTorsion_pairComplex, mul_one,
    ← map_reidemeisterTorsion (RingHom.id F) fun j ↦ toMatrix_matrixBaseChange_d D e _ (j + 1) j,
    RingHom.id_apply] at h
  simp only [hrk] at h
  exact h

private theorem d_sumBasis_castAdd (j : ℤ) (s : Fin (m (j + 1))) :
    ((sumComplex i e).d (j + 1) j).hom (sumBasis i e (j + 1) (Fin.castAdd _ s)) =
      ∑ r, LinearMap.toMatrix (e (j + 1)) (e j) (D.d (j + 1) j).hom r s •
        sumBasis i e j (Fin.castAdd _ r) := by
  have hmat (r : Fin (m j)) : LinearMap.toMatrix (D.matrixBaseChangeBasis e (RingHom.id F) (j + 1))
      (D.matrixBaseChangeBasis e (RingHom.id F) j)
      ((D.matrixBaseChange e (RingHom.id F)).d (j + 1) j).hom r s =
        LinearMap.toMatrix (e (j + 1)) (e j) (D.d (j + 1) j).hom r s := by
    rw [toMatrix_matrixBaseChange_d, Matrix.map_apply, RingHom.id_apply]
  simp only [← hmat, sumBasis, Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd,
    biprodXBasis_inl, Hom.comm_apply, LinearMap.toMatrix_apply]
  nth_rewrite 1 [← (D.matrixBaseChangeBasis e (RingHom.id F) j).sum_repr
    (((D.matrixBaseChange e (RingHom.id F)).d (j + 1) j).hom
      (D.matrixBaseChangeBasis e (RingHom.id F) (j + 1) s))]
  rw [map_sum]
  simp only [map_smul]

private theorem d_sumBasis_natAdd (j : ℤ) (t : Fin (pairRank i (j + 1))) :
    ((sumComplex i e).d (j + 1) j).hom (sumBasis i e (j + 1) (Fin.natAdd _ t)) =
      ∑ t' : Fin (pairRank i j), (if j = i then (1 : F) else 0) •
        sumBasis i e j (Fin.natAdd _ t') := by
  simp only [sumBasis, Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd, biprodXBasis_inr,
    Hom.comm_apply]
  conv_lhs => rw [← (pairBasis i j).sum_repr
    (((pairComplex F i).d (j + 1) j).hom (pairBasis i (j + 1) t))]
  simp only [← LinearMap.toMatrix_apply, toMatrix_pairComplex_d_apply, map_sum, map_smul]

/-- After the elimination, the matrices of the differentials of `C` are those of the direct sum
of `D` and the elementary complex. -/
private theorem toMatrix_newBasis
    (ha : pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)) ≠ 0)
    (he : IsGaussianElimination c e)
    (j : ℤ) :
    LinearMap.toMatrix (newBasis ha (j + 1)) (newBasis ha j) (C.d (j + 1) j).hom =
      (LinearMap.toMatrix (sumBasis i e (j + 1)) (sumBasis i e j)
        ((sumComplex i e).d (j + 1) j).hom).map (RingHom.id F) := by
  ext k l
  refine Fin.addCases (fun s ↦ ?_) (fun t ↦ ?_) l
  · rw [Matrix.map_apply, RingHom.id_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
      coe_newBasis, d_newFamily_castAdd e ha he, d_sumBasis_castAdd, ← coe_newBasis ha]
    simp
  · rw [Matrix.map_apply, RingHom.id_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
      coe_newBasis, d_newFamily_natAdd, d_sumBasis_natAdd, ← coe_newBasis ha]
    split_ifs <;> simp

/-- In the bases adapted to the elimination, the torsion of `C` is that of `D`, up to the sign
`(-1) ^ (dim Bᵢ₋₁(D))` of the direct sum. -/
private theorem reidemeisterTorsion_newBasis
    (ha : pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)) ≠ 0)
    (he : IsGaussianElimination c e) :
    C.reidemeisterTorsion (newBasis ha) =
      (-1) ^ finrank F (LinearMap.range (D.d i (i - 1)).hom) * D.reidemeisterTorsion e := by
  have hrank (k : ℤ) (hk : k = i) : finrank F (LinearMap.range (D.d k (i - 1)).hom) =
      finrank F (LinearMap.range (D.d i (i - 1)).hom) := by
    subst hk
    rfl
  rw [← map_reidemeisterTorsion (RingHom.id F) (toMatrix_newBasis e ha he), RingHom.id_apply,
    reidemeisterTorsion_sumBasis, finprod_eq_single _ (i - 1) fun j hj ↦ by
      rw [finrank_range_pairComplex_d, ite_eq_right (by omega), zero_mul, pow_zero],
    finrank_range_pairComplex_d, ite_eq_left (by omega), one_mul, hrank _ (by omega)]

/-- The elimination preserves acyclicity. -/
private theorem acyclic_iff_of_newBasis
    (ha : pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)) ≠ 0)
    (he : IsGaussianElimination c e) :
    C.Acyclic ↔ D.Acyclic := by
  rw [acyclic_iff_of_toMatrix_eq (RingHom.id F) fun a b (hab : b + 1 = a) ↦ by
      subst hab
      exact toMatrix_newBasis e ha he b,
    acyclic_biprod_iff, acyclic_matrixBaseChange_id_iff]
  exact and_iff_left (acyclic_pairComplex i)

end Elimination

/-- **Gaussian elimination and torsion.** Let `C` be a based chain complex of vector spaces whose
bases `c j` consist, in degrees `i + 1` and `i`, of `m (i + 1)`, respectively `m i`, vectors
followed by one more vector `z⁺`, respectively `z⁻`, and of `m j` vectors in every other degree
`j`; the identification of the index types of `c` with these blocks is `hn`. Suppose that the
coefficient `a` of `z⁻` in `d z⁺` is nonzero, and let `D` be a based complex, with bases `e j` of
`m j` vectors, whose differential `Dᵢ₊₁ → Dᵢ` has the Schur complement `N - w a⁻¹ v` as matrix
and whose other differentials have the matrices of `C` with the rows and columns of `z⁺` and `z⁻`
deleted; here `N`, `w`, `v` are the blocks of the matrix of `d : Cᵢ₊₁ → Cᵢ` away from `z⁺` and
`z⁻`, in the column of `z⁺`, and in the row of `z⁻`. Then

`τ(C) = (-1) ^ (dim Bᵢ₋₁(D)) · a ^ ((-1) ^ (i + 1)) · τ(D)`,

where `Bᵢ₋₁(D)` is the image of `Dᵢ → Dᵢ₋₁`. Both torsions vanish unless `C`, equivalently `D`
(`HomologicalComplex.acyclic_iff_of_gaussianElimination`), is acyclic. -/
theorem reidemeisterTorsion_eq_mul_of_gaussianElimination {C : ChainComplex (ModuleCat F) ℤ}
    {D : ChainComplex (ModuleCat.{v} F) ℤ} {n m : ℤ → ℕ} {i : ℤ}
    (c : ∀ j, Basis (Fin (n j)) F (C.X j)) (e : ∀ j, Basis (Fin (m j)) F (D.X j))
    (hn : ∀ j, n j = m j + if j = i + 1 ∨ j = i then 1 else 0)
    (ha : LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom
      (Fin.cast (hn i).symm (Fin.natAdd (m i) ⟨0, by simp⟩))
      (Fin.cast (hn (i + 1)).symm (Fin.natAdd (m (i + 1)) ⟨0, by simp⟩)) ≠ 0)
    (hDi : ∀ r s, LinearMap.toMatrix (e (i + 1)) (e i) (D.d (i + 1) i).hom r s =
      LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom
          (Fin.cast (hn i).symm (Fin.castAdd _ r)) (Fin.cast (hn (i + 1)).symm (Fin.castAdd _ s)) -
        LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom
            (Fin.cast (hn i).symm (Fin.castAdd _ r))
            (Fin.cast (hn (i + 1)).symm (Fin.natAdd (m (i + 1)) ⟨0, by simp⟩)) *
          (LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom
            (Fin.cast (hn i).symm (Fin.natAdd (m i) ⟨0, by simp⟩))
            (Fin.cast (hn (i + 1)).symm (Fin.natAdd (m (i + 1)) ⟨0, by simp⟩)))⁻¹ *
          LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom
            (Fin.cast (hn i).symm (Fin.natAdd (m i) ⟨0, by simp⟩))
            (Fin.cast (hn (i + 1)).symm (Fin.castAdd _ s)))
    (hD : ∀ j, j ≠ i → ∀ r s, LinearMap.toMatrix (e (j + 1)) (e j) (D.d (j + 1) j).hom r s =
      LinearMap.toMatrix (c (j + 1)) (c j) (C.d (j + 1) j).hom
        (Fin.cast (hn j).symm (Fin.castAdd _ r)) (Fin.cast (hn (j + 1)).symm (Fin.castAdd _ s))) :
    C.reidemeisterTorsion c =
      (-1) ^ finrank F (LinearMap.range (D.d i (i - 1)).hom) *
        LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom
          (Fin.cast (hn i).symm (Fin.natAdd (m i) ⟨0, by simp⟩))
          (Fin.cast (hn (i + 1)).symm (Fin.natAdd (m (i + 1)) ⟨0, by simp⟩)) ^
            ((i + 1).negOnePow : ℤ) *
        D.reidemeisterTorsion e := by
  obtain rfl : n = fun j ↦ m j + pairRank i j := funext hn
  -- After substituting `n`, the casts are identities and the indices of the pair are `pairIdx`.
  simp only [Fin.cast_eq_self, natAdd_eq_pairIdx (m := m) (i := i) (j := i + 1) (.inl rfl),
    natAdd_eq_pairIdx (m := m) (i := i) (j := i) (.inr rfl)] at ha hDi hD ⊢
  have he : IsGaussianElimination c e := ⟨hDi, hD⟩
  -- Changing to the bases adapted to the elimination multiplies the torsion by `a ^ (-1) ^ i`.
  have hdet (j : ℤ) : (c j).det (newBasis ha j) = if j = i then
      pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)) else 1 := by
    rw [coe_newBasis]
    exact det_newFamily c j
  have hchange : C.reidemeisterTorsion (newBasis ha) = C.reidemeisterTorsion c *
      pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)) ^
        (i.negOnePow : ℤ) := by
    rw [reidemeisterTorsion_eq_mul_finprod_det C c (newBasis ha)]
    congr 1
    rw [finprod_eq_single _ i fun j hj ↦ by simp [hdet, hj]]
    simp [hdet]
  have hsum := reidemeisterTorsion_newBasis e ha he
  rw [hchange] at hsum
  have hu : pivotMatrix c (pairIdx m i i (.inr rfl)) (pairIdx m i (i + 1) (.inl rfl)) ^
      (i.negOnePow : ℤ) ≠ 0 := zpow_ne_zero _ ha
  rw [Int.negOnePow_succ, Units.val_neg, zpow_neg]
  field_simp
  linear_combination hsum

/-- **Gaussian elimination preserves acyclicity.** Under the hypotheses of
`HomologicalComplex.reidemeisterTorsion_eq_mul_of_gaussianElimination`, the complex `C` is acyclic
if and only if the complex `D` obtained by cancelling the pair `z⁺`, `z⁻` is. -/
theorem acyclic_iff_of_gaussianElimination {C : ChainComplex (ModuleCat F) ℤ}
    {D : ChainComplex (ModuleCat.{v} F) ℤ} {n m : ℤ → ℕ} {i : ℤ}
    (c : ∀ j, Basis (Fin (n j)) F (C.X j)) (e : ∀ j, Basis (Fin (m j)) F (D.X j))
    (hn : ∀ j, n j = m j + if j = i + 1 ∨ j = i then 1 else 0)
    (ha : LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom
      (Fin.cast (hn i).symm (Fin.natAdd (m i) ⟨0, by simp⟩))
      (Fin.cast (hn (i + 1)).symm (Fin.natAdd (m (i + 1)) ⟨0, by simp⟩)) ≠ 0)
    (hDi : ∀ r s, LinearMap.toMatrix (e (i + 1)) (e i) (D.d (i + 1) i).hom r s =
      LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom
          (Fin.cast (hn i).symm (Fin.castAdd _ r)) (Fin.cast (hn (i + 1)).symm (Fin.castAdd _ s)) -
        LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom
            (Fin.cast (hn i).symm (Fin.castAdd _ r))
            (Fin.cast (hn (i + 1)).symm (Fin.natAdd (m (i + 1)) ⟨0, by simp⟩)) *
          (LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom
            (Fin.cast (hn i).symm (Fin.natAdd (m i) ⟨0, by simp⟩))
            (Fin.cast (hn (i + 1)).symm (Fin.natAdd (m (i + 1)) ⟨0, by simp⟩)))⁻¹ *
          LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom
            (Fin.cast (hn i).symm (Fin.natAdd (m i) ⟨0, by simp⟩))
            (Fin.cast (hn (i + 1)).symm (Fin.castAdd _ s)))
    (hD : ∀ j, j ≠ i → ∀ r s, LinearMap.toMatrix (e (j + 1)) (e j) (D.d (j + 1) j).hom r s =
      LinearMap.toMatrix (c (j + 1)) (c j) (C.d (j + 1) j).hom
        (Fin.cast (hn j).symm (Fin.castAdd _ r)) (Fin.cast (hn (j + 1)).symm (Fin.castAdd _ s))) :
    C.Acyclic ↔ D.Acyclic := by
  obtain rfl : n = fun j ↦ m j + pairRank i j := funext hn
  -- After substituting `n`, the casts are identities and the indices of the pair are `pairIdx`.
  simp only [Fin.cast_eq_self, natAdd_eq_pairIdx (m := m) (i := i) (j := i + 1) (.inl rfl),
    natAdd_eq_pairIdx (m := m) (i := i) (j := i) (.inr rfl)] at ha hDi hD
  exact acyclic_iff_of_newBasis e ha ⟨hDi, hD⟩

end HomologicalComplex
