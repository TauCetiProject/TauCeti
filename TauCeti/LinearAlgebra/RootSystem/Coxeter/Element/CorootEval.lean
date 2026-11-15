/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Bipartite
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Bipartite
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.ActsBy
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
public import TauCeti.LinearAlgebra.RootSystem.Positive
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Coordinate coroot functionals and bipartite Coxeter matrices

For a base `b` of a crystallographic root pairing `P`, this file defines:
* `RootPairing.Base.corootEval`: coordinate evaluation of the `j`-th coroot functional on formal
  simple-root combinations `b.support → S`, its Weyl equivariance, and its sign characterization of
  positive and negative roots over `ℝ`.
* `RootPairing.Base.colorClassMatrix` and `RootPairing.Base.bipartiteCoxeterMatrix`: integer
  matrices in the simple-root basis for the colour-class involutions and bipartite Coxeter element,
  together with their `RootPairing.Base.ActsBy` compatibility with `TauCeti.weylCoxeterSystem`.

## References
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, §§ 3.16–3.17.
-/

public section

open Matrix Submodule TauCeti

namespace RootPairing.Base

/-! ### Coordinate coroot evaluation across arbitrary rings -/

section CorootEval

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] (b : P.Base)

/-- Evaluation of the `j`-th coroot functional on formal simple-root coordinate vectors
`b.support → S`, defined using the crystallographic integer pairings `⟨αᵢ, αⱼ^∨⟩`. -/
noncomputable def corootEval (S : Type*) [CommRing S] (j : ι) : (b.support → S) →ₗ[S] S where
  toFun y := ∑ i : b.support, (P.pairingIn ℤ (i : ι) j : S) * y i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c y := by simp [mul_left_comm, Finset.mul_sum]

/-- Explicit formula for `RootPairing.Base.corootEval`. -/
@[simp]
theorem corootEval_apply (S : Type*) [CommRing S] (j : ι) (y : b.support → S) :
    b.corootEval S j y = ∑ i : b.support, (P.pairingIn ℤ (i : ι) j : S) * y i := by rfl

/-- On a simple root `k : b.support`, `corootEval` evaluates against column `k` of the Cartan
matrix. -/
theorem corootEval_coe_support (S : Type*) [CommRing S] (k : b.support) (y : b.support → S) :
    b.corootEval S (k : ι) y = ∑ i : b.support, (b.cartanMatrix i k : S) * y i := by rfl

/-- On an actual linear combination `∑ i, y i • αᵢ` in `M`, `P.coroot' j` agrees with
`b.corootEval R j y`. -/
theorem coroot'_sum_smul_root (j : ι) (y : b.support → R) :
    P.coroot' j (∑ i : b.support, y i • P.root i) = b.corootEval R j y := by
  rw [map_sum, corootEval_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, smul_eq_mul, root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ, eq_intCast,
    mul_comm]

/-- Root negation negates `corootEval`. -/
theorem corootEval_reflectionPerm_self [CharZero R] (S : Type*) [CommRing S] (j : ι)
    (y : b.support → S) :
    b.corootEval S (P.reflectionPerm j j) y = -b.corootEval S j y := by
  simp [corootEval_apply, P.pairingIn_reflectionPerm_self_right, ← Finset.sum_neg_distrib]

/-- Equivariance of `corootEval` under a Weyl-group element `w` acting on the simple roots by an
integer matrix `W`. -/
theorem corootEval_weylGroupToPerm_inv [CharZero R] {w : P.weylGroup}
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy w W) (S : Type*) [CommRing S]
    (j : ι) (y : b.support → S) :
    b.corootEval S (P.weylGroupToPerm w⁻¹ j) y =
      b.corootEval S j ((W.map (Int.castRingHom S)) *ᵥ y) := by
  have hint (i : b.support) : P.pairingIn ℤ (i : ι) (P.weylGroupToPerm w⁻¹ j) =
      ∑ l : b.support, W l i * P.pairingIn ℤ (l : ι) j := by
    apply FaithfulSMul.algebraMap_injective ℤ R
    rw [P.algebraMap_pairingIn ℤ, ← root_coroot'_eq_pairing,
      ← P.coroot'_weylGroupToPerm_smul w (P.weylGroupToPerm w⁻¹ j) (P.root i),
      ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply,
      actsBy_iff.mp hW i, map_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_zsmul, zsmul_eq_mul, root_coroot'_eq_pairing, map_mul, P.algebraMap_pairingIn ℤ,
      eq_intCast]
  simp only [corootEval_apply, mulVec, dotProduct, map_apply, Int.coe_castRingHom, hint,
    Int.cast_sum, Int.cast_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Positive coroot expansion for `corootEval`: for a positive root `j`, `b.corootEval S j` is a
nonnegative integer combination of the simple `corootEval` functionals, not all zero. -/
theorem exists_corootEval_eq_sum_nat_of_mem_posRoots [Finite ι] [CharZero R] [IsDomain R]
    [P.IsReduced] {j : ι} (hj : j ∈ posRoots P b) :
    ∃ f : b.support → ℕ, (∃ k : b.support, f k ≠ 0) ∧
      ∀ (S : Type*) [CommRing S] (y : b.support → S),
        b.corootEval S j y = ∑ k : b.support, (f k : S) * b.corootEval S (k : ι) y := by
  have := P.flip_isReduced
  obtain ⟨f, -, hcor⟩ := exists_coroot_eq_sum_nat_of_mem_posRoots P b hj
  have hne : ∃ k : b.support, f k ≠ 0 := by
    by_contra! h0
    exact P.ne_zero' j (hcor.trans (Finset.sum_eq_zero fun k hk ↦ by simp [h0 ⟨k, hk⟩]))
  have hint (i : b.support) :
      P.pairingIn ℤ (i : ι) j = ∑ k : b.support, (f k : ℤ) * P.pairingIn ℤ (i : ι) (k : ι) := by
    apply FaithfulSMul.algebraMap_injective ℤ R
    rw [P.algebraMap_pairingIn ℤ, ← root'_coroot_eq_pairing, hcor, map_sum, map_sum,
      ← Finset.sum_coe_sort b.support]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_nsmul, nsmul_eq_mul, map_mul, map_natCast, root'_coroot_eq_pairing,
      P.algebraMap_pairingIn ℤ]
  refine ⟨fun k ↦ f k, hne, fun S _ y ↦ ?_⟩
  simp only [corootEval_apply, Finset.mul_sum, hint, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- If every simple coroot functional is positive at `y : b.support → ℝ`, then every positive
coroot functional is positive at `y`. -/
theorem corootEval_pos_of_mem_posRoots [Finite ι] [CharZero R] [IsDomain R] [P.IsReduced]
    {y : b.support → ℝ} (hy : ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) y)
    {j : ι} (hj : j ∈ posRoots P b) : 0 < b.corootEval ℝ j y := by
  obtain ⟨f, ⟨k₀, hk₀⟩, hsum⟩ := b.exists_corootEval_eq_sum_nat_of_mem_posRoots hj
  rw [hsum ℝ y]
  exact Finset.sum_pos' (fun k _ ↦ mul_nonneg (Nat.cast_nonneg _) (hy k).le)
    ⟨k₀, Finset.mem_univ k₀, mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk₀)) (hy k₀)⟩

/-- If every simple coroot functional is positive at `y : b.support → ℝ`, then every negative
coroot functional is negative at `y`. -/
theorem corootEval_neg_of_mem_negRoots [Finite ι] [CharZero R] [IsDomain R] [P.IsReduced]
    {y : b.support → ℝ} (hy : ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) y)
    {j : ι} (hj : j ∈ negRoots P b) : b.corootEval ℝ j y < 0 := by
  have hpos : P.reflectionPerm j j ∈ posRoots P b := by
    rwa [mem_posRoots, isPos_reflectionPerm_self_iff_mem_negRoots]
  linarith [b.corootEval_pos_of_mem_posRoots hy hpos, b.corootEval_reflectionPerm_self ℝ j y]

/-- At a coordinate vector `y : b.support → ℝ` where every simple coroot is positive, positivity of
`b.corootEval ℝ j y` characterizes the positive roots. -/
theorem corootEval_pos_iff_mem_posRoots [Finite ι] [CharZero R] [IsDomain R] [P.IsReduced]
    {y : b.support → ℝ} (hy : ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) y) (j : ι) :
    0 < b.corootEval ℝ j y ↔ j ∈ posRoots P b := by
  refine ⟨fun h ↦ ?_, b.corootEval_pos_of_mem_posRoots hy⟩
  by_contra hneg; rw [not_mem_posRoots_iff_mem_negRoots] at hneg
  exact (b.corootEval_neg_of_mem_negRoots hy hneg).not_gt h

/-- At a coordinate vector `y : b.support → ℝ` where every simple coroot is positive, no coroot
functional vanishes. -/
theorem corootEval_ne_zero_of_forall_pos [Finite ι] [CharZero R] [IsDomain R] [P.IsReduced]
    {y : b.support → ℝ} (hy : ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) y) (j : ι) :
    b.corootEval ℝ j y ≠ 0 := by
  by_cases hj : j ∈ posRoots P b
  · exact (b.corootEval_pos_of_mem_posRoots hy hj).ne'
  · rw [not_mem_posRoots_iff_mem_negRoots] at hj
    exact (b.corootEval_neg_of_mem_negRoots hy hj).ne

end CorootEval

/-! ### Matrices of colour-class involutions and the bipartite Coxeter element -/

section BipartiteMatrices

private theorem prod_map_reflMatrix_of_orthogonal {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) {l : List κ} (hl : l.Nodup)
    (horth : ∀ p ∈ l, ∀ q ∈ l, p ≠ q → A p q = 0) (k j : κ) :
    ((l.map (reflMatrix A)).prod) k j =
      (if k = j then 1 else 0) - (if k ∈ l then A j k else 0) := by
  induction l generalizing k j with
  | nil => simp [Matrix.one_apply]
  | cons p l ih =>
    rw [List.nodup_cons] at hl
    have hrow (M : Matrix κ κ ℤ) :
        (reflMatrix A p * M) k j = M k j - if k = p then ∑ m, A m p * M m j else 0 := by
      simp only [Matrix.mul_apply, reflMatrix_apply, sub_mul, Finset.sum_sub_distrib, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      by_cases hkp : k = p <;> simp [hkp]
    rw [List.map_cons, List.prod_cons, hrow]
    simp only [ih hl.2 fun a ha b hb ↦
      horth a (List.mem_cons_of_mem p ha) b (List.mem_cons_of_mem p hb)]
    rcases eq_or_ne k p with rfl | hkp
    · simp only [↓reduceIte, hl.1, sub_zero, List.mem_cons, true_or, mul_sub, mul_ite, mul_one,
        mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]
      rw [Finset.sum_eq_zero fun m _ ↦ ?_, sub_zero]
      split_ifs with hm
      · rw [horth m (List.mem_cons_of_mem k hm) k List.mem_cons_self
          (ne_of_mem_of_not_mem hm hl.1), zero_mul]
      · rfl
    · simp [hkp, List.mem_cons]

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]

omit [DecidableEq ι] in
/-- Distinct simple roots of the same colour in a two-colouring of the Coxeter graph are
orthogonal. -/
theorem cartanMatrix_eq_zero_of_color_eq (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) {p q : b.support}
    (hpq : p ≠ q) (hc : col p = col q) : b.cartanMatrix p q = 0 := by
  by_contra hne
  refine col.valid ?_ hc
  rw [graph_coxeterMatrixOfBase P b, diagramGraph_adj]
  exact ⟨hpq, hne, fun hqp ↦ hne (b.cartanMatrix_apply_eq_zero_iff_symm.mpr hqp)⟩

/-- Integer matrix of the colour-class involution `colorClassProd col s` in the simple-root
basis. -/
noncomputable def colorClassMatrix (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) (s : Bool) :
    Matrix b.support b.support ℤ :=
  (((Finset.univ.filter fun i : b.support ↦ col i = s).toList).map (reflMatrix b.cartanMatrix)).prod

/-- Explicit entries of `b.colorClassMatrix col s`: simple roots of the same colour are pairwise
orthogonal. -/
theorem colorClassMatrix_apply (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) (s : Bool) (k j : b.support) :
    b.colorClassMatrix col s k j =
      (if k = j then 1 else 0) - (if col k = s then b.cartanMatrix j k else 0) := by
  let fs := Finset.univ.filter fun i : b.support ↦ col i = s
  have horth : ∀ p ∈ fs.toList, ∀ q ∈ fs.toList, p ≠ q → b.cartanMatrix p q = 0 := by
    intro p hp q hq hpq
    rw [Finset.mem_toList, Finset.mem_filter] at hp hq
    exact b.cartanMatrix_eq_zero_of_color_eq col hpq (hp.2.trans hq.2.symm)
  simpa [colorClassMatrix, fs] using
    prod_map_reflMatrix_of_orthogonal b.cartanMatrix (Finset.nodup_toList fs) horth k j

/-- `b.colorClassMatrix col s` is an involution (`M * M = 1`). -/
theorem colorClassMatrix_mul_self (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) (s : Bool) :
    b.colorClassMatrix col s * b.colorClassMatrix col s = 1 := by
  ext k j
  simp only [Matrix.mul_apply, colorClassMatrix_apply, Matrix.one_apply]
  by_cases hck : col k = s
  · have hsum : ∑ x : b.support,
        (if col x = s then b.cartanMatrix x k * b.cartanMatrix j x else 0) =
        2 * b.cartanMatrix j k := by
      rw [Finset.sum_eq_single k (fun x _ hxk ↦ ?_) (by simp)]
      · simp [hck]
      · split_ifs with hcx
        · rw [b.cartanMatrix_eq_zero_of_color_eq col hxk (hcx.trans hck.symm), zero_mul]
        · rfl
    have hterm (x : b.support) :
        ((if k = x then 1 else 0) - b.cartanMatrix x k) *
          ((if x = j then 1 else 0) - if col x = s then b.cartanMatrix j x else 0) =
        (if k = x then (if x = j then 1 else 0) - (if col x = s then b.cartanMatrix j x else 0)
          else 0) - (if x = j then b.cartanMatrix x k else 0) +
          (if col x = s then b.cartanMatrix x k * b.cartanMatrix j x else 0) := by
      split_ifs <;> ring
    simp only [hck, ↓reduceIte, hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, hsum]
    ring
  · simp [hck]

/-- Integer matrix of the bipartite Coxeter element in the simple-root basis. -/
@[expose] noncomputable def bipartiteCoxeterMatrix (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) : Matrix b.support b.support ℤ :=
  b.colorClassMatrix col true * b.colorClassMatrix col false

variable [P.IsReduced]

/-- The colour-class involution `colorClassProd col s` acts on the simple roots by
`b.colorClassMatrix col s`. -/
theorem actsBy_colorClassProd (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) (s : Bool) :
    b.ActsBy ((weylCoxeterSystem P b).colorClassProd col s) (b.colorClassMatrix col s) := by
  let fs := Finset.univ.filter fun i : b.support ↦ col i = s
  rw [← (weylCoxeterSystem P b).wordProd_eq_colorClassProd col (Finset.nodup_toList fs)
    (by simp [fs]), weylCoxeterSystem_wordProd]
  exact b.actsBy_wordProd fs.toList

/-- The bipartite Coxeter element acts on the simple roots by `b.bipartiteCoxeterMatrix col`. -/
theorem actsBy_bipartiteCoxeterElement (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    b.ActsBy ((weylCoxeterSystem P b).bipartiteCoxeterElement col)
      (b.bipartiteCoxeterMatrix col) := by
  rw [CoxeterSystem.bipartiteCoxeterElement_def]
  exact (b.actsBy_colorClassProd col true).mul (b.actsBy_colorClassProd col false)

/-- The inverse of the bipartite Coxeter element acts by
`b.colorClassMatrix col false * b.colorClassMatrix col true`. -/
theorem actsBy_bipartiteCoxeterElement_inv (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    b.ActsBy ((weylCoxeterSystem P b).bipartiteCoxeterElement col)⁻¹
      (b.colorClassMatrix col false * b.colorClassMatrix col true) := by
  rw [CoxeterSystem.bipartiteCoxeterElement_def, _root_.mul_inv_rev,
    CoxeterSystem.colorClassProd_inv, CoxeterSystem.colorClassProd_inv]
  exact (b.actsBy_colorClassProd col false).mul (b.actsBy_colorClassProd col true)

end BipartiteMatrices

end RootPairing.Base

end
