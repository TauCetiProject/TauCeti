/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.GroupTheory.Coxeter.CoxeterElement
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Bipartite
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.ActsBy
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Conj
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Coleman's Coxeter plane and regular primitive-root eigenvectors

Let `b` be a base of a finite, reduced, irreducible, crystallographic root system `P`, and let `c`
be a Coxeter element of `b`, the product of all the simple reflections each taken once. Every such
element is conjugate in the Weyl group to the bipartite Coxeter element `c₁ c₂` attached to a
two-colouring of the Dynkin tree (`RootPairing.isConj_wordProd_of_perm`,
`CoxeterSystem.isConj_wordProd_bipartiteCoxeterElement`).

Following Coleman and Steinberg (Humphreys, §§3.16–3.17), when the rank is at least two the
nonnegative matrix `(2 : ℝ) • 1 - Aᵀ` (where `A = b.cartanMatrix`) is irreducible because the
Dynkin diagram is connected. Its Perron–Frobenius eigenvector `x > 0` for eigenvalue `μ > 0` splits
along the two colour classes into vectors `u_true` and `u_false` in the simple-root coordinate
space. Because simple roots of the same colour are orthogonal, the colour-class involutions `c₁`
and `c₂` preserve the plane spanned by `u_true` and `u_false`, acting by

`c₁ u_true = -u_true`, `c₁ u_false = u_false + μ u_true`,
`c₂ u_false = -u_false`, `c₂ u_true = u_true + μ u_false`.

Positive definiteness of the symmetrized Cartan matrix forces `μ < 2`, so `μ = 2 cos θ` with
`0 < θ < π / 2`. Passing to an adapted basis `(e₁, e₂)` of the plane turns `c₁` and `c₂` into two
reflections meeting at angle `θ` whose open sector `0 < φ < θ` lies inside the open dominant cone
and therefore meets no root hyperplane, while the boundary rays lie on the simple-root walls of the
two colour classes. Since `c = c₁ c₂` rotates the plane by `2 θ` and has finite order `h`, Bézout's
identity forces `θ = π / h` (any larger multiple `m π / h` would rotate a boundary wall ray into
the interior of the dominant sector).

Complexifying `(e₁, e₂)` to `e₁ + i e₂` (and treating rank one directly on the single simple root)
produces, for **every** Coxeter element `c = wordProd P b l`, an eigenvector for the primitive
`h`-th root of unity `exp (2πi / h)` that lies strictly off every root hyperplane and has trivial
pointwise stabilizer in `P.weylGroup`.

## Main definitions

* `RootPairing.Base.corootEval`: coordinate evaluation of the `j`-th coroot functional on formal
  simple-root combinations `b.support → S`.
* `RootPairing.Base.colorClassMatrix`: integer matrix of a colour-class involution in the
  simple-root basis.
* `RootPairing.Base.bipartiteCoxeterMatrix`: integer matrix of a bipartite Coxeter element in the
  simple-root basis.

## Main results

* `RootPairing.Base.isIrreducible_two_smul_one_sub_transpose_cartanMatrix`: for rank at least two,
  the real matrix `(2 : ℝ) • 1 - Aᵀ` of an irreducible reduced root pairing is irreducible.
* `RootPairing.Base.exists_coxeterPlane_bipartiteCoxeterElement` (and
  `RootPairing.Base.exists_coxeterPlane_bipartiteCoxeterElement_of_isFiniteType`): **Coleman's
  Coxeter plane** for a bipartite Coxeter element, rotated through exact angle `2π / h` with open
  sector `(0, π / h)` in the open dominant cone.
* `RootPairing.Base.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd` (and
  `RootPairing.Base.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd_of_isFiniteType`):
  matrix-level regular `exp (2πi / h)`-eigenvector of any Coxeter element over any
  characteristic-zero domain.
* `RootPairing.Base.exists_regularWeight_eigenvector_wordProd`: for an irreducible finite complex
  crystallographic reduced root pairing, every Coxeter element has a regular weight eigenvector
  (`P.IsRegularWeight v`) with eigenvalue `exp (2πi / h)` (`IsPrimitiveRoot`) and trivial
  stabilizer in `P.weylGroup`.

## References

* A. J. Coleman, *The Betti numbers of the simple Lie groups*, Canad. J. Math. **10** (1958),
  349–356.
* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.17.
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
  map_smul' c y := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- Explicit formula for `RootPairing.Base.corootEval`. -/
@[simp]
theorem corootEval_apply (S : Type*) [CommRing S] (j : ι) (y : b.support → S) :
    b.corootEval S j y = ∑ i : b.support, (P.pairingIn ℤ (i : ι) j : S) * y i := by
  rfl

/-- On a simple root `k : b.support`, `corootEval` evaluates against column `k` of the Cartan
matrix. -/
theorem corootEval_coe_support (S : Type*) [CommRing S] (k : b.support) (y : b.support → S) :
    b.corootEval S (k : ι) y = ∑ i : b.support, (b.cartanMatrix i k : S) * y i := by
  rfl

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
  rw [corootEval_apply, corootEval_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [P.pairingIn_reflectionPerm_self_right, Int.cast_neg, neg_mul]

/-- Equivariance of `corootEval` under a Weyl-group element `w` acting on the simple roots by an
integer matrix `W`. -/
theorem corootEval_weylGroupToPerm_inv [CharZero R] {w : P.weylGroup}
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy w W) (S : Type*) [CommRing S]
    (j : ι) (y : b.support → S) :
    b.corootEval S (P.weylGroupToPerm w⁻¹ j) y =
      b.corootEval S j ((W.map (Int.castRingHom S)) *ᵥ y) := by
  have hint (i : b.support) :
      P.pairingIn ℤ (i : ι) (P.weylGroupToPerm w⁻¹ j) =
        ∑ l : b.support, W l i * P.pairingIn ℤ (l : ι) j := by
    apply FaithfulSMul.algebraMap_injective ℤ R
    rw [P.algebraMap_pairingIn ℤ, ← root_coroot'_eq_pairing,
      ← P.coroot'_weylGroupToPerm_smul w (P.weylGroupToPerm w⁻¹ j) (P.root i),
      ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply,
      actsBy_iff.mp hW i, map_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_zsmul, zsmul_eq_mul, root_coroot'_eq_pairing, map_mul, P.algebraMap_pairingIn ℤ,
      eq_intCast]
  simp only [corootEval_apply, mulVec, dotProduct, map_apply, Int.coe_castRingHom]
  simp_rw [hint, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

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
    refine P.ne_zero' j ?_
    rw [hcor]
    exact Finset.sum_eq_zero fun k hk ↦ by simp [h0 ⟨k, hk⟩]
  have hint (i : b.support) :
      P.pairingIn ℤ (i : ι) j = ∑ k : b.support, (f k : ℤ) * P.pairingIn ℤ (i : ι) (k : ι) := by
    apply FaithfulSMul.algebraMap_injective ℤ R
    rw [P.algebraMap_pairingIn ℤ, ← root'_coroot_eq_pairing, hcor, map_sum, map_sum,
      ← Finset.sum_coe_sort b.support]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_nsmul, nsmul_eq_mul, map_mul, map_natCast, root'_coroot_eq_pairing,
      P.algebraMap_pairingIn ℤ]
  refine ⟨fun k ↦ f k, hne, fun S _ y ↦ ?_⟩
  simp only [corootEval_apply, Finset.mul_sum]
  simp_rw [hint, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring

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
  have h := b.corootEval_pos_of_mem_posRoots hy hpos
  rw [b.corootEval_reflectionPerm_self] at h
  linarith

/-- At a coordinate vector `y : b.support → ℝ` where every simple coroot is positive, positivity of
`b.corootEval ℝ j y` characterizes the positive roots. -/
theorem corootEval_pos_iff_mem_posRoots [Finite ι] [CharZero R] [IsDomain R] [P.IsReduced]
    {y : b.support → ℝ} (hy : ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) y) (j : ι) :
    0 < b.corootEval ℝ j y ↔ j ∈ posRoots P b := by
  refine ⟨fun h ↦ ?_, b.corootEval_pos_of_mem_posRoots hy⟩
  by_contra hneg
  rw [not_mem_posRoots_iff_mem_negRoots] at hneg
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

/-! ### Irreducibility of `(2 : ℝ) • 1 - Aᵀ` and orthogonal reflection products -/

section MatrixPreparation

/-- Convert a walk in `diagramGraph A` into a quiver path of the same length for a real matrix `B`
that is strictly positive on every edge of `diagramGraph A`. -/
private noncomputable def walkToQuiverPath {κ : Type*} {A : Matrix κ κ ℤ} {B : Matrix κ κ ℝ}
    (hB : ∀ {i j : κ}, (diagramGraph A).Adj i j → 0 < B i j) :
    let _ : Quiver κ := B.toQuiver
    ∀ {i j : κ} (w : (diagramGraph A).Walk i j),
      {p : Quiver.Path i j // p.length = w.length} := by
  intro _ i j w
  induction w with
  | nil => exact ⟨Quiver.Path.nil, rfl⟩
  | @cons u v _ hadj _ ih =>
    exact ⟨(Quiver.Hom.toPath (PLift.up (hB hadj))).comp ih.1, by
      rw [Quiver.Path.length_comp, Quiver.Path.length_toPath, ih.2]
      exact Nat.add_comm 1 _⟩

/-- When the Dynkin diagram of a base `b` of rank at least two is preconnected, the nonnegative
real matrix `(2 : ℝ) • 1 - Aᵀ` is irreducible. -/
theorem isIrreducible_two_smul_one_sub_transpose_cartanMatrix_of_preconnected
    {ι R M N : Type*} [DecidableEq ι] [CommRing R] [CharZero R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]
    (b : P.Base) [Nontrivial b.support] (hconn : (diagramGraph b.cartanMatrix).Preconnected) :
    ((2 : ℝ) • (1 : Matrix b.support b.support ℝ) -
      (b.cartanMatrixᵀ).map (Int.castRingHom ℝ)).IsIrreducible := by
  set B : Matrix b.support b.support ℝ :=
    (2 : ℝ) • 1 - (b.cartanMatrixᵀ).map (Int.castRingHom ℝ)
  have hnonneg (i j : b.support) : 0 ≤ B i j := by
    rcases eq_or_ne i j with rfl | hij
    · simp [B]
    · simpa [B, hij] using b.cartanMatrix_le_zero_of_ne j i hij.symm
  have hadj_pos {i j : b.support} (h : (diagramGraph b.cartanMatrix).Adj i j) : 0 < B i j := by
    rw [diagramGraph_adj] at h
    simpa [B, h.1] using lt_of_le_of_ne (b.cartanMatrix_le_zero_of_ne j i h.1.symm) h.2.2
  refine ⟨hnonneg, fun i j ↦ ?_⟩
  let _ : Quiver b.support := B.toQuiver
  rcases eq_or_ne i j with rfl | hij
  · obtain ⟨k, hki⟩ := exists_ne i
    obtain ⟨w⟩ := hconn i k
    have hw : 0 < w.length := Nat.pos_of_ne_zero fun h0 ↦ hki.symm (w.eq_of_length_eq_zero h0)
    obtain ⟨p, hp⟩ := walkToQuiverPath hadj_pos (w.append w.reverse)
    exact ⟨p, by simp [hp]; omega⟩
  · obtain ⟨w⟩ := hconn i j
    obtain ⟨p, hp⟩ := walkToQuiverPath hadj_pos w
    exact ⟨p, hp ▸ Nat.pos_of_ne_zero fun h0 ↦ hij (w.eq_of_length_eq_zero h0)⟩

/-- **For an irreducible reduced crystallographic root pairing of rank at least two, the nonnegative
real matrix `(2 : ℝ) • 1 - Aᵀ` is irreducible.** -/
theorem isIrreducible_two_smul_one_sub_transpose_cartanMatrix {ι R M N : Type*} [DecidableEq ι]
    [CommRing R] [CharZero R] [IsDomain R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] (b : P.Base) [Nontrivial b.support] :
    ((2 : ℝ) • (1 : Matrix b.support b.support ℝ) -
      (b.cartanMatrixᵀ).map (Int.castRingHom ℝ)).IsIrreducible :=
  b.isIrreducible_two_smul_one_sub_transpose_cartanMatrix_of_preconnected
    (preconnected_diagramGraph_cartanMatrix b)

/-- Product of reflection matrices along a duplicate-free list of pairwise orthogonal indices:
each letter `p ∈ l` subtracts `A j p` in row `p` without interfering with the other letters. -/
private theorem prod_map_reflMatrix_of_orthogonal {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) {l : List κ} (hl : l.Nodup)
    (horth : ∀ p ∈ l, ∀ q ∈ l, p ≠ q → A p q = 0) (k j : κ) :
    ((l.map (reflMatrix A)).prod) k j =
      (if k = j then 1 else 0) - (if k ∈ l then A j k else 0) := by
  induction l generalizing k j with
  | nil => simp [Matrix.one_apply]
  | cons p l ih =>
    rw [List.nodup_cons] at hl
    have horth' : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → A a b = 0 :=
      fun a ha b hb ↦ horth a (List.mem_cons_of_mem p ha) b (List.mem_cons_of_mem p hb)
    rw [List.map_cons, List.prod_cons, Matrix.mul_apply]
    simp only [reflMatrix_apply, ih hl.2 horth']
    have hsum : ∑ m : κ, ((if k = m then 1 else 0) - (if k = p then A m p else 0)) *
          ((if m = j then 1 else 0) - (if m ∈ l then A j m else 0)) =
        ((if k = j then 1 else 0) - (if k ∈ l then A j k else 0)) -
          if k = p then ∑ m : κ, A m p *
            ((if m = j then 1 else 0) - (if m ∈ l then A j m else 0)) else 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      congr 1
      by_cases hkp : k = p <;> simp [hkp]
    rw [hsum]
    rcases eq_or_ne k p with rfl | hkp
    · simp only [↓reduceIte, hl.1, sub_zero, List.mem_cons, true_or]
      congr 1
      simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have hzero : ∑ m : κ, (if m ∈ l then A m k * A j m else 0) = 0 := by
        refine Finset.sum_eq_zero fun m _ ↦ ?_
        split_ifs with hm
        · have hmk : m ≠ k := fun h ↦ hl.1 (h ▸ hm)
          rw [horth m (List.mem_cons_of_mem k hm) k List.mem_cons_self hmk, zero_mul]
        · rfl
      rw [hzero, sub_zero]
    · simp [hkp, List.mem_cons]

end MatrixPreparation

/-! ### Matrices of colour-class involutions and the bipartite Coxeter element -/

section BipartiteMatrices

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]

/-- Integer matrix of the colour-class involution `colorClassProd col s` in the simple-root
basis. -/
noncomputable def colorClassMatrix (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) (s : Bool) :
    Matrix b.support b.support ℤ :=
  (((Finset.univ.filter fun i : b.support ↦ col i = s).toList).map
    (reflMatrix b.cartanMatrix)).prod

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
    by_contra hne
    have hadj : (coxeterMatrixOfBase P b).graph.Adj p q := by
      rw [graph_coxeterMatrixOfBase P b, diagramGraph_adj]
      exact ⟨hpq, hne, fun hqp ↦ hne (b.cartanMatrix_apply_eq_zero_iff_symm.mpr hqp)⟩
    exact col.valid hadj (hp.2.trans hq.2.symm)
  simpa [colorClassMatrix, fs] using
    prod_map_reflMatrix_of_orthogonal b.cartanMatrix (Finset.nodup_toList fs) horth k j

/-- `b.colorClassMatrix col s` is an involution (`M * M = 1`). -/
theorem colorClassMatrix_mul_self (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) (s : Bool) :
    b.colorClassMatrix col s * b.colorClassMatrix col s = 1 := by
  ext k j
  simp only [Matrix.mul_apply, colorClassMatrix_apply, Matrix.one_apply]
  by_cases hck : col k = s
  · have hterm (x : b.support) :
        ((if k = x then 1 else 0) - b.cartanMatrix x k) *
          ((if x = j then 1 else 0) - if col x = s then b.cartanMatrix j x else 0) =
        (if k = x then (if x = j then 1 else 0) - (if col x = s then b.cartanMatrix j x else 0)
          else 0) -
        (if x = j then b.cartanMatrix x k else 0) +
        (if col x = s then b.cartanMatrix x k * b.cartanMatrix j x else 0) := by
      split_ifs <;> ring
    have hsum : ∑ x : b.support,
        (if col x = s then b.cartanMatrix x k * b.cartanMatrix j x else 0) =
        2 * b.cartanMatrix j k := by
      rw [Finset.sum_eq_single k]
      · simp [hck]
      · intro x _ hxk
        split_ifs with hcx
        · have hadj : ¬ (coxeterMatrixOfBase P b).graph.Adj x k :=
            fun h ↦ col.valid h (hcx.trans hck.symm)
          rw [graph_coxeterMatrixOfBase P b, diagramGraph_adj, not_and_or, not_and_or] at hadj
          rcases hadj with h | h | h
          · exact (h hxk).elim
          · push Not at h; simp [h]
          · push Not at h; simp [b.cartanMatrix_apply_eq_zero_iff_symm.mpr h]
        · rfl
      · simp
    simp only [hck, ↓reduceIte, hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, hsum]
    ring
  · simp [hck]

/-- Integer matrix of the bipartite Coxeter element in the simple-root basis. -/
noncomputable def bipartiteCoxeterMatrix (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) : Matrix b.support b.support ℤ :=
  b.colorClassMatrix col true * b.colorClassMatrix col false

variable [P.IsReduced]

/-- The colour-class involution `colorClassProd col s` acts on the simple roots by
`b.colorClassMatrix col s`. -/
theorem actsBy_colorClassProd (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) (s : Bool) :
    b.ActsBy ((weylCoxeterSystem P b).colorClassProd col s) (b.colorClassMatrix col s) := by
  let fs := Finset.univ.filter fun i : b.support ↦ col i = s
  have hw : (weylCoxeterSystem P b).colorClassProd col s = wordProd P b fs.toList := by
    rw [← (weylCoxeterSystem P b).wordProd_eq_colorClassProd col (Finset.nodup_toList fs)
      (by simp [fs]), weylCoxeterSystem_wordProd]
  rw [hw]
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

/-! ### Coleman's Coxeter plane and the exact rotation angle `2π / h` -/

section CoxeterPlane

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- First arithmetic step for the Coxeter plane angle: if `h θ = m π` (`0 < m`) and no smaller
positive integer `h' < h` makes `h' θ` an integer multiple of `π`, then `m.natAbs` and `h` are
coprime. -/
private theorem coprime_of_mul_eq_mul_pi {h : ℕ} (hh : 2 ≤ h) {θ : ℝ} {m : ℤ}
    (hmθ : (h : ℝ) * θ = (m : ℝ) * Real.pi)
    (hmin : ∀ h' : ℕ, 0 < h' → h' < h → ∀ m' : ℤ, (h' : ℝ) * θ ≠ (m' : ℝ) * Real.pi) :
    m.natAbs.Coprime h := by
  rw [Nat.Coprime]
  by_contra hne1
  set d := m.natAbs.gcd h
  have hd_dvd_h : d ∣ h := Nat.gcd_dvd_right _ _
  have hd_dvd_m : (d : ℤ) ∣ m := Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_right _ (by omega)
  have hd_gt : 1 < d := by omega
  have hh'_pos : 0 < h / d := Nat.div_pos (Nat.le_of_dvd (by omega) hd_dvd_h) hd_pos
  have hh'_lt : h / d < h := Nat.div_lt_self (by omega) hd_gt
  have hd_real : (d : ℝ) ≠ 0 := by exact_mod_cast hd_pos.ne'
  refine hmin (h / d) hh'_pos hh'_lt (m / (d : ℤ)) (mul_left_cancel₀ hd_real ?_)
  have h1 : (d : ℝ) * ((h / d : ℕ) : ℝ) = (h : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' hd_dvd_h
  have h2 : (d : ℝ) * ((m / (d : ℤ) : ℤ) : ℝ) = (m : ℝ) := by
    exact_mod_cast Int.mul_ediv_cancel' hd_dvd_m
  calc (d : ℝ) * (((h / d : ℕ) : ℝ) * θ) = ((d : ℝ) * ((h / d : ℕ) : ℝ)) * θ := by ring
    _ = (m : ℝ) * Real.pi := by rw [h1, hmθ]
    _ = (d : ℝ) * (((m / (d : ℤ) : ℤ) : ℝ) * Real.pi) := by rw [← h2]; ring

/-- Bézout arithmetic step identifying the half-angle `θ` of the bipartite Coxeter plane with
`π / h`: if `cos (2 h θ) = 1` (`0 < θ`), no smaller positive power `h' < h` makes `h' θ` a
multiple of `π`, and no combination `2 n θ + q π` falls strictly inside `(0, θ)`, then
`θ = π / h`. -/
private theorem eq_pi_div_of_cos_two_mul_eq_one {h : ℕ} (hh : 2 ≤ h) {θ : ℝ}
    (hθpos : 0 < θ) (hcos : Real.cos (2 * (h : ℝ) * θ) = 1)
    (hmin : ∀ h' : ℕ, 0 < h' → h' < h → ∀ m' : ℤ, (h' : ℝ) * θ ≠ (m' : ℝ) * Real.pi)
    (hwall : ∀ (n : ℕ) (q : ℤ),
      ¬ (0 < 2 * (n : ℝ) * θ + (q : ℝ) * Real.pi ∧ 2 * (n : ℝ) * θ + (q : ℝ) * Real.pi < θ)) :
    θ = Real.pi / (h : ℝ) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast (by omega : 0 < h)
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff (2 * (h : ℝ) * θ)).mp hcos
  have hmθ : (h : ℝ) * θ = (m : ℝ) * Real.pi := by linarith
  have hmpos : 0 < m := Int.cast_pos.mp
    (pos_of_mul_pos_left (hmθ ▸ mul_pos hhpos hθpos) hpi.le)
  have hcop : m.natAbs.Coprime h := coprime_of_mul_eq_mul_pi hh hmθ hmin
  suffices m = 1 by rw [this, Int.cast_one, one_mul] at hmθ; rw [eq_div_iff hhpos.ne']; linarith
  by_contra hm1
  set g : ℕ := (2 * m).gcd (h : ℤ)
  have hg_dvd_h : g ∣ h := by
    simpa [g] using Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_right (2 * m) (h : ℤ))
  have hg_dvd_2 : g ∣ 2 := by
    have hgm : g ∣ 2 * m.natAbs := by
      have : (g : ℤ) ∣ (2 * m.natAbs : ℤ) := by
        simpa [Int.natAbs_of_nonneg hmpos.le] using Int.gcd_dvd_left (2 * m) (h : ℤ)
      exact_mod_cast this
    exact (hcop.coprime_dvd_right hg_dvd_h).symm.dvd_of_dvd_mul_right hgm
  have hg_pos : 0 < g := Int.gcd_pos_of_ne_zero_right _ (by omega)
  have hg_lt_m : (g : ℤ) < m := by
    rcases eq_or_lt_of_le (Nat.le_of_dvd (by norm_num) hg_dvd_2) with hg2 | hlt
    · have hne2 : m ≠ 2 := fun hm2 ↦ by
        have : 2 ∣ 1 :=
          (by simpa [hm2] using hcop : (2 : ℕ).Coprime h) ▸
            Nat.dvd_gcd (dvd_refl 2) (hg2 ▸ hg_dvd_h)
        omega
      omega
    · omega
  set a := Int.gcdA (2 * m) (h : ℤ)
  set n : ℕ := (a % (h : ℤ)).toNat
  set q : ℤ := Int.gcdB (2 * m) (h : ℤ) + 2 * m * (a / (h : ℤ))
  have hcomb : 2 * m * (n : ℤ) + (h : ℤ) * q = (g : ℤ) := by
    have hbez := Int.gcd_eq_gcd_ab (2 * m) (h : ℤ)
    have hdiv := Int.mul_ediv_add_emod a (h : ℤ)
    have hn_eq : (n : ℤ) = a % (h : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg a (by omega))
    linear_combination -hbez + 2 * m * hdiv + 2 * m * hn_eq
  have hcomb_real : (h : ℝ) * (2 * (n : ℝ) * θ + (q : ℝ) * Real.pi) = (g : ℝ) * Real.pi := by
    have hcr : (2 : ℝ) * (m : ℝ) * (n : ℝ) + (h : ℝ) * (q : ℝ) = (g : ℝ) := by exact_mod_cast hcomb
    calc (h : ℝ) * (2 * (n : ℝ) * θ + (q : ℝ) * Real.pi)
        = 2 * (n : ℝ) * ((h : ℝ) * θ) + (h : ℝ) * (q : ℝ) * Real.pi := by ring
      _ = (2 * (m : ℝ) * (n : ℝ) + (h : ℝ) * (q : ℝ)) * Real.pi := by rw [hmθ]; ring
      _ = (g : ℝ) * Real.pi := by rw [hcr]
  refine hwall n q ⟨pos_of_mul_pos_right ?_ hhpos.le, lt_of_mul_lt_mul_left ?_ hhpos.le⟩
  · rw [hcomb_real]; exact mul_pos (by exact_mod_cast hg_pos) hpi
  · rw [hcomb_real, hmθ]; exact mul_lt_mul_of_pos_right (by exact_mod_cast hg_lt_m) hpi

omit [CharZero R] [IsDomain R] [Finite ι] [P.IsReduced] in
/-- **Perron–Frobenius eigenvalue bound `< 2`** for `(2 : ℝ) • 1 - Aᵀ` of a finite-type Cartan
matrix: positive definiteness of the symmetrized Cartan matrix forces any positive eigenvector `x`
of `(2 : ℝ) • 1 - Aᵀ` to have eigenvalue `< 2`. -/
private theorem perronEigenvalue_lt_two (b : P.Base) [Nonempty b.support]
    (hft : IsFiniteType b.cartanMatrix) {μ : ℝ} {x : b.support → ℝ} (hx : ∀ i, 0 < x i)
    (hBx : ((2 : ℝ) • (1 : Matrix b.support b.support ℝ) -
      (b.cartanMatrixᵀ).map (Int.castRingHom ℝ)) *ᵥ x = μ • x) : μ < 2 := by
  obtain ⟨d, hd, hpd_rat⟩ := hft.exists_symmetrizer
  set S_rat : Matrix b.support b.support ℚ := Matrix.of fun i j ↦ d i * (b.cartanMatrix i j : ℚ)
  have hpd : (S_rat.map (Rat.cast : ℚ → ℝ)).PosDef :=
    TauCeti.Matrix.posDef_map_ratCast_iff.mpr hpd_rat
  have hd_pos (i : b.support) : 0 < (d i : ℝ) := by exact_mod_cast hd i
  let y : b.support → ℝ := fun i ↦ x i / (d i : ℝ)
  have hy_pos (i : b.support) : 0 < y i := div_pos (hx i) (hd_pos i)
  obtain ⟨i₀⟩ := ‹Nonempty b.support›
  have hy_ne : y ≠ 0 := fun h ↦ (hy_pos i₀).ne' (congrFun h i₀)
  have hAx : ((b.cartanMatrixᵀ).map (Int.castRingHom ℝ)) *ᵥ x = (2 - μ) • x := by
    rw [sub_mulVec, smul_mulVec, one_mulVec] at hBx
    ext i
    have hi := congrFun hBx i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul] at hi ⊢
    linarith
  have hM : (S_rat.map (Rat.cast : ℚ → ℝ)) *ᵥ y = (2 - μ) • x := by
    rw [← hAx]
    ext i
    simp only [mulVec, dotProduct, Matrix.map_apply, Int.coe_castRingHom, transpose_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hsym := congrArg (Rat.cast : ℚ → ℝ) (hpd_rat.isHermitian.apply j i)
    simp only [S_rat, Matrix.of_apply, star_trivial, Rat.cast_mul, Rat.cast_intCast] at hsym ⊢
    rw [hsym]
    calc (d j : ℝ) * (b.cartanMatrix j i : ℝ) * y j
        = (b.cartanMatrix j i : ℝ) * ((d j : ℝ) * (x j / (d j : ℝ))) := by simp only [y]; ring
      _ = (b.cartanMatrix j i : ℝ) * x j := by rw [mul_div_cancel₀ _ (hd_pos j).ne']
  have hq : 0 < star y ⬝ᵥ ((S_rat.map (Rat.cast : ℚ → ℝ)) *ᵥ y) := hpd.dotProduct_mulVec_pos hy_ne
  rw [hM, star_trivial, dotProduct_smul, smul_eq_mul] at hq
  have hyx : 0 < y ⬝ᵥ x :=
    Finset.sum_pos (fun i _ ↦ mul_pos (hy_pos i) (hx i)) Finset.univ_nonempty
  linarith [pos_of_mul_pos_left hq hyx.le]

omit [DecidableEq ι] [P.IsReduced] in
/-- Restriction of a vector `x : b.support → ℝ` to a single colour class `s : Bool` of `col`. -/
private def colorVec (b : P.Base) (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    (x : b.support → ℝ) (s : Bool) (i : b.support) : ℝ :=
  if col i = s then x i else 0

omit [DecidableEq ι] [P.IsReduced] in
@[simp]
private theorem colorVec_apply (b : P.Base) (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    (x : b.support → ℝ) (s : Bool) (i : b.support) :
    b.colorVec col x s i = if col i = s then x i else 0 :=
  rfl

omit [DecidableEq ι] [P.IsReduced] in
/-- For a preconnected Dynkin diagram on at least two vertices, every two-colouring uses both
colours. -/
private theorem exists_mem_colorClass (b : P.Base) [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) (s : Bool) :
    ∃ i : b.support, col i = s := by
  obtain ⟨i₀, j₀, hij⟩ := exists_pair_ne b.support
  by_cases hi : col i₀ = s
  · exact ⟨i₀, hi⟩
  · obtain ⟨w⟩ := hconn i₀ j₀
    cases w with
    | nil => exact (hij rfl).elim
    | @cons _ p _ hadj _ =>
      have hadj' : (coxeterMatrixOfBase P b).graph.Adj i₀ p := by
        rwa [graph_coxeterMatrixOfBase P b]
      have hne : col i₀ ≠ col p := col.valid hadj'
      exact ⟨p, by cases hc1 : col i₀ <;> cases hc2 : col p <;> cases s <;> simp_all⟩

omit [P.IsReduced] in
/-- Simple coroot evaluation on the colour-split pieces of an eigenvector `x` of
`(2 : ℝ) • 1 - Aᵀ`: at a vertex `k`, the piece of `k`'s own colour gives `2 * x k`, while the
opposite colour piece gives `-μ * x k`. -/
private theorem corootEval_colorVec (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) {μ : ℝ} {x : b.support → ℝ}
    (hBx : ((2 : ℝ) • (1 : Matrix b.support b.support ℝ) -
      (b.cartanMatrixᵀ).map (Int.castRingHom ℝ)) *ᵥ x = μ • x) (k : b.support) :
    b.corootEval ℝ (k : ι) (b.colorVec col x (col k)) = 2 * x k ∧
      b.corootEval ℝ (k : ι) (b.colorVec col x (!(col k))) = -μ * x k := by
  have hsame : b.corootEval ℝ (k : ι) (b.colorVec col x (col k)) = 2 * x k := by
    rw [corootEval_coe_support, Finset.sum_eq_single k]
    · simp
    · intro i _ hik
      simp only [colorVec_apply]
      split_ifs with hci
      · have hadj : ¬ (coxeterMatrixOfBase P b).graph.Adj i k := fun h ↦ col.valid h hci
        rw [graph_coxeterMatrixOfBase P b, diagramGraph_adj, not_and_or, not_and_or] at hadj
        rcases hadj with h | h | h
        · exact (h hik).elim
        · push Not at h; simp [h]
        · push Not at h; simp [b.cartanMatrix_apply_eq_zero_iff_symm.mpr h]
      · simp
    · simp
  refine ⟨hsame, ?_⟩
  have hkB := congrFun hBx k
  rw [sub_mulVec, smul_mulVec, one_mulVec] at hkB
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, transpose_apply,
    map_apply, Int.coe_castRingHom] at hkB
  have htot : ∑ i : b.support, (b.cartanMatrix i k : ℝ) * x i =
      b.corootEval ℝ (k : ι) (b.colorVec col x (col k)) +
        b.corootEval ℝ (k : ι) (b.colorVec col x (!(col k))) := by
    simp only [corootEval_coe_support, ← Finset.sum_add_distrib, colorVec_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    cases col i <;> cases col k <;> simp
  linarith

omit [P.IsReduced] in
/-- Action of `b.colorClassMatrix col s` over `ℝ` on the colour-split pieces of a Perron–Frobenius
eigenvector `x` of `(2 : ℝ) • 1 - Aᵀ`: it negates its own colour vector and shears the opposite
colour vector by `μ`. -/
private theorem colorClassMatrix_mulVec_colorVec (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) {μ : ℝ} {x : b.support → ℝ}
    (hBx : ((2 : ℝ) • (1 : Matrix b.support b.support ℝ) -
      (b.cartanMatrixᵀ).map (Int.castRingHom ℝ)) *ᵥ x = μ • x) (s : Bool) :
    let C := (b.colorClassMatrix col s).map (Int.castRingHom ℝ)
    C *ᵥ b.colorVec col x s = -b.colorVec col x s ∧
      C *ᵥ b.colorVec col x (!s) = b.colorVec col x (!s) + μ • b.colorVec col x s := by
  intro C
  have hrow (k : b.support) (t : Bool) :
      (C *ᵥ b.colorVec col x t) k =
        b.colorVec col x t k -
          if col k = s then b.corootEval ℝ (k : ι) (b.colorVec col x t) else 0 := by
    simp only [C, mulVec, dotProduct, map_apply, Int.coe_castRingHom, colorClassMatrix_apply,
      Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, sub_mul, Finset.sum_sub_distrib,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      corootEval_coe_support]
    congr 1
    by_cases hck : col k = s <;> simp [hck]
  constructor
  · ext k
    rw [hrow k s, Pi.neg_apply]
    obtain ⟨hsame, -⟩ := corootEval_colorVec b col hBx k
    by_cases hck : col k = s
    · subst hck
      simp only [↓reduceIte, hsame, colorVec_apply]
      ring
    · simp [hck]
  · ext k
    rw [hrow k (!s), Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨-, hopp⟩ := corootEval_colorVec b col hBx k
    by_cases hck : col k = s
    · subst hck
      have hne : col k ≠ !(col k) := by simp
      simp only [↓reduceIte, hopp, colorVec_apply, hne]
      ring
    · simp [hck]

omit [DecidableEq ι] [P.IsReduced] in
/-- Linear independence of the adapted Coxeter-plane basis `(e₁, e₂)` built from a positive vector
`x` when both colour classes are nonempty and `sin θ > 0`. -/
private theorem coxeterPlane_linearIndependent (b : P.Base) [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {θ : ℝ} {x : b.support → ℝ} (hx : ∀ i, 0 < x i) (hsinθ : 0 < Real.sin θ) :
    LinearIndependent ℝ
      ![Real.cos θ • b.colorVec col x true + b.colorVec col x false,
        Real.sin θ • b.colorVec col x true] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg; rw [Fin.sum_univ_two] at hg
  obtain ⟨i_t, hit⟩ := exists_mem_colorClass b hconn col true
  obtain ⟨i_f, hif⟩ := exists_mem_colorClass b hconn col false
  have hf0 : g 0 = 0 := by
    have h := congrFun hg i_f
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      colorVec_apply, hif, Bool.false_eq_true, ↓reduceIte, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, mul_zero, zero_add, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (hx i_f).ne'
  have ht0 : g 1 = 0 := by
    have h := congrFun hg i_t; rw [hf0, zero_smul, zero_add] at h
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, colorVec_apply, hit,
      ↓reduceIte, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_right (mul_ne_zero hsinθ.ne' (hx i_t).ne')
  intro k; fin_cases k <;> assumption

omit [P.IsReduced] in
/-- Rotation action of `W` and `Winv ^ k` on the adapted plane basis `(e₁, e₂)` associated to an
eigenvector `x` of `(2 : ℝ) • 1 - Aᵀ` with eigenvalue `μ = 2 cos θ`. -/
private theorem coxeterPlane_rotation (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {μ θ : ℝ} {x : b.support → ℝ} (hμ_eq : μ = 2 * Real.cos θ)
    (hBx : ((2 : ℝ) • (1 : Matrix b.support b.support ℝ) -
      (b.cartanMatrixᵀ).map (Int.castRingHom ℝ)) *ᵥ x = μ • x) :
    let e₁ : b.support → ℝ := Real.cos θ • b.colorVec col x true + b.colorVec col x false
    let e₂ : b.support → ℝ := Real.sin θ • b.colorVec col x true
    let W := (b.bipartiteCoxeterMatrix col).map (Int.castRingHom ℝ)
    let Winv := (b.colorClassMatrix col false * b.colorClassMatrix col true).map
      (Int.castRingHom ℝ)
    W *ᵥ e₁ = Real.cos (2 * θ) • e₁ - Real.sin (2 * θ) • e₂ ∧
      W *ᵥ e₂ = Real.sin (2 * θ) • e₁ + Real.cos (2 * θ) • e₂ ∧
      ∀ (k : ℕ) (φ : ℝ),
        (Winv ^ k) *ᵥ (Real.cos φ • e₁ + Real.sin φ • e₂) =
          Real.cos (φ + 2 * (k : ℝ) * θ) • e₁ + Real.sin (φ + 2 * (k : ℝ) * θ) • e₂ := by
  intro e₁ e₂ W Winv
  set C₁ := (b.colorClassMatrix col true).map (Int.castRingHom ℝ)
  set C₂ := (b.colorClassMatrix col false).map (Int.castRingHom ℝ)
  obtain ⟨hC₁t, hC₁f⟩ := colorClassMatrix_mulVec_colorVec b col hBx true
  obtain ⟨hC₂f, hC₂t⟩ := colorClassMatrix_mulVec_colorVec b col hBx false
  simp only [Bool.not_true] at hC₁f; simp only [Bool.not_false] at hC₂t
  have hsin2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith [Real.cos_sq_add_sin_sq θ]
  have hC₁_e₁ : C₁ *ᵥ e₁ = e₁ := by
    simp only [e₁, mulVec_add, mulVec_smul, C₁]; rw [hC₁t, hC₁f, hμ_eq]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring
  have hC₁_e₂ : C₁ *ᵥ e₂ = -e₂ := by simp only [e₂, mulVec_smul, C₁]; rw [hC₁t, smul_neg]
  have hC₂_e₁ : C₂ *ᵥ e₁ = Real.cos (2 * θ) • e₁ + Real.sin (2 * θ) • e₂ := by
    simp only [e₁, e₂, mulVec_add, mulVec_smul, C₂]; rw [hC₂t, hC₂f, hμ_eq, Real.cos_two_mul,
      Real.sin_two_mul]; ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination -2 * (b.colorVec col x true i) * Real.cos θ * hsin2
  have hC₂_e₂ : C₂ *ᵥ e₂ = Real.sin (2 * θ) • e₁ - Real.cos (2 * θ) • e₂ := by
    simp only [e₁, e₂, mulVec_smul, C₂]; rw [hC₂t, hμ_eq, Real.cos_two_mul, Real.sin_two_mul]
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hW_mul : W = C₁ * C₂ := by simp only [W, bipartiteCoxeterMatrix, Matrix.map_mul, C₁, C₂]
  have hWinv_mul : Winv = C₂ * C₁ := by simp only [Winv, Matrix.map_mul, C₁, C₂]
  refine ⟨by rw [hW_mul, ← mulVec_mulVec, hC₂_e₁, mulVec_add,
      mulVec_smul, mulVec_smul, hC₁_e₁, hC₁_e₂, smul_neg, sub_eq_add_neg],
    by rw [hW_mul, ← mulVec_mulVec, hC₂_e₂, mulVec_sub,
      mulVec_smul, mulVec_smul, hC₁_e₁, hC₁_e₂, smul_neg, sub_neg_eq_add],
    fun k φ ↦ ?_⟩
  have hstep (ψ : ℝ) :
      Real.cos ψ • (Real.cos (2 * θ) • e₁ + Real.sin (2 * θ) • e₂) -
        Real.sin ψ • (Real.sin (2 * θ) • e₁ - Real.cos (2 * θ) • e₂) =
      Real.cos (ψ + 2 * θ) • e₁ + Real.sin (ψ + 2 * θ) • e₂ := by
    rw [Real.cos_add, Real.sin_add]
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  induction k generalizing φ with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, hWinv_mul,
      ← mulVec_mulVec, mulVec_add, mulVec_smul, mulVec_smul, hC₁_e₁, hC₁_e₂, smul_neg,
      ← sub_eq_add_neg, mulVec_sub, mulVec_smul, mulVec_smul, hC₂_e₁, hC₂_e₂, hstep, Nat.cast_succ,
      show φ + 2 * (k : ℝ) * θ + 2 * θ = φ + 2 * ((k : ℝ) + 1) * θ by ring]

omit [P.IsReduced] in
/-- Trigonometric formula for simple coroot evaluations along `cos φ • e₁ + sin φ • e₂`. -/
private theorem coxeterPlane_corootEval (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {μ θ : ℝ} {x : b.support → ℝ} (hμ_eq : μ = 2 * Real.cos θ)
    (hBx : ((2 : ℝ) • (1 : Matrix b.support b.support ℝ) -
      (b.cartanMatrixᵀ).map (Int.castRingHom ℝ)) *ᵥ x = μ • x) (k : b.support) (φ : ℝ) :
    let e₁ : b.support → ℝ := Real.cos θ • b.colorVec col x true + b.colorVec col x false
    let e₂ : b.support → ℝ := Real.sin θ • b.colorVec col x true
    b.corootEval ℝ (k : ι) (Real.cos φ • e₁ + Real.sin φ • e₂) =
      2 * Real.sin θ * x k * if col k = true then Real.sin φ else Real.sin (θ - φ) := by
  intro e₁ e₂
  have hsin2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith [Real.cos_sq_add_sin_sq θ]
  obtain ⟨hs, ho⟩ := corootEval_colorVec b col hBx k
  cases hck : col k
  · simp only [hck, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hs ho ⊢
    simp only [e₁, e₂, map_add, map_smul, smul_eq_mul, hs, ho, hμ_eq, Real.sin_sub]
    linear_combination -2 * x k * Real.cos φ * hsin2
  · simp only [hck, ↓reduceIte, Bool.not_true] at hs ho ⊢
    simp only [e₁, e₂, map_add, map_smul, smul_eq_mul, hs, ho, hμ_eq]; ring

/-- If `M ^ h = 1` acts on linearly independent `(e₁, e₂)` by `M ^ k *ᵥ e₁ = cos (2 k θ) • e₁ +
sin (2 k θ) • e₂`, then `cos (2 h θ) = 1`. -/
private lemma cos_two_mul_eq_one_of_pow_eq_one {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Matrix κ κ ℝ} {h : ℕ} {θ : ℝ} {e₁ e₂ : κ → ℝ}
    (hli : LinearIndependent ℝ ![e₁, e₂]) (hMh : M ^ h = 1)
    (hrot : (M ^ h) *ᵥ (Real.cos 0 • e₁ + Real.sin 0 • e₂) =
      Real.cos (0 + 2 * (h : ℝ) * θ) • e₁ + Real.sin (0 + 2 * (h : ℝ) * θ) • e₂) :
    Real.cos (2 * (h : ℝ) * θ) = 1 := by
  rw [hMh, one_mulVec, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero, zero_add]
    at hrot
  have hrel : (Real.cos (2 * (h : ℝ) * θ) - 1) • e₁ + Real.sin (2 * (h : ℝ) * θ) • e₂ = 0 := by
    ext i; have hi := congrFun hrot i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢; linarith
  have h0 := Fintype.linearIndependent_iff.mp hli
    ![Real.cos (2 * (h : ℝ) * θ) - 1, Real.sin (2 * (h : ℝ) * θ)]
    (by simpa [Fin.sum_univ_two] using hrel) 0
  simpa only [Matrix.cons_val_zero, sub_eq_zero] using h0

omit [DecidableEq ι] in
/-- Any Weyl-group element whose simple-root matrix fixes a dominant-interior vector `y₀` (`0 <
corootEval ℝ k y₀` for all simple `k`) is trivial. -/
private theorem eq_one_of_actsBy_fix_of_forall_pos (b : P.Base)
    {y₀ : b.support → ℝ} (hy₀ : ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) y₀)
    {g : P.weylGroup} {G : Matrix b.support b.support ℤ} (hG : b.ActsBy g G)
    (hGy₀ : (G.map (Int.castRingHom ℝ)) *ᵥ y₀ = y₀) : g = 1 := by
  have hinv : inversions P b g⁻¹ = ∅ := by
    rw [inversions_eq_empty_iff]; intro j hj
    rw [← b.corootEval_pos_iff_mem_posRoots hy₀,
      b.corootEval_weylGroupToPerm_inv hG ℝ j y₀, hGy₀]
    exact b.corootEval_pos_of_mem_posRoots hy₀ hj
  exact inv_eq_one.mp (eq_one_of_inversions_eq_empty hinv)

/-- At every angle `φ = 2 n θ + q π`, at least one coroot vanishes on `cos φ • e₁ + sin φ • e₂`
(namely the `c ^ n`-translate of any simple root in the `true` colour class). -/
private theorem coxeterPlane_exists_corootEval_zero (b : P.Base) [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {μ θ : ℝ} {x : b.support → ℝ} (hμ_eq : μ = 2 * Real.cos θ)
    (hBx : ((2 : ℝ) • (1 : Matrix b.support b.support ℝ) -
      (b.cartanMatrixᵀ).map (Int.castRingHom ℝ)) *ᵥ x = μ • x) (n : ℕ) (q : ℤ) :
    let e₁ : b.support → ℝ := Real.cos θ • b.colorVec col x true + b.colorVec col x false
    let e₂ : b.support → ℝ := Real.sin θ • b.colorVec col x true
    let φ := 2 * (n : ℝ) * θ + (q : ℝ) * Real.pi
    ∃ j : ι, b.corootEval ℝ j (Real.cos φ • e₁ + Real.sin φ • e₂) = 0 := by
  intro e₁ e₂ φ
  set c := (weylCoxeterSystem P b).bipartiteCoxeterElement col
  set Winv := (b.colorClassMatrix col false * b.colorClassMatrix col true).map (Int.castRingHom ℝ)
  have hWinv_pow : ∀ (k : ℕ) (ψ : ℝ),
      (Winv ^ k) *ᵥ (Real.cos ψ • e₁ + Real.sin ψ • e₂) =
        Real.cos (ψ + 2 * (k : ℝ) * θ) • e₁ + Real.sin (ψ + 2 * (k : ℝ) * θ) • e₂ :=
    (coxeterPlane_rotation b col hμ_eq hBx).2.2
  obtain ⟨i₁, hi₁⟩ := exists_mem_colorClass b hconn col true
  have hp_eq : Real.cos φ • e₁ + Real.sin φ • e₂ =
      ((-1 : ℝ) ^ q) • ((Winv ^ n) *ᵥ (Real.cos 0 • e₁ + Real.sin 0 • e₂)) := by
    rw [hWinv_pow n 0]; ext i
    simp only [φ, zero_add, Real.cos_add_int_mul_pi, Real.sin_add_int_mul_pi,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have heq := b.corootEval_weylGroupToPerm_inv
    ((b.actsBy_bipartiteCoxeterElement_inv col).pow n) ℝ
    (P.weylGroupToPerm (c ^ n)⁻¹ (i₁ : ι)) (Real.cos 0 • e₁ + Real.sin 0 • e₂)
  rw [inv_pow, inv_inv, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Equiv.Perm.one_apply, Matrix.map_pow] at heq
  refine ⟨P.weylGroupToPerm (c ^ n)⁻¹ (i₁ : ι), ?_⟩
  rw [hp_eq, map_smul, ← heq, coxeterPlane_corootEval b col hμ_eq hBx i₁ 0]; simp [hi₁]

/-- Identification of the Perron–Frobenius half-angle `θ` with `π / orderOf c` on the bipartite
Coxeter plane. -/
private theorem coxeterPlane_angle_eq_pi_div_orderOf (b : P.Base) [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {μ θ : ℝ} {x : b.support → ℝ} (hx : ∀ i, 0 < x i)
    (hθpos : 0 < θ) (hθlt : θ < Real.pi / 2) (hμ_eq : μ = 2 * Real.cos θ)
    (hsinθ : 0 < Real.sin θ)
    (hBx : ((2 : ℝ) • (1 : Matrix b.support b.support ℝ) -
      (b.cartanMatrixᵀ).map (Int.castRingHom ℝ)) *ᵥ x = μ • x) :
    θ = Real.pi / (orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement col) : ℝ) := by
  have := P.finite_weylGroup_of_base b
  set c := (weylCoxeterSystem P b).bipartiteCoxeterElement col
  set h := orderOf c
  set e₁ : b.support → ℝ := Real.cos θ • b.colorVec col x true + b.colorVec col x false
  set e₂ : b.support → ℝ := Real.sin θ • b.colorVec col x true
  set Winv := (b.colorClassMatrix col false * b.colorClassMatrix col true).map (Int.castRingHom ℝ)
  have hli : LinearIndependent ℝ ![e₁, e₂] := coxeterPlane_linearIndependent b hconn col hx hsinθ
  have hWinv_pow : ∀ (k : ℕ) (φ : ℝ),
      (Winv ^ k) *ᵥ (Real.cos φ • e₁ + Real.sin φ • e₂) =
        Real.cos (φ + 2 * (k : ℝ) * θ) • e₁ + Real.sin (φ + 2 * (k : ℝ) * θ) • e₂ :=
    (coxeterPlane_rotation b col hμ_eq hBx).2.2
  have hsector {φ : ℝ} (hφ0 : 0 < φ) (hφθ : φ < θ) (k : b.support) :
      0 < b.corootEval ℝ (k : ι) (Real.cos φ • e₁ + Real.sin φ • e₂) := by
    rw [coxeterPlane_corootEval b col hμ_eq hBx k φ]; split_ifs
    · exact mul_pos (mul_pos (mul_pos two_pos hsinθ) (hx k))
        (Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith [Real.pi_pos]))
    · exact mul_pos (mul_pos (mul_pos two_pos hsinθ) (hx k))
        (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hφθ) (by linarith [Real.pi_pos]))
  have hh_ge_two : 2 ≤ h := by
    have hpos : 0 < h := orderOf_pos c
    have hne1 : h ≠ 1 := fun h1 ↦
      (weylCoxeterSystem P b).bipartiteCoxeterElement_ne_one col (orderOf_eq_one_iff.mp h1)
    omega
  have hWinv_h : Winv ^ h = 1 := by
    have hpow := (b.actsBy_bipartiteCoxeterElement_inv col).pow h
    rw [inv_pow, pow_orderOf_eq_one, inv_one] at hpow
    rw [← Matrix.map_pow, hpow.unique b.actsBy_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcos_2hθ : Real.cos (2 * (h : ℝ) * θ) = 1 :=
    cos_two_mul_eq_one_of_pow_eq_one hli hWinv_h (hWinv_pow h 0)
  refine eq_pi_div_of_cos_two_mul_eq_one hh_ge_two hθpos hcos_2hθ
    (fun h' hh'0 hh'lt m' hm' ↦ ?_) (fun n q ⟨h0, hlt⟩ ↦ ?_)
  · set y₀ := Real.cos (θ / 2) • e₁ + Real.sin (θ / 2) • e₂
    have hy₀ := hsector (by linarith : 0 < θ / 2) (by linarith : θ / 2 < θ)
    have hfix : (Winv ^ h') *ᵥ y₀ = y₀ := by
      rw [hWinv_pow h' (θ / 2),
        show θ / 2 + 2 * (h' : ℝ) * θ = θ / 2 + (m' : ℝ) * (2 * Real.pi) by linarith,
        Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
    have hc_inv : c⁻¹ ^ h' = 1 := eq_one_of_actsBy_fix_of_forall_pos b hy₀
      ((b.actsBy_bipartiteCoxeterElement_inv col).pow h') (by rwa [Matrix.map_pow])
    have hc_pow : c ^ h' = 1 := inv_eq_one.mp (inv_pow c h' ▸ hc_inv)
    exact Nat.not_dvd_of_pos_of_lt hh'0 hh'lt (orderOf_dvd_iff_pow_eq_one.mpr hc_pow)
  · obtain ⟨j, hj⟩ := coxeterPlane_exists_corootEval_zero b hconn col hμ_eq hBx n q
    exact b.corootEval_ne_zero_of_forall_pos (hsector h0 hlt) j hj

/-- **Coleman's Coxeter plane** for a base `b` of rank at least two whose Cartan matrix is of
finite type with preconnected Dynkin diagram (requiring neither spanning nor irreducibility over
`R`). -/
theorem exists_coxeterPlane_bipartiteCoxeterElement_of_isFiniteType
    (b : P.Base) [Nontrivial b.support] (hft : IsFiniteType b.cartanMatrix)
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    let c := (weylCoxeterSystem P b).bipartiteCoxeterElement col
    let h := orderOf c
    let W := (b.bipartiteCoxeterMatrix col).map (Int.castRingHom ℝ)
    let Winv := (b.colorClassMatrix col false * b.colorClassMatrix col true).map
      (Int.castRingHom ℝ)
    ∃ e₁ e₂ : b.support → ℝ,
      LinearIndependent ℝ ![e₁, e₂] ∧
      W *ᵥ e₁ = Real.cos (2 * Real.pi / h) • e₁ - Real.sin (2 * Real.pi / h) • e₂ ∧
      W *ᵥ e₂ = Real.sin (2 * Real.pi / h) • e₁ + Real.cos (2 * Real.pi / h) • e₂ ∧
      (∀ (k : ℕ) (φ : ℝ),
        (Winv ^ k) *ᵥ (Real.cos φ • e₁ + Real.sin φ • e₂) =
          Real.cos (φ + 2 * Real.pi * k / h) • e₁ +
            Real.sin (φ + 2 * Real.pi * k / h) • e₂) ∧
      (∀ φ : ℝ, 0 < φ → φ < Real.pi / h →
        ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) (Real.cos φ • e₁ + Real.sin φ • e₂)) := by
  intro c h W Winv
  obtain ⟨μ, hμpos, x, hx, hBx⟩ :=
    (b.isIrreducible_two_smul_one_sub_transpose_cartanMatrix_of_preconnected
      hconn).exists_mulVec_eq_smul
  have hμlt : μ < 2 := perronEigenvalue_lt_two b hft hx hBx
  set θ : ℝ := Real.arccos (μ / 2)
  have hθpos : 0 < θ := Real.arccos_pos.mpr (by linarith)
  have hθlt : θ < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr (by linarith)
  have hμ_eq : μ = 2 * Real.cos θ := by
    linarith [Real.cos_arccos (by linarith : -1 ≤ μ / 2) (by linarith : μ / 2 ≤ 1)]
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith [Real.pi_pos])
  have hli := coxeterPlane_linearIndependent b hconn col hx hsinθ
  obtain ⟨hWe₁, hWe₂, hWinv_pow⟩ := coxeterPlane_rotation b col hμ_eq hBx
  have hθ_eq : θ = Real.pi / (h : ℝ) :=
    coxeterPlane_angle_eq_pi_div_orderOf b hconn col hx hθpos hθlt hμ_eq hsinθ hBx
  refine ⟨Real.cos θ • b.colorVec col x true + b.colorVec col x false,
    Real.sin θ • b.colorVec col x true, hli, ?_, ?_, fun k φ ↦ ?_, fun φ hφ0 hφh k ↦ ?_⟩
  · rw [hWe₁, hθ_eq, mul_div_assoc]
  · rw [hWe₂, hθ_eq, mul_div_assoc]
  · rw [hWinv_pow k φ, hθ_eq,
      show φ + 2 * (k : ℝ) * (Real.pi / h) = φ + 2 * Real.pi * k / h by ring]
  · rw [coxeterPlane_corootEval b col hμ_eq hBx k φ]; split_ifs
    · exact mul_pos (mul_pos (mul_pos two_pos hsinθ) (hx k))
        (Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith [Real.pi_pos, hθ_eq.symm ▸ hφh]))
    · exact mul_pos (mul_pos (mul_pos two_pos hsinθ) (hx k))
        (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr (hθ_eq.symm ▸ hφh)) (by linarith [Real.pi_pos]))

/-- **Coleman's Coxeter plane** for the bipartite Coxeter element of a finite, reduced,
irreducible, crystallographic root pairing of rank at least two.

There exist linearly independent vectors `e₁, e₂ : b.support → ℝ` such that, putting
`p φ := cos φ • e₁ + sin φ • e₂` and `h := orderOf c`:
1. the bipartite Coxeter matrix `W` acts on `(e₁, e₂)` as rotation by `-2π / h`, and its inverse
   `Winv` acts on `p φ` by `p φ ↦ p (φ + 2π / h)`;
2. for every `φ ∈ (0, π / h)` and every simple root `k : b.support`,
   `0 < b.corootEval ℝ k (p φ)`. -/
theorem exists_coxeterPlane_bipartiteCoxeterElement [P.IsIrreducible]
    (b : P.Base) [Nontrivial b.support]
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    let c := (weylCoxeterSystem P b).bipartiteCoxeterElement col
    let h := orderOf c
    let W := (b.bipartiteCoxeterMatrix col).map (Int.castRingHom ℝ)
    let Winv := (b.colorClassMatrix col false * b.colorClassMatrix col true).map
      (Int.castRingHom ℝ)
    ∃ e₁ e₂ : b.support → ℝ,
      LinearIndependent ℝ ![e₁, e₂] ∧
      W *ᵥ e₁ = Real.cos (2 * Real.pi / h) • e₁ - Real.sin (2 * Real.pi / h) • e₂ ∧
      W *ᵥ e₂ = Real.sin (2 * Real.pi / h) • e₁ + Real.cos (2 * Real.pi / h) • e₂ ∧
      (∀ (k : ℕ) (φ : ℝ),
        (Winv ^ k) *ᵥ (Real.cos φ • e₁ + Real.sin φ • e₂) =
          Real.cos (φ + 2 * Real.pi * k / h) • e₁ +
            Real.sin (φ + 2 * Real.pi * k / h) • e₂) ∧
      (∀ φ : ℝ, 0 < φ → φ < Real.pi / h →
        ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) (Real.cos φ • e₁ + Real.sin φ • e₂)) := by
  obtain ⟨i₀, -⟩ := exists_pair_ne b.support
  have : Nonempty ι := ⟨i₀.1⟩
  have : NeZero (2 : R) := ⟨by norm_num⟩
  exact b.exists_coxeterPlane_bipartiteCoxeterElement_of_isFiniteType
    (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) col

end CoxeterPlane

/-! ### Regular primitive-root eigenvectors of arbitrary Coxeter elements -/

section RegularEigenvector

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- Rank-one case of the regular `exp (2πi / h)`-eigenvector: when `b.support` is a singleton
`{i₀}`, the Coxeter element is the reflection `s_{i₀}` of order `2`, acting by `-1 = exp (2πi / 2)`
on the regular vector `1`. -/
private theorem exists_eigenvector_subsingleton [Nonempty ι] (b : P.Base) [Subsingleton b.support]
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    let c := wordProd P b l
    ∃ v : b.support → ℂ,
      v ≠ 0 ∧
      (W.map (Int.castRingHom ℂ)) *ᵥ v =
        Complex.exp (2 * Real.pi * Complex.I / orderOf c) • v ∧
      IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / orderOf c)) (orderOf c) ∧
      (∀ j : ι, b.corootEval ℂ j v ≠ 0) ∧
      (∀ (g : P.weylGroup) (G : Matrix b.support b.support ℤ),
        b.ActsBy g G → (G.map (Int.castRingHom ℂ)) *ᵥ v = v → g = 1) := by
  classical
  intro c
  obtain ⟨i₀⟩ : Nonempty b.support := b.support_nonempty.to_subtype
  have hl_eq : l = [i₀] := by
    obtain ⟨a, tail, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem (hall i₀))
    rw [List.nodup_cons] at hnd
    have htail : tail = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx ↦
      hnd.1 (Subsingleton.elim x a ▸ hx)
    rw [htail, Subsingleton.elim a i₀]
  have hW_eq : W = -1 := by
    have hact : b.ActsBy c (reflMatrix b.cartanMatrix i₀) := by
      simpa [c, hl_eq, wordProd_cons, wordProd_nil] using b.actsBy_ofIdx i₀
    rw [hW.unique hact]; ext k j
    rw [Subsingleton.elim k i₀, Subsingleton.elim j i₀]; simp [reflMatrix_apply]
  have hord : orderOf c = 2 := by
    rw [hW.orderOf_eq, hW_eq]
    refine orderOf_eq_prime (by simp) fun h1 ↦ ?_
    have := congrFun (congrFun h1 i₀) i₀; norm_num at this
  set v : b.support → ℂ := fun _ ↦ 1
  have hv_re : ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) (fun _ ↦ (1 : ℝ)) := by
    intro k; rw [Subsingleton.elim k i₀, corootEval_coe_support, Fintype.sum_subsingleton _ i₀,
      b.cartanMatrix_apply_same i₀]; norm_num
  refine ⟨v, fun h ↦ one_ne_zero (congrFun h i₀), ?_,
    hord ▸ Complex.isPrimitiveRoot_exp 2 (by norm_num), fun j hj ↦ ?_, fun g G hG hGv ↦ ?_⟩
  · rw [hW_eq, hord, show (2 : ℂ) * ↑Real.pi * Complex.I / (2 : ℕ) = ↑Real.pi * Complex.I by
      push_cast; ring, Complex.exp_pi_mul_I]
    ext k; rw [Subsingleton.elim k i₀]
    rw [Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _), neg_mulVec,
      one_mulVec]
    simp [v]
  · have hreal : (b.corootEval ℝ j (fun _ ↦ (1 : ℝ)) : ℂ) = b.corootEval ℂ j v := by
      simp [corootEval_apply, v]
    exact b.corootEval_ne_zero_of_forall_pos hv_re j (Complex.ofReal_eq_zero.mp (hreal.trans hj))
  · refine eq_one_of_actsBy_fix_of_forall_pos b hv_re hG ?_
    ext i; simpa [mulVec, dotProduct, v] using congrArg Complex.re (congrFun hGv i)

/-- An integer matrix acting on real vectors `(e₁, e₂)` by rotation through `-α` acts on the
complexification `e₁ + i e₂` with eigenvalue `exp (α i)`. -/
private lemma mulVec_complex_of_rotation {κ : Type*} [Fintype κ] {W₀ : Matrix κ κ ℤ}
    {e₁ e₂ : κ → ℝ} {α : ℝ}
    (hWe₁ : (W₀.map (Int.castRingHom ℝ)) *ᵥ e₁ = Real.cos α • e₁ - Real.sin α • e₂)
    (hWe₂ : (W₀.map (Int.castRingHom ℝ)) *ᵥ e₂ = Real.sin α • e₁ + Real.cos α • e₂) :
    (W₀.map (Int.castRingHom ℂ)) *ᵥ (fun i ↦ (e₁ i : ℂ) + Complex.I * (e₂ i : ℂ)) =
      Complex.exp ((α : ℂ) * Complex.I) • (fun i ↦ (e₁ i : ℂ) + Complex.I * (e₂ i : ℂ)) := by
  have hexp : Complex.exp ((α : ℂ) * Complex.I) =
      ↑(Real.cos α) + ↑(Real.sin α) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  ext i
  have hi1 : ∑ j : κ, (W₀ i j : ℂ) * (e₁ j : ℂ) =
      ↑(Real.cos α) * (e₁ i : ℂ) - ↑(Real.sin α) * (e₂ i : ℂ) := by
    have h1 := congrFun hWe₁ i
    simp only [mulVec, dotProduct, map_apply, Int.coe_castRingHom, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] at h1
    exact_mod_cast h1
  have hi2 : ∑ j : κ, (W₀ i j : ℂ) * (e₂ j : ℂ) =
      ↑(Real.sin α) * (e₁ i : ℂ) + ↑(Real.cos α) * (e₂ i : ℂ) := by
    have h2 := congrFun hWe₂ i
    simp only [mulVec, dotProduct, map_apply, Int.coe_castRingHom, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at h2
    exact_mod_cast h2
  have hsplit : ((W₀.map (Int.castRingHom ℂ)) *ᵥ
      (fun j ↦ (e₁ j : ℂ) + Complex.I * (e₂ j : ℂ))) i =
      (∑ j : κ, (W₀ i j : ℂ) * (e₁ j : ℂ)) +
        Complex.I * ∑ j : κ, (W₀ i j : ℂ) * (e₂ j : ℂ) := by
    simp only [mulVec, dotProduct, map_apply, Int.coe_castRingHom, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    exact congrArg (_ + ·) (Finset.sum_congr rfl fun j _ ↦ by ring)
  rw [hsplit, hi1, hi2]; simp only [Pi.smul_apply, smul_eq_mul, hexp]
  linear_combination -↑(Real.sin α) * (e₂ i : ℂ) * Complex.I_sq

/-- Rank `≥ 2` bipartite Coxeter eigenvector `v₀ = e₁ + i e₂`, constructed directly from
`exists_coxeterPlane_bipartiteCoxeterElement_of_isFiniteType`. -/
private theorem exists_eigenvector_bipartite_of_isFiniteType [DecidableEq ι]
    (b : P.Base) [Nontrivial b.support] (hft : IsFiniteType b.cartanMatrix)
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    let c₀ := (weylCoxeterSystem P b).bipartiteCoxeterElement col
    let W₀ := b.bipartiteCoxeterMatrix col
    ∃ v₀ : b.support → ℂ,
      v₀ ≠ 0 ∧
      (W₀.map (Int.castRingHom ℂ)) *ᵥ v₀ =
        Complex.exp (2 * Real.pi * Complex.I / orderOf c₀) • v₀ ∧
      (∀ j : ι, b.corootEval ℂ j v₀ ≠ 0) ∧
      (∀ (g : P.weylGroup) (G : Matrix b.support b.support ℤ),
        b.ActsBy g G → (G.map (Int.castRingHom ℂ)) *ᵥ v₀ = v₀ → g = 1) := by
  intro c₀ W₀
  have := P.finite_weylGroup_of_base b
  set h := orderOf c₀
  have hh_pos : 0 < h := orderOf_pos c₀
  obtain ⟨e₁, e₂, hli, hWe₁, hWe₂, -, hsector⟩ :=
    b.exists_coxeterPlane_bipartiteCoxeterElement_of_isFiniteType hft hconn col
  set v₀ : b.support → ℂ := fun i ↦ (e₁ i : ℂ) + Complex.I * (e₂ i : ℂ)
  set φ₀ := (Real.pi / (h : ℝ)) / 2
  set y₀ := Real.cos φ₀ • e₁ + Real.sin φ₀ • e₂
  have hy₀ : ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) y₀ :=
    hsector φ₀ (by positivity) (half_lt_self (by positivity))
  refine ⟨v₀, fun hv0 ↦ hli.ne_zero 0 ?_, ?_, fun j hj0 ↦ ?_, fun g G hG hGv ↦ ?_⟩
  · ext i; simpa [v₀] using congrArg Complex.re (congrFun hv0 i)
  · rw [show (2 : ℂ) * ↑Real.pi * Complex.I / (h : ℂ) = ↑(2 * Real.pi / (h : ℝ)) * Complex.I by
      push_cast; ring]
    exact mulVec_complex_of_rotation hWe₁ hWe₂
  · have hre : b.corootEval ℝ j e₁ = 0 := by
      simpa [corootEval_apply, v₀] using congrArg Complex.re hj0
    have him : b.corootEval ℝ j e₂ = 0 := by
      simpa [corootEval_apply, v₀] using congrArg Complex.im hj0
    exact b.corootEval_ne_zero_of_forall_pos hy₀ j (by simp [y₀, map_add, map_smul, hre, him])
  · have hGe₁ : (G.map (Int.castRingHom ℝ)) *ᵥ e₁ = e₁ := by
      ext i; simpa [mulVec, dotProduct, v₀] using congrArg Complex.re (congrFun hGv i)
    have hGe₂ : (G.map (Int.castRingHom ℝ)) *ᵥ e₂ = e₂ := by
      ext i; simpa [mulVec, dotProduct, v₀] using congrArg Complex.im (congrFun hGv i)
    exact eq_one_of_actsBy_fix_of_forall_pos b hy₀ hG
      (by rw [mulVec_add, mulVec_smul, mulVec_smul, hGe₁, hGe₂])

/-- Conjugating a regular `exp (2πi / orderOf c₀)`-eigenvector `v₀` of `c₀` along `IsConj c c₀`
transports nonvanishing, eigenvalue, primitivity, coroot regularity, and trivial stabilizer to `c`.
-/
private theorem exists_eigenvector_of_isConj (b : P.Base)
    {c c₀ : P.weylGroup} {W W₀ : Matrix b.support b.support ℤ}
    (hW : b.ActsBy c W) (hW₀ : b.ActsBy c₀ W₀) (hconj : IsConj c c₀)
    {v₀ : b.support → ℂ} (hv₀_ne : v₀ ≠ 0)
    (hW₀_eigen : (W₀.map (Int.castRingHom ℂ)) *ᵥ v₀ =
      Complex.exp (2 * Real.pi * Complex.I / orderOf c₀) • v₀)
    (hv₀_reg : ∀ j : ι, b.corootEval ℂ j v₀ ≠ 0)
    (hv₀_stab : ∀ (g : P.weylGroup) (G : Matrix b.support b.support ℤ),
      b.ActsBy g G → (G.map (Int.castRingHom ℂ)) *ᵥ v₀ = v₀ → g = 1) :
    ∃ v : b.support → ℂ,
      v ≠ 0 ∧
      (W.map (Int.castRingHom ℂ)) *ᵥ v =
        Complex.exp (2 * Real.pi * Complex.I / orderOf c) • v ∧
      IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / orderOf c)) (orderOf c) ∧
      (∀ j : ι, b.corootEval ℂ j v ≠ 0) ∧
      (∀ (g : P.weylGroup) (G : Matrix b.support b.support ℤ),
        b.ActsBy g G → (G.map (Int.castRingHom ℂ)) *ᵥ v = v → g = 1) := by
  classical
  have := P.finite_weylGroup_of_base b
  obtain ⟨u, hu⟩ := isConj_iff.mp hconj.symm
  obtain ⟨cu, hcu⟩ := hconj
  have hord_eq : orderOf c = orderOf c₀ := hcu.orderOf_eq
  obtain ⟨lu, hlu⟩ := exists_wordProd_eq P b u
  obtain ⟨lu_inv, hlu_inv⟩ := exists_wordProd_eq P b u⁻¹
  set U := (lu.map (reflMatrix b.cartanMatrix)).prod
  set Uinv := (lu_inv.map (reflMatrix b.cartanMatrix)).prod
  have hU : b.ActsBy u U := hlu ▸ b.actsBy_wordProd lu
  have hUinv : b.ActsBy u⁻¹ Uinv := hlu_inv ▸ b.actsBy_wordProd lu_inv
  have hUinvU_one : b.ActsBy 1 (Uinv * U) := by simpa using hUinv.mul hU
  have hUinvU_C : Uinv.map (Int.castRingHom ℂ) * U.map (Int.castRingHom ℂ) = 1 := by
    rw [← Matrix.map_mul, hUinvU_one.unique b.actsBy_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hW_conj : W = U * W₀ * Uinv :=
    hW.unique (hu ▸ (hU.mul hW₀).mul hUinv)
  refine ⟨(U.map (Int.castRingHom ℂ)) *ᵥ v₀, fun hv0 ↦ hv₀_ne ?_, ?_,
    hord_eq ▸ Complex.isPrimitiveRoot_exp _ (orderOf_pos c₀).ne',
    fun j ↦ ?_, fun g G hG hGv ↦ ?_⟩
  · have h0 := congrArg ((Uinv.map (Int.castRingHom ℂ)) *ᵥ ·) hv0
    rwa [mulVec_mulVec, hUinvU_C, one_mulVec, mulVec_zero] at h0
  · rw [hW_conj, hord_eq, Matrix.map_mul, Matrix.map_mul, mulVec_mulVec,
      Matrix.mul_assoc, hUinvU_C, Matrix.mul_one, ← mulVec_mulVec, hW₀_eigen, mulVec_smul]
  · rw [← b.corootEval_weylGroupToPerm_inv hU ℂ j v₀]; exact hv₀_reg _
  · have hfix : ((Uinv * G * U).map (Int.castRingHom ℂ)) *ᵥ v₀ = v₀ := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc, ← mulVec_mulVec,
        ← mulVec_mulVec, hGv, mulVec_mulVec, hUinvU_C, one_mulVec]
    have h1 := hv₀_stab (u⁻¹ * g * u) (Uinv * G * U) ((hUinv.mul hG).mul hU) hfix
    calc g = u * (u⁻¹ * g * u) * u⁻¹ := by group
      _ = 1 := by rw [h1]; group

/-- **Matrix-level regular primitive-root eigenvector** of any Coxeter element for a base whose
Cartan matrix is of finite type with preconnected Dynkin diagram (requiring neither spanning nor
irreducibility over `R`). -/
theorem exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd_of_isFiniteType
    [Nonempty ι] (b : P.Base) (hft : IsFiniteType b.cartanMatrix)
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    let c := wordProd P b l
    ∃ v : b.support → ℂ,
      v ≠ 0 ∧
      (W.map (Int.castRingHom ℂ)) *ᵥ v =
        Complex.exp (2 * Real.pi * Complex.I / orderOf c) • v ∧
      IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / orderOf c)) (orderOf c) ∧
      (∀ j : ι, b.corootEval ℂ j v ≠ 0) ∧
      (∀ (g : P.weylGroup) (G : Matrix b.support b.support ℤ),
        b.ActsBy g G → (G.map (Int.castRingHom ℂ)) *ᵥ v = v → g = 1) := by
  classical
  by_cases hnt : Nontrivial b.support
  · have hacyc : (coxeterMatrixOfBase P b).graph.IsAcyclic := by
      rw [graph_coxeterMatrixOfBase]; exact hft.isAcyclic_diagramGraph
    obtain ⟨col⟩ : Nonempty ((coxeterMatrixOfBase P b).graph.Coloring Bool) :=
      Nonempty.map ((coxeterMatrixOfBase P b).graph.recolorOfEquiv finTwoEquiv) hacyc.isBipartite
    obtain ⟨v₀, hv₀_ne, hW₀_eigen, hv₀_reg, hv₀_stab⟩ :=
      b.exists_eigenvector_bipartite_of_isFiniteType hft hconn col
    have hconj : IsConj (wordProd P b l) ((weylCoxeterSystem P b).bipartiteCoxeterElement col) := by
      rw [← weylCoxeterSystem_wordProd]
      exact (weylCoxeterSystem P b).isConj_wordProd_bipartiteCoxeterElement hacyc col hnd hall
    exact b.exists_eigenvector_of_isConj hW (b.actsBy_bipartiteCoxeterElement col) hconj
      hv₀_ne hW₀_eigen hv₀_reg hv₀_stab
  · have : Subsingleton b.support := not_nontrivial_iff_subsingleton.mp hnt
    exact exists_eigenvector_subsingleton b hnd hall hW

/-- **Matrix-level regular primitive-root eigenvector of any Coxeter element.**

For any base `b` of a nonempty, finite, reduced, irreducible, crystallographic root pairing over
any characteristic-zero domain, and any Coxeter word `l` listing `b.support` once each, let
`c = wordProd P b l` act on the simple roots by the integer matrix `W`. Then `W` has a nonzero
complex eigenvector `v : b.support → ℂ` for the primitive `orderOf c`-th root of unity
`exp (2πi / orderOf c)` on which no coroot functional `b.corootEval ℂ j` vanishes, and whose
pointwise stabilizer in `P.weylGroup` is trivial. -/
theorem exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd
    [Nonempty ι] [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    let c := wordProd P b l
    ∃ v : b.support → ℂ,
      v ≠ 0 ∧
      (W.map (Int.castRingHom ℂ)) *ᵥ v =
        Complex.exp (2 * Real.pi * Complex.I / orderOf c) • v ∧
      IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / orderOf c)) (orderOf c) ∧
      (∀ j : ι, b.corootEval ℂ j v ≠ 0) ∧
      (∀ (g : P.weylGroup) (G : Matrix b.support b.support ℤ),
        b.ActsBy g G → (G.map (Int.castRingHom ℂ)) *ᵥ v = v → g = 1) := by
  have : NeZero (2 : R) := ⟨by norm_num⟩
  exact b.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd_of_isFiniteType
    (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall hW

end RegularEigenvector

/-! ### Weight-space regular primitive-root eigenvector for complex root systems -/

section ComplexRootSystem

variable {ι M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  {P : RootPairing ι ℂ M N} [Finite ι]
  [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

omit [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] in
/-- Action of a Weyl-group element `g` with simple-root matrix `G` on a complex linear combination
`∑ i, y i • P.root i` of the simple roots. -/
private theorem smul_sum_root_of_actsBy (b : P.Base) (y : b.support → ℂ)
    {g : P.weylGroup} {G : Matrix b.support b.support ℤ} (hG : b.ActsBy g G) :
    g • ∑ i : b.support, y i • P.root i =
      ∑ i : b.support, ((G.map (Int.castRingHom ℂ)) *ᵥ y) i • P.root i := by
  rw [Finset.smul_sum]
  calc ∑ j : b.support, g • (y j • P.root j)
      = ∑ j : b.support, y j • ∑ i : b.support, G i j • P.root i :=
        Finset.sum_congr rfl fun j _ ↦ by rw [smul_comm, actsBy_iff.mp hG j]
    _ = ∑ i : b.support, ((G.map (Int.castRingHom ℂ)) *ᵥ y) i • P.root i := by
        simp only [Finset.smul_sum, mulVec, dotProduct, map_apply, Int.coe_castRingHom,
          Finset.sum_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul, mul_comm]

/-- Rootless degenerate case (`IsEmpty ι`) of `exists_regularWeight_eigenvector_wordProd`: an
irreducible rootless pairing on `M` is nontrivial (`dim_ℂ M = 1`), with trivial Weyl group and
Coxeter order `1`. -/
private theorem exists_regularWeight_eigenvector_isEmpty [IsEmpty ι] (b : P.Base)
    (l : List b.support) :
    let c := wordProd P b l
    let ζ := Complex.exp (2 * Real.pi * Complex.I / orderOf c)
    ∃ v : M,
      v ≠ 0 ∧ c • v = ζ • v ∧ IsPrimitiveRoot ζ (orderOf c) ∧
      P.IsRegularWeight v ∧ MulAction.stabilizer P.weylGroup v = ⊥ := by
  intro c ζ
  have : IsEmpty b.support := ⟨fun i ↦ IsEmpty.false i.1⟩
  have := IsIrreducible.nontrivial (P := P)
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  have hl : l = [] := List.eq_nil_iff_forall_not_mem.mpr fun i _ ↦ IsEmpty.false i
  have hc : c = 1 := by simp only [c, hl, wordProd_nil]
  have hord : orderOf c = 1 := by rw [hc, orderOf_one]
  have hprim : IsPrimitiveRoot ζ (orderOf c) := by
    simp only [ζ, hord]
    exact Complex.isPrimitiveRoot_exp 1 one_ne_zero
  have hζ1 : ζ = 1 := IsPrimitiveRoot.one_right_iff.mp (hord ▸ hprim)
  refine ⟨v, hv, by rw [hc, hζ1, one_smul, one_smul], hprim,
    (isRegularWeight_iff P v).mpr fun j ↦ (IsEmpty.false j).elim, eq_bot_iff.mpr fun g _ ↦ ?_⟩
  obtain ⟨lg, hlg⟩ := exists_wordProd_eq P b g
  rw [Subgroup.mem_bot, ← hlg,
    show lg = [] from List.eq_nil_iff_forall_not_mem.mpr fun i _ ↦ IsEmpty.false i, wordProd_nil]

/-- **Every Coxeter element of an irreducible finite complex crystallographic reduced root pairing
has a regular primitive-root eigenvector with trivial Weyl stabilizer.**

Specifically, for `c = wordProd P b l` listing the simple roots of `b` once each, there exists a
nonzero weight `v : M` such that:
1. `c • v = exp (2πi / orderOf c) • v`, where `exp (2πi / orderOf c)` is a primitive
   `orderOf c`-th root of unity;
2. `P.IsRegularWeight v`, i.e., `P.coroot' j v ≠ 0` for every root `j : ι`;
3. `MulAction.stabilizer P.weylGroup v = ⊥`, so `v` lies on no fixed hyperplane of any nontrivial
   element of `P.weylGroup`. -/
theorem exists_regularWeight_eigenvector_wordProd (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    let c := wordProd P b l
    let ζ := Complex.exp (2 * Real.pi * Complex.I / orderOf c)
    ∃ v : M,
      v ≠ 0 ∧
      c • v = ζ • v ∧
      IsPrimitiveRoot ζ (orderOf c) ∧
      P.IsRegularWeight v ∧
      MulAction.stabilizer P.weylGroup v = ⊥ := by
  by_cases hne : Nonempty ι
  · classical
    intro c ζ
    set W := (l.map (reflMatrix b.cartanMatrix)).prod
    have hW : b.ActsBy c W := b.actsBy_wordProd l
    obtain ⟨y, hy_ne, hy_eig, hprim, hy_reg, hy_stab⟩ :=
      b.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd hnd hall hW
    set v : M := ∑ i : b.support, y i • P.root i
    have hli := b.linearIndepOn_root
    refine ⟨v, fun hv0 ↦ hy_ne (funext (Fintype.linearIndependent_iff.mp hli y hv0)), ?_, hprim,
      (isRegularWeight_iff P v).mpr fun j ↦ b.coroot'_sum_smul_root j y ▸ hy_reg j, ?_⟩
    · rw [smul_sum_root_of_actsBy b y hW, hy_eig]
      simp [v, c, ζ, Finset.smul_sum, smul_smul]
    · rw [eq_bot_iff]; intro g hg
      rw [MulAction.mem_stabilizer_iff] at hg
      obtain ⟨lg, hlg⟩ := exists_wordProd_eq P b g
      have hG : b.ActsBy g (lg.map (reflMatrix b.cartanMatrix)).prod := hlg ▸ b.actsBy_wordProd lg
      rw [smul_sum_root_of_actsBy b y hG] at hg
      have hdiff : ∑ i : b.support,
          ((((lg.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℂ)) *ᵥ y) i - y i) •
            P.root i = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, hg, v, sub_self]
      have hGy : ((lg.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℂ)) *ᵥ y = y := by
        ext i; exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ hdiff i)
      exact Subgroup.mem_bot.mpr (hy_stab g _ hG hGy)
  · have : IsEmpty ι := not_nonempty_iff.mp hne
    exact exists_regularWeight_eigenvector_isEmpty b l

end ComplexRootSystem

end RootPairing.Base

end
