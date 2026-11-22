/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.TypeA.BoxTypeDA
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Algebra.Order.BigOperators.Fin

/-!
# Associativity of the box tensor product with a type `DA` bimodule

Gluing three bordered pieces along two surfaces can be done in either order, and the bordered
invariants reflect this as the associativity `(M ⊠ P) ⊠ N = M ⊠ (P ⊠ N)` of box tensor products,
for a type `A` module `M` over `B`, a type `DA` bimodule `P = ^B P_A` and a type `D` structure `N`
over `A`. For a differential module `M` this is
`TauCeti.TypeDAStructure.typeABoxDifferential_boxModule`. This file proves it for an `A∞` module
`M` whose operations vanish from some arity on, so that `M ⊠ P` is the type `A` module
`TauCeti.TypeDAStructure.typeABoxModule`, with higher operations, over a ring of characteristic two.
As for differential modules, one of `N` and `P` is bounded, which makes `P ⊠ N`
(`TauCeti.TypeDAStructure.boxTypeD`) and the box tensor differential of `M ⊠ P` with `N` finite
sums.

Both sides are sums over the paths `x₀ → x₁ → ⋯ → xₙ` of generators of `N`. On the left the
operation `m_{n+1}` of `M ⊠ P` cuts the coefficients `δ x₀ x₁, …, δ xₙ₋₁ xₙ` of `N` along such a
path into `k` consecutive, possibly empty, blocks at `0 = c₀ ≤ c₁ ≤ ⋯ ≤ c_k = n`, feeds each block
to the operations `δ¹` of `P`, and the resulting coefficient matrices to `m_{k+1}` of the matrix
module of `M`. On the right the coefficient of `P ⊠ N` from `y ⊗ x` to `y' ⊗ x'` sums the operations
of `P` on the iterates `δ^j` of `N` from `x` to `x'`, which are sums over the paths of length `j`,
and the box tensor differential of `M` with `P ⊠ N` feeds `k` of these coefficients to `m_{k+1}`.
The matrix module of the generators `Y × X` of `P ⊠ N` is the matrix module over `X` of the matrix
module over `Y` (`TauCeti.UngradedAInfinityRightModule.matrixAct_prod_apply`), so both sides are
sums of `m_{k+1}` over the paths `w₀ → ⋯ → w_k` and the tuples `(j₀, …, j_{k-1})` of block lengths.
Two reindexings identify them.

* A path of length `n = j₀ + ⋯ + j_{k-1}` cut at the partial sums of the `jₜ` is the concatenation
  of `k` paths of lengths `jₜ`, from `wₜ` to `wₜ₊₁`. This is proved by induction on `k`, splitting
  off the last block.
* The nondecreasing cuts `0 = c₀ ≤ ⋯ ≤ c_k = n` are exactly the partial sums of the tuples of block
  lengths with total `n`; a cut with a decreasing step meets an entry of the block matrix below the
  diagonal and contributes nothing.

Under either boundedness hypothesis the iterates contribute only for block lengths below some `J`,
so only paths of length less than `K * J` contribute, where `M` has no operations of arity `K` or
more.

## Main results

* `TauCeti.TypeDAStructure.typeABoxDifferential_typeABoxModule_apply`: associativity on row
  vectors, for the coefficient matrix of `P ⊠ N`.
* `TauCeti.TypeDAStructure.typeABoxDifferential_typeABoxModule`: associativity,
  `(M ⊠ P) ⊠ N = M ⊠ (P ⊠ N)`, through the type `D` structure `P ⊠ N`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bimodules in bordered Heegaard Floer homology*,
  Geom. Topol. **19** (2015), 525–724, [arXiv:1003.0598](https://arxiv.org/abs/1003.0598), §2.3
  (box tensor products of type `A` modules with type `DA` bimodules and of type `DA` bimodules with
  type `D` structures, their boundedness hypotheses, and the associativity of box tensor
  products).
-/

public section

open Finset

namespace TauCeti

namespace TypeDAStructure

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {S : Type*} {ιB : S → B} {Y : Type*} [Fintype Y]
  (P : TypeDAStructure dA dB ιB Y) {T : Type*} {ιA : T → A} {X : Type*}

/-- The block of length `j t` starting at the `t`-th partial sum of `j` ends before the total. -/
private theorem partialSum_castSucc_add_le {k : ℕ} (j : Fin k → ℕ) (t : Fin k) :
    Fin.partialSum j t.castSucc + j t ≤ Fin.partialSum j (Fin.last k) := by
  rw [← Fin.partialSum_succ]
  exact Fin.monotone_partialSum (fun _ => Nat.zero_le _) (Fin.le_last _)

variable [Fintype X] (N : TypeDStructure dA ιA X)

/-- The coefficients of `N` along the block of length `len` of a path `x` starting at `s`. -/
private noncomputable def pathBlock {n : ℕ} (x : Fin (n + 1) → X) (s len : ℕ) (h : s + len ≤ n) :
    Fin len → A :=
  fun l => N.coeff (x ⟨s + l, by have := l.isLt; omega⟩) (x ⟨s + l + 1, by have := l.isLt; omega⟩)

/-- Blocks of two paths agreeing on the block are equal. -/
private theorem pathBlock_congr {n n' : ℕ} {x : Fin (n + 1) → X} {x' : Fin (n' + 1) → X}
    {s s' len : ℕ}
    (hs : s = s') (h : s + len ≤ n) (h' : s' + len ≤ n')
    (hx : ∀ i (hi : i ≤ s + len), x ⟨i, by omega⟩ = x' ⟨i, by omega⟩) :
    pathBlock N x s len h = pathBlock N x' s' len h' := by
  subst hs
  funext l
  simp only [pathBlock]
  rw [hx _ (by have := l.isLt; omega), hx _ (by have := l.isLt; omega)]

/-- The entry of the block matrix of the coefficients along a path between two cut points is the
coefficient matrix of `P` on the block of the path between them. -/
private theorem blockMatrix_eq_pathBlock {n : ℕ} (x : Fin (n + 1) → X) {c c' : Fin (n + 1)}
    {s len : ℕ}
    (hc : (c : ℕ) = s) (hc' : (c' : ℕ) = s + len) (h : s + len ≤ n) :
    P.blockMatrix (fun l => N.coeff (x l.castSucc) (x l.succ)) c c' =
      P.coeff len (pathBlock N x s len h) := by
  rw [P.blockMatrix_apply_of_le _ (by omega)]
  refine P.coeff_congr (by omega) fun l => ?_
  simp only [pathBlock]
  congr 2 <;> ext <;> simp [hc]

variable [DecidableEq X]

/-- The matrix of the evaluations of `δ¹_{len+1}` on the iterates `δ^len` of `N`. -/
private noncomputable def iterMatrix (len : ℕ) : Matrix X X (Matrix Y Y B) :=
  Matrix.of fun x x' => PiTensorProduct.lift (P.coeff len) (N.iteratedCoeff len x x')

/-- Splitting a path at `L`: the sum over paths of length `L + a` is the sum over pairs of a
path `x'` of length `L` and a path `r` of length `a` with `r 0 = x' L`. -/
private theorem sum_pathBlock_snoc_left {W : Type*} [AddCommGroup W] [Module R W] {k : ℕ}
    (j : Fin (k + 1) → ℕ)
    (f : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) => Matrix Y Y B) W) (a z : X)
    (hn : Fin.partialSum j (Fin.last (k + 1)) =
      Fin.partialSum (Fin.init j) (Fin.last k) + j (Fin.last k)) :
    ∑ x : Fin (Fin.partialSum (Fin.init j) (Fin.last k) + (j (Fin.last k) + 1)) → X,
      (if x 0 = a ∧
          x (Fin.last (Fin.partialSum (Fin.init j) (Fin.last k) + j (Fin.last k))) = z then
        f (fun t => P.coeff (j t) (pathBlock
          (n := Fin.partialSum (Fin.init j) (Fin.last k) + j (Fin.last k)) N x
          (Fin.partialSum j t.castSucc) (j t) (hn ▸ partialSum_castSucc_add_le j t))) else 0) =
    ∑ x' : Fin (Fin.partialSum (Fin.init j) (Fin.last k) + 1) → X,
      ∑ r : Fin (j (Fin.last k) + 1) → X,
        if x' 0 = a ∧ x' (Fin.last _) = r 0 ∧ r (Fin.last _) = z then
          f (Fin.snoc (fun t => P.coeff (Fin.init j t) (pathBlock N x'
            (Fin.partialSum (Fin.init j) t.castSucc) (Fin.init j t)
            (partialSum_castSucc_add_le (Fin.init j) t)))
            (P.coeff (j (Fin.last k)) fun l => N.coeff (r l.castSucc) (r l.succ))) else 0 := by
  have hL : Fin.partialSum j (Fin.last k).castSucc = Fin.partialSum (Fin.init j) (Fin.last k) :=
    (Fin.partialSum_init (Fin.last k)).symm
  have key (p q s : Prop) [Decidable p] [Decidable q] [Decidable s] (v : W) :
      (if p ∧ q ∧ s then v else 0) = if q then (if p ∧ s then v else 0) else 0 := by
    split_ifs <;> tauto
  simp only [key]
  rw [Fin.sum_sum_ite_apply_last_eq_apply_zero rfl]
  refine Finset.sum_congr rfl fun w _ => ?_
  refine if_congr Iff.rfl (congrArg f (funext fun t => ?_)) rfl
  refine Fin.lastCases ?_ (fun t => ?_) t
  · rw [Fin.snoc_last]
    refine congrArg _ (funext fun l => ?_)
    exact congrArg₂ N.coeff (congrArg w (Fin.ext (by simp [hL])))
      (congrArg w (Fin.ext (by simp [hL, add_assoc])))
  · rw [Fin.snoc_castSucc]
    exact congrArg _ (pathBlock_congr N (Fin.partialSum_init t.castSucc).symm _ _ fun i hi => rfl)

/-- Splitting a path of the generators of `N` at its last step, the evaluations of `f` on the
matrices `iterMatrix` along it become evaluations of `f` with its last input fixed. -/
private theorem sum_iterMatrix_snoc {W : Type*} [AddCommGroup W] [Module R W] {k : ℕ}
    (j : Fin (k + 1) → ℕ)
    (f : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) => Matrix Y Y B) W) (a z : X) :
    ∑ w : Fin (k + 1 + 1) → X, (if w 0 = a ∧ w (Fin.last (k + 1)) = z then
      f (fun t => P.iterMatrix N (j t) (w t.castSucc) (w t.succ)) else 0) =
    ∑ m : X, ∑ w : Fin (k + 1) → X, if w 0 = a ∧ w (Fin.last k) = m then
      (LinearMap.applyₗ (P.iterMatrix N (j (Fin.last k)) m z)).compMultilinearMap f.curryRight
        (fun t => P.iterMatrix N (Fin.init j t) (w t.castSucc) (w t.succ)) else 0 := by
  conv_lhs => rw [← (Fin.snocEquiv fun _ => X).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Fintype.sum_eq_single z fun b hb => ?_, Fintype.sum_eq_single (w (Fin.last k)) fun m hm => ?_]
  · have hw0 : Fin.snoc (α := fun _ => X) w z 0 = w 0 := Fin.snoc_castSucc (i := 0) ..
    simp only [Fin.snocEquiv_apply, Fin.snoc_last, hw0, and_true,
      LinearMap.compMultilinearMap_apply,
      LinearMap.applyₗ_apply_apply, MultilinearMap.curryRight_apply]
    refine if_congr Iff.rfl (congrArg f (funext fun t => ?_)) rfl
    refine Fin.lastCases ?_ (fun t => ?_) t
    · simp
    · simp only [Fin.succ_castSucc, Fin.snoc_castSucc]
      rfl
  · rw [ite_eq_right fun h => hm h.2.symm]
  · simp only [Fin.snocEquiv_apply, Fin.snoc_last]
    rw [ite_eq_right fun h => hb h.2]

/-- The last block: evaluating on the matrix `iterMatrix` from the endpoint of a path sums over the
paths `r` continuing it. -/
private theorem sum_iterMatrix_last {W : Type*} [AddCommGroup W] [Module R W] {k n : ℕ}
    (j : Fin (k + 1) → ℕ)
    (f : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) => Matrix Y Y B) W) (a z : X)
    (G : (Fin (n + 1) → X) → Fin k → Matrix Y Y B) :
    ∑ m : X, ∑ x : Fin (n + 1) → X, (if x 0 = a ∧ x (Fin.last n) = m then
      (LinearMap.applyₗ (P.iterMatrix N (j (Fin.last k)) m z)).compMultilinearMap f.curryRight
        (G x) else 0) =
    ∑ x : Fin (n + 1) → X, ∑ r : Fin (j (Fin.last k) + 1) → X,
      if x 0 = a ∧ x (Fin.last n) = r 0 ∧ r (Fin.last _) = z then
        f (Fin.snoc (G x) (P.coeff (j (Fin.last k)) fun l => N.coeff (r l.castSucc) (r l.succ)))
      else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_eq_single (x (Fin.last n)) fun m hm => ?_]
  swap
  · exact ite_eq_right fun h => hm h.2.symm
  rw [LinearMap.compMultilinearMap_apply, LinearMap.applyₗ_apply_apply, iterMatrix,
    Matrix.of_apply, TypeDStructure.lift_iteratedCoeff, map_sum]
  simp only [and_true, MultilinearMap.curryRight_apply]
  split_ifs with ha
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [ha, true_and, eq_comm (a := r 0)]
  · exact (Finset.sum_eq_zero fun r _ => ite_eq_right fun h => absurd h.1 ha).symm

/-- **Cutting paths into blocks.** For lengths `j₀, …, j_{k-1}` with total `n`, summing a
multilinear map `f` over the paths of length `n`, evaluated on the coefficient matrices of `P` on
the `k` consecutive blocks of the coefficients of `N` along the path, is summing `f` over the paths
`w₀ → ⋯ → w_k` of the matrices `iterMatrix (j t)`: a path of length `n` is the concatenation of its
blocks, and the sum over the paths of length `j t` between two generators is the iterate
`δ^{j t}` of `N`. -/
private theorem sum_pathBlock {W : Type*} [AddCommGroup W] [Module R W] (k : ℕ) (j : Fin k → ℕ)
    (f : MultilinearMap (RingHom.id R) (fun _ : Fin k => Matrix Y Y B) W) (a z : X) (n : ℕ)
    (hn : Fin.partialSum j (Fin.last k) = n) :
    ∑ x : Fin (n + 1) → X, (if x 0 = a ∧ x (Fin.last n) = z then
      f (fun t => P.coeff (j t) (pathBlock N x (Fin.partialSum j t.castSucc) (j t)
        (hn ▸ partialSum_castSucc_add_le j t))) else 0) =
    ∑ w : Fin (k + 1) → X, if w 0 = a ∧ w (Fin.last k) = z then
      f (fun t => P.iterMatrix N (j t) (w t.castSucc) (w t.succ)) else 0 := by
  induction k generalizing n z with
  | zero =>
    obtain rfl : n = 0 := by rw [← hn]; rfl
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    funext t
    exact t.elim0
  | succ k ih =>
    have hps : Fin.partialSum j (Fin.last (k + 1)) =
        Fin.partialSum (Fin.init j) (Fin.last k) + j (Fin.last k) := by
      rw [← Fin.succ_last, Fin.partialSum_succ, Fin.partialSum_init]
    obtain rfl := hn.symm.trans hps
    refine (sum_pathBlock_snoc_left P N j f a z hps).trans ?_
    rw [sum_iterMatrix_snoc P N j f a z,
      Finset.sum_congr rfl fun m _ => (ih (Fin.init j) _ m _ rfl).symm, sum_iterMatrix_last]

/-- Under either boundedness hypothesis the matrices `iterMatrix len` vanish from some length
on. -/
private theorem exists_iterMatrix_eq_zero (h : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) :
    ∃ J, 1 ≤ J ∧ ∀ len, J ≤ len → P.iterMatrix N len = 0 := by
  rcases h with hN | ⟨K, hK⟩
  · obtain ⟨J, hJ⟩ := N.isBounded_iff.mp hN
    exact ⟨J + 1, by omega, fun len hlen => Matrix.ext fun x x' => by
      simp [iterMatrix, hJ len (by omega)]⟩
  · exact ⟨K + 1, by omega, fun len hlen => Matrix.ext fun x x' => by
      simp [iterMatrix, hK len (by omega)]⟩

/-- A path cut into `k < K` blocks of lengths less than `J` has length less than `K * J`. -/
private theorem partialSum_last_lt_mul {k K J : ℕ} (hk : k < K) (hJ : 1 ≤ J) {j : Fin k → ℕ}
    (hj : j ∈ Fintype.piFinset fun _ : Fin k => range J) :
    Fin.partialSum j (Fin.last k) < K * J := by
  have := Fin.partialSum_le_nsmul (c := J - 1)
    (fun t => Nat.le_sub_one_of_lt (Finset.mem_range.mp (Fintype.mem_piFinset.mp hj t)))
    (Fin.last k)
  rw [Fin.val_last, smul_eq_mul] at this
  have hlt : k * (J - 1) < K * J :=
    (Nat.mul_le_mul_left k (Nat.sub_le J 1)).trans_lt (Nat.mul_lt_mul_of_pos_right hk hJ)
  omega

section Assoc

variable [DecidableEq Y] {M : Type*} [AddCommGroup M] [Module R M]
  (Mm : UngradedAInfinityRightModule dB M)

/-- A cut point sequence from partial sums. -/
private def cutOfPartialSum {k n : ℕ} (j : Fin k → ℕ) (hn : Fin.partialSum j (Fin.last k) = n)
    (t : Fin (k + 1)) : Fin (n + 1) :=
  ⟨Fin.partialSum j t,
    Nat.lt_succ_of_le (hn ▸ Fin.monotone_partialSum (fun _ => Nat.zero_le _) (Fin.le_last t))⟩

/-- The summand `T` of the operations of `M ⊠ P` along the coefficients of paths, at a cut. -/
private noncomputable def cutTerm {k n : ℕ} (φ : X → Y → M) (z : X) (y' : Y)
    (c : Fin (k + 1) → Fin (n + 1)) : M :=
  ∑ x : Fin (n + 1) → X with x (Fin.last n) = z,
    (Mm.matrix Y).act k (fun t => P.blockMatrix (fun l => N.coeff (x l.castSucc) (x l.succ))
      (c t.castSucc) (c t.succ)) (φ (x 0)) y'

/-- A cut of the inputs with a decreasing step contributes nothing. -/
private theorem cutTerm_eq_zero {k n : ℕ} (φ : X → Y → M) (z : X) (y' : Y)
    {c : Fin (k + 1) → Fin (n + 1)} (hc : ¬ Monotone c) : P.cutTerm N Mm φ z y' c = 0 := by
  obtain ⟨t, ht⟩ : ∃ t : Fin k, c t.succ < c t.castSucc := by
    by_contra! h
    exact hc (Fin.monotone_iff_le_succ.mpr h)
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [((Mm.matrix Y).act k).map_coord_zero t (P.blockMatrix_apply_of_lt _ ht),
    LinearMap.zero_apply, Pi.zero_apply]

/-- The contribution of the cut at the partial sums of `j` is the operation of the matrix module
of the matrix module of `M` along the matrices `iterMatrix (j t)`. -/
private theorem cutTerm_cutOfPartialSum {k n : ℕ} (j : Fin k → ℕ)
    (hn : Fin.partialSum j (Fin.last k) = n) (φ : X → Y → M) (z : X) (y' : Y) :
    P.cutTerm N Mm φ z y' (cutOfPartialSum j hn) =
      (Mm.matrix Y).matrixAct X k (fun t => P.iterMatrix N (j t)) φ z y' := by
  rw [UngradedAInfinityRightModule.matrixAct_apply, Finset.sum_apply, cutTerm,
    Finset.sum_filter]
  -- Sort the paths by their starting points.
  rw [← Finset.sum_fiberwise (s := univ) (g := fun x : Fin (n + 1) → X => x 0),
    ← Finset.sum_fiberwise (s := univ) (g := fun w : Fin (k + 1) → X => w 0)]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hFC := P.sum_pathBlock N k j
    ((LinearMap.proj y' ∘ₗ LinearMap.applyₗ (φ a)).compMultilinearMap ((Mm.matrix Y).act k))
    a z n hn
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.applyₗ_apply_apply, LinearMap.coe_proj, Function.eval] at hFC
  simp only [Finset.sum_filter, apply_ite (fun m : Y → M => m y'), Pi.zero_apply, ← ite_and]
  refine Eq.trans (Finset.sum_congr rfl fun x _ => ?_) (hFC.trans (Finset.sum_congr rfl
    fun w _ => ?_))
  · split_ifs with h
    · have hblock : (fun t => P.blockMatrix (fun l => N.coeff (x l.castSucc) (x l.succ))
          (cutOfPartialSum j hn t.castSucc) (cutOfPartialSum j hn t.succ)) =
          fun t => P.coeff (j t) (pathBlock N x (Fin.partialSum j t.castSucc) (j t)
            (hn ▸ partialSum_castSucc_add_le j t)) :=
        funext fun t => P.blockMatrix_eq_pathBlock N x rfl (Fin.partialSum_succ j t) _
      rw [h.1, hblock]
    · rfl
  · split_ifs with h
    · rw [h.1]
    · rfl

/-- **Cuts are compositions.** The nondecreasing cuts `0 = c₀ ≤ ⋯ ≤ c_k = n` are the partial sums
of the tuples of block lengths `j` with total `n`, and the contribution of a cut vanishes unless it
is nondecreasing with blocks shorter than the bound `J` of the iterates. -/
private theorem sum_cutTerm (k n J : ℕ) (hJ : ∀ len, J ≤ len → P.iterMatrix N len = 0)
    (φ : X → Y → M) (z : X) (y' : Y) :
    ∑ c : Fin (k + 1) → Fin (n + 1) with c 0 = 0 ∧ c (Fin.last k) = Fin.last n,
      P.cutTerm N Mm φ z y' c =
    ∑ j ∈ Fintype.piFinset (fun _ : Fin k => range J) with Fin.partialSum j (Fin.last k) = n,
      (Mm.matrix Y).matrixAct X k (fun t => P.iterMatrix N (j t)) φ z y' := by
  symm
  refine Finset.sum_bij_ne_zero (fun j hj _ => cutOfPartialSum j (Finset.mem_filter.mp hj).2)
    (fun j hj _ => ?_) (fun j₁ _ _ j₂ _ _ h => funext fun t => ?_) (fun c hc hT => ?_)
    (fun j hj _ => (P.cutTerm_cutOfPartialSum N Mm j _ φ z y').symm)
  · simp only [Finset.mem_filter, Finset.mem_univ, Fin.ext_iff, cutOfPartialSum,
      Fin.partialSum_zero, Fin.val_zero, Fin.val_last, (Finset.mem_filter.mp hj).2, and_self]
  · have := congrArg (fun c : Fin (k + 1) → Fin (n + 1) => (c t.succ : ℕ) - c t.castSucc) h
    simpa [cutOfPartialSum, Fin.partialSum_succ] using this
  · obtain ⟨hc0, hcl⟩ := (Finset.mem_filter.mp hc).2
    have hmono : Monotone c := by
      by_contra hm
      exact hT (P.cutTerm_eq_zero N Mm φ z y' hm)
    set j : Fin k → ℕ := fun t => (c t.succ : ℕ) - c t.castSucc with hj
    have hps (t : Fin (k + 1)) : Fin.partialSum j t = c t := by
      induction t using Fin.induction with
      | zero => simp [hc0]
      | succ t ih =>
        have := Fin.le_def.mp (hmono (Fin.castSucc_le_succ t))
        rw [Fin.partialSum_succ, ih]
        simp only [hj]
        omega
    have hjn : Fin.partialSum j (Fin.last k) = n := by rw [hps, hcl, Fin.val_last]
    have hcj : cutOfPartialSum j hjn = c := funext fun t => Fin.ext (hps t)
    have hH : (Mm.matrix Y).matrixAct X k (fun t => P.iterMatrix N (j t)) φ z y' ≠ 0 := by
      rwa [← P.cutTerm_cutOfPartialSum N Mm j hjn, hcj]
    refine ⟨j, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun t => Finset.mem_range.mpr ?_,
      hjn⟩, hH, hcj⟩
    by_contra hJt
    exact hH (by rw [((Mm.matrix Y).matrixAct X k).map_coord_zero t (hJ _ (not_lt.mp hJt)),
      LinearMap.zero_apply, Pi.zero_apply, Pi.zero_apply])

variable [CharP R 2]

/-- The operations of `M ⊠ P` along the coefficients of `N`, on paths of length `n`, sum the
operations of the matrix module of the matrix module of `M` along the matrices `iterMatrix`, over
the tuples of block lengths with total `n`. -/
private theorem typeABoxModule_matrixAct_apply (hM : ∃ K, ∀ k, K ≤ k → Mm.act k = 0) {K J : ℕ}
    (hK : ∀ k, K ≤ k → Mm.act k = 0) (hJ : ∀ len, J ≤ len → P.iterMatrix N len = 0) (n : ℕ)
    (φ : X → Y → M) (z : X) (y' : Y) :
    (P.typeABoxModule Mm hM).matrixAct X n (fun _ => N.coeff) φ z y' =
      ∑ k ∈ range K, ∑ j ∈ Fintype.piFinset (fun _ : Fin k => range J)
        with Fin.partialSum j (Fin.last k) = n,
        (Mm.matrix Y).matrixAct X k (fun t => P.iterMatrix N (j t)) φ z y' := by
  simp_rw [← P.sum_cutTerm N Mm _ n J hJ φ z y', cutTerm]
  rw [UngradedAInfinityRightModule.matrixAct_apply, Finset.sum_apply]
  simp only [typeABoxModule_act, P.typeABoxAct_apply Mm hK, apply_ite (fun m : Y → M => m y'),
    Finset.sum_apply, Pi.zero_apply]
  simp only [← Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Finset.sum_comm

/-- **Associativity of the box tensor product, on row vectors.** For an `A∞` right module `M`
over `B` whose operations vanish from some arity on, a type `DA` bimodule `P = ^B P_A` and a type
`D` structure `N` over `A`, one of `N` and `P` bounded, the box tensor differential of the type `A`
module `M ⊠ P` with `N` is the differential of the matrix module of `M` over the generators
`y ⊗ x` twisted by the coefficient matrix of `P ⊠ N`: on a row vector `φ`, standing for
`∑ m ⊗ y ⊗ x` with coefficients `φ x y`, both sides agree at every generator `y' ⊗ z`. -/
theorem typeABoxDifferential_typeABoxModule_apply (hM : ∃ K, ∀ k, K ≤ k → Mm.act k = 0)
    (h : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) (φ : X → Y → M) (z : X) (y' : Y) :
    N.typeABoxDifferential (P.typeABoxModule Mm hM) φ z y' =
      (Mm.matrix (Y × X)).twistedDifferential (P.boxCoeff N) (fun p => φ p.2 p.1) (y', z) := by
  obtain ⟨K, hK⟩ := hM
  obtain ⟨J, hJ1, hJ⟩ := P.exists_iterMatrix_eq_zero N h
  -- Paths of `N` cut into fewer than `K` blocks of lengths less than `J` have length less than
  -- `K * J`, so the operations of `M ⊠ P` along the coefficients of `N` vanish from there on.
  have hvanish (n : ℕ) (hn : K * J ≤ n) :
      (P.typeABoxModule Mm ⟨K, hK⟩).matrixAct X n (fun _ => N.coeff) = 0 := by
    refine LinearMap.ext fun φ => funext fun z => funext fun y' => ?_
    rw [P.typeABoxModule_matrixAct_apply N Mm _ hK hJ]
    refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun j hj => ?_
    obtain ⟨hjJ, hjn⟩ := Finset.mem_filter.mp hj
    exact absurd (hjn ▸ partialSum_last_lt_mul (Finset.mem_range.mp hk) hJ1 hjJ) (not_lt.mpr hn)
  have hKY (k : ℕ) (hk : K ≤ k) : ((Mm.matrix (Y × X)).act k fun _ => P.boxCoeff N) = 0 := by
    rw [UngradedAInfinityRightModule.matrix_act,
      Mm.matrixAct_eq_zero_of_act_eq_zero _ (hK k hk)]
    rfl
  rw [TypeDStructure.typeABoxDifferential_def,
    UngradedAInfinityRightModule.twistedDifferential_eq_sum _ (K := K * J) fun n hn => by
      rw [UngradedAInfinityRightModule.matrix_act, hvanish n hn],
    UngradedAInfinityRightModule.twistedDifferential_eq_sum _ hKY]
  have hC : (Matrix.of fun x x' => (P.boxCoeff N).submatrix (·, x) (·, x')) =
      ∑ len ∈ range J, P.iterMatrix N len := by
    ext x x' y y'
    rw [Matrix.of_apply, Matrix.submatrix_apply,
      P.boxCoeff_eq_sum N (K := J) fun len hlen x x' => by
      simpa [iterMatrix] using congrFun (congrFun (hJ len hlen) x) x']
    simp [iterMatrix, Matrix.sum_apply]
  simp only [LinearMap.sum_apply, Finset.sum_apply, UngradedAInfinityRightModule.matrix_act,
    P.typeABoxModule_matrixAct_apply N Mm _ hK hJ,
    UngradedAInfinityRightModule.matrixAct_prod_apply,
    hC, MultilinearMap.map_sum_finset]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_range.mpr
    (partialSum_last_lt_mul (Finset.mem_range.mp hk) hJ1 hj)) _

/-- **Associativity of the box tensor product**, `(M ⊠ P) ⊠ N = M ⊠ (P ⊠ N)`, for an `A∞` module
`M` whose operations vanish from some arity on: the box tensor differential of the type `A` module
`M ⊠ P` with `N` is the box tensor differential of `M` with the type `D` structure `P ⊠ N`, under
the identification of the row vectors `X → Y → M` with the row vectors `Y × X → M`. -/
theorem typeABoxDifferential_typeABoxModule (hdB : IsUngradedDGAlgebra dB)
    (hM : ∃ K, ∀ k, K ≤ k → Mm.act k = 0) (h : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (φ : X → Y → M) (z : X) (y' : Y) :
    N.typeABoxDifferential (P.typeABoxModule Mm hM) φ z y' =
      (P.boxTypeD N hdB h).typeABoxDifferential Mm (fun p => φ p.2 p.1) (y', z) := by
  rw [P.typeABoxDifferential_typeABoxModule_apply N Mm hM h,
    TypeDStructure.typeABoxDifferential_def, boxTypeD_coeff]

end Assoc

end TypeDAStructure

end TauCeti
