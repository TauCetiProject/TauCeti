/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.TypeDA.Basic
import TauCeti.Data.Fin.Basic
import TauCeti.Data.Fin.Crossing
import TauCeti.Data.Fin.Tuple.Basic
import TauCeti.Data.Matrix.Update

/-!
# The box tensor product of a type `A` module with a type `DA` bimodule

Gluing a bordered three-manifold with one boundary component to one with two boundary components
gives a bordered three-manifold whose type `A` module is the box tensor product `M ⊠ P` of the type
`A` module `M` of the first with the type `DA` bimodule `P` of the second. This file constructs
`M ⊠ P` for an `A∞` right module `M` over `(B, dB)` whose operations vanish from some arity on,
and a type `DA` bimodule `P = ^B P_A` (`TauCeti.TypeDAStructure`), over a ring of characteristic
two. For a differential module `M` this is `TauCeti.TypeDAStructure.boxModule`.

In a basis `Y` of generators of `P`, the elements of `M ⊠ P` are the row vectors `ψ : Y → M`,
standing for `∑ y, ψ y ⊗ y`. The operation `m_{n+1}(ψ, a₁, …, aₙ)` of `M ⊠ P` cuts `a₁, …, aₙ`
into `k` consecutive, possibly empty, blocks, feeds each block to the operations `δ¹` of `P`, and
the resulting `k` coefficient matrices to the operation `m_{k+1}` of `M`:

`m_{n+1}(ψ, a₁, …, aₙ) = ∑_k ∑_{0 = x₀ ≤ x₁ ≤ ⋯ ≤ x_k = n}`
`  m_{k+1}(ψ, δ(a_{x₀+1}, …, a_{x₁}), …, δ(a_{x_{k-1}+1}, …, a_{x_k}))`,

where `m_{k+1}` is the operation of the matrix module of `M`
(`TauCeti.UngradedAInfinityRightModule.matrix`) over `Matrix Y Y B`. Empty blocks contribute the
coefficient matrix `δ₀` of `δ¹₁`, which may appear any number of times; the sum is finite because
the operations of `M` vanish from some arity on.

The cuts are the paths from `0` to `n` along the **block matrix** of `a₁, …, aₙ`
(`TauCeti.TypeDAStructure.blockMatrix`), indexed by `0, …, n`, whose entry from `x` to `x' ≥ x` is
the coefficient matrix of the block `a_{x+1}, …, a_{x'}`. So `m_{n+1}(ψ, a)` is the component at
`n` of the differential of the matrix module over `0, …, n` twisted by the block matrix, applied to
`ψ` placed at `0` (`TauCeti.TypeDAStructure.typeABoxAct_apply_eq_twistedDifferential`). This is how
the `A∞` relations are proved, with no bookkeeping of cuts:

* the composite terms of the relation of length `n` are the component at `n` of the square of the
  twisted differential, since composing the operations on `a₁, …, aᵢ` and on `aᵢ₊₁, …, aₙ` is
  passing through `i` along the paths from `0` to `n`;
* the square of a twisted differential inserts the curvature `d Γ + Γ * Γ` of the block matrix `Γ`
  once (`TauCeti.UngradedAInfinityRightModule.twistedDifferential_twistedDifferential_eq_sum`);
* the entry of `Γ * Γ` from `x` to `x'` cuts the block between them in two, so by the structure
  relations of `P` the curvature is the matrix of the differential and product terms of the blocks;
* inserting these once gives the differential and product terms of the relation: a product
  `aᵢ aᵢ₊₁` inside a block is a product in the contracted tuple, along a path that does not stop
  at `i + 1`.

## Main definitions

* `TauCeti.TypeDAStructure.blockMatrix`: the block matrix of a tuple of inputs.
* `TauCeti.TypeDAStructure.typeABoxAct`: the operations of `M ⊠ P`.
* `TauCeti.TypeDAStructure.typeABoxModule`: the `A∞` module `M ⊠ P`.

## Main results

* `TauCeti.TypeDAStructure.typeABoxAct_apply`: the operations of `M ⊠ P` as sums over cuts.
* `TauCeti.TypeDAStructure.typeABoxAct_apply_eq_twistedDifferential`: the operations of `M ⊠ P` as
  a twisted differential along the block matrix.
* `TauCeti.TypeDAStructure.blockMatrix_mul_blockMatrix_apply_of_le`: products of block matrices
  are the composite terms of the structure relations of `P`.
* `TauCeti.TypeDAStructure.typeABoxModule_toUngradedAInfinityRightModule`: for a differential module
  `M`, `M ⊠ P` is `TauCeti.TypeDAStructure.boxModule`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bimodules in bordered Heegaard Floer homology*,
  Geom. Topol. **19** (2015), 525–724, [arXiv:1003.0598](https://arxiv.org/abs/1003.0598), §2.3
  (box tensor products of type `A` modules with type `DA` bimodules, and their boundedness
  hypotheses).
-/

public section

open Finset MulOpposite

namespace TauCeti

namespace TypeDAStructure

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {S : Type*} {ιB : S → B} {Y : Type*} [Fintype Y]
  (P : TypeDAStructure dA dB ιB Y)

/-- The **block matrix** of a tuple `a₁, …, aₙ`: the matrix indexed by `0, …, n` whose entry
from `x` to `x' ≥ x` is the coefficient matrix `δ_{x' - x}(a_{x+1}, …, a_{x'})` of the block of
inputs between `x` and `x'`, and whose entries below the diagonal vanish. A path from `0` to `n`
along its nonzero entries cuts `a₁, …, aₙ` into consecutive, possibly empty, blocks. -/
noncomputable def blockMatrix {n : ℕ} (a : Fin n → A) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (Matrix Y Y B) := fun x x' =>
  if h : (x : ℕ) ≤ x' then
    P.coeff ((x' : ℕ) - x) fun l => a ⟨x + l, by have := x'.isLt; have := l.isLt; omega⟩
  else 0

/-- The entries of the block matrix: coefficient matrices of blocks on and above the diagonal,
zero below it. -/
theorem blockMatrix_apply {n : ℕ} (a : Fin n → A) (x x' : Fin (n + 1)) :
    P.blockMatrix a x x' = if h : (x : ℕ) ≤ x' then
      P.coeff ((x' : ℕ) - x) (fun l => a ⟨x + l, by have := x'.isLt; have := l.isLt; omega⟩)
    else 0 :=
  (rfl)

/-- The entries of the block matrix below the diagonal vanish. -/
theorem blockMatrix_apply_of_lt {n : ℕ} (a : Fin n → A) {x x' : Fin (n + 1)} (h : x' < x) :
    P.blockMatrix a x x' = 0 :=
  dite_eq_right (not_le.mpr h)

/-- The entry of the block matrix from `x` to `x' ≥ x` is the coefficient matrix of the block of
inputs between `x` and `x'`. -/
theorem blockMatrix_apply_of_le {n : ℕ} (a : Fin n → A) {x x' : Fin (n + 1)} (h : (x : ℕ) ≤ x') :
    P.blockMatrix a x x' =
      P.coeff ((x' : ℕ) - x) (fun l => a ⟨x + l, by have := x'.isLt; have := l.isLt; omega⟩) :=
  dite_eq_left h

/-- Changing an input outside the block from `x` to `x'` does not change the entry. -/
private theorem blockMatrix_update_of_not_le_lt {n : ℕ} (a : Fin n → A) {i : Fin n} (u : A)
    {x x' : Fin (n + 1)} (h : ¬ ((x : ℕ) ≤ i ∧ (i : ℕ) < x')) :
    P.blockMatrix (Function.update a i u) x x' = P.blockMatrix a x x' := by
  simp only [blockMatrix_apply]
  split_ifs with hxx'
  · congr 1
    funext l
    refine Function.update_of_ne (fun heq => h ?_) _ _
    have := congrArg Fin.val heq
    simp only at this
    omega
  · rfl

/-- Changing an input inside the block from `x` to `x'` changes the corresponding input of the
coefficient. -/
private theorem blockMatrix_update_of_le_lt {n : ℕ} (a : Fin n → A) {i : Fin n} (u : A)
    {x x' : Fin (n + 1)} (h : (x : ℕ) ≤ i ∧ (i : ℕ) < x') :
    P.blockMatrix (Function.update a i u) x x' =
      P.coeff ((x' : ℕ) - x) (Function.update
        (fun l => a ⟨x + l, by have := x'.isLt; have := l.isLt; omega⟩)
        ⟨i - x, by omega⟩ u) := by
  rw [blockMatrix_apply_of_le P _ (by omega)]
  congr 1
  funext l
  simp only [Function.update_apply, Fin.ext_iff]
  split_ifs with h₁ h₂ h₂
  · rfl
  · omega
  · omega
  · rfl

private theorem blockMatrix_update_add {n : ℕ} (a : Fin n → A) {i : Fin n} (u v : A)
    {x x' : Fin (n + 1)} (h : (x : ℕ) ≤ i ∧ (i : ℕ) < x') :
    P.blockMatrix (Function.update a i (u + v)) x x' =
      P.blockMatrix (Function.update a i u) x x' + P.blockMatrix (Function.update a i v) x x' := by
  simp only [P.blockMatrix_update_of_le_lt a _ h, MultilinearMap.map_update_add]

private theorem blockMatrix_update_smul {n : ℕ} (a : Fin n → A) {i : Fin n} (c : R) (u : A)
    {x x' : Fin (n + 1)} (h : (x : ℕ) ≤ i ∧ (i : ℕ) < x') :
    P.blockMatrix (Function.update a i (c • u)) x x' =
      c • P.blockMatrix (Function.update a i u) x x' := by
  simp only [P.blockMatrix_update_of_le_lt a _ h, MultilinearMap.map_update_smul, RingHom.id_apply]

/-- Along a path from `0` to `n` without decreasing steps, changing the input `aᵢ` changes only
the entry of the step across `i`. -/
private theorem blockMatrix_update_comp {n k : ℕ} (a : Fin n → A) {i : Fin n} (u : A)
    {x : Fin (k + 1) → Fin (n + 1)} {l : Fin k}
    (huniq : ∀ l' : Fin k, (x l'.castSucc : ℕ) ≤ i ∧ (i : ℕ) < x l'.succ → l' = l) :
    (fun t : Fin k => P.blockMatrix (Function.update a i u) (x t.castSucc) (x t.succ)) =
      Function.update (fun t : Fin k => P.blockMatrix a (x t.castSucc) (x t.succ)) l
        (P.blockMatrix (Function.update a i u) (x l.castSucc) (x l.succ)) := by
  funext t
  rcases eq_or_ne t l with rfl | ht
  · rw [Function.update_self]
  · rw [Function.update_of_ne ht,
      P.blockMatrix_update_of_not_le_lt a u fun h => ht (huniq t h)]

variable [DecidableEq Y] {M : Type*} [AddCommGroup M] [Module R M]
  (Mm : UngradedAInfinityRightModule dB M)

/-- Along a path with a decreasing step, the operation of the matrix module along the block
matrix vanishes: the entry of that step lies below the diagonal. -/
private theorem act_blockMatrix_eq_zero_of_lt {n k : ℕ} (w : Fin n → A)
    {x : Fin (k + 1) → Fin (n + 1)} {l : Fin k} (hl : x l.succ < x l.castSucc) :
    (Mm.matrix Y).act k (fun t => P.blockMatrix w (x t.castSucc) (x t.succ)) = 0 :=
  ((Mm.matrix Y).act k).map_coord_zero l (P.blockMatrix_apply_of_lt w hl)

/-- Along a path with a decreasing step `l₀`, the operation of the matrix module along the block
matrix with the entry of a step `l` replaced by `G` vanishes, provided `G = 0` when `l = l₀`. -/
private theorem act_update_blockMatrix_eq_zero_of_lt {n k : ℕ} (w : Fin n → A)
    {x : Fin (k + 1) → Fin (n + 1)} {l₀ : Fin k} (hl₀ : x l₀.succ < x l₀.castSucc) (l : Fin k)
    {G : Matrix Y Y B} (hG : l = l₀ → G = 0) :
    (Mm.matrix Y).act k
      (Function.update (fun t => P.blockMatrix w (x t.castSucc) (x t.succ)) l G) = 0 := by
  rcases eq_or_ne l l₀ with rfl | hl
  · exact ((Mm.matrix Y).act k).map_coord_zero l (by rw [Function.update_self, hG rfl])
  · exact ((Mm.matrix Y).act k).map_coord_zero l₀
      (by rw [Function.update_of_ne hl.symm, P.blockMatrix_apply_of_lt w hl₀])

/-- The operation of the matrix module along a path from `0` to `n` is additive in each input. -/
private theorem act_blockMatrix_update_add {n k : ℕ} (a : Fin n → A) (i : Fin n) (u v : A)
    {x : Fin (k + 1) → Fin (n + 1)} (hx0 : x 0 = 0) (hxl : x (Fin.last k) = Fin.last n) :
    (Mm.matrix Y).act k (fun t => P.blockMatrix (Function.update a i (u + v)) (x t.castSucc)
        (x t.succ)) =
      (Mm.matrix Y).act k (fun t => P.blockMatrix (Function.update a i u) (x t.castSucc)
        (x t.succ)) +
      (Mm.matrix Y).act k (fun t => P.blockMatrix (Function.update a i v) (x t.castSucc)
        (x t.succ)) := by
  rcases Fin.exists_succ_lt_castSucc_or_existsUnique_castSucc_le_and_lt_succ (fun t => (x t : ℕ))
      (c := i) (by simp [hx0]) (by simp [hxl]) with ⟨l, hl⟩ | ⟨l, hl, huniq⟩
  · simp only [P.act_blockMatrix_eq_zero_of_lt Mm _ (Fin.lt_def.mpr hl), add_zero]
  · rw [P.blockMatrix_update_comp a _ huniq, P.blockMatrix_update_comp a _ huniq,
      P.blockMatrix_update_comp a _ huniq, P.blockMatrix_update_add a u v hl,
      MultilinearMap.map_update_add]

/-- The operation of the matrix module along a path from `0` to `n` is homogeneous in each
input. -/
private theorem act_blockMatrix_update_smul {n k : ℕ} (a : Fin n → A) (i : Fin n) (c : R) (u : A)
    {x : Fin (k + 1) → Fin (n + 1)} (hx0 : x 0 = 0) (hxl : x (Fin.last k) = Fin.last n) :
    (Mm.matrix Y).act k (fun t => P.blockMatrix (Function.update a i (c • u)) (x t.castSucc)
        (x t.succ)) =
      c • (Mm.matrix Y).act k (fun t => P.blockMatrix (Function.update a i u) (x t.castSucc)
        (x t.succ)) := by
  rcases Fin.exists_succ_lt_castSucc_or_existsUnique_castSucc_le_and_lt_succ (fun t => (x t : ℕ))
      (c := i) (by simp [hx0]) (by simp [hxl]) with ⟨l, hl⟩ | ⟨l, hl, huniq⟩
  · simp only [P.act_blockMatrix_eq_zero_of_lt Mm _ (Fin.lt_def.mpr hl), smul_zero]
  · rw [P.blockMatrix_update_comp a _ huniq, P.blockMatrix_update_comp a _ huniq,
      P.blockMatrix_update_smul a c u hl, MultilinearMap.map_update_smul, RingHom.id_apply]

/-- The part of the operation `m_{n+1}(ψ, a₁, …, aₙ)` of `M ⊠ P` coming from the cuts of
`a₁, …, aₙ` into `k` consecutive, possibly empty, blocks: the operation `m_{k+1}` of the matrix
module of `M` applied to `ψ` and the coefficient matrices `δ` of the blocks. -/
private noncomputable def blockAct (k n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A) ((Y → M) →ₗ[R] Y → M) where
  toFun a := LinearMap.proj (Fin.last n) ∘ₗ
    ((Mm.matrix Y).matrixAct (Fin (n + 1)) k fun _ => P.blockMatrix a) ∘ₗ
    LinearMap.single R (fun _ : Fin (n + 1) => Y → M) 0
  map_update_add' := by
    intro inst a i u v
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    refine LinearMap.ext fun ψ => ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval,
      LinearMap.coe_single, UngradedAInfinityRightModule.matrixAct_single_apply, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rw [act_blockMatrix_update_add P Mm a i u v hx.1 hx.2, LinearMap.add_apply]
    · rw [add_zero]
  map_update_smul' := by
    intro inst a i c u
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    refine LinearMap.ext fun ψ => ?_
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval,
      LinearMap.coe_single, UngradedAInfinityRightModule.matrixAct_single_apply, smul_sum]
    refine sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rw [act_blockMatrix_update_smul P Mm a i c u hx.1 hx.2, LinearMap.smul_apply,
        RingHom.id_apply]
    · rw [smul_zero]

private theorem blockAct_apply (k n : ℕ) (a : Fin n → A) (ψ : Y → M) :
    P.blockAct Mm k n a ψ =
      ((Mm.matrix Y).matrixAct (Fin (n + 1)) k fun _ => P.blockMatrix a) (Pi.single 0 ψ)
        (Fin.last n) :=
  (rfl)

private theorem blockAct_eq_zero {k : ℕ} (h : Mm.act k = 0) (n : ℕ) :
    P.blockAct Mm k n = 0 := by
  have h' : (Mm.matrix Y).matrixAct (Fin (n + 1)) k = 0 :=
    (Mm.matrix Y).matrixAct_eq_zero_of_act_eq_zero _ (by
      rw [UngradedAInfinityRightModule.matrix_act]
      exact Mm.matrixAct_eq_zero_of_act_eq_zero Y h)
  refine MultilinearMap.ext fun a => LinearMap.ext fun ψ => ?_
  simp [blockAct_apply, h']

/-- The operation `m_{n+1}` of `M ⊠ P`: the sum, over the cuts of `a₁, …, aₙ` into `k`
consecutive, possibly empty, blocks, of the operation `m_{k+1}` of the matrix module of `M` on `ψ`
and the coefficient matrices `δ` of the blocks (`TauCeti.TypeDAStructure.typeABoxAct_apply`). The
sum is finite when the operations of `M` vanish from some arity on; otherwise this `finsum` is `0`
by convention. -/
noncomputable def typeABoxAct (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A) ((Y → M) →ₗ[R] Y → M) :=
  ∑ᶠ k, P.blockAct Mm k n

private theorem typeABoxAct_eq_sum {K : ℕ} (hK : ∀ k, K ≤ k → Mm.act k = 0) (n : ℕ) :
    P.typeABoxAct Mm n = ∑ k ∈ range K, P.blockAct Mm k n := by
  refine finsum_eq_sum_of_support_subset _ fun k hk => ?_
  simp only [coe_range, Set.mem_Iio]
  by_contra hlt
  exact hk (P.blockAct_eq_zero Mm (hK k (not_lt.mp hlt)) n)

/-- The operations of the matrix module of the matrix module vanish with those of `M`. -/
private theorem matrix_matrix_act_eq_zero {K : ℕ} (hK : ∀ k, K ≤ k → Mm.act k = 0) (n : ℕ)
    {k : ℕ} (hk : K ≤ k) : ((Mm.matrix Y).matrix (Fin (n + 1))).act k = 0 := by
  rw [UngradedAInfinityRightModule.matrix_act]
  exact (Mm.matrix Y).matrixAct_eq_zero_of_act_eq_zero _ (by
    rw [UngradedAInfinityRightModule.matrix_act]
    exact Mm.matrixAct_eq_zero_of_act_eq_zero Y (hK k hk))

/-- **The operations of `M ⊠ P` as a twisted differential.** The operation `m_{n+1}(ψ, a)` is the
component at `n` of the differential of the matrix module over `0, …, n`, twisted by the block
matrix of `a`, applied to `ψ` placed at `0`. -/
theorem typeABoxAct_apply_eq_twistedDifferential {K : ℕ} (hK : ∀ k, K ≤ k → Mm.act k = 0)
    (n : ℕ) (a : Fin n → A) (ψ : Y → M) :
    P.typeABoxAct Mm n a ψ = ((Mm.matrix Y).matrix (Fin (n + 1))).twistedDifferential
      (P.blockMatrix a) (Pi.single 0 ψ) (Fin.last n) := by
  rw [P.typeABoxAct_eq_sum Mm hK, ((Mm.matrix Y).matrix (Fin (n + 1))).twistedDifferential_eq_sum
    (K := K) fun k hk => by rw [matrix_matrix_act_eq_zero (Y := Y) Mm hK n hk, zero_apply]]
  simp only [_root_.sum_apply, LinearMap.sum_apply, Finset.sum_apply,
    blockAct_apply, UngradedAInfinityRightModule.matrix_act]

/-- The paths of the block matrix ending at `j` stay below `j`: the component at `j` of the
operations along the block matrix of `a₁, …, aₙ`, on a row vector at `0`, are those along the
block matrix of `a₁, …, aⱼ`. -/
private theorem matrixAct_blockMatrix_single_apply_castLE {n k : ℕ} (a : Fin n → A)
    (j : Fin (n + 1)) (ψ : Y → M) :
    ((Mm.matrix Y).matrixAct (Fin (n + 1)) k fun _ => P.blockMatrix a) (Pi.single 0 ψ) j =
      ((Mm.matrix Y).matrixAct (Fin (j + 1)) k fun _ =>
        P.blockMatrix (fun l : Fin j => a ⟨l, by have := j.isLt; omega⟩)) (Pi.single 0 ψ)
        (Fin.last j) := by
  have hj : (j : ℕ) + 1 ≤ n + 1 := j.isLt
  have he : Function.Injective (Fin.castLE hj) := Fin.castLE_injective hj
  have hz : j = Fin.castLE hj (Fin.last j) := Fin.ext rfl
  conv_lhs => rw [hz]
  rw [(Mm.matrix Y).matrixAct_apply_of_injective he _
    (fun _ => P.blockMatrix (fun l : Fin j => a ⟨l, by have := j.isLt; omega⟩))
    (fun _ _ _ => rfl)]
  · rw [show (Pi.single 0 ψ ∘ Fin.castLE hj : Fin (j + 1) → Y → M) = Pi.single 0 ψ from
      funext fun x => by
        rw [Function.comp_apply, Pi.single_apply, Pi.single_apply]
        exact if_congr (by rw [Fin.ext_iff, Fin.ext_iff]; simp) rfl rfl]
  · intro _ x y hx
    refine P.blockMatrix_apply_of_lt a ?_
    rw [Fin.lt_def]
    by_contra hxy
    exact hx ⟨⟨x, by have := y.isLt; simp only [Fin.val_castLE] at hxy; omega⟩, Fin.ext rfl⟩

/-- The paths of the block matrix starting at `j` stay above `j`: the component at `n` of the
operations along the block matrix of `a₁, …, aₙ`, on a row vector at `j`, are those along the
block matrix of `aⱼ₊₁, …, aₙ`. -/
private theorem matrixAct_blockMatrix_single_apply_last {n k : ℕ} (a : Fin n → A)
    (j : Fin (n + 1)) (ψ : Y → M) :
    ((Mm.matrix Y).matrixAct (Fin (n + 1)) k fun _ => P.blockMatrix a) (Pi.single j ψ)
        (Fin.last n) =
      ((Mm.matrix Y).matrixAct (Fin (n - j + 1)) k fun _ =>
        P.blockMatrix (fun l : Fin (n - j) => a ⟨j + l, by omega⟩)) (Pi.single 0 ψ)
        (Fin.last (n - j)) := by
  have hjn : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.isLt
  set e : Fin (n - j + 1) → Fin (n + 1) := fun x => ⟨j + x, by omega⟩ with he_def
  have he : Function.Injective e := fun x y h => Fin.ext (by
    have := congrArg Fin.val h
    simp only [he_def] at this
    omega)
  have hz : Fin.last n = e (Fin.last (n - j)) := Fin.ext (by simp [he_def]; omega)
  conv_lhs => rw [hz]
  rw [(Mm.matrix Y).matrixAct_apply_of_injective_of_forall_notMem_range he _
    (fun _ => P.blockMatrix (fun l : Fin (n - j) => a ⟨j + l, by omega⟩))]
  · rw [show (Pi.single j ψ ∘ e : Fin (n - j + 1) → Y → M) = Pi.single 0 ψ from
      funext fun x => by
        rw [Function.comp_apply, Pi.single_apply, Pi.single_apply]
        exact if_congr (by rw [Fin.ext_iff, Fin.ext_iff]; simp [he_def]) rfl rfl]
  · intro _ x y
    simp only [blockMatrix_apply, he_def]
    by_cases h : (x : ℕ) ≤ y
    · rw [dite_eq_left (by omega), dite_eq_left h]
      exact P.coeff_congr (by omega) fun l => congrArg a (Fin.ext (by simp; omega))
    · rw [dite_eq_right (by omega), dite_eq_right h]
  · intro _ x y hy
    refine P.blockMatrix_apply_of_lt a ?_
    rw [Fin.lt_def]
    by_contra hxy
    exact hy ⟨⟨y - j, by simp only [he_def] at hxy; omega⟩,
      Fin.ext (by simp only [he_def] at hxy ⊢; omega)⟩
  · intro x hx
    refine Pi.single_eq_of_ne (fun h => hx ⟨0, ?_⟩) _
    rw [h]
    exact Fin.ext (by simp [he_def])

/-- **The composite terms of the `A∞` relations of `M ⊠ P`** are the component at `n` of the
square of the twisted differential along the block matrix: composing `m_{i+1}` on `a₁, …, aᵢ`
with `m_{n-i+1}` on `aᵢ₊₁, …, aₙ` is passing through `i` along the paths from `0` to `n`. -/
private theorem ungradedStasheffComp_typeABoxAct {K : ℕ} (hK : ∀ k, K ≤ k → Mm.act k = 0)
    (n : ℕ) (a : Fin n → A) (ψ : Y → M) :
    ungradedStasheffComp (P.typeABoxAct Mm) n a ψ =
      ((Mm.matrix Y).matrix (Fin (n + 1))).twistedDifferential (P.blockMatrix a)
        (((Mm.matrix Y).matrix (Fin (n + 1))).twistedDifferential (P.blockMatrix a)
          (Pi.single 0 ψ)) (Fin.last n) := by
  set D := ((Mm.matrix Y).matrix (Fin (n + 1))).twistedDifferential (P.blockMatrix a)
  have hDsum : D = ∑ k ∈ range K, ((Mm.matrix Y).matrix (Fin (n + 1))).act k
      fun _ => P.blockMatrix a :=
    ((Mm.matrix Y).matrix (Fin (n + 1))).twistedDifferential_eq_sum
      fun k hk => by rw [matrix_matrix_act_eq_zero (Y := Y) Mm hK n hk, zero_apply]
  -- The first operation ends at `j`, the second starts there.
  have hfirst (j : Fin (n + 1)) :
      P.typeABoxAct Mm j (fun l => a ⟨l, by have := j.isLt; omega⟩) ψ = D (Pi.single 0 ψ) j := by
    rw [P.typeABoxAct_eq_sum Mm hK, hDsum]
    simp only [_root_.sum_apply, LinearMap.sum_apply, Finset.sum_apply,
      blockAct_apply, UngradedAInfinityRightModule.matrix_act,
      P.matrixAct_blockMatrix_single_apply_castLE Mm a j]
  have hsecond (j : Fin (n + 1)) (ψ' : Y → M) :
      P.typeABoxAct Mm (n - j) (fun l => a ⟨j + l, by omega⟩) ψ' =
        D (Pi.single j ψ') (Fin.last n) := by
    rw [P.typeABoxAct_eq_sum Mm hK, hDsum]
    simp only [_root_.sum_apply, LinearMap.sum_apply, Finset.sum_apply,
      blockAct_apply, UngradedAInfinityRightModule.matrix_act,
      P.matrixAct_blockMatrix_single_apply_last Mm a j]
  rw [ungradedStasheffComp_def]
  simp only [hfirst, hsecond]
  rw [← Finset.sum_apply, ← map_sum, Finset.univ_sum_single]

omit [DecidableEq Y] in
/-- **Products of block matrices.** The entry from `x` to `x' ≥ x` of the square of the block
matrix is the composite term of the type `DA` relation on the block between `x` and `x'`: a path
`x → y → x'` cuts the block at `y`. -/
theorem blockMatrix_mul_blockMatrix_apply_of_le {n : ℕ} (a : Fin n → A) {x x' : Fin (n + 1)}
    (h : (x : ℕ) ≤ x') :
    (P.blockMatrix a * P.blockMatrix a) x x' = typeDAComp P.coeff ((x' : ℕ) - x)
      (fun l => a ⟨x + l, by have := x'.isLt; have := l.isLt; omega⟩) := by
  rw [Matrix.mul_apply, typeDAComp_def]
  symm
  refine Fintype.sum_of_injective (fun k : Fin ((x' : ℕ) - x + 1) =>
    (⟨x + k, by have := x'.isLt; have := k.isLt; omega⟩ : Fin (n + 1)))
    (fun k k' hk => Fin.ext (by have := congrArg Fin.val hk; simp only at this; omega)) _ _
    (fun y hy => ?_) fun k => ?_
  · -- Off the interval from `x` to `x'` one of the two entries vanishes.
    by_cases hxy : (x : ℕ) ≤ y
    · rw [P.blockMatrix_apply_of_lt a (x := y) (x' := x') ?_, Matrix.mul_zero]
      rw [Fin.lt_def]
      by_contra hyx
      exact hy ⟨⟨y - x, by omega⟩, Fin.ext (by simp only; omega)⟩
    · rw [P.blockMatrix_apply_of_lt a (Fin.lt_def.mpr (not_le.mp hxy)), Matrix.zero_mul]
  · rw [P.blockMatrix_apply_of_le a (by simp only; omega), P.blockMatrix_apply_of_le a (by
      simp only; have := k.isLt; omega)]
    congr 1
    · exact P.coeff_congr (by simp) fun l => congrArg a (Fin.ext (by simp))
    · exact P.coeff_congr (by simp only; omega) fun l => congrArg a (Fin.ext (by simp; omega))

omit [DecidableEq Y] in
/-- **The differential terms of a block, indexed by the inputs.** The differential term of the type
`DA` relation on the block between `x` and `x'` is the sum, over the inputs `aᵢ` of the block, of
the entries of the block matrix of the tuple with `aᵢ` replaced by `dA aᵢ`. -/
private theorem ungradedStasheffDiff_block {n : ℕ} (a : Fin n → A) {x x' : Fin (n + 1)}
    (h : (x : ℕ) ≤ x') :
    ungradedStasheffDiff P.coeff dA ((x' : ℕ) - x)
        (fun l => a ⟨x + l, by have := x'.isLt; have := l.isLt; omega⟩) =
      ∑ i : Fin n, if (x : ℕ) ≤ i ∧ (i : ℕ) < x' then
        P.blockMatrix (Function.update a i (dA (a i))) x x' else 0 := by
  rw [ungradedStasheffDiff_def]
  refine Fintype.sum_of_injective (fun l : Fin ((x' : ℕ) - x) =>
    (⟨x + l, by have := x'.isLt; have := l.isLt; omega⟩ : Fin n))
    (fun l l' hl => Fin.ext (by have := congrArg Fin.val hl; simp only at this; omega)) _ _
    (fun i hi => ?_) fun l => ?_
  · refine ite_eq_right ?_
    rintro ⟨h₁, h₂⟩
    exact hi ⟨⟨i - x, by omega⟩, Fin.ext (by simp only; omega)⟩
  · rw [ite_eq_left ⟨by simp, by simp only; have := l.isLt; omega⟩,
      P.blockMatrix_update_of_le_lt a _ ⟨by simp, by simp only; have := l.isLt; omega⟩]
    congr 2
    exact Fin.ext (by simp)

omit [DecidableEq Y] in
/-- **The product terms of a block, indexed by the inputs.** The product term of the type `DA`
relation on the block between `x` and `x'` is the sum, over the pairs `aᵢ, aᵢ₊₁` of consecutive
inputs of the block, of the entries from `x` to `x' - 1` of the block matrix of the tuple with
`aᵢ` and `aᵢ₊₁` replaced by `aᵢ aᵢ₊₁`. -/
private theorem ungradedStasheffMul_block {m : ℕ} (a : Fin (m + 1) → A) {x x' : Fin (m + 2)}
    (h : (x : ℕ) ≤ x') :
    (ungradedStasheffMul P.coeff ((x' : ℕ) - x)
        (fun l => a ⟨x + l, by have := x'.isLt; have := l.isLt; omega⟩) : Matrix Y Y B) =
      ∑ i : Fin m, if hi : (x : ℕ) ≤ i ∧ (i : ℕ) + 2 ≤ x' then
        P.blockMatrix (Fin.contractNth i.castSucc (· * ·) a) ⟨x, by omega⟩
          ⟨x' - 1, by have := x'.isLt; omega⟩ else 0 := by
  rcases Nat.eq_zero_or_pos ((x' : ℕ) - x) with hc | hc
  · refine (ungradedStasheffMul_congr P.coeff hc (a := fun l : Fin 0 => a ⟨x + l, by omega⟩)
      fun l => congrArg a (Fin.ext rfl)).trans ?_
    rw [ungradedStasheffMul_zero]
    exact (Finset.sum_eq_zero fun i _ => dite_eq_right (by omega)).symm
  obtain ⟨c, hc'⟩ : ∃ c, (x' : ℕ) - x = c + 1 := ⟨(x' : ℕ) - x - 1, by omega⟩
  refine (ungradedStasheffMul_congr P.coeff hc' (a := fun l : Fin (c + 1) => a ⟨x + l, by omega⟩)
      fun l => congrArg a (Fin.ext rfl)).trans ?_
  rw [ungradedStasheffMul_succ]
  refine Fintype.sum_of_injective (fun j : Fin c => (⟨x + j, by omega⟩ : Fin m))
    (fun j j' hj => Fin.ext (by have := congrArg Fin.val hj; simp only at this; omega)) _ _
    (fun i hi => ?_) fun j => ?_
  · refine dite_eq_right ?_
    rintro ⟨h₁, h₂⟩
    exact hi ⟨⟨i - x, by omega⟩, Fin.ext (by simp only; omega)⟩
  · rw [dite_eq_left ⟨by simp, by simp only; omega⟩,
      P.blockMatrix_apply_of_le _ (by simp only; omega)]
    exact P.coeff_congr (by simp only; omega) fun l => by
      rw [Fin.contractNth_castSucc_window_apply _ a (by omega) j l]
      exact congrArg _ (Fin.ext (by simp))

/-- The entry from `x` to `x'` of the differential terms of the block matrix: on the diagonal and
above, the differential term of the type `DA` relation on the block between `x` and `x'`. -/
private noncomputable def diffMatrix {n : ℕ} (a : Fin n → A) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (Matrix Y Y B) := fun x x' =>
  if h : (x : ℕ) ≤ x' then ungradedStasheffDiff P.coeff dA ((x' : ℕ) - x)
    (fun l => a ⟨x + l, by have := x'.isLt; have := l.isLt; omega⟩) else 0

/-- The entry from `x` to `x'` of the product terms of the block matrix: on the diagonal and
above, the product term of the type `DA` relation on the block between `x` and `x'`. -/
private noncomputable def mulMatrix {n : ℕ} (a : Fin n → A) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (Matrix Y Y B) := fun x x' =>
  if h : (x : ℕ) ≤ x' then ungradedStasheffMul P.coeff ((x' : ℕ) - x)
    (fun l => a ⟨x + l, by have := x'.isLt; have := l.isLt; omega⟩) else 0

omit [DecidableEq Y] in
/-- **The curvature of the block matrix.** Over a ring of characteristic two, the structure
relations of `P`, one for each block, say that the curvature `d Γ + Γ * Γ` of the block matrix
`Γ` is the matrix of the differential and product terms of the blocks. -/
private theorem curvature_blockMatrix [CharP R 2] {n : ℕ} (a : Fin n → A) :
    ((dB.mapMatrix : Matrix Y Y B →ₗ[R] Matrix Y Y B).mapMatrix :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (Matrix Y Y B) →ₗ[R] _) (P.blockMatrix a) +
      P.blockMatrix a * P.blockMatrix a = P.diffMatrix a + P.mulMatrix a := by
  ext1 x x'
  rw [Matrix.add_apply, Matrix.add_apply, LinearMap.mapMatrix_apply, Matrix.map_apply]
  by_cases h : (x : ℕ) ≤ x'
  · rw [P.blockMatrix_mul_blockMatrix_apply_of_le a h, P.blockMatrix_apply_of_le a h, diffMatrix,
      mulMatrix, dite_eq_left h, dite_eq_left h, LinearMap.mapMatrix_apply]
    have hrel := P.stasheff ((x' : ℕ) - x)
      (fun l => a ⟨x + l, by have := x'.isLt; have := l.isLt; omega⟩)
    refine (add_eq_zero_iff_eq_of_charTwo R).mp ?_
    rw [← hrel]
    abel
  · have hlt : x' < x := Fin.lt_def.mpr (not_le.mp h)
    rw [P.blockMatrix_apply_of_lt a hlt, Matrix.mul_apply, diffMatrix, mulMatrix, dite_eq_right h,
      dite_eq_right h, LinearMap.map_zero, zero_add, add_zero]
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases hxy : x ≤ y
    · rw [P.blockMatrix_apply_of_lt a (x := y) (x' := x') (lt_of_lt_of_le hlt hxy), Matrix.mul_zero]
    · rw [P.blockMatrix_apply_of_lt a (not_le.mp hxy), Matrix.zero_mul]

omit [DecidableEq Y] in
private theorem diffMatrix_apply {n : ℕ} (a : Fin n → A) (x x' : Fin (n + 1)) :
    P.diffMatrix a x x' = ∑ i : Fin n, if (x : ℕ) ≤ i ∧ (i : ℕ) < x' then
      P.blockMatrix (Function.update a i (dA (a i))) x x' else 0 := by
  by_cases h : (x : ℕ) ≤ x'
  · rw [diffMatrix, dite_eq_left h, P.ungradedStasheffDiff_block a h]
  · rw [diffMatrix, dite_eq_right h]
    exact (Finset.sum_eq_zero fun i _ => ite_eq_right (by omega)).symm

/-- **The differential terms along one path.** Along a path from `0` to `n`, replacing the entry
of each step by the differential terms of its block and summing over the steps is summing over
the inputs `aᵢ` the operations along the block matrix with `aᵢ` replaced by `dA aᵢ`. -/
private theorem sum_act_update_diffEntry {n k : ℕ} (a : Fin n → A) (i : Fin n)
    {x : Fin (k + 1) → Fin (n + 1)} (hx0 : x 0 = 0) (hxl : x (Fin.last k) = Fin.last n) :
    ∑ l : Fin k, (Mm.matrix Y).act k (Function.update
        (fun t => P.blockMatrix a (x t.castSucc) (x t.succ)) l
        (if (x l.castSucc : ℕ) ≤ i ∧ (i : ℕ) < x l.succ then
          P.blockMatrix (Function.update a i (dA (a i))) (x l.castSucc) (x l.succ) else 0)) =
      (Mm.matrix Y).act k (fun t => P.blockMatrix (Function.update a i (dA (a i)))
        (x t.castSucc) (x t.succ)) := by
  rcases Fin.exists_succ_lt_castSucc_or_existsUnique_castSucc_le_and_lt_succ (fun t => (x t : ℕ))
      (c := i) (by simp [hx0]) (by simp [hxl]) with ⟨l₀, hl₀⟩ | ⟨l₀, hl₀, huniq⟩
  · -- A decreasing step kills every term.
    rw [P.act_blockMatrix_eq_zero_of_lt Mm _ (Fin.lt_def.mpr hl₀)]
    exact Finset.sum_eq_zero fun l _ => P.act_update_blockMatrix_eq_zero_of_lt Mm a
      (Fin.lt_def.mpr hl₀) l fun h => by subst h; exact ite_eq_right (by omega)
  · -- Only the step across `i` contributes.
    rw [Finset.sum_eq_single l₀ (fun l _ hl => ((Mm.matrix Y).act k).map_coord_zero l (by
        rw [Function.update_self, ite_eq_right fun h => hl (huniq l h)]))
        (fun h => (h (Finset.mem_univ _)).elim), ite_eq_left hl₀,
      P.blockMatrix_update_comp a _ huniq]

/-- **The differential terms of the `A∞` relations of `M ⊠ P`, of a given length.** -/
private theorem sum_matrixAct_update_diffMatrix {n k : ℕ} (a : Fin n → A) (ψ : Y → M) :
    ∑ l : Fin k, ((Mm.matrix Y).matrixAct (Fin (n + 1)) k
        (Function.update (fun _ => P.blockMatrix a) l (P.diffMatrix a))) (Pi.single 0 ψ)
        (Fin.last n) =
      ∑ i : Fin n, P.blockAct Mm k n (Function.update a i (dA (a i))) ψ := by
  simp only [UngradedAInfinityRightModule.matrixAct_single_apply, blockAct_apply,
    Matrix.update_apply_path, P.diffMatrix_apply, MultilinearMap.map_update_sum,
    LinearMap.sum_apply]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x 0 = 0 ∧ x (Fin.last k) = Fin.last n
  · simp only [hx, and_self, ↓reduceIte]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← LinearMap.sum_apply, P.sum_act_update_diffEntry Mm a i hx.1 hx.2]
  · simp [hx]

omit [DecidableEq Y] in
private theorem mulMatrix_eq_zero (a : Fin 0 → A) : P.mulMatrix a = 0 := by
  ext1 x x'
  rw [mulMatrix, Matrix.zero_apply]
  split_ifs with h
  · refine (ungradedStasheffMul_congr P.coeff (n := 0) (by omega)
      (a := fun l : Fin 0 => a ⟨x + l, by omega⟩) fun l => congrArg a (Fin.ext rfl)).trans ?_
    exact ungradedStasheffMul_zero _ _
  · rfl

omit [DecidableEq Y] in
private theorem mulMatrix_apply {m : ℕ} (a : Fin (m + 1) → A) (x x' : Fin (m + 2)) :
    P.mulMatrix a x x' = ∑ i : Fin m, if hi : (x : ℕ) ≤ i ∧ (i : ℕ) + 2 ≤ x' then
      P.blockMatrix (Fin.contractNth i.castSucc (· * ·) a) ⟨x, by omega⟩
        ⟨x' - 1, by have := x'.isLt; omega⟩ else 0 := by
  by_cases h : (x : ℕ) ≤ x'
  · rw [mulMatrix, dite_eq_left h, P.ungradedStasheffMul_block a h]
  · rw [mulMatrix, dite_eq_right h]
    exact (Finset.sum_eq_zero fun i _ => dite_eq_right (by omega)).symm

/-- The values of the embedding of `0, …, m` into `0, …, m + 1` skipping `i + 1`. -/
private theorem val_succAbove_of_val_eq {m : ℕ} (i : Fin m) {p : Fin (m + 2)}
    (hp : (p : ℕ) = i + 1) (z : Fin (m + 1)) :
    ((p.succAbove z : Fin (m + 2)) : ℕ) = if (z : ℕ) ≤ i then (z : ℕ) else (z : ℕ) + 1 := by
  rw [Fin.val_succAbove, hp]
  exact if_congr Nat.lt_succ_iff rfl rfl

omit [DecidableEq Y] in
/-- Away from the contracted pair, the block matrix of the contracted tuple is that of the tuple,
read through the embedding skipping `i + 1`. -/
private theorem blockMatrix_contractNth {m : ℕ} (a : Fin (m + 1) → A) (i : Fin m)
    {p : Fin (m + 2)} (hp : (p : ℕ) = i + 1) {z z' : Fin (m + 1)}
    (h : ¬ ((z : ℕ) ≤ i ∧ (i : ℕ) < z')) :
    P.blockMatrix (Fin.contractNth i.castSucc (· * ·) a) z z' =
      P.blockMatrix a (p.succAbove z) (p.succAbove z') := by
  have hz := val_succAbove_of_val_eq i hp z
  have hz' := val_succAbove_of_val_eq i hp z'
  simp only [blockMatrix_apply]
  by_cases hzz : (z : ℕ) ≤ z'
  · by_cases hzi : (z' : ℕ) ≤ i
    · -- The block lies below the contracted pair.
      have e₁ : ((p.succAbove z : Fin (m + 2)) : ℕ) = z := by
        rw [hz]; exact ite_eq_left (by omega)
      have e₂ : ((p.succAbove z' : Fin (m + 2)) : ℕ) = z' := by
        rw [hz']; exact ite_eq_left hzi
      rw [dite_eq_left hzz, dite_eq_left (by rw [e₁, e₂]; exact hzz)]
      refine P.coeff_congr (by rw [e₁, e₂]) fun l => ?_
      rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp only [Fin.val_castSucc]; omega)]
      refine congrArg a (Fin.ext ?_)
      simp only [Fin.val_castSucc, Fin.val_cast]
      rw [e₁]
    · -- The block lies above the contracted pair.
      have e₁ : ((p.succAbove z : Fin (m + 2)) : ℕ) = z + 1 := by
        rw [hz]; exact ite_eq_right (by omega)
      have e₂ : ((p.succAbove z' : Fin (m + 2)) : ℕ) = z' + 1 := by
        rw [hz']; exact ite_eq_right hzi
      rw [dite_eq_left hzz, dite_eq_left (by rw [e₁, e₂]; omega)]
      refine P.coeff_congr (by rw [e₁, e₂]; omega) fun l => ?_
      rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp only [Fin.val_castSucc]; omega)]
      refine congrArg a (Fin.ext ?_)
      simp only [Fin.val_succ, Fin.val_cast]
      rw [e₁]
      omega
  · have hlt := Fin.lt_def.mp ((Fin.strictMono_succAbove p) (Fin.lt_def.mpr (not_le.mp hzz)))
    rw [dite_eq_right hzz, dite_eq_right (by omega)]

/-- **The product terms along one path.** Along a path from `0` to `m` in `0, …, m`, read in
`0, …, m + 1` through the embedding skipping `i + 1`, replacing the entry of each step by the
product term contracting `aᵢ` and `aᵢ₊₁` and summing over the steps gives the operation along
the block matrix of the contracted tuple. -/
private theorem sum_act_update_mulEntry {m k : ℕ} (a : Fin (m + 1) → A) (i : Fin m)
    {p : Fin (m + 2)} (hp : (p : ℕ) = i + 1)
    {y : Fin (k + 1) → Fin (m + 1)} (hy0 : y 0 = 0) (hyl : y (Fin.last k) = Fin.last m) :
    ∑ l : Fin k, (Mm.matrix Y).act k (Function.update
        (fun t => P.blockMatrix a (p.succAbove (y t.castSucc)) (p.succAbove (y t.succ))) l
        (if hi : ((p.succAbove (y l.castSucc) : Fin (m + 2)) : ℕ) ≤ i ∧
              (i : ℕ) + 2 ≤ p.succAbove (y l.succ)
          then P.blockMatrix (Fin.contractNth i.castSucc (· * ·) a)
            ⟨p.succAbove (y l.castSucc), by omega⟩
            ⟨(p.succAbove (y l.succ) : ℕ) - 1, by
              have := (p.succAbove (y l.succ)).isLt; omega⟩
          else 0)) =
      (Mm.matrix Y).act k (fun t =>
        P.blockMatrix (Fin.contractNth i.castSucc (· * ·) a) (y t.castSucc) (y t.succ)) := by
  have hv (z : Fin (m + 1)) := val_succAbove_of_val_eq i hp z
  rcases Fin.exists_succ_lt_castSucc_or_existsUnique_castSucc_le_and_lt_succ (fun t => (y t : ℕ))
      (c := i) (by simp [hy0]) (by simp [hyl]) with ⟨l₀, hl₀⟩ | ⟨l₀, hl₀, huniq⟩
  · -- A decreasing step kills every term.
    have hp₀ := Fin.strictMono_succAbove p (Fin.lt_def.mpr hl₀)
    rw [P.act_blockMatrix_eq_zero_of_lt Mm _ (Fin.lt_def.mpr hl₀)]
    exact Finset.sum_eq_zero fun l _ => P.act_update_blockMatrix_eq_zero_of_lt Mm a
      (x := fun t => p.succAbove (y t)) hp₀ l fun h => by
        subst h; exact dite_eq_right (by have := Fin.lt_def.mp hp₀; omega)
  · -- Only the step across the contracted pair contributes.
    rw [Finset.sum_eq_single l₀ (fun l _ hl => ((Mm.matrix Y).act k).map_coord_zero l (by
        rw [Function.update_self, dite_eq_right]
        rintro ⟨h₁, h₂⟩
        refine hl (huniq l ⟨?_, ?_⟩)
        · rw [hv] at h₁; split_ifs at h₁ <;> omega
        · rw [hv] at h₂; split_ifs at h₂ <;> omega))
        (fun h => (h (Finset.mem_univ _)).elim)]
    have h₁ : ((p.succAbove (y l₀.castSucc) : Fin (m + 2)) : ℕ) = y l₀.castSucc := by
      rw [hv]; exact ite_eq_left hl₀.1
    have h₂ : ((p.succAbove (y l₀.succ) : Fin (m + 2)) : ℕ) = y l₀.succ + 1 := by
      rw [hv]; exact ite_eq_right (by omega)
    rw [dite_eq_left (by omega)]
    congr 1
    funext t
    rcases eq_or_ne t l₀ with rfl | ht
    · rw [Function.update_self]
      congr 1
      · exact Fin.ext h₁
      · exact Fin.ext (by simp only; omega)
    · rw [Function.update_of_ne ht, P.blockMatrix_contractNth a i hp fun h => ht (huniq t h)]

/-- **Paths through `i + 1` carry no contracted pair at `i`.** Along a path in `0, …, m + 1`
visiting `i + 1`, no step carries both `aᵢ` and `aᵢ₊₁`, so replacing the entry of a step by the
product term contracting them gives zero. -/
private theorem sum_act_update_mulEntry_eq_zero {m k : ℕ} (a : Fin (m + 1) → A) (i : Fin m)
    {p : Fin (m + 2)} (hp : (p : ℕ) = i + 1) {x : Fin (k + 1) → Fin (m + 2)} {q : Fin (k + 1)}
    (hq : x q = p) :
    ∑ l : Fin k, (Mm.matrix Y).act k (Function.update
        (fun t => P.blockMatrix a (x t.castSucc) (x t.succ)) l
        (if hi : (x l.castSucc : ℕ) ≤ i ∧ (i : ℕ) + 2 ≤ x l.succ
          then P.blockMatrix (Fin.contractNth i.castSucc (· * ·) a) ⟨x l.castSucc, by omega⟩
            ⟨(x l.succ : ℕ) - 1, by have := (x l.succ).isLt; omega⟩
          else 0)) = 0 := by
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hdec : ∃ l₀ : Fin k, x l₀.succ < x l₀.castSucc
  · -- A decreasing step kills the term.
    obtain ⟨l₀, hl₀⟩ := hdec
    exact P.act_update_blockMatrix_eq_zero_of_lt Mm a hl₀ l fun h => by
      subst h; exact dite_eq_right (by have := Fin.lt_def.mp hl₀; omega)
  · -- A nondecreasing path through `i + 1` has no step from at most `i` to at least `i + 2`.
    push Not at hdec
    have hm : Monotone x := Fin.monotone_iff_le_succ.mpr hdec
    refine ((Mm.matrix Y).act k).map_coord_zero l ?_
    rw [Function.update_self, dite_eq_right]
    rintro ⟨h₁, h₂⟩
    rcases le_or_gt q l.castSucc with hql | hql
    · have := Fin.le_def.mp (hm hql)
      rw [hq] at this
      omega
    · have := Fin.le_def.mp (hm (Fin.castSucc_lt_iff_succ_le.mp hql))
      rw [hq] at this
      omega

/-- **The product terms of the `A∞` relations of `M ⊠ P`, of a given length.** A path in
`0, …, m + 1` along which one step carries a contracted pair `aᵢ aᵢ₊₁` does not visit `i + 1`, so
it is a path in `0, …, m` read through the embedding skipping `i + 1`. -/
private theorem sum_matrixAct_update_mulMatrix {m k : ℕ} (a : Fin (m + 1) → A) (ψ : Y → M) :
    ∑ l : Fin k, ((Mm.matrix Y).matrixAct (Fin (m + 2)) k
        (Function.update (fun _ => P.blockMatrix a) l (P.mulMatrix a))) (Pi.single 0 ψ)
        (Fin.last (m + 1)) =
      ∑ i : Fin m, P.blockAct Mm k m (Fin.contractNth i.castSucc (· * ·) a) ψ := by
  simp only [UngradedAInfinityRightModule.matrixAct_single_apply, blockAct_apply,
    Matrix.update_apply_path, P.mulMatrix_apply, MultilinearMap.map_update_sum,
    LinearMap.sum_apply]
  -- Bring the sum over the contracted pairs `i` outside.
  simp only [← Finset.sum_filter]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.sum_filter]
  -- For a fixed pair, compare the paths in `0, …, m` with those in `0, …, m + 1`.
  set p : Fin (m + 2) := ⟨i + 1, by omega⟩
  have hp : (p : ℕ) = i + 1 := rfl
  symm
  refine Fintype.sum_of_injective (fun y => p.succAbove ∘ y)
    (fun y y' h => funext fun q => Fin.succAbove_right_injective (congrFun h q)) _ _
    (fun x hx => ?_) fun y => ?_
  · -- A path through `i + 1` carries no contracted pair at `i`.
    split_ifs with hc
    · obtain ⟨q, hq⟩ : ∃ q, x q = p := by
        by_contra hq
        push Not at hq
        exact hx ⟨fun q => (Fin.exists_succAbove_eq (hq q)).choose,
          funext fun q => (Fin.exists_succAbove_eq (hq q)).choose_spec⟩
      rw [← LinearMap.sum_apply, P.sum_act_update_mulEntry_eq_zero Mm a i hp hq,
        LinearMap.zero_apply]
    · rfl
  · -- A path in `0, …, m` gives a path in `0, …, m + 1` with the same ends.
    have hc0 : p.succAbove (y 0) = 0 ↔ y 0 = 0 :=
      Fin.succAbove_eq_zero_iff (Fin.ne_of_val_ne (by rw [hp]; simp))
    have hcl : p.succAbove (y (Fin.last k)) = Fin.last (m + 1) ↔ y (Fin.last k) = Fin.last m :=
      Fin.succAbove_eq_last_iff (Fin.ne_of_val_ne (by rw [hp, Fin.val_last]; omega))
    simp only [Function.comp_apply]
    by_cases hy : y 0 = 0 ∧ y (Fin.last k) = Fin.last m
    · rw [ite_eq_left hy, ite_eq_left ⟨hc0.mpr hy.1, hcl.mpr hy.2⟩, ← LinearMap.sum_apply,
        P.sum_act_update_mulEntry Mm a i hp hy.1 hy.2]
    · rw [ite_eq_right hy, ite_eq_right fun h => hy ⟨hc0.mp h.1, hcl.mp h.2⟩]

/-- **The curvature insertions are the differential and product terms.** Inserting the
differential and product terms of the blocks once into the operations along the block matrix
gives the differential and product terms of the `A∞` relations of `M ⊠ P`. -/
private theorem sum_matrixAct_update_curvature {K : ℕ} (hK : ∀ k, K ≤ k → Mm.act k = 0)
    (n : ℕ) (a : Fin n → A) (ψ : Y → M) :
    (∑ k ∈ range K, ∑ l : Fin k, ((Mm.matrix Y).matrix (Fin (n + 1))).act k
        (Function.update (fun _ => P.blockMatrix a) l (P.diffMatrix a + P.mulMatrix a))
        (Pi.single 0 ψ)) (Fin.last n) =
      ungradedStasheffDiff (P.typeABoxAct Mm) dA n a ψ +
        ungradedStasheffMul (P.typeABoxAct Mm) n a ψ := by
  simp only [MultilinearMap.map_update_add, LinearMap.add_apply, Finset.sum_add_distrib,
    Finset.sum_apply, Pi.add_apply, UngradedAInfinityRightModule.matrix_act]
  congr 1
  · rw [ungradedStasheffDiff_apply]
    simp only [P.typeABoxAct_eq_sum Mm hK, _root_.sum_apply, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => P.sum_matrixAct_update_diffMatrix Mm a ψ
  · cases n with
    | zero =>
      rw [ungradedStasheffMul_zero_apply]
      refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
      rw [P.mulMatrix_eq_zero, MultilinearMap.map_update_zero, LinearMap.zero_apply,
        Pi.zero_apply]
    | succ m =>
      rw [ungradedStasheffMul_succ_apply]
      simp only [P.typeABoxAct_eq_sum Mm hK, _root_.sum_apply, LinearMap.sum_apply]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => P.sum_matrixAct_update_mulMatrix Mm a ψ

/-- **The box tensor product `M ⊠ P` of a type `A` module with a type `DA` bimodule.** For an
`A∞` right module `M` over `(B, dB)` whose operations vanish from some arity on, and a type `DA`
bimodule `P = ^B P_A`, the row vectors `Y → M`, standing for `∑ y, ψ y ⊗ y`, form an `A∞` right
module over `(A, dA)`, over a ring of characteristic two. Its operation `m_{n+1}(ψ, a₁, …, aₙ)`
(`TauCeti.TypeDAStructure.typeABoxAct`) sums, over the ways of cutting `a₁, …, aₙ` into
consecutive, possibly empty, blocks, the operations of the matrix module of `M` on `ψ` and the
coefficient matrices `δ` of `P` on the blocks. -/
noncomputable def typeABoxModule [CharP R 2] (hM : ∃ K, ∀ k, K ≤ k → Mm.act k = 0) :
    UngradedAInfinityRightModule dA (Y → M) where
  act := P.typeABoxAct Mm
  stasheff n a ψ := by
    -- The composite terms are the square of the twisted differential along the block matrix,
    -- which inserts its curvature once; by the structure relations of `P` the curvature is made of
    -- the differential and product terms of the blocks, and these insertions are the
    -- differential and product terms of the relation. In characteristic two the sum vanishes.
    obtain ⟨K, hK⟩ := hM
    have hU : ∀ k, K ≤ k → ∀ u : Fin k → Matrix (Fin (n + 1)) (Fin (n + 1)) (Matrix Y Y B),
        (∀ l, u l ∈ (Set.univ : Set _)) → ((Mm.matrix Y).matrix (Fin (n + 1))).act k u = 0 :=
      fun k hk u _ => by rw [matrix_matrix_act_eq_zero (Y := Y) Mm hK n hk, zero_apply]
    rw [P.ungradedStasheffComp_typeABoxAct Mm hK,
      ((Mm.matrix Y).matrix (Fin (n + 1))).twistedDifferential_twistedDifferential_eq_sum
        (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) hU,
      P.curvature_blockMatrix a, P.sum_matrixAct_update_curvature Mm hK]
    rw [add_assoc, add_self_eq_zero_of_charTwo R]

@[simp]
theorem typeABoxModule_act [CharP R 2] (hM : ∃ K, ∀ k, K ≤ k → Mm.act k = 0) :
    (P.typeABoxModule Mm hM).act = P.typeABoxAct Mm :=
  (rfl)

/-- **The operations of `M ⊠ P` as sums over paths.** If the operations of `M` vanish from arity
`K` on, `m_{n+1}(ψ, a₁, …, aₙ)` is the sum, over the lengths `k < K` and the paths
`0 = x₀ → x₁ → ⋯ → x_k = n`, of `m_{k+1}` of the matrix module of `M` on `ψ` and the entries of
the block matrix along the path; only the nondecreasing paths, which cut `a₁, …, aₙ` into the
blocks between consecutive `xⱼ`, contribute. -/
theorem typeABoxAct_apply {K : ℕ} (hK : ∀ k, K ≤ k → Mm.act k = 0) (n : ℕ) (a : Fin n → A)
    (ψ : Y → M) :
    P.typeABoxAct Mm n a ψ = ∑ k ∈ range K, ∑ x : Fin (k + 1) → Fin (n + 1),
      if x 0 = 0 ∧ x (Fin.last k) = Fin.last n then
        (Mm.matrix Y).act k (fun t => P.blockMatrix a (x t.castSucc) (x t.succ)) ψ else 0 := by
  rw [P.typeABoxAct_eq_sum Mm hK, _root_.sum_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun k _ =>
    (Mm.matrix Y).matrixAct_single_apply (Fin (n + 1)) k _ 0 ψ (Fin.last n)

/-- **For a differential module, `M ⊠ P` is `TauCeti.TypeDAStructure.boxModule`.**
A differential module, viewed as an `A∞` module, has no operations beyond `m₂`, so only the cuts
of `a₁, …, aₙ` into at most one block contribute: `m₁ ψ = dM ψ + ψ ⬝ δ₀` and
`m_{n+1}(ψ, a) = ψ ⬝ δₙ(a)`. -/
theorem typeABoxModule_toUngradedAInfinityRightModule [CharP R 2] [Module Bᵐᵒᵖ M]
    [SMulCommClass R Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M] {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule dB dM) :
    P.typeABoxModule hM.toUngradedAInfinityRightModule
        ⟨2, fun _ => hM.toUngradedAInfinityRightModule_act_eq_zero_of_two_le⟩ =
      P.boxModule hM := by
  refine UngradedAInfinityRightModule.ext (funext fun n => MultilinearMap.ext fun a =>
    LinearMap.ext fun ψ => funext fun z => ?_)
  rw [typeABoxModule_act, P.typeABoxAct_eq_sum _
    fun _ => hM.toUngradedAInfinityRightModule_act_eq_zero_of_two_le, boxModule_act_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, _root_.add_apply,
    LinearMap.add_apply, Pi.add_apply, blockAct_apply]
  congr 1
  · -- The empty cut, with no block, contributes the differential of `M` when `n = 0`.
    rw [UngradedAInfinityRightModule.matrixAct_zero_apply, UngradedAInfinityRightModule.matrix_act,
      UngradedAInfinityRightModule.matrixAct_zero_apply,
      IsUngradedDGRightModule.toUngradedAInfinityRightModule_act_zero, Pi.single_apply]
    have hlast : Fin.last n = 0 ↔ n = 0 := by simp [Fin.ext_iff]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact absurd (hlast.mp h₁) h₂
    · exact absurd (hlast.mpr h₂) h₁
    · simp
  · -- The cut into a single block contributes the right action of `δₙ(a)`.
    rw [UngradedAInfinityRightModule.matrixAct_one_apply,
      Fintype.sum_eq_single 0 fun x hx => by rw [Pi.single_eq_of_ne hx, map_zero],
      Pi.single_eq_same, UngradedAInfinityRightModule.matrix_act,
      UngradedAInfinityRightModule.matrixAct_one_apply,
      continuationMap_apply (R := R) (M := M) (P.coeff n a)]
    have hΓ : P.blockMatrix a 0 (Fin.last n) = P.coeff n a := by
      rw [P.blockMatrix_apply_of_le a (by simp)]
      exact P.coeff_congr (by simp) fun l =>
        congrArg a (Fin.ext (by simp only [Fin.val_zero, zero_add]; rfl))
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [IsUngradedDGRightModule.toUngradedAInfinityRightModule_act_one, hΓ]

end TypeDAStructure

end TauCeti
