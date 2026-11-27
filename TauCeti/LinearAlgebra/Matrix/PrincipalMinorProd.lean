/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.Matrix.Block
public import TauCeti.LinearAlgebra.Matrix.Minor
import TauCeti.Algebra.BigOperators.ZPow
import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# Products of principal minors of a given weight

Let `K` be a field, `ι` a finite index type and `w : ι → ℤ` a weight. For `t : ℤ` let
`S_t = {a | t ≤ w a}`, a superlevel set of `w`. The **product of principal minors of weight `w`**
of a square matrix `g` is

`m_w(g) = ∏_{t ∈ ℤ} det(g_{S_t}) · det(g)^{-[t ≤ 0]}`,

where `g_S` is the principal submatrix of `g` on `S` (with `det g_∅ = 1`) and `[t ≤ 0]` is `1` if
`t ≤ 0` and `0` otherwise. For invertible `g` almost all factors are `1`: for `t > max |w|` the set
`S_t` is empty, and for `t ≤ -max |w|` it is everything. The definition
`Matrix.principalMinorProd g w` takes the product over the window `-N < t ≤ N` with
`N = max_a |w a|`; any larger window gives the same value when `det g ≠ 0`
(`Matrix.principalMinorProd_eq_prod_Ioc`). For singular `g` the value is the product over this
window, which has no further meaning.

On `GL_n(ℂ)`, products of principal minors of this kind span the highest weight lines of the
polynomial representations twisted by powers of the determinant (not proved here), and for a
unitary group `U(p, q)` the integrand of Flensted-Jensen's integral formula for the coefficients of
discrete series is built from functions `m_w`. Their basic property, proved here, is equivariance
under triangular matrices. If `b` is block upper triangular for the order on the indices given by
the decreasing values of `w`, then `b` maps the coordinates of every `S_t` into themselves, so
`m_w(x b) = m_w(x) · m_w(b)` (`Matrix.BlockTriangular.principalMinorProd_mul_right`), and dually
`m_w(b x) = m_w(b) · m_w(x)` when `b` is block upper triangular for increasing `w`
(`Matrix.BlockTriangular.principalMinorProd_mul_left`). If `b` is triangular for an injective
ranking of the indices, then `m_w(b) = ∏_a b_aa ^ w_a`
(`Matrix.BlockTriangular.principalMinorProd_eq_prod_zpow`).

For a labelling `ε` of the indices (for `U(p, q)`, the signs of `diag ε`) and an injective ranking
`o`, the weight `w` is `K`-dominant for `o` (`TauCeti.IsKDominant ε o w`) if `w b ≤ w a` whenever
`ε a = ε b` and `o a < o b`. Then a matrix `b` that is block diagonal for `ε` and triangular for
`o` satisfies `m_w(x b) = m_w(x) · ∏_a b_aa ^ w_a`
(`TauCeti.IsKDominant.principalMinorProd_mul_right`), and one that is block diagonal for `ε` and
triangular for the reversed ranking satisfies `m_w(b x) = (∏_a b_aa ^ w_a) · m_w(x)`
(`TauCeti.IsKDominant.principalMinorProd_mul_left`).

## Main definitions

* `Matrix.principalMinorProd g w`: the product of principal minors of weight `w`.
* `TauCeti.IsKDominant ε o w`: `w` is antitone along `o` on each fibre of `ε`.

## Main results

* `Matrix.principalMinorProd_eq_prod_Ioc`: for `det g ≠ 0`, the product may be taken over any
  window `-N < t ≤ N` with `N ≥ max |w|`.
* `Matrix.principalMinorProd_mul_of_principalMinor`: `m_w` is multiplicative on a pair of matrices
  whose principal minors on the superlevel sets of `w` are.
* `Matrix.BlockTriangular.principalMinorProd_mul_right`,
  `Matrix.BlockTriangular.principalMinorProd_mul_left`: equivariance under block triangular
  matrices.
* `Matrix.principalMinorProd_of_principalMinor_eq_prod`, `Matrix.principalMinorProd_diagonal`,
  `Matrix.BlockTriangular.principalMinorProd_eq_prod_zpow`: the value `∏_a d_a ^ w_a` on matrices
  whose principal minors are the products of the nonzero numbers `d_a`, such as diagonal and
  triangular matrices.
* `Matrix.principalMinorProd_zero`, `Matrix.principalMinorProd_one`,
  `Matrix.principalMinorProd_const`, `Matrix.principalMinorProd_smul`,
  `Matrix.principalMinorProd_transpose`, `Matrix.principalMinorProd_map`: the weight zero, the
  identity matrix, constant weights (`m_k(g) = det(g)^k`), scalar multiples, transposition and
  field homomorphisms.
* `TauCeti.IsKDominant.blockTriangular_toDual`, `TauCeti.IsKDominant.blockTriangular`: a block
  diagonal triangular matrix is block triangular for the order given by `w`.
* `TauCeti.IsKDominant.principalMinorProd_mul_right`,
  `TauCeti.IsKDominant.principalMinorProd_mul_left`: equivariance under block diagonal triangular
  matrices.

## References

* M. Flensted-Jensen, *Discrete series for semisimple symmetric spaces*, Ann. of Math. 111 (1980),
  253–311.
* The shorter formal proof of the Riemann hypothesis for Dirichlet `L`-functions,
  <https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh>
  (Apache 2.0): the definitions here follow `New.weightMinors` and `New.IsKDominant` in
  `src/Lib/DiscreteSeries/FlenstedJensen/Defs.lean`, and the equivariance statements follow
  `New.IsKDominant.weightMinors_mul_borel` and `New.IsKDominant.weightMinors_oppBorel_mul` in
  `src/Lib/DiscreteSeries/Holomorphic/MaximalCompactMinors.lean`.
-/

public section

open Finset OrderDual

namespace Matrix

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- The **product of principal minors of weight `w`** of a square matrix `g`:
`m_w(g) = ∏_t det(g_{S_t}) · det(g)^{-[t ≤ 0]}` with `S_t = {a | t ≤ w a}`, the product taken over
the window `-N < t ≤ N` with `N = max_a |w a|`, outside of which every factor is `1` when `g` is
invertible (`Matrix.principalMinorProd_eq_prod_Ioc`). -/
def principalMinorProd (g : Matrix ι ι K) (w : ι → ℤ) : K :=
  ∏ t ∈ Ioc (-((univ.sup fun a ↦ (w a).natAbs : ℕ) : ℤ))
      ((univ.sup fun a ↦ (w a).natAbs : ℕ) : ℤ),
    g.principalMinor {a | t ≤ w a} / if t ≤ 0 then g.det else 1

omit [DecidableEq ι] in
/-- Every entry of a weight is bounded in absolute value by the window of
`Matrix.principalMinorProd`. -/
private theorem natAbs_le_sup_natAbs (w : ι → ℤ) (a : ι) :
    (w a).natAbs ≤ univ.sup fun a ↦ (w a).natAbs :=
  le_sup (f := fun a ↦ (w a).natAbs) (mem_univ a)

/-- For invertible `g`, the product of principal minors of weight `w` may be taken over any
window `-N < t ≤ N` with `|w a| ≤ N` for every `a`. -/
theorem principalMinorProd_eq_prod_Ioc {g : Matrix ι ι K} (hg : g.det ≠ 0) {w : ι → ℤ} {N : ℕ}
    (hN : ∀ a, (w a).natAbs ≤ N) :
    g.principalMinorProd w =
      ∏ t ∈ Ioc (-(N : ℤ)) N, g.principalMinor {a | t ≤ w a} / if t ≤ 0 then g.det else 1 := by
  have hN₀ : (univ.sup fun a ↦ (w a).natAbs) ≤ N := Finset.sup_le fun a _ ↦ hN a
  refine prod_subset (fun t ht ↦ ?_) fun t ht ht₀ ↦ ?_
  · simp only [mem_Ioc] at ht ⊢
    omega
  · simp only [mem_Ioc, not_and_or, not_lt, not_le] at ht ht₀
    rcases ht₀ with ht₀ | ht₀
    · -- Below the window every index lies in `S_t`, and the factor is `det g / det g`.
      have hS : ({a | t ≤ w a} : Finset ι) = univ := by
        refine eq_univ_of_forall fun a ↦ ?_
        have := natAbs_le_sup_natAbs w a
        simp only [mem_filter, mem_univ, true_and]
        omega
      rw [hS, principalMinor_univ, ite_eq_left (by omega), div_self hg]
    · -- Above the window `S_t` is empty, and the factor is `1 / 1`.
      have hS : ({a | t ≤ w a} : Finset ι) = ∅ := by
        refine filter_false_of_mem fun a _ ↦ ?_
        have := natAbs_le_sup_natAbs w a
        omega
      rw [hS, principalMinor_empty, ite_eq_right (by omega), div_one]

/-- The product of principal minors of weight `0` is `1`. -/
@[simp]
theorem principalMinorProd_zero (g : Matrix ι ι K) : g.principalMinorProd 0 = 1 := by
  simp [principalMinorProd]

/-- The product of principal minors of the identity matrix is `1`. -/
@[simp]
theorem principalMinorProd_one (w : ι → ℤ) : (1 : Matrix ι ι K).principalMinorProd w = 1 := by
  simp [principalMinorProd]

/-- The product of principal minors is unchanged by transposition. -/
@[simp]
theorem principalMinorProd_transpose (g : Matrix ι ι K) (w : ι → ℤ) :
    gᵀ.principalMinorProd w = g.principalMinorProd w := by
  simp [principalMinorProd]

/-- A field homomorphism carries the product of principal minors to the product of principal
minors of the mapped matrix. -/
@[simp]
theorem principalMinorProd_map {L : Type*} [Field L] (f : K →+* L) (g : Matrix ι ι K)
    (w : ι → ℤ) : (g.map f).principalMinorProd w = f (g.principalMinorProd w) := by
  simp [principalMinorProd, map_prod, map_div₀, apply_ite, RingHom.map_det]

/-- The product of principal minors of weight `w` is multiplicative on a pair of matrices whose
principal minors on the superlevel sets `{a | t ≤ w a}` are multiplicative. -/
theorem principalMinorProd_mul_of_principalMinor (x y : Matrix ι ι K) {w : ι → ℤ}
    (h : ∀ t : ℤ, (x * y).principalMinor {a | t ≤ w a} =
      x.principalMinor {a | t ≤ w a} * y.principalMinor {a | t ≤ w a}) :
    (x * y).principalMinorProd w = x.principalMinorProd w * y.principalMinorProd w := by
  rw [principalMinorProd, principalMinorProd, principalMinorProd, ← prod_mul_distrib]
  refine prod_congr rfl fun t _ ↦ ?_
  rw [h, det_mul]
  split_ifs
  · exact mul_div_mul_comm _ _ _ _
  · simp only [div_one]

/-- If `b` is block upper triangular for the decreasing values of `w` (no entry of `b` leads from
an index to one of smaller weight), then `m_w(x * b) = m_w(x) * m_w(b)`. -/
theorem BlockTriangular.principalMinorProd_mul_right {b : Matrix ι ι K} {w : ι → ℤ}
    (hb : b.BlockTriangular (toDual ∘ w)) (x : Matrix ι ι K) :
    (x * b).principalMinorProd w = x.principalMinorProd w * b.principalMinorProd w := by
  refine principalMinorProd_mul_of_principalMinor x b fun t ↦
    principalMinor_mul_of_apply_eq_zero_right x b fun i hi j hj ↦ hb ?_
  simp only [mem_filter, mem_univ, true_and, not_le] at hi hj
  exact toDual_lt_toDual.mpr (hi.trans_le hj)

/-- If `b` is block upper triangular for the increasing values of `w` (no entry of `b` leads from
an index to one of larger weight), then `m_w(b * x) = m_w(b) * m_w(x)`. -/
theorem BlockTriangular.principalMinorProd_mul_left {b : Matrix ι ι K} {w : ι → ℤ}
    (hb : b.BlockTriangular w) (x : Matrix ι ι K) :
    (b * x).principalMinorProd w = b.principalMinorProd w * x.principalMinorProd w := by
  refine principalMinorProd_mul_of_principalMinor b x fun t ↦
    principalMinor_mul_of_apply_eq_zero_left b x fun i hi j hj ↦ hb ?_
  simp only [mem_filter, mem_univ, true_and, not_le] at hi hj
  exact hj.trans_le hi

/-- The product over a window `-N < t ≤ N` with `|k| ≤ N` of `d` to the power
`[t ≤ k] - [t ≤ 0]` is `d ^ k`. -/
private theorem prod_Ioc_ite_div_ite {d : K} (hd : d ≠ 0) {k : ℤ} {N : ℕ} (hk : k.natAbs ≤ N) :
    ∏ t ∈ Ioc (-(N : ℤ)) N, (if t ≤ k then d else 1) / (if t ≤ 0 then d else 1) = d ^ k := by
  have hcard : ∀ m : ℤ, m.natAbs ≤ N → #{t ∈ Ioc (-(N : ℤ)) N | t ≤ m} = m + N := by
    intro m hm
    have : ({t ∈ Ioc (-(N : ℤ)) N | t ≤ m} : Finset ℤ) = Ioc (-(N : ℤ)) m := by
      ext t
      simp only [mem_filter, mem_Ioc]
      omega
    rw [this, Int.card_Ioc]
    omega
  rw [prod_div_distrib, prod_ite, prod_ite]
  simp only [prod_const, one_pow, mul_one]
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hd, hcard k hk, hcard 0 (by simp)]
  congr 1
  ring

/-- If every principal minor of `g` is the product of the corresponding entries of a family `d`
of nonzero numbers, then `m_w(g) = ∏_a d_a ^ w_a`. -/
theorem principalMinorProd_of_principalMinor_eq_prod {g : Matrix ι ι K} {d : ι → K}
    (hd : ∀ a, d a ≠ 0) (h : ∀ s, g.principalMinor s = ∏ a ∈ s, d a) (w : ι → ℤ) :
    g.principalMinorProd w = ∏ a, d a ^ w a := by
  have hdet : g.det = ∏ a, d a := by rw [← principalMinor_univ, h]
  rw [principalMinorProd]
  -- Write each factor as a product over the indices, and exchange the two products.
  have hfactor : ∀ t : ℤ, g.principalMinor {a | t ≤ w a} / (if t ≤ 0 then g.det else 1) =
      ∏ a, (if t ≤ w a then d a else 1) / (if t ≤ 0 then d a else 1) := by
    intro t
    rw [h, prod_filter, prod_div_distrib, hdet]
    split_ifs <;> simp
  simp_rw [hfactor]
  rw [prod_comm]
  exact prod_congr rfl fun a _ ↦ prod_Ioc_ite_div_ite (hd a) (natAbs_le_sup_natAbs w a)

/-- The product of principal minors of weight `w` of a diagonal matrix with nonzero entries `d` is
`∏_a d_a ^ w_a`. -/
theorem principalMinorProd_diagonal {d : ι → K} (hd : ∀ a, d a ≠ 0) (w : ι → ℤ) :
    (diagonal d).principalMinorProd w = ∏ a, d a ^ w a :=
  principalMinorProd_of_principalMinor_eq_prod hd (principalMinor_diagonal d) w

omit [Fintype ι] in
/-- A principal minor of a matrix that is block triangular for an injective ranking of its
indices is the product of the chosen diagonal entries. -/
theorem BlockTriangular.principalMinor_eq_prod_diag {α : Type*} [LinearOrder α]
    {b : Matrix ι ι K} {o : ι → α} (hb : b.BlockTriangular o) (ho : Function.Injective o)
    (s : Finset ι) : b.principalMinor s = ∏ a ∈ s, b a a := by
  rw [principalMinor_def,
    (hb.submatrix (f := Subtype.val)).det_eq_prod_diag (ho.comp Subtype.val_injective),
    ← prod_coe_sort s]
  simp only [submatrix_apply]

/-- The product of principal minors of weight `w` of a matrix that is triangular for an injective
ranking of the indices, with nonzero diagonal entries, is `∏_a b_aa ^ w_a`. -/
theorem BlockTriangular.principalMinorProd_eq_prod_zpow {α : Type*} [LinearOrder α]
    {b : Matrix ι ι K} {o : ι → α} (hb : b.BlockTriangular o) (ho : Function.Injective o)
    (hd : ∀ a, b a a ≠ 0) (w : ι → ℤ) : b.principalMinorProd w = ∏ a, b a a ^ w a :=
  principalMinorProd_of_principalMinor_eq_prod hd (hb.principalMinor_eq_prod_diag ho) w

/-- For singular `g` and a nonzero weight, the window of `Matrix.principalMinorProd` contains
`t = 0`, whose factor has the denominator `det g = 0`; so the product is the junk value `0`. -/
private theorem principalMinorProd_eq_zero_of_det_eq_zero {g : Matrix ι ι K} (hg : g.det = 0)
    {w : ι → ℤ} {a : ι} (ha : w a ≠ 0) : g.principalMinorProd w = 0 := by
  have := natAbs_le_sup_natAbs w a
  refine prod_eq_zero (i := 0) (mem_Ioc.mpr ⟨by omega, by omega⟩) ?_
  rw [ite_eq_left (le_refl (0 : ℤ)), hg, div_zero]

/-- For a constant weight `k`, the product of principal minors is `det(g) ^ k`. -/
theorem principalMinorProd_const (g : Matrix ι ι K) (k : ℤ) :
    g.principalMinorProd (fun _ ↦ k) = g.det ^ k := by
  by_cases hg : g.det = 0
  · -- A singular matrix has a nonempty index type, and both sides are the junk value `0`.
    rcases eq_or_ne k 0 with rfl | hk
    · exact (principalMinorProd_zero g).trans (zpow_zero _).symm
    obtain ⟨a⟩ : Nonempty ι := not_isEmpty_iff.mp fun _ ↦ one_ne_zero (det_isEmpty.symm.trans hg)
    rw [principalMinorProd_eq_zero_of_det_eq_zero hg (a := a) hk, hg, zero_zpow k hk]
  rw [principalMinorProd_eq_prod_Ioc hg (N := k.natAbs) fun _ ↦ le_rfl,
    ← prod_Ioc_ite_div_ite hg le_rfl]
  refine prod_congr rfl fun t _ ↦ ?_
  -- The superlevel set of a constant weight is everything or nothing.
  by_cases htk : t ≤ k
  · rw [filter_true_of_mem fun _ _ ↦ htk, principalMinor_univ, ite_eq_left htk]
  · rw [filter_false_of_mem fun _ _ ↦ htk, principalMinor_empty, ite_eq_right htk]

/-- Scaling a matrix by a nonzero `c` scales its product of principal minors of weight `w` by
`c ^ ∑_a w_a`. -/
theorem principalMinorProd_smul {c : K} (hc : c ≠ 0) (g : Matrix ι ι K) (w : ι → ℤ) :
    (c • g).principalMinorProd w = c ^ (∑ a, w a) * g.principalMinorProd w := by
  rw [smul_eq_diagonal_mul, (blockTriangular_diagonal _).principalMinorProd_mul_left,
    principalMinorProd_diagonal fun _ ↦ hc, prod_zpow_eq_zpow_sum_of_isUnit _ hc.isUnit]

end Matrix

namespace TauCeti

variable {ι α β : Type*} [LinearOrder α]

/-- A weight `w` is **`K`-dominant** for a labelling `ε` and a ranking `o` of the indices if it is
antitone along `o` on each fibre of `ε`: `w b ≤ w a` whenever `ε a = ε b` and `o a < o b`. For the
unitary group of `diag ε`, whose maximal compact subgroup consists of the matrices that are block
diagonal for `ε`, these are the weights dominant for the Borel subgroup of that compact subgroup
determined by `o`. -/
def IsKDominant (ε : ι → β) (o : ι → α) (w : ι → ℤ) : Prop :=
  ∀ a b, ε a = ε b → o a < o b → w b ≤ w a

theorem isKDominant_iff {ε : ι → β} {o : ι → α} {w : ι → ℤ} :
    IsKDominant ε o w ↔ ∀ a b, ε a = ε b → o a < o b → w b ≤ w a :=
  Iff.rfl

namespace IsKDominant

variable {R : Type*} [Zero R] {ε : ι → β} {o : ι → α} {w : ι → ℤ} {b : Matrix ι ι R}

/-- For a `K`-dominant weight `w`, a matrix that is block diagonal for `ε` and triangular for an
injective ranking `o` is block upper triangular for the decreasing values of `w`. -/
theorem blockTriangular_toDual (hw : IsKDominant ε o w) (ho : Function.Injective o)
    (hbε : ∀ a c, ε a ≠ ε c → b a c = 0) (hbo : b.BlockTriangular o) :
    b.BlockTriangular (OrderDual.toDual ∘ w) := by
  intro i j hij
  simp only [Function.comp_apply, OrderDual.toDual_lt_toDual] at hij
  by_cases hε : ε i = ε j
  · rcases lt_trichotomy (o i) (o j) with h | h | h
    · exact absurd (hw i j hε h) (not_le.mpr hij)
    · exact absurd (ho h ▸ hij) (lt_irrefl _)
    · exact hbo h
  · exact hbε i j hε

/-- For a `K`-dominant weight `w`, a matrix that is block diagonal for `ε` and triangular for the
reverse of an injective ranking `o` is block upper triangular for the increasing values of `w`. -/
theorem blockTriangular (hw : IsKDominant ε o w) (ho : Function.Injective o)
    (hbε : ∀ a c, ε a ≠ ε c → b a c = 0) (hbo : b.BlockTriangular (OrderDual.toDual ∘ o)) :
    b.BlockTriangular w := by
  intro i j hij
  by_cases hε : ε i = ε j
  · rcases lt_trichotomy (o i) (o j) with h | h | h
    · exact hbo (OrderDual.toDual_lt_toDual.mpr h)
    · exact absurd (ho h ▸ hij) (lt_irrefl _)
    · exact absurd (hw j i hε.symm h) (not_le.mpr hij)
  · exact hbε i j hε

variable {K : Type*} [Fintype ι] [DecidableEq ι] [Field K] {b : Matrix ι ι K}

/-- **Equivariance on the right.** For a `K`-dominant weight `w` and a matrix `b` that is block
diagonal for `ε` and triangular for an injective ranking `o`, with nonzero diagonal entries,
`m_w(x * b) = m_w(x) * ∏_a b_aa ^ w_a`. -/
theorem principalMinorProd_mul_right (hw : IsKDominant ε o w) (ho : Function.Injective o)
    (hbε : ∀ a c, ε a ≠ ε c → b a c = 0) (hbo : b.BlockTriangular o) (hd : ∀ a, b a a ≠ 0)
    (x : Matrix ι ι K) :
    (x * b).principalMinorProd w = x.principalMinorProd w * ∏ a, b a a ^ w a := by
  rw [(hw.blockTriangular_toDual ho hbε hbo).principalMinorProd_mul_right,
    hbo.principalMinorProd_eq_prod_zpow ho hd]

/-- **Equivariance on the left.** For a `K`-dominant weight `w` and a matrix `b` that is block
diagonal for `ε` and triangular for the reverse of an injective ranking `o`, with nonzero
diagonal entries, `m_w(b * x) = (∏_a b_aa ^ w_a) * m_w(x)`. -/
theorem principalMinorProd_mul_left (hw : IsKDominant ε o w) (ho : Function.Injective o)
    (hbε : ∀ a c, ε a ≠ ε c → b a c = 0) (hbo : b.BlockTriangular (OrderDual.toDual ∘ o))
    (hd : ∀ a, b a a ≠ 0) (x : Matrix ι ι K) :
    (b * x).principalMinorProd w = (∏ a, b a a ^ w a) * x.principalMinorProd w := by
  rw [(hw.blockTriangular ho hbε hbo).principalMinorProd_mul_left,
    hbo.principalMinorProd_eq_prod_zpow (OrderDual.toDual.injective.comp ho) hd]

end IsKDominant

end TauCeti
