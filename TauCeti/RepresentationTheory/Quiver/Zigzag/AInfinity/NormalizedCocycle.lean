/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Degenerate
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.HochschildClass
import Mathlib.LinearAlgebra.Multilinear.Basis
import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Basic

/-!
# Normalized Hochschild cocycles of zigzag algebras are loop operations

Let `Z` be the zigzag algebra of a finite simple graph `G` with no isolated vertex, graded by path
length and regarded as an `A∞` algebra whose only operation is the product
(`TauCeti.zigzagStrictAInfinityAlgebra`). A suspended Hochschild cochain `F` of degree one
concentrated on the words of length `n + 2` has arity `n + 2` and internal degree `-n`; these
cochains carry the obstruction classes in `HH^{n + 2, -n}(Z, Z)` of minimal `A∞` structures on `Z`
(`TauCeti.AInfinityAlgebra.HochschildVanishesAt`). Call `F` *normalized* relative to the vertex
idempotents when it vanishes on every word one of whose letters is a vertex idempotent `e_v`
(`TauCeti.ReducedTensorWords.degenerateWords`). This file shows that for `n ≥ 1` the normalized
Hochschild cocycles of this bidegree are exactly the operations of arity `n + 2` of the loop
deformations `TauCeti.zigzagLoopAInfinityAlgebra`: the finite linear combinations of the loop
operations `TauCeti.zigzagLoopOperation` of closed walks of length `n + 2`.

Loop operations vanish on vertex idempotents, which have no arrow coordinate, and they are
cocycles. For the converse, `F` sends a word of `n + 2` letters of positive path lengths
`d₀, …, d_{n+1}` to path length `∑ dᵢ - n`. Since `Z` vanishes above path length two, a normalized
`F` is nonzero only on words of arrows, where it takes values among the volume classes. On the word
obtained by inserting a vertex idempotent `e` at position `j` into a word `x` of arrows, the
cocycle condition reads

```text
0 = -e F(x) [j = 0] + F(x) e [j = n + 2] - F(…, x_{j-1} e, x_j, …) [0 < j]
      + F(…, x_{j-1}, e x_j, …) [j < n + 2],
```

the only terms which do not keep the letter `e`. Hence the value of `F` on the arrows of darts
`w` lies in `e_v Z e_{v'}` for the head `v` of `w 0` and the tail `v'` of the last dart, and it
vanishes unless consecutive darts compose. A volume class lies in such a corner only when
`v = v'`, so `F` vanishes off the closed walks, and on a closed walk it is the volume class at `v`
times its volume coordinate there. These coordinates, up to the sign of the suspension, are the
coefficients of the loop deformation.

Whether every Hochschild cocycle of `Z` of this bidegree is cohomologous to a normalized one is
not addressed here.

## Main results

* `TauCeti.degenerateWords_le_ker_obstruction_zigzagLoopAInfinityAlgebra`: the higher operation of
  a loop deformation is normalized relative to the vertex idempotents.
* `TauCeti.exists_obstruction_zigzagLoopAInfinityAlgebra_eq_iff`: for `n ≥ 1`, a suspended
  cochain of degree one concentrated on the words of length `n + 2` is the higher operation of a
  loop deformation if and only if it is a Hochschild cocycle normalized relative to the vertex
  idempotents.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Section 4, for minimal `A∞` deformations of zigzag algebras and
  their Hochschild cohomology.
* J.-L. Loday, *Cyclic Homology*, Sections 1.1 and 1.5, for Hochschild cochains and their
  normalization.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver AInfinity ReducedTensorWords

universe u w

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} [Finite V]
  {hns : ∀ i : V, ∃ j, G.Adj i j}

local notation "𝒵" => zigzagStrictAInfinityAlgebra k hns

local notation "𝔞" d:max => zigzagMk k G (ofArrow (arrow G (SimpleGraph.Dart.adj d)))

local notation "𝔢" v:max => zigzagMk k G (vertexIdempotent k (vertex G v))

/-! ### Words with an inserted letter -/

section Insert

variable {M : Type*}

/-- The letters `a 0, …, a (j - 1), e, a j, a (j + 1), …`: the letter `e` inserted at position
`j` into a natural-indexed family of letters. -/
private def insertLetter (a : ℕ → M) (j : ℕ) (e : M) (i : ℕ) : M :=
  if i < j then a i else if i = j then e else a (i - 1)

variable (R : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Collapsing a block of two letters which contains the inserted letter replaces the letter of
the original word next to it. -/
private theorem splice_insertLetter {N : ℕ} (a : ℕ → M) {j : ℕ} (e z : M) {p : ℕ} (hpj : p ≤ j)
    (hjp : j ≤ p + 1) (hpN : p < N) :
    splice R (fun i : Fin (N + 1) ↦ insertLetter a j e i) 0 (N + 1) p 2 z =
      of R M ⟨N, by omega⟩ (PiTensorProduct.tprod R fun i : Fin N ↦ Function.update a p z i) := by
  rw [splice_eq_of_tprod R _ z two_pos (by omega) (by omega)]
  refine of_tprod_congr R M _ (by omega) fun i ↦ ?_
  simp only [Nat.zero_add, Fin.val_cast, insertLetter, Function.update_apply]
  split_ifs <;> first | rfl | omega

/-- Dropping an inserted first letter. -/
private theorem subword_one_insertLetter_zero {N : ℕ} (hN : 0 < N) (a : ℕ → M) (e : M) :
    subword R (fun i : Fin (N + 1) ↦ insertLetter a 0 e i) 1 N =
      of R M ⟨N, hN⟩ (PiTensorProduct.tprod R fun i : Fin N ↦ a i) := by
  rw [subword_eq_of_tprod R _ hN (by omega)]
  refine of_tprod_congr R M _ rfl fun i ↦ ?_
  simp only [Fin.val_cast, insertLetter]
  split_ifs <;> first | omega | (congr 1; omega)

/-- Dropping an inserted last letter. -/
private theorem subword_zero_insertLetter_self {N : ℕ} (hN : 0 < N) (a : ℕ → M) (e : M) :
    subword R (fun i : Fin (N + 1) ↦ insertLetter a N e i) 0 N =
      of R M ⟨N, hN⟩ (PiTensorProduct.tprod R fun i : Fin N ↦ a i) := by
  rw [subword_eq_of_tprod R _ hN (by omega)]
  refine of_tprod_congr R M _ rfl fun i ↦ ?_
  simp only [Fin.val_cast, Nat.zero_add, insertLetter]
  split_ifs <;> first | rfl | omega

end Insert

/-! ### The Hochschild differential on a word with a vertex idempotent -/

section Differential

local notation "Z" => nonisolatedZigzagQuotient k G

variable {N : ℕ}

/-- A cochain concentrated on the words of length `N` vanishes on the words of other lengths. -/
private theorem apply_of_ne_of_comp_lengthProj {F : ReducedTensorWords k Z →ₗ[k] Z} (hN : 0 < N)
    (hFN : F ∘ₗ lengthProj k Z ⟨N, hN⟩ = F)
    {m : {m : ℕ // 0 < m}} (hm : m.val ≠ N) (t : TensorPower k m.val Z) : F (of k Z m t) = 0 := by
  rw [← hFN, LinearMap.comp_apply, lengthProj_of_of_ne k Z (fun h ↦ hm (by rw [h])), map_zero]

/-- A cochain concentrated on the words of length `N` vanishes on the subwords of other lengths. -/
private theorem apply_subword_of_ne_of_comp_lengthProj {F : ReducedTensorWords k Z →ₗ[k] Z}
    (hN : 0 < N) (hFN : F ∘ₗ lengthProj k Z ⟨N, hN⟩ = F) {n : ℕ} (y : Fin n → Z) (p : ℕ)
    {d : ℕ} (hd : d ≠ N) :
    F (subword k y p d) = 0 := by
  by_cases h : 0 < d ∧ p + d ≤ n
  · rw [subword_eq_of_tprod k y h.1 h.2]
    exact apply_of_ne_of_comp_lengthProj hN hFN hd _
  · rcases Nat.eq_zero_or_pos d with rfl | hd₀
    · rw [subword_length_zero, map_zero]
    · rw [subword_eq_zero_of_lt_add k y (by omega), map_zero]

/-- The letters of a word with a vertex idempotent inserted into letters of path length one are
homogeneous for the suspended grading, of degree `-1` at the idempotent and `0` elsewhere. -/
private theorem insertLetter_mem_shift_piece {a : ℕ → Z}
    (ha : ∀ i < N, a i ∈ zigzagIntegerGrade k G 1) {j : ℕ} (hj : j ≤ N) (u : V) :
    ∀ i < N + 1, insertLetter a j (𝔢 u) i ∈
      ((𝒵).grading.shift 1).piece (if i = j then -1 else 0) := by
  intro i hi
  rw [InternalGrading.shift_piece, zigzagStrictAInfinityAlgebra_grading_piece, insertLetter]
  by_cases h₁ : i < j
  · simpa [h₁, h₁.ne] using ha i (by omega)
  by_cases h₂ : i = j
  · simpa [h₁, h₂] using zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G u
  · simpa [h₁, h₂] using ha (i - 1) (by omega)

/-- A cochain of degree one sends a word of `N` letters of path length one to path length two. -/
private theorem apply_mem_zigzagIntegerGrade_two {F : ReducedTensorWords k Z →ₗ[k] Z} (hN : 0 < N)
    (hF : LinearMap.IsHomogeneous F (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 1)
    {a : ℕ → Z} (ha : ∀ i < N, a i ∈ zigzagIntegerGrade k G 1) :
    F (of k Z ⟨N, hN⟩ (PiTensorProduct.tprod k fun i : Fin N ↦ a i)) ∈
      zigzagIntegerGrade k G 2 := by
  have h := hF.map_mem (mem_gradedPiece_of_tprod ((𝒵).grading.shift 1) hN
    (fun i : Fin N ↦ a i) (fun _ ↦ 0) fun i ↦ by
      rw [InternalGrading.shift_piece, zigzagStrictAInfinityAlgebra_grading_piece, zero_add]
      exact ha i i.isLt)
  simpa [InternalGrading.shift_piece, zigzagStrictAInfinityAlgebra_grading_piece,
    show (1 : ℤ) + 1 = 2 by norm_num] using h

/-- One term of the `m{F}` half of the Hochschild differential of a normalized cochain on a word
with an inserted vertex idempotent: the collapse of the block of `d` letters at position `p`. -/
private theorem taylor_splice_insertLetter {F : ReducedTensorWords k Z →ₗ[k] Z} (hN : 2 ≤ N)
    (hF : LinearMap.IsHomogeneous F (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 1)
    (hFN : F ∘ₗ lengthProj k Z ⟨N, by omega⟩ = F)
    (hFe : ∀ v, degenerateWords k Z (𝔢 v) ≤ LinearMap.ker F)
    {a : ℕ → Z} (ha : ∀ i < N, a i ∈ zigzagIntegerGrade k G 1) {j : ℕ} (hj : j ≤ N) (u : V)
    {p d : ℕ} (hp : p < N + 1) (hd : d < N + 1 + 1) :
    negOnePowCast k (1 * ∑ i ∈ Finset.range p, if i = j then (-1 : ℤ) else 0) •
        (𝒵).taylor (splice k (fun i : Fin (N + 1) ↦ insertLetter a j (𝔢 u) i) 0 (N + 1) p d
          (F (subword k (fun i : Fin (N + 1) ↦ insertLetter a j (𝔢 u) i) p d))) =
      (if p = 1 ∧ d = N ∧ j = 0 then -(𝔢 u * F (of k Z ⟨N, by omega⟩
          (PiTensorProduct.tprod k fun i : Fin N ↦ a i))) else 0) +
        (if p = 0 ∧ d = N ∧ j = N then F (of k Z ⟨N, by omega⟩
          (PiTensorProduct.tprod k fun i : Fin N ↦ a i)) * 𝔢 u else 0) := by
  set W := of k Z ⟨N, by omega⟩ (PiTensorProduct.tprod k fun i : Fin N ↦ a i)
  set y := fun i : Fin (N + 1) ↦ insertLetter a j (𝔢 u) i
  have hFW : F W ∈ zigzagIntegerGrade k G 2 := apply_mem_zigzagIntegerGrade_two (by omega) hF ha
  by_cases hdN : d = N
  swap
  · rw [apply_subword_of_ne_of_comp_lengthProj (by omega) hFN y p hdN, splice_zero, map_zero,
      smul_zero]
    simp [hdN]
  subst d
  by_cases hfit : p + N ≤ N + 1
  swap
  · rw [subword_eq_zero_of_lt_add k y (by omega), map_zero, splice_zero, map_zero, smul_zero,
      ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
  by_cases hblock : p ≤ j ∧ j < p + N
  · -- The block contains the idempotent, so `F` kills it.
    rw [LinearMap.mem_ker.mp (hFe u (subword_mem_degenerateWords y
      ⟨⟨j, by omega⟩, hblock.1, hblock.2, by simp [y, insertLetter]⟩)), splice_zero, map_zero,
      smul_zero, ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
  rcases Nat.lt_or_ge p 1 with hp0 | hp1
  · -- Everything but a final idempotent collapses.
    obtain rfl : p = 0 := by omega
    have hjN : j = N := by omega
    subst j
    have hy : y (Fin.last N) = 𝔢 u := by simp [y, insertLetter]
    rw [ite_eq_right (by omega), ite_eq_left ⟨rfl, rfl, rfl⟩, zero_add, Finset.sum_range_zero,
      mul_zero, negOnePowCast_zero, one_smul, subword_zero_insertLetter_self k (by omega),
      splice_collapse_init_eq k (by omega), hy, AInfinityAlgebra.taylor_of_two,
      zigzagStrictAInfinityAlgebra_m_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [InternalGrading.koszulTwist_one_apply_of_mem _ (e := 2)
      (by rwa [zigzagStrictAInfinityAlgebra_grading_piece])]
    simp [W]
  · -- Everything but an initial idempotent collapses.
    obtain rfl : p = 1 := by omega
    obtain rfl : j = 0 := by omega
    have hy : y 0 = 𝔢 u := by simp [y, insertLetter]
    rw [ite_eq_left ⟨rfl, rfl, rfl⟩, ite_eq_right (by omega), add_zero, Finset.sum_range_one,
      ite_eq_left rfl, subword_one_insertLetter_zero k (by omega),
      splice_collapse_tail_eq k (by omega), hy, AInfinityAlgebra.taylor_of_two,
      zigzagStrictAInfinityAlgebra_m_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [InternalGrading.koszulTwist_apply_of_mem_zero _
      (by rw [zigzagStrictAInfinityAlgebra_grading_piece]
          exact zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G u)]
    simp [W, negOnePowCast_neg]

/-- The `m{F}` half of the Hochschild differential of a normalized cochain concentrated on the
words of length `N`, on a word with a vertex idempotent inserted at position `j` into letters of
path length one: only the collapses of everything but an idempotent at either end survive. -/
private theorem taylor_gradedCoderiv_insertLetter {F : ReducedTensorWords k Z →ₗ[k] Z}
    (hN : 2 ≤ N)
    (hF : LinearMap.IsHomogeneous F (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 1)
    (hFN : F ∘ₗ lengthProj k Z ⟨N, by omega⟩ = F)
    (hFe : ∀ v, degenerateWords k Z (𝔢 v) ≤ LinearMap.ker F)
    {a : ℕ → Z} (ha : ∀ i < N, a i ∈ zigzagIntegerGrade k G 1) {j : ℕ} (hj : j ≤ N) (u : V) :
    (𝒵).taylor (gradedCoderiv ((𝒵).grading.shift 1) F 1 (of k Z ⟨N + 1, by omega⟩
        (PiTensorProduct.tprod k fun i : Fin (N + 1) ↦ insertLetter a j (𝔢 u) i))) =
      (if j = 0 then -(𝔢 u * F (of k Z ⟨N, by omega⟩
          (PiTensorProduct.tprod k fun i : Fin N ↦ a i))) else 0) +
        (if j = N then F (of k Z ⟨N, by omega⟩
          (PiTensorProduct.tprod k fun i : Fin N ↦ a i)) * 𝔢 u else 0) := by
  rw [gradedCoderiv_of_tprod_of_homogeneous_nat _ F 1 (by omega) _ _
    (insertLetter_mem_shift_piece ha hj u)]
  simp only [map_sum, map_smul]
  rw [Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun d hd ↦
    taylor_splice_insertLetter hN hF hFN hFe ha hj u (Finset.mem_range.mp hp)
      (Finset.mem_range.mp hd)]
  -- Each of the two families of terms is supported at a single pair `(p, d)`.
  simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_range]
  congr 1 <;> split_ifs <;> first | rfl | omega

/-- The Koszul sign of the letters before position `p ≤ j`, none of which is the inserted
idempotent, is trivial. -/
private theorem negOnePowCast_sum_range_of_le {j p : ℕ} (hp : p ≤ j) :
    negOnePowCast k (1 * ∑ i ∈ Finset.range p, if i = j then (-1 : ℤ) else 0) = 1 := by
  rw [Finset.sum_eq_zero (fun i hi ↦ by
    rw [Finset.mem_range] at hi
    exact ite_eq_right (by omega)), mul_zero, negOnePowCast_zero]

/-- One term of the `F{m}` half of the Hochschild differential of a normalized cochain on a word
with an inserted vertex idempotent: the collapse of the block of `d` letters at position `p`. -/
private theorem apply_splice_taylor_insertLetter {F : ReducedTensorWords k Z →ₗ[k] Z}
    (hN : 2 ≤ N) (hFe : ∀ v, degenerateWords k Z (𝔢 v) ≤ LinearMap.ker F)
    {a : ℕ → Z} (ha : ∀ i < N, a i ∈ zigzagIntegerGrade k G 1) {j : ℕ} (hj : j ≤ N) (u : V)
    {p d : ℕ} (hp : p < N + 1) (hd : d < N + 1 + 1) :
    negOnePowCast k (1 * ∑ i ∈ Finset.range p, if i = j then (-1 : ℤ) else 0) •
        F (splice k (fun i : Fin (N + 1) ↦ insertLetter a j (𝔢 u) i) 0 (N + 1) p d
          ((𝒵).taylor (subword k (fun i : Fin (N + 1) ↦ insertLetter a j (𝔢 u) i) p d))) =
      (if p = j - 1 ∧ d = 2 ∧ 0 < j then -F (of k Z ⟨N, by omega⟩ (PiTensorProduct.tprod k
          fun i : Fin N ↦ Function.update a p (a p * 𝔢 u) i)) else 0) +
        (if p = j ∧ d = 2 ∧ j < N then F (of k Z ⟨N, by omega⟩ (PiTensorProduct.tprod k
          fun i : Fin N ↦ Function.update a p (𝔢 u * a p) i)) else 0) := by
  set y := fun i : Fin (N + 1) ↦ insertLetter a j (𝔢 u) i
  by_cases hd2 : d = 2
  swap
  · rw [zigzagStrictAInfinityAlgebra_taylor_subword_eq_zero_of_ne_two y p d hd2, splice_zero,
      map_zero, smul_zero, ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
  subst d
  by_cases hfit : p + 2 ≤ N + 1
  swap
  · rw [subword_eq_zero_of_lt_add k y (by omega), map_zero, splice_zero, map_zero, smul_zero,
      ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
  by_cases hblock : p ≤ j ∧ j < p + 2
  swap
  · -- The collapse leaves the idempotent in place, so `F` kills the spliced word.
    obtain ⟨z, ⟨i, hi⟩, hz⟩ := exists_splice_eq_of_tprod k y hfit
      ((𝒵).taylor (subword k y p 2)) (i := ⟨j, by omega⟩) hblock
    rw [hz, LinearMap.mem_ker.mp (hFe u (of_tprod_mem_degenerateWords
      ⟨N + 1 + 1 - 2, by omega⟩ z ⟨i, hi.trans (by simp [y, insertLetter])⟩)), smul_zero,
      ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
  rw [zigzagStrictAInfinityAlgebra_taylor_subword_two y p hfit,
    negOnePowCast_sum_range_of_le hblock.1, one_smul]
  rcases Nat.lt_or_ge p j with hpj | hpj
  · -- The idempotent is the second letter of the collapsed block.
    have hy₀ : y ⟨p, by omega⟩ = a p := by simp [y, insertLetter, hpj]
    have hpj' : p + 1 = j := by omega
    have hy₁ : y ⟨p + 1, by omega⟩ = 𝔢 u := by simp [y, insertLetter, hpj']
    rw [hy₀, hy₁, InternalGrading.koszulTwist_one_apply_of_mem _ (e := 1)
      (by rw [zigzagStrictAInfinityAlgebra_grading_piece]; exact ha p (by omega)),
      Int.negOnePow_one, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul,
      neg_mul, splice_neg, map_neg, splice_insertLetter k a _ _ (by omega) (by omega) (by omega),
      ite_eq_left (by and_intros <;> first | trivial | omega), ite_eq_right (by omega),
      add_zero]
  · -- The idempotent is the first letter of the collapsed block.
    obtain rfl : p = j := by omega
    have hy₀ : y ⟨p, by omega⟩ = 𝔢 u := by simp [y, insertLetter]
    have hy₁ : y ⟨p + 1, by omega⟩ = a p := by simp [y, insertLetter]
    rw [hy₀, hy₁, InternalGrading.koszulTwist_apply_of_mem_zero _
      (by rw [zigzagStrictAInfinityAlgebra_grading_piece]
          exact zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G u),
      splice_insertLetter k a _ _ le_rfl (by omega) (by omega), ite_eq_right (by omega),
      ite_eq_left (by and_intros <;> first | trivial | omega), zero_add]

/-- The `F{m}` half of the Hochschild differential of a normalized cochain, on a word with a
vertex idempotent inserted at position `j` into letters of path length one: only the products of
the idempotent with its two neighbours survive. -/
private theorem apply_gradedCoderiv_taylor_insertLetter {F : ReducedTensorWords k Z →ₗ[k] Z}
    (hN : 2 ≤ N) (hFe : ∀ v, degenerateWords k Z (𝔢 v) ≤ LinearMap.ker F)
    {a : ℕ → Z} (ha : ∀ i < N, a i ∈ zigzagIntegerGrade k G 1) {j : ℕ} (hj : j ≤ N) (u : V) :
    F (gradedCoderiv ((𝒵).grading.shift 1) (𝒵).taylor 1 (of k Z ⟨N + 1, by omega⟩
        (PiTensorProduct.tprod k fun i : Fin (N + 1) ↦ insertLetter a j (𝔢 u) i))) =
      (if 0 < j then -F (of k Z ⟨N, by omega⟩ (PiTensorProduct.tprod k fun i : Fin N ↦
          Function.update a (j - 1) (a (j - 1) * 𝔢 u) i)) else 0) +
        (if j < N then F (of k Z ⟨N, by omega⟩ (PiTensorProduct.tprod k fun i : Fin N ↦
          Function.update a j (𝔢 u * a j) i)) else 0) := by
  rw [gradedCoderiv_of_tprod_of_homogeneous_nat _ _ 1 (by omega) _ _
    (insertLetter_mem_shift_piece ha hj u)]
  simp only [map_sum, map_smul]
  rw [Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun d hd ↦
    apply_splice_taylor_insertLetter hN hFe ha hj u (Finset.mem_range.mp hp)
      (Finset.mem_range.mp hd)]
  -- Each of the two families of terms is supported at a single pair `(p, d)`.
  simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_range]
  congr 1 <;> split_ifs <;> first | rfl | omega

/-- **The cocycle condition on a word with an inserted vertex idempotent.** For a normalized
Hochschild cocycle of degree one concentrated on the words of length `N`, inserting a vertex
idempotent `e` at position `j` into letters `a` of path length one gives

```text
0 = -e F(a) [j = 0] + F(a) e [j = N] - F(…, a (j - 1) e, …) [0 < j] + F(…, e a j, …) [j < N].
``` -/
private theorem cocycle_insertLetter {F : ReducedTensorWords k Z →ₗ[k] Z} (hN : 2 ≤ N)
    (hF : LinearMap.IsHomogeneous F (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 1)
    (hFN : F ∘ₗ lengthProj k Z ⟨N, by omega⟩ = F) (hδF : (𝒵).hochschildDifferential 1 F = 0)
    (hFe : ∀ v, degenerateWords k Z (𝔢 v) ≤ LinearMap.ker F)
    {a : ℕ → Z} (ha : ∀ i < N, a i ∈ zigzagIntegerGrade k G 1) {j : ℕ} (hj : j ≤ N) (u : V) :
    (if j = 0 then -(𝔢 u * F (of k Z ⟨N, by omega⟩
          (PiTensorProduct.tprod k fun i : Fin N ↦ a i))) else 0) +
        (if j = N then F (of k Z ⟨N, by omega⟩
          (PiTensorProduct.tprod k fun i : Fin N ↦ a i)) * 𝔢 u else 0) +
      ((if 0 < j then -F (of k Z ⟨N, by omega⟩ (PiTensorProduct.tprod k fun i : Fin N ↦
          Function.update a (j - 1) (a (j - 1) * 𝔢 u) i)) else 0) +
        (if j < N then F (of k Z ⟨N, by omega⟩ (PiTensorProduct.tprod k fun i : Fin N ↦
          Function.update a j (𝔢 u * a j) i)) else 0)) = 0 := by
  have h : (𝒵).hochschildDifferential 1 F (of k Z ⟨N + 1, by omega⟩
      (PiTensorProduct.tprod k fun i : Fin (N + 1) ↦ insertLetter a j (𝔢 u) i)) = 0 := by
    rw [hδF, LinearMap.zero_apply]
  rwa [AInfinityAlgebra.hochschildDifferential_eq_brace_sub, LinearMap.sub_apply,
    LinearMap.smul_apply, brace_def, brace_def, LinearMap.comp_apply, LinearMap.comp_apply,
    taylor_gradedCoderiv_insertLetter hN hF hFN hFe ha hj u,
    apply_gradedCoderiv_taylor_insertLetter hN hFe ha hj u, negOnePowCast_one, neg_one_smul,
    sub_neg_eq_add] at h

end Differential

/-! ### Normalized cocycles on words of arrows -/

section Arrows

local notation "Z" => nonisolatedZigzagQuotient k G

variable {N : ℕ}

/-- The arrows of `N` darts, as a natural-indexed family of letters. -/
private noncomputable def arrowFamily (w : Fin N → G.Dart) (i : ℕ) : Z :=
  if h : i < N then 𝔞 (w ⟨i, h⟩) else 0

private theorem arrowFamily_mem (w : Fin N → G.Dart) :
    ∀ i < N, arrowFamily w i ∈ zigzagIntegerGrade k G 1 := fun i hi ↦ by
  rw [arrowFamily, dite_eq_left hi]
  exact zigzagMk_ofArrow_mem_zigzagIntegerGrade_one k G _

private theorem arrowFamily_fin (w : Fin N → G.Dart) :
    (fun i : Fin N ↦ arrowFamily (k := k) w i) = fun i ↦ 𝔞 (w i) :=
  funext fun i ↦ by simp [arrowFamily]

/-- Replacing one arrow of a word by zero kills the word. -/
private theorem tprod_update_arrowFamily_zero (w : Fin N → G.Dart) {p : ℕ} (hp : p < N) :
    (PiTensorProduct.tprod k fun i : Fin N ↦ Function.update (arrowFamily (k := k) w) p 0 i) =
      0 :=
  (PiTensorProduct.tprod k).map_coord_zero ⟨p, hp⟩ (by simp)

/-- Replacing one arrow of a word by itself does not change the word. -/
private theorem update_arrowFamily_self (w : Fin N → G.Dart) {p : ℕ} :
    Function.update (arrowFamily (k := k) w) p (arrowFamily w p) = arrowFamily w :=
  Function.update_eq_self _ _

/-- A normalized cocycle on the arrows of a word `w` takes values in the corner of the vertex
idempotent at the head of `w 0` on the left. -/
private theorem vertexIdempotent_mul_apply_arrows {F : ReducedTensorWords k Z →ₗ[k] Z} (hN : 2 ≤ N)
    (hF : LinearMap.IsHomogeneous F (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 1)
    (hFN : F ∘ₗ lengthProj k Z ⟨N, by omega⟩ = F) (hδF : (𝒵).hochschildDifferential 1 F = 0)
    (hFe : ∀ v, degenerateWords k Z (𝔢 v) ≤ LinearMap.ker F) (w : Fin N → G.Dart) :
    𝔢 (w ⟨0, by omega⟩).snd * F (of k Z ⟨N, by omega⟩ (PiTensorProduct.tprod k fun i ↦ 𝔞 (w i))) =
      F (of k Z ⟨N, by omega⟩ (PiTensorProduct.tprod k fun i ↦ 𝔞 (w i))) := by
  have h := cocycle_insertLetter hN hF hFN hδF hFe (arrowFamily_mem w) (j := 0) (by omega)
    (w ⟨0, by omega⟩).snd
  have he : 𝔢 (w ⟨0, by omega⟩).snd * arrowFamily (k := k) w 0 = arrowFamily w 0 := by
    rw [arrowFamily, dite_eq_left (by omega), zigzagMk_vertexIdempotent_mul_ofArrow]
  rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
    he, update_arrowFamily_self, arrowFamily_fin, add_zero, zero_add, neg_add_eq_zero] at h
  exact h

/-- A normalized cocycle on the arrows of a word `w` takes values in the corner of the vertex
idempotent at the tail of the last dart on the right. -/
private theorem apply_arrows_mul_vertexIdempotent {F : ReducedTensorWords k Z →ₗ[k] Z} (hN : 2 ≤ N)
    (hF : LinearMap.IsHomogeneous F (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 1)
    (hFN : F ∘ₗ lengthProj k Z ⟨N, by omega⟩ = F) (hδF : (𝒵).hochschildDifferential 1 F = 0)
    (hFe : ∀ v, degenerateWords k Z (𝔢 v) ≤ LinearMap.ker F) (w : Fin N → G.Dart) :
    F (of k Z ⟨N, by omega⟩ (PiTensorProduct.tprod k fun i ↦ 𝔞 (w i))) *
        𝔢 (w ⟨N - 1, by omega⟩).fst =
      F (of k Z ⟨N, by omega⟩ (PiTensorProduct.tprod k fun i ↦ 𝔞 (w i))) := by
  have h := cocycle_insertLetter hN hF hFN hδF hFe (arrowFamily_mem w) (j := N) le_rfl
    (w ⟨N - 1, by omega⟩).fst
  have he : arrowFamily (k := k) w (N - 1) * 𝔢 (w ⟨N - 1, by omega⟩).fst =
      arrowFamily w (N - 1) := by
    rw [arrowFamily, dite_eq_left (by omega), zigzagMk_ofArrow_mul_vertexIdempotent]
  rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left (by omega), ite_eq_right (by omega),
    he, update_arrowFamily_self, arrowFamily_fin, add_zero, zero_add, ← sub_eq_add_neg,
    sub_eq_zero] at h
  exact h

/-- A normalized cocycle vanishes on the arrows of a word `w` two of whose consecutive darts do not
compose. -/
private theorem apply_arrows_eq_zero_of_ne {F : ReducedTensorWords k Z →ₗ[k] Z} (hN : 2 ≤ N)
    (hF : LinearMap.IsHomogeneous F (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 1)
    (hFN : F ∘ₗ lengthProj k Z ⟨N, by omega⟩ = F) (hδF : (𝒵).hochschildDifferential 1 F = 0)
    (hFe : ∀ v, degenerateWords k Z (𝔢 v) ≤ LinearMap.ker F) (w : Fin N → G.Dart) {p : ℕ}
    (hp : p + 1 < N) (hw : (w ⟨p, by omega⟩).fst ≠ (w ⟨p + 1, hp⟩).snd) :
    F (of k Z ⟨N, by omega⟩ (PiTensorProduct.tprod k fun i ↦ 𝔞 (w i))) = 0 := by
  have h := cocycle_insertLetter hN hF hFN hδF hFe (arrowFamily_mem w) (j := p + 1) (by omega)
    (w ⟨p, by omega⟩).fst
  have he₁ : arrowFamily (k := k) w p * 𝔢 (w ⟨p, by omega⟩).fst = arrowFamily w p := by
    rw [arrowFamily, dite_eq_left (by omega), zigzagMk_ofArrow_mul_vertexIdempotent]
  have he₂ : 𝔢 (w ⟨p, by omega⟩).fst * arrowFamily (k := k) w (p + 1) = 0 := by
    rw [arrowFamily, dite_eq_left hp, zigzagMk_vertexIdempotent_mul_ofArrow_of_ne k G _ hw]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
    ite_eq_left (by omega), Nat.add_sub_cancel, he₁, update_arrowFamily_self, he₂,
    tprod_update_arrowFamily_zero w hp, map_zero, map_zero, arrowFamily_fin] at h
  simpa using h

end Arrows

/-! ### Volume classes -/

section Volume

local notation "Z" => nonisolatedZigzagQuotient k G

/-- The volume coordinate at `v` of the volume class at `v'`. -/
private theorem zigzagBasis_coord_zigzagVolume [DecidableEq V] (v v' : V) :
    (zigzagBasis k G hns).coord (.inr (.inr v)) (zigzagVolume k G v') =
      if v' = v then 1 else 0 := by
  rw [← zigzagBasisFun_inr_inr, ← zigzagBasis_apply k G hns, zigzagBasis_coord_apply]
  simp

/-- On the left, a vertex idempotent cuts an element of path length two down to its volume
coordinate at that vertex. -/
private theorem zigzagMk_vertexIdempotent_mul_of_mem_two {y : Z}
    (hy : y ∈ zigzagIntegerGrade k G 2) (v : V) :
    𝔢 v * y = (zigzagBasis k G hns).coord (.inr (.inr v)) y • zigzagVolume k G v := by
  classical
  rw [← Nat.cast_ofNat (R := ℤ) (n := 2), zigzagIntegerGrade_ofNat,
    zigzagGrade_two_eq_span_range_zigzagVolume] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v', rfl⟩ := hx
    rw [zigzagBasis_coord_zigzagVolume]
    rcases eq_or_ne v' v with rfl | h
    · simp
    · rw [zigzagMk_vertexIdempotent_mul_zigzagVolume_of_ne k G h.symm, ite_eq_right h,
        zero_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, hx, hy, map_add, add_smul]
  | smul r x _ hx => rw [mul_smul_comm, hx, map_smul, smul_eq_mul, mul_smul]

/-- On the right, a vertex idempotent cuts an element of path length two down to its volume
coordinate at that vertex. -/
private theorem mul_zigzagMk_vertexIdempotent_of_mem_two {y : Z}
    (hy : y ∈ zigzagIntegerGrade k G 2) (v : V) :
    y * 𝔢 v = (zigzagBasis k G hns).coord (.inr (.inr v)) y • zigzagVolume k G v := by
  classical
  rw [← Nat.cast_ofNat (R := ℤ) (n := 2), zigzagIntegerGrade_ofNat,
    zigzagGrade_two_eq_span_range_zigzagVolume] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v', rfl⟩ := hx
    rw [zigzagBasis_coord_zigzagVolume]
    rcases eq_or_ne v' v with rfl | h
    · simp
    · rw [zigzagVolume_mul_zigzagMk_vertexIdempotent_of_ne k G h.symm, ite_eq_right h,
        zero_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul, hx, hy, map_add, add_smul]
  | smul r x _ hx => rw [smul_mul_assoc, hx, map_smul, smul_eq_mul, mul_smul]

end Volume

/-! ### Normalized cocycles are loop operations -/

section Main

local notation "Z" => nonisolatedZigzagQuotient k G

/-- A normalized cocycle on the arrows of a word `w` is a multiple of the volume class at the head
of `w 0`, with its volume coordinate there as coefficient. -/
private theorem apply_arrows_eq_smul_zigzagVolume {N : ℕ} {F : ReducedTensorWords k Z →ₗ[k] Z}
    (hN : 2 ≤ N)
    (hF : LinearMap.IsHomogeneous F (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 1)
    (hFN : F ∘ₗ lengthProj k Z ⟨N, by omega⟩ = F) (hδF : (𝒵).hochschildDifferential 1 F = 0)
    (hFe : ∀ v, degenerateWords k Z (𝔢 v) ≤ LinearMap.ker F) (w : Fin N → G.Dart) :
    F (of k Z ⟨N, by omega⟩ (PiTensorProduct.tprod k fun i ↦ 𝔞 (w i))) =
      (zigzagBasis k G hns).coord (.inr (.inr (w ⟨0, by omega⟩).snd))
          (F (of k Z ⟨N, by omega⟩ (PiTensorProduct.tprod k fun i ↦ 𝔞 (w i)))) •
        zigzagVolume k G (w ⟨0, by omega⟩).snd := by
  have h2 := apply_mem_zigzagIntegerGrade_two (by omega) hF (arrowFamily_mem w)
  rw [arrowFamily_fin] at h2
  rw [← zigzagMk_vertexIdempotent_mul_of_mem_two h2,
    vertexIdempotent_mul_apply_arrows hN hF hFN hδF hFe w]

/-- A normalized cocycle vanishes on the arrows of every word which is not a closed walk. -/
private theorem fst_eq_snd_of_apply_arrows_ne_zero {n : ℕ}
    {F : ReducedTensorWords k Z →ₗ[k] Z}
    (hF : LinearMap.IsHomogeneous F (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 1)
    (hFN : F ∘ₗ lengthProj k Z ⟨n + 2, by omega⟩ = F) (hδF : (𝒵).hochschildDifferential 1 F = 0)
    (hFe : ∀ v, degenerateWords k Z (𝔢 v) ≤ LinearMap.ker F) (w : Fin (n + 2) → G.Dart)
    (h0 : F (of k Z ⟨n + 2, by omega⟩
      (PiTensorProduct.tprod k fun i ↦ zigzagMk k G (ofArrow (arrow G (w i).adj)))) ≠ 0)
    (i : Fin (n + 2)) :
    (w i).fst = (w (i + 1)).snd := by
  by_cases hi : i.val + 1 < n + 2
  · -- Two consecutive darts inside the word.
    have hi' : i + 1 = ⟨i.val + 1, hi⟩ := Fin.ext (Fin.val_add_one_of_lt (by
      rw [Fin.lt_def, Fin.val_last]; omega))
    by_contra hne
    exact h0 (apply_arrows_eq_zero_of_ne (by omega) hF hFN hδF hFe w (p := i.val) hi
      (by rwa [Fin.eta, ← hi']))
  · -- The last dart and the first.
    obtain rfl : i = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [Fin.last_add_one]
    by_contra hne
    apply h0
    have h := apply_arrows_mul_vertexIdempotent (N := n + 2) (by omega) hF hFN hδF hFe w
    have hl : (⟨n + 2 - 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := Fin.ext (by simp)
    rw [hl, apply_arrows_eq_smul_zigzagVolume (by omega) hF hFN hδF hFe w, smul_mul_assoc,
      zigzagVolume_mul_zigzagMk_vertexIdempotent_of_ne k G (i := (w ⟨0, by omega⟩).snd)
        (v := (w (Fin.last (n + 1))).fst) hne, smul_zero] at h
    rw [apply_arrows_eq_smul_zigzagVolume (by omega) hF hFN hδF hFe w]
    exact h.symm

/-- The obstruction of a loop deformation vanishes on a word one of whose letters is homogeneous
of path length other than one, such as a vertex idempotent or a volume class. -/
private theorem obstruction_of_tprod_eq_zero_of_mem {n : ℕ} (hn : 1 ≤ n)
    (c : (Fin (n + 2) → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)
    (y : Fin (n + 2) → Z) {i : Fin (n + 2)} {e : ℤ} (he : e ≠ 1)
    (hy : y i ∈ zigzagIntegerGrade k G e) :
    (zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨n + 2, by omega⟩
      (of k Z ⟨n + 2, by omega⟩ (PiTensorProduct.tprod k y)) = 0 := by
  simp only [AInfinityAlgebra.obstruction_def, LinearMap.comp_apply, LinearMap.sub_apply]
  rw [lengthProj_of_self, AInfinityAlgebra.taylor_of_tprod, AInfinityAlgebra.taylor_of_tprod,
    zigzagStrictAInfinityAlgebra_m_eq_zero (by dsimp only; omega), _root_.zero_apply, sub_zero,
    zigzagLoopAInfinityAlgebra_m_eq_linearCombination c hc (by omega),
    Finsupp.linearCombination_apply, Finsupp.sum, _root_.sum_apply]
  refine Finset.sum_eq_zero fun w _ ↦ ?_
  rw [_root_.smul_apply, zigzagLoopOperation_apply,
    Finset.prod_eq_zero (Finset.mem_univ i), zero_smul, smul_zero]
  refine zigzagBasis_coord_dart_eq_zero_of_mem_zigzagIntegerGrade k G hns _ he ?_
  have hy' : y i ∈ (zigzagLoopAInfinityAlgebra hns c hc).grading.piece e := by
    rwa [zigzagLoopAInfinityAlgebra_grading_piece]
  simpa using InternalGrading.koszulTwist_mem_piece _ hy' _

/-- A cochain of degree one vanishes on a word of letters of positive path length, at least one
of which has path length two: its value would have path length at least three. -/
private theorem apply_of_tprod_eq_zero_of_three_le {F : ReducedTensorWords k Z →ₗ[k] Z}
    (hF : LinearMap.IsHomogeneous F (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 1)
    {N : ℕ} (hN : 0 < N) (y : Fin N → Z) (𝒟 : Fin N → ℤ)
    (hy : ∀ i, y i ∈ zigzagIntegerGrade k G (𝒟 i + 1)) (h𝒟 : 1 ≤ ∑ i, 𝒟 i) :
    F (of k Z ⟨N, hN⟩ (PiTensorProduct.tprod k y)) = 0 := by
  have h := hF.map_mem (mem_gradedPiece_of_tprod ((𝒵).grading.shift 1) hN y 𝒟 fun i ↦ by
    rw [InternalGrading.shift_piece, zigzagStrictAInfinityAlgebra_grading_piece]
    exact hy i)
  rw [InternalGrading.shift_piece, zigzagStrictAInfinityAlgebra_grading_piece,
    zigzagIntegerGrade_eq_bot_of_three_le k G (by omega)] at h
  exact (Submodule.mem_bot k).mp h

/-- A normalized cocycle and a loop obstruction agree on a word of basis vectors when the
coefficient of every walk is the signed volume coordinate of the cocycle on its arrows. -/
private theorem obstruction_basis_eq {n : ℕ} (hn : 1 ≤ n) {F : ReducedTensorWords k Z →ₗ[k] Z}
    (hF : LinearMap.IsHomogeneous F (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 1)
    (hFn : F ∘ₗ lengthProj k Z ⟨n + 2, by omega⟩ = F) (hδF : (𝒵).hochschildDifferential 1 F = 0)
    (hFe : ∀ v, degenerateWords k Z (𝔢 v) ≤ LinearMap.ker F)
    (c : (Fin (n + 2) → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)
    (hcw : ∀ w, (((∏ i : Fin (n + 2), ((n + 1 - i : ℕ) : ℤ).negOnePow : ℤˣ) : ℤ) : k) * c w =
      (zigzagBasis k G hns).coord (.inr (.inr (w 0).snd))
        (F (of k Z ⟨n + 2, by omega⟩
          (PiTensorProduct.tprod k fun i ↦ zigzagMk k G (ofArrow (arrow G (w i).adj))))))
    (ι : Fin (n + 2) → ZigzagBasisIndex G) :
    (zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨n + 2, by omega⟩
        (of k Z ⟨n + 2, by omega⟩ (PiTensorProduct.tprod k fun i ↦ zigzagBasis k G hns (ι i))) =
      F (of k Z ⟨n + 2, by omega⟩ (PiTensorProduct.tprod k fun i ↦ zigzagBasis k G hns (ι i))) := by
  classical
  by_cases hι₀ : ∃ i v, ι i = .inl v
  · -- A vertex idempotent among the letters.
    obtain ⟨i, v, hi⟩ := hι₀
    rw [obstruction_of_tprod_eq_zero_of_mem hn c hc _ (i := i) (e := 0) (by norm_num)
      (by simpa [hi] using zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G v),
      LinearMap.mem_ker.mp (hFe v (of_tprod_mem_degenerateWords _ _ ⟨i, by simp [hi]⟩))]
  simp only [not_exists] at hι₀
  by_cases hι₂ : ∃ i v, ι i = .inr (.inr v)
  · -- A volume class among the letters, and otherwise arrows.
    obtain ⟨i, v, hi⟩ := hι₂
    rw [obstruction_of_tprod_eq_zero_of_mem hn c hc _ (i := i) (e := 2) (by norm_num)
      (by simpa [hi] using zigzagVolume_mem_zigzagIntegerGrade_two k G v)]
    let 𝒟 : Fin (n + 2) → ℤ := fun i ↦ if ∃ v, ι i = .inr (.inr v) then 1 else 0
    refine (apply_of_tprod_eq_zero_of_three_le hF (by omega) _ 𝒟 (fun t ↦ ?_) ?_).symm
    · rcases h : ι t with v' | d | v'
      · exact absurd h (hι₀ t v')
      · simpa [𝒟, h] using zigzagMk_ofArrow_mem_zigzagIntegerGrade_one k G d
      · simpa [𝒟, h, show (1 : ℤ) + 1 = 2 by norm_num] using
          zigzagVolume_mem_zigzagIntegerGrade_two k G v'
    · calc (1 : ℤ) = 𝒟 i := by simp [𝒟, hi]
        _ ≤ ∑ t, 𝒟 t := Finset.single_le_sum (fun t _ ↦ by dsimp only [𝒟]; split_ifs <;> norm_num)
            (Finset.mem_univ i)
  simp only [not_exists] at hι₂
  -- Only arrows: compare the coefficient of the walk with the volume coordinate.
  have hd : ∀ i, ∃ d, ι i = .inr (.inl d) := fun i ↦ by
    rcases h : ι i with v | d | v
    · exact absurd h (hι₀ i v)
    · exact ⟨d, rfl⟩
    · exact absurd h (hι₂ i v)
  choose w hw using hd
  have hι : (fun i ↦ zigzagBasis k G hns (ι i)) = fun i ↦ 𝔞 (w i) := funext fun i ↦ by simp [hw i]
  rw [hι, obstruction_zigzagLoopAInfinityAlgebra_of_tprod hn, hcw w]
  exact (apply_arrows_eq_smul_zigzagVolume (by omega) hF hFn hδF hFe w).symm

/-- **Loop operations are normalized relative to the vertex idempotents.** The obstruction of a
loop deformation, its operation of arity `n + 2`, vanishes on every word one of whose letters is a
vertex idempotent. -/
theorem degenerateWords_le_ker_obstruction_zigzagLoopAInfinityAlgebra {n : ℕ}
    (c : (Fin (n + 2) → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)
    (v : V) :
    degenerateWords k Z (𝔢 v) ≤
      LinearMap.ker ((zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨n + 2, by omega⟩) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- In arity two the obstruction vanishes: the two binary operations agree.
    rw [AInfinityAlgebra.obstruction_eq_zero_of_m_eq
      (zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading c hc)
      (zigzagLoopAInfinityAlgebra_m_two_eq_zigzagStrictAInfinityAlgebra_m_two c hc),
      LinearMap.ker_zero]
    exact le_top
  rw [degenerateWords_le_iff]
  rintro ⟨m, hm⟩ y ⟨i, hi⟩
  rw [LinearMap.mem_ker]
  by_cases hmn : m = n + 2
  · subst hmn
    exact obstruction_of_tprod_eq_zero_of_mem hn c hc y (e := 0) (by norm_num)
      (by rw [hi]; exact zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G v)
  · rw [AInfinityAlgebra.obstruction_def, LinearMap.comp_apply,
      lengthProj_of_of_ne k Z (fun h ↦ hmn (congrArg Subtype.val h)), map_zero]

/-- **Normalized Hochschild cocycles of a zigzag algebra are loop operations.** Let `F` be a
suspended Hochschild cochain of degree one of the strict zigzag algebra of a finite graph without
isolated vertices, concentrated on the words of length `n + 2` with `n ≥ 1`: a cochain of arity
`n + 2` and internal degree `-n`. Then `F` is a Hochschild cocycle vanishing on every word with a
vertex idempotent among its letters if and only if it is the operation of arity `n + 2` of a loop
deformation `TauCeti.zigzagLoopAInfinityAlgebra`, a linear combination of the loop operations
`TauCeti.zigzagLoopOperation` of closed walks of length `n + 2`. -/
theorem exists_obstruction_zigzagLoopAInfinityAlgebra_eq_iff {n : ℕ} (hn : 1 ≤ n)
    {F : ReducedTensorWords k Z →ₗ[k] Z}
    (hF : LinearMap.IsHomogeneous F (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 1)
    (hFn : F ∘ₗ lengthProj k Z ⟨n + 2, by omega⟩ = F) :
    (∃ (c : (Fin (n + 2) → G.Dart) →₀ k)
        (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd),
        (zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨n + 2, by omega⟩ = F) ↔
      (𝒵).hochschildDifferential 1 F = 0 ∧
        ∀ v, degenerateWords k Z (𝔢 v) ≤ LinearMap.ker F := by
  classical
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨hochschildDifferential_obstruction_zigzagLoopAInfinityAlgebra c hc,
      degenerateWords_le_ker_obstruction_zigzagLoopAInfinityAlgebra c hc⟩
  rintro ⟨hδF, hFe⟩
  have := Fintype.ofFinite V
  -- The coefficient of a walk is the signed volume coordinate of `F` on its arrows.
  have hss : (((∏ i : Fin (n + 2), ((n + 1 - i : ℕ) : ℤ).negOnePow : ℤˣ) : ℤ) : k) *
      (((∏ i : Fin (n + 2), ((n + 1 - i : ℕ) : ℤ).negOnePow : ℤˣ) : ℤ) : k) = 1 := by
    simp only [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  let c : (Fin (n + 2) → G.Dart) →₀ k := Finsupp.equivFunOnFinite.symm fun w ↦
    (((∏ i : Fin (n + 2), ((n + 1 - i : ℕ) : ℤ).negOnePow : ℤˣ) : ℤ) : k) *
      (zigzagBasis k G hns).coord (.inr (.inr (w 0).snd))
        (F (of k Z ⟨n + 2, by omega⟩ (PiTensorProduct.tprod k fun i ↦ 𝔞 (w i))))
  have hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd := fun w hw ↦
    fst_eq_snd_of_apply_arrows_ne_zero hF hFn hδF hFe w fun h0 ↦
      Finsupp.mem_support_iff.mp hw (by
        simp only [c, Finsupp.coe_equivFunOnFinite_symm, h0, map_zero, mul_zero])
  refine ⟨c, hc, linearMap_ext k Z fun m x ↦ ?_⟩
  obtain ⟨m, hm⟩ := m
  by_cases hmn : m = n + 2
  swap
  · rw [AInfinityAlgebra.obstruction_def, LinearMap.comp_apply,
      lengthProj_of_of_ne k Z (fun h ↦ hmn (congrArg Subtype.val h)), map_zero,
      apply_of_ne_of_comp_lengthProj (by omega) hFn hmn]
  subst hmn
  -- On the words of length `n + 2`, compare the two multilinear maps on basis vectors.
  have hext := Module.Basis.ext_multilinear
    (f := ((zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨n + 2, by omega⟩ ∘ₗ
      of k Z ⟨n + 2, hm⟩).compMultilinearMap (PiTensorProduct.tprod k))
    (g := (F ∘ₗ of k Z ⟨n + 2, hm⟩).compMultilinearMap (PiTensorProduct.tprod k))
    (fun _ ↦ zigzagBasis k G hns) fun ι ↦ by
      simpa only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply] using
        obstruction_basis_eq hn hF hFn hδF hFe c hc (fun w ↦ by
          simp only [c, Finsupp.coe_equivFunOnFinite_symm, ← mul_assoc, hss, one_mul]) ι
  simpa only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply] using
    congrArg (fun f ↦ f x) hext

end Main

end TauCeti
