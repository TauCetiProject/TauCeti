/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.IntegralNullVector
public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Recognition

/-!
# Integral matrices with a positive null vector are negative affine Cartan matrices

Let `M` be a symmetric integral matrix on a nonempty finite index set with diagonal entries `-2`,
nonnegative off-diagonal entries and connected graph of positive entries, and let `m` be a vector
with positive entries and coordinate gcd one such that `M m = 0`. Then, after a simultaneous
reindexing, `M` is the negative generalized Cartan matrix of a valid affine simply-laced diagram
and `m` is its vector of marks. Such matrices arise as the intersection matrices of the reducible
fibres of relatively minimal genus-one fibrations, whose components are `(-2)`-curves, with `m` the
primitive vector of multiplicities; the theorem is the combinatorial part of Kodaira's
classification of these fibres.

The proof first bounds the off-diagonal entries by the row identity `∑_{j ≠ i} Mᵢⱼ mⱼ = 2 mᵢ`:
two indices give `Mᵢⱼ mⱼ ≤ 2 mᵢ` and `Mᵢⱼ mᵢ ≤ 2 mⱼ`, so `Mᵢⱼ ≤ 2`. An entry `2` uses up both
rows, so its two indices are all of them, and the matrix is that of `Ã₁`. Otherwise every
off-diagonal entry is `0` or `1`, `M` is `A - 2I` for the adjacency matrix `A` of a connected
simple graph, and `m` is a nonzero additive function on that graph; the recognition theorem
`SimpleGraph.Connected.exists_sum_eq_two_mul_iff_existsUnique_affineDynkinType_iso` identifies the
graph, and `SimpleGraph.Iso.eq_gcd_smul_marks_comp` identifies `m` with the marks.

## Main results

* `Matrix.exists_affineDynkinType_of_mulVec_eq_zero`: **the affine matrix classification**.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 4, Theorems 4.3 and 4.8 and
  Table Aff 1.
* S. Schröer, *There is no Enriques surface over the integers*, arXiv:2004.07025v3, §3.
-/

public section

open Finset

namespace Matrix

variable {ι : Type*} [Fintype ι] {M : Matrix ι ι ℤ} {m : ι → ℤ}

/-- The row identity of a null vector of a matrix with diagonal `-2`: the off-diagonal terms of
row `i` add up to `2 mᵢ`. -/
private theorem sum_erase_mul_eq_two_mul [DecidableEq ι] (hdiag : ∀ i, M i i = -2)
    (hnull : M *ᵥ m = 0) (i : ι) :
    ∑ j ∈ univ.erase i, M i j * m j = 2 * m i := by
  have h := congrFun hnull i
  rw [mulVec, dotProduct, ← add_sum_erase _ _ (mem_univ i), hdiag] at h
  simp only [Pi.zero_apply] at h
  linarith

/-- A single off-diagonal term of row `i` is at most `2 mᵢ`. -/
private theorem mul_le_two_mul (hdiag : ∀ i, M i i = -2) (hoff : ∀ i j, i ≠ j → 0 ≤ M i j)
    (hpos : ∀ i, 0 < m i) (hnull : M *ᵥ m = 0) {i j : ι} (hij : i ≠ j) :
    M i j * m j ≤ 2 * m i := by
  classical
  rw [← sum_erase_mul_eq_two_mul hdiag hnull i]
  exact single_le_sum (fun k hk ↦ mul_nonneg (hoff i k (ne_of_mem_erase hk).symm) (hpos k).le)
    (mem_erase.2 ⟨hij.symm, mem_univ j⟩)

/-- The off-diagonal entries are at most `2`. -/
private theorem le_two (hsymm : ∀ i j, M i j = M j i) (hdiag : ∀ i, M i i = -2)
    (hoff : ∀ i j, i ≠ j → 0 ≤ M i j) (hpos : ∀ i, 0 < m i) (hnull : M *ᵥ m = 0) {i j : ι}
    (hij : i ≠ j) : M i j ≤ 2 := by
  have h₁ := mul_le_two_mul hdiag hoff hpos hnull hij
  have h₂ := mul_le_two_mul hdiag hoff hpos hnull hij.symm
  rw [hsymm j i] at h₂
  have h₀ := hoff i j hij
  have hi := hpos i
  have hj := hpos j
  by_contra! h
  nlinarith [mul_le_mul h₁ h₂ (mul_nonneg h₀ hi.le) (by linarith)]

/-- An entry `2` uses up its row: every other off-diagonal entry of that row vanishes, and the
null vector takes the same value at the two indices. -/
private theorem eq_zero_of_eq_two (hsymm : ∀ i j, M i j = M j i) (hdiag : ∀ i, M i i = -2)
    (hoff : ∀ i j, i ≠ j → 0 ≤ M i j) (hpos : ∀ i, 0 < m i) (hnull : M *ᵥ m = 0) {i j : ι}
    (hij : i ≠ j) (h2 : M i j = 2) :
    m i = m j ∧ ∀ k, k ≠ i → k ≠ j → M i k = 0 := by
  classical
  have h₁ := mul_le_two_mul hdiag hoff hpos hnull hij
  have h₂ := mul_le_two_mul hdiag hoff hpos hnull hij.symm
  rw [hsymm j i, h2] at h₂
  rw [h2] at h₁
  have hm : m i = m j := by linarith
  refine ⟨hm, fun k hki hkj ↦ ?_⟩
  have hrow := sum_erase_mul_eq_two_mul hdiag hnull i
  have hj : j ∈ univ.erase i := mem_erase.2 ⟨hij.symm, mem_univ j⟩
  have hk : k ∈ (univ.erase i).erase j := mem_erase.2 ⟨hkj, mem_erase.2 ⟨hki, mem_univ k⟩⟩
  rw [← add_sum_erase _ _ hj, h2, hm] at hrow
  have hrest : ∑ l ∈ (univ.erase i).erase j, M i l * m l = 0 := by linarith
  have hnonneg (l : ι) (hl : l ∈ (univ.erase i).erase j) : 0 ≤ M i l * m l :=
    mul_nonneg (hoff i l (ne_of_mem_erase (mem_of_mem_erase hl)).symm) (hpos l).le
  have hzero := (sum_eq_zero_iff_of_nonneg hnonneg).1 hrest k hk
  exact (mul_eq_zero.1 hzero).resolve_right (hpos k).ne'

/-- The case of an entry `2`: the two indices are all of them, and the pair is that of `Ã₁`. -/
private theorem exists_eq_A_one (hsymm : ∀ i j, M i j = M j i) (hdiag : ∀ i, M i i = -2)
    (hoff : ∀ i j, i ≠ j → 0 ≤ M i j)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b ↦ a ≠ b ∧ 0 < M a b) i j)
    (hpos : ∀ i, 0 < m i) (hprim : univ.gcd (fun i ↦ (m i).natAbs) = 1) (hnull : M *ᵥ m = 0)
    {i j : ι} (hij : i ≠ j) (h2 : M i j = 2) :
    ∃ e : ι ≃ Fin (TauCeti.AffineDynkinType.A 1).nodes,
      (∀ k l, M k l = -(TauCeti.AffineDynkinType.A 1).cartanMatrix (e k) (e l)) ∧
        ∀ k, m k = (TauCeti.AffineDynkinType.A 1).marks (e k) := by
  classical
  obtain ⟨hm, hi⟩ := eq_zero_of_eq_two hsymm hdiag hoff hpos hnull hij h2
  obtain ⟨-, hj⟩ := eq_zero_of_eq_two hsymm hdiag hoff hpos hnull hij.symm (by rw [hsymm, h2])
  -- No positive entry leaves `{i, j}`, so by connectedness every index is `i` or `j`.
  have hcover (k : ι) : k = i ∨ k = j := by
    induction hconn i k with
    | refl => exact .inl rfl
    | @tail a b _ hab ih =>
      by_contra! hb
      rcases ih with rfl | rfl
      · exact hab.2.ne' (hi b hb.1 hb.2)
      · exact hab.2.ne' (hj b hb.2 hb.1)
  -- The common value of the null vector is its coordinate gcd, which is one.
  have hm1 : m i = 1 := by
    have hgcd : univ.gcd (fun k ↦ (m k).natAbs) = (m i).natAbs := by
      refine dvd_antisymm (gcd_dvd (mem_univ i)) (Finset.dvd_gcd fun k _ ↦ ?_)
      rcases hcover k with rfl | rfl
      · rfl
      · rw [hm]
    rw [hprim] at hgcd
    have := Int.natAbs_of_nonneg (hpos i).le
    omega
  let e : ι ≃ Fin 2 :=
    { toFun k := if k = i then 0 else 1
      invFun := ![i, j]
      left_inv k := by rcases hcover k with rfl | rfl <;> simp [hij.symm]
      right_inv a := by fin_cases a <;> simp [hij.symm] }
  have hei : e i = 0 := by simp [e]
  have hej : e j = 1 := by simp [e, hij.symm]
  -- `Fin (A 1).nodes` is `Fin 2`; restate the entries there to compute with numerals.
  have hc (a b : Fin 2) :
      (TauCeti.AffineDynkinType.A 1).cartanMatrix a b = if a = b then 2 else -2 :=
    TauCeti.AffineDynkinType.cartanMatrix_A_one_apply a b
  refine ⟨e, fun k l ↦ ?_, fun k ↦ ?_⟩
  · refine Eq.trans ?_ (congrArg Neg.neg (hc (e k) (e l))).symm
    rcases hcover k with hk | hk <;> rcases hcover l with hl | hl <;>
      simp [hk, hl, hei, hej, hdiag, h2, hsymm j i]
  · rw [TauCeti.AffineDynkinType.marks_A_apply]
    rcases hcover k with rfl | rfl
    · exact hm1
    · rw [← hm, hm1]

/-- The case of off-diagonal entries `0` and `1`: they are the adjacency matrix of a connected
simple graph carrying the null vector as a nonzero additive function, so the recognition theorem
identifies the pair with that of a graphical affine diagram. -/
private theorem exists_isGraphical [Nonempty ι] (hsymm : ∀ i j, M i j = M j i)
    (hdiag : ∀ i, M i i = -2)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b ↦ a ≠ b ∧ 0 < M a b) i j)
    (hpos : ∀ i, 0 < m i) (hprim : univ.gcd (fun i ↦ (m i).natAbs) = 1) (hnull : M *ᵥ m = 0)
    (h01 : ∀ i j, i ≠ j → M i j = 0 ∨ M i j = 1) :
    ∃ t : TauCeti.AffineDynkinType, t.Valid ∧ ∃ e : ι ≃ Fin t.nodes,
      (∀ i j, M i j = -t.cartanMatrix (e i) (e j)) ∧ ∀ i, m i = t.marks (e i) := by
  classical
  let G : SimpleGraph ι := SimpleGraph.fromRel fun a b ↦ 0 < M a b
  have hadj (i j : ι) : G.Adj i j ↔ i ≠ j ∧ 0 < M i j := by
    simp only [G, SimpleGraph.fromRel_adj, hsymm j i, or_self]
  have hG : G.Connected := by
    refine ⟨fun i j ↦ ?_⟩
    rw [SimpleGraph.reachable_iff_reflTransGen]
    exact Relation.ReflTransGen.mono (fun a b hab ↦ (hadj a b).2 hab) _ _ (hconn i j)
  -- The null vector is a nonzero additive function on this graph.
  let a : ι → ℕ := fun i ↦ (m i).natAbs
  have hcast (i : ι) : (a i : ℤ) = m i := Int.natAbs_of_nonneg (hpos i).le
  -- Entry by entry, `M` is minus the matrix `2I - A` of this graph.
  have hM : M = -G.graphCartanMatrix ℤ := by
    ext i j
    rw [Matrix.neg_apply, SimpleGraph.graphCartanMatrix_apply]
    rcases eq_or_ne i j with rfl | hij
    · simp [hdiag]
    · rcases h01 i j hij with h | h <;> simp [hadj, h, hij]
  have hsum (i : ι) : ∑ j ∈ G.neighborFinset i, a j = 2 * a i := by
    have h := congrFun hnull i
    rw [hM, neg_mulVec, Pi.neg_apply, SimpleGraph.graphCartanMatrix_mulVec_apply,
      Pi.zero_apply] at h
    have : ((∑ j ∈ G.neighborFinset i, a j : ℕ) : ℤ) = ((2 * a i : ℕ) : ℤ) := by
      push_cast [hcast]
      linarith
    exact_mod_cast this
  have ha : a ≠ 0 := fun h ↦ by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := hcast i
    rw [h, Pi.zero_apply, Nat.cast_zero] at this
    exact (hpos i).ne this
  obtain ⟨t, ⟨ht, hg, ⟨e⟩⟩, -⟩ :=
    hG.exists_sum_eq_two_mul_iff_existsUnique_affineDynkinType_iso.1 ⟨a, ha, hsum⟩
  refine ⟨t, ht, e.toEquiv, fun i j ↦ ?_, fun i ↦ ?_⟩
  · rw [hM, Matrix.neg_apply, SimpleGraph.graphCartanMatrix_apply,
      TauCeti.AffineDynkinType.cartanMatrix_apply hg, RelIso.coe_fn_toEquiv]
    simp only [e.injective.eq_iff, e.map_adj_iff]
  · have h := congrFun (e.eq_gcd_smul_marks_comp ht hg hsum) i
    simp only [a, hprim, Nat.cast_one, one_smul] at h
    rw [← hcast, h, Function.comp_apply, RelIso.coe_fn_toEquiv]

/-- **The affine matrix classification.** A symmetric integral matrix on a nonempty finite index
set, with diagonal entries `-2`, nonnegative off-diagonal entries and connected graph of positive
entries, which kills a vector `m` with positive entries and coordinate gcd one, is the negative
generalized Cartan matrix of a valid affine simply-laced diagram under a simultaneous reindexing,
and the same reindexing sends `m` to the marks of the diagram.

For the intersection matrix of the components of a fibre of a relatively minimal genus-one
fibration with all components `(-2)`-curves, and `m` its primitive vector of multiplicities, this
says that the dual graph is an affine `ADE` diagram whose marks are the multiplicities. A single
index is excluded by the hypotheses: `[-2]` kills no positive vector. -/
theorem exists_affineDynkinType_of_mulVec_eq_zero [Nonempty ι]
    (hsymm : ∀ i j, M i j = M j i) (hdiag : ∀ i, M i i = -2)
    (hoff : ∀ i j, i ≠ j → 0 ≤ M i j)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b ↦ a ≠ b ∧ 0 < M a b) i j)
    (hpos : ∀ i, 0 < m i) (hprim : univ.gcd (fun i ↦ (m i).natAbs) = 1)
    (hnull : M *ᵥ m = 0) :
    ∃ t : TauCeti.AffineDynkinType, t.Valid ∧ ∃ e : ι ≃ Fin t.nodes,
      (∀ i j, M i j = -t.cartanMatrix (e i) (e j)) ∧ ∀ i, m i = t.marks (e i) := by
  classical
  by_cases h2 : ∃ i j, i ≠ j ∧ M i j = 2
  · obtain ⟨i, j, hij, h2⟩ := h2
    exact ⟨_, TauCeti.AffineDynkinType.valid_A.2 le_rfl,
      exists_eq_A_one hsymm hdiag hoff hconn hpos hprim hnull hij h2⟩
  push Not at h2
  -- Otherwise every off-diagonal entry is `0` or `1`.
  refine exists_isGraphical hsymm hdiag hconn hpos hprim hnull fun i j hij ↦ ?_
  have := le_two hsymm hdiag hoff hpos hnull hij
  have := hoff i j hij
  have := h2 i j hij
  omega

end Matrix
