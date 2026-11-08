/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Constant
public import Mathlib.Tactic.GCongr

/-!
# Balanced replication for `Sym(3)` cochains on `K_k`

Balanced replication, kernel-checked (Lemma 6 and Corollary 7 of the paper).

Replace each vertex of `K_k` by a cluster of `q` vertices; put the identity on every edge inside
a cluster and the seed value on every edge between two clusters. For every cochain `α`, every
`k` and every `q ≥ 1`:

* `rep_defect`: the triangle defect is multiplied by exactly `q³`;
* `rep_attain`: a gauge constant on clusters costs exactly `q²` times its seed cost;
* `rep_lower`: every gauge, constant on clusters or not, costs at least `q²` times the seed
  minimum (the finite double count over the `q^k` sections);
* `rep_seed`: with `witness_k4`, the replicated seed on `K_{4q}` has `N = 8q³` and gauge minimum
  exactly `6q²`, so `N/D = 4q/3 = k/3` at every multiple of four;
* `h1_mul_of_seed`: with the star bound of `Constant`, any non-coboundary seed on `K_m` with
  `3N = mD` gives `h₁(K_{mq}) = mq/3` for every `q ≥ 1`;
* `h1_eq_four_mul`: the seed `w4` gives `h₁(K_{4q}) = 4q/3` for every `q ≥ 1`.

`cost` and `defect` are rewritten as sums over all pairs and triples with an order indicator by
`cost_eq_sum` and `defect_eq_sum` of `Sym3.Constant`, so that they can be reindexed by clusters.
-/

public section

namespace TauCeti.CoboundaryExpansion.Sym3

open Finset

variable {k : ℕ}

/-! ## Clusters

`finProdFinEquiv : Fin k × Fin q ≃ Fin (k * q)` sends `(i, a)` to `a + q * i`, so the vertices
of cluster `i` are the contiguous block `q * i, …, q * i + q - 1`. -/

/-- The cluster of a vertex of `K_{kq}`. -/
@[expose] def clus (q : ℕ) (x : Fin (k * q)) : Fin k := (finProdFinEquiv.symm x).1

/-- Vertex `a` of cluster `i`. -/
@[expose] def vert (q : ℕ) (i : Fin k) (a : Fin q) : Fin (k * q) := finProdFinEquiv (i, a)

@[simp] theorem clus_vert (q : ℕ) (i : Fin k) (a : Fin q) : clus q (vert q i a) = i := by
  simp [clus, vert]

/-- A sum over the vertices of `K_{kq}` is a sum over clusters and positions inside them. -/
private theorem sum_blocks {q : ℕ} (F : Fin (k * q) → ℕ) : ∑ x, F x = ∑ i, ∑ a, F (vert q i a) := by
  rw [← Equiv.sum_comp finProdFinEquiv F, Fintype.sum_prod_type]
  rfl

private theorem block_lt (a b i j q : ℕ) (ha : a < q) (hb : b < q) :
    a + q * i < b + q * j ↔ i < j ∨ (i = j ∧ a < b) := by
  rcases lt_trichotomy i j with h | rfl | h
  · have h' : q * (i + 1) ≤ q * j := Nat.mul_le_mul_left q h
    rw [Nat.mul_add, Nat.mul_one] at h'
    generalize q * i = X at *
    generalize q * j = Y at *
    constructor
    · intro; exact Or.inl h
    · intro; omega
  · constructor
    · intro hh; right; exact ⟨rfl, by omega⟩
    · rintro (hh | ⟨_, hh⟩)
      · exact absurd hh (lt_irrefl _)
      · omega
  · have h' : q * (j + 1) ≤ q * i := Nat.mul_le_mul_left q h
    rw [Nat.mul_add, Nat.mul_one] at h'
    generalize q * i = X at *
    generalize q * j = Y at *
    constructor
    · intro; omega
    · rintro (hh | ⟨hh, _⟩) <;> omega

/-- Vertices are ordered cluster first, then position. -/
private theorem vert_lt_iff {q : ℕ} (i j : Fin k) (a b : Fin q) :
    vert q i a < vert q j b ↔ i < j ∨ (i = j ∧ a < b) := by
  rw [Fin.lt_def]
  simp only [vert, finProdFinEquiv_apply_val]
  rw [block_lt _ _ _ _ _ a.isLt b.isLt, Fin.lt_def, Fin.lt_def, Fin.ext_iff]

/-! ## Balanced replication -/

/-- The replicated cochain on `K_{kq}`: the identity inside a cluster, the seed value between
clusters. -/
@[expose] def rep (q : ℕ) (α : Fin k → Fin k → S3) : Fin (k * q) → Fin (k * q) → S3 :=
  fun x y => if clus q x = clus q y then 1 else val α (clus q x) (clus q y)

/-- A triangle across three clusters carries the seed holonomy; any other triangle closes. -/
private theorem rep_tri {q : ℕ} (α : Fin k → Fin k → S3) (i j l : Fin k) (a b c : Fin q) :
    (if vert q i a < vert q j b ∧ vert q j b < vert q l c then
        moved (val (rep q α) (vert q i a) (vert q j b) * val (rep q α) (vert q j b) (vert q l c) *
          val (rep q α) (vert q l c) (vert q i a)) else 0) =
      if i < j ∧ j < l then moved (val α i j * val α j l * val α l i) else 0 := by
  by_cases hijl : i < j ∧ j < l
  · have h1 : vert q i a < vert q j b := (vert_lt_iff _ _ _ _).2 (Or.inl hijl.1)
    have h2 : vert q j b < vert q l c := (vert_lt_iff _ _ _ _).2 (Or.inl hijl.2)
    have hil : i < l := lt_trans hijl.1 hijl.2
    have h3 : ¬ vert q l c < vert q i a := not_lt.2 (lt_trans h1 h2).le
    simp only [h1, h2, hijl, and_self, ↓reduceIte]
    simp [val, rep, h1, h2, h3, hijl.1, hijl.2, hil, hijl.1.ne, hijl.2.ne, hil.ne, not_lt.2 hil.le]
  · simp only [hijl, ↓reduceIte]
    split_ifs with hord
    · have hxz : vert q i a < vert q l c := lt_trans hord.1 hord.2
      have h3 : ¬ vert q l c < vert q i a := not_lt.2 hxz.le
      rcases (vert_lt_iff _ _ _ _).1 hord.1 with hij | ⟨rfl, _⟩
      · rcases (vert_lt_iff _ _ _ _).1 hord.2 with hjl | ⟨rfl, _⟩
        · exact absurd ⟨hij, hjl⟩ hijl
        · simp [val, rep, hord.1, hord.2, h3, hij.ne, moved_one]
      · simp [val, rep, hord.1, hord.2, h3, moved_one]
    · rfl

/-- **The defect of the replicated cochain.** Each seed triangle has `q³` lifts across three
clusters, each with the seed holonomy; every other triangle closes. -/
theorem rep_defect (q : ℕ) (α : Fin k → Fin k → S3) :
    defect (rep q α) = q ^ 3 * defect α := by
  rw [defect_eq_sum, defect_eq_sum]
  simp only [hol, sum_blocks (q := q), rep_tri, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum]
  ring

private theorem rep_edge_attain {q : ℕ} (α : Fin k → Fin k → S3) (β : Fin k → S3) (i j : Fin k)
    (a b : Fin q) :
    (if vert q i a < vert q j b then moved ((β i)⁻¹ * rep q α (vert q i a) (vert q j b) * β j)
      else 0) = if i < j then moved ((β i)⁻¹ * α i j * β j) else 0 := by
  by_cases hij : i < j
  · simp only [(vert_lt_iff _ _ _ _).2 (Or.inl hij), hij, ↓reduceIte]
    simp [rep, val, hij, hij.ne]
  · simp only [hij, ↓reduceIte]
    split_ifs with h
    · rcases (vert_lt_iff _ _ _ _).1 h with h' | ⟨rfl, _⟩
      · exact absurd h' hij
      · simp [rep, moved_one]
    · rfl

/-- **Attainment.** A gauge constant on clusters costs `q²` times its seed cost. -/
theorem rep_attain (q : ℕ) (α : Fin k → Fin k → S3) (β : Fin k → S3) :
    cost (rep q α) (fun x => β (clus q x)) = q ^ 2 * cost α β := by
  rw [cost_eq_sum, cost_eq_sum]
  simp only [sum_blocks (q := q), clus_vert, rep_edge_attain, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
  ring

private theorem rep_edge_lower {q : ℕ} (α : Fin k → Fin k → S3) (γ : Fin (k * q) → S3) (i j : Fin k)
    (a b : Fin q) :
    (if i < j then moved ((γ (vert q i a))⁻¹ * α i j * γ (vert q j b)) else 0) ≤
      if vert q i a < vert q j b then
        moved ((γ (vert q i a))⁻¹ * rep q α (vert q i a) (vert q j b) * γ (vert q j b)) else 0 := by
  by_cases hij : i < j
  · simp only [(vert_lt_iff _ _ _ _).2 (Or.inl hij), hij, ↓reduceIte]
    simp [rep, val, hij, hij.ne]
  · simp only [hij, ↓reduceIte]
    exact Nat.zero_le _

/-! ## Sections -/

/-- Fixing one coordinate of a function `ι → Fin q` leaves `q ^ (|ι| - 1)` functions. -/
private theorem sum_one_coord {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} (j : ι)
    (H : Fin q → ℕ) :
    ∑ s : ι → Fin q, H (s j) = q ^ (Fintype.card ι - 1) * ∑ b, H b := by
  rw [← Equiv.sum_comp (Equiv.funSplitAt j (Fin q)).symm, Fintype.sum_prod_type]
  simp only [ne_eq, Equiv.funSplitAt_symm_apply, ↓reduceDIte, sum_const, card_univ,
    Fintype.card_pi, Fintype.card_fin, prod_const, Fintype.card_subtype_compl,
    Fintype.card_unique, smul_eq_mul]
  rw [Finset.mul_sum]

/-- Fixing two coordinates leaves `q ^ (k - 2)` functions. -/
private theorem sum_two_coords {q : ℕ} (i j : Fin k) (hij : i ≠ j) (G : Fin q → Fin q → ℕ) :
    ∑ s : Fin k → Fin q, G (s i) (s j) = q ^ (k - 2) * ∑ a, ∑ b, G a b := by
  rw [← Equiv.sum_comp (Equiv.funSplitAt i (Fin q)).symm, Fintype.sum_prod_type]
  have hj : j ≠ i := hij.symm
  have key : ∀ a : Fin q, ∑ s' : {x // x ≠ i} → Fin q,
      G ((Equiv.funSplitAt i (Fin q)).symm (a, s') i)
        ((Equiv.funSplitAt i (Fin q)).symm (a, s') j) =
      q ^ (k - 2) * ∑ b, G a b := by
    intro a
    have e : ∀ s' : {x // x ≠ i} → Fin q,
        G ((Equiv.funSplitAt i (Fin q)).symm (a, s') i)
          ((Equiv.funSplitAt i (Fin q)).symm (a, s') j) = G a (s' ⟨j, hj⟩) := by
      intro s'
      simp [Equiv.funSplitAt, Equiv.piSplitAt, hj]
    simp only [e]
    rw [sum_one_coord (ι := {x // x ≠ i}) ⟨j, hj⟩ (G a)]
    congr 2
    simp
    omega
  simp only [key, ← Finset.mul_sum]

/-- **The lower bound.** Every gauge of the replicated cochain, constant on clusters or not,
costs at least `q²` times the seed minimum. Proof: a section picks one vertex per cluster; each
of the `q^k` sections restricts the gauge to a gauge of the seed, costing at least `D`; each edge
between two clusters lies in exactly `q^(k-2)` sections; edges inside clusters cost `≥ 0`. -/
theorem rep_lower (q : ℕ) (hq : 0 < q) (α : Fin k → Fin k → S3) (D : ℕ)
    (hD : ∀ β : Fin k → S3, D ≤ cost α β) :
    ∀ γ : Fin (k * q) → S3, q ^ 2 * D ≤ cost (rep q α) γ := by
  intro γ
  by_cases hk : k < 2
  · have h0 : cost α (fun _ => 1) = 0 := by
      rw [cost_eq_sum]
      refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => ?_
      have huv : ¬ u < v := by
        intro huv; have := u.isLt; have := v.isLt; rw [Fin.lt_def] at huv; omega
      simp [huv]
    have : D = 0 := by have := hD (fun _ => 1); omega
    simp [this]
  · set G : Fin k → Fin k → Fin q → Fin q → ℕ := fun i j a b =>
      if i < j then moved ((γ (vert q i a))⁻¹ * α i j * γ (vert q j b)) else 0 with hG
    -- the cost between clusters is at most the full cost
    have hI' : ∑ i, ∑ a, ∑ j, ∑ b, G i j a b ≤ cost (rep q α) γ := by
      rw [cost_eq_sum]
      simp only [sum_blocks (q := q)]
      gcongr with i _ a _ j _ b _
      exact rep_edge_lower α γ i j a b
    have hswap : ∑ i, ∑ a, ∑ j, ∑ b, G i j a b = ∑ i, ∑ j, ∑ a, ∑ b, G i j a b :=
      Finset.sum_congr rfl fun i _ => Finset.sum_comm
    have hI : ∑ i, ∑ j, ∑ a, ∑ b, G i j a b ≤ cost (rep q α) γ := hswap ▸ hI'
    -- the section double count
    have hS : ∑ s : Fin k → Fin q, cost α (fun i => γ (vert q i (s i))) =
        q ^ (k - 2) * ∑ i, ∑ j, ∑ a, ∑ b, G i j a b := by
      simp only [cost_eq_sum]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i < j
      · exact sum_two_coords i j hij.ne (G i j)
      · simp [hG, hij]
    have hsec : q ^ k * D ≤ ∑ s : Fin k → Fin q, cost α (fun i => γ (vert q i (s i))) := by
      have := Finset.sum_le_sum fun (s : Fin k → Fin q) (_ : s ∈ Finset.univ) =>
        hD (fun i => γ (vert q i (s i)))
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        mul_comm] using this
    have hpow : q ^ k = q ^ (k - 2) * q ^ 2 := by
      rw [← pow_add]; congr 1; omega
    have hmain : q ^ (k - 2) * (q ^ 2 * D) ≤ q ^ (k - 2) * cost (rep q α) γ := by
      calc q ^ (k - 2) * (q ^ 2 * D) = q ^ k * D := by rw [hpow, mul_assoc]
        _ ≤ _ := hsec
        _ = _ := hS
        _ ≤ _ := Nat.mul_le_mul_left _ hI
    exact Nat.le_of_mul_le_mul_left hmain (pow_pos hq _)

/-- **The `k = 4q` seed.** The replicated `k = 4` witness has defect `8q³`, a gauge of cost
`6q²`, and no gauge cheaper than `6q²`: `N/D = 4q/3 = k/3` for every `q ≥ 1`. -/
theorem rep_seed (q : ℕ) (hq : 0 < q) :
    defect (rep q w4) = 8 * q ^ 3 ∧ cost (rep q w4) (fun _ => 1) = 6 * q ^ 2 ∧
      ∀ γ : Fin (4 * q) → S3, 6 * q ^ 2 ≤ cost (rep q w4) γ := by
  obtain ⟨hN, hD, hC, -⟩ := witness_k4
  refine ⟨by rw [rep_defect, hN]; ring, ?_,
    fun γ => by simpa [mul_comm] using rep_lower q hq w4 6 hD γ⟩
  have h := rep_attain q w4 (fun _ => 1)
  simpa [hC, mul_comm] using h

/-! ## The constant at every multiple of four -/

/-- The replicated seed has gauge distance exactly `6q²`. -/
theorem gaugeDist_rep_seed (q : ℕ) (hq : 0 < q) : gaugeDist (rep q w4) = 6 * q ^ 2 := by
  obtain ⟨-, hC, hlow⟩ := rep_seed q hq
  exact gaugeDist_eq_of hlow _ hC

/-- **Any seed replicates.** If a cochain on `K_m` is not a coboundary and `3N = mD`, then
`h₁(K_{mq}) = mq/3` for every `q ≥ 1`. -/
theorem h1_mul_of_seed {m : ℕ} (α : Fin m → Fin m → S3) (hpos : 0 < gaugeDist α)
    (hratio : 3 * defect α = m * gaugeDist α) (q : ℕ) (hq : 0 < q) :
    h1 (m * q) = ((m * q : ℕ) : ℝ) / 3 := by
  set D := gaugeDist α
  obtain ⟨β₀, hβ₀⟩ := exists_cost_eq_gaugeDist α
  have hatt' : cost (rep q α) (fun x => β₀ (clus q x)) = q ^ 2 * D := by
    rw [rep_attain, hβ₀]
  have hlow' : ∀ γ, q ^ 2 * D ≤ cost (rep q α) γ := rep_lower q hq α D (gaugeDist_le α)
  have hG : gaugeDist (rep q α) = q ^ 2 * D := gaugeDist_eq_of hlow' _ hatt'
  have hpos' : 0 < gaugeDist (rep q α) := by
    rw [hG]
    exact Nat.mul_pos (pow_pos hq 2) hpos
  apply le_antisymm
  · have h := h1_le_of_pos hpos'
    rw [hG, rep_defect] at h
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    have h3 : (3 : ℝ) * (defect α : ℝ) = (m : ℝ) * (D : ℝ) := by exact_mod_cast hratio
    have hdef : (defect α : ℝ) = (m : ℝ) * (D : ℝ) / 3 := by linarith
    calc h1 (m * q) ≤ ((q ^ 3 * defect α : ℕ) : ℝ) / ((q ^ 2 * D : ℕ) : ℝ) := h
      _ = ((m * q : ℕ) : ℝ) / 3 := by
        push_cast
        rw [hdef, div_eq_iff (mul_ne_zero (pow_ne_zero 2 hq0) hD0)]
        ring
  · exact k_div_three_le_h1 ⟨rep q α, hpos'⟩

/-- **Corollary 7.** `h₁(K_{4q}) = 4q/3` for every `q ≥ 1`: the coboundary constant equals `k/3`
at every multiple of four. -/
theorem h1_eq_four_mul (q : ℕ) (hq : 0 < q) : h1 (4 * q) = ((4 * q : ℕ) : ℝ) / 3 :=
  h1_mul_of_seed w4 (by rw [gaugeDist_w4]; norm_num) (by rw [witness_k4.1, gaugeDist_w4]) q hq

end TauCeti.CoboundaryExpansion.Sym3
