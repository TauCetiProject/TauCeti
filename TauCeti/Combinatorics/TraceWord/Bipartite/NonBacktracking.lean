/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Bipartite.Basic
public import Mathlib.Analysis.Real.Sqrt
import TauCeti.Combinatorics.TraceWord.Bipartite.Coding
import TauCeti.Combinatorics.TraceWord.Coding
import TauCeti.Data.Fin.Basic

/-!
# Weighted counts for bipartite non-backtracking walks

Powers of the row block of a bipartite non-backtracking walk matrix expand over closed
bipartite words. Reversals are allowed only where the constituent walks join. For centered
independent entries, each contributing word reads each matrix position at least twice.

In the Füredi–Komlós code, a discovery can be followed immediately by a forced closing step
only at a join, and the weights of consecutive row and column discoveries are reciprocal.
This gives a factor per walk that is linear in the walk length, times a correction from the
jumps. With small entries and trace order proportional to the logarithm of the matrix size,
the correction tends to one for each fixed walk length.

## Main declarations

* `TauCeti.bipartiteNonbacktrackingWords` indexes the words that contribute to the trace moment.
* `TauCeti.sum_pow_card_bipartiteEdge_mul_pow_le_of_nonbacktracking` bounds the weighted sum
  that occurs in trace moments of bipartite non-backtracking walk matrices.

## References

* Z. D. Bai and Y. Q. Yin, *Limit of the smallest eigenvalue of a large dimensional sample
  covariance matrix*, Ann. Probab. 21 (1993), 1275–1294.
* Z. Füredi and J. Komlós, *The eigenvalues of random symmetric matrices*, Combinatorica 1
  (1981), 233–241.
-/

public section

open Finset

namespace TauCeti

variable {α β : Type*}

variable [Fintype α] [Fintype β]

/-- A scale whose successive ratios are the alternating row and column discovery weights. -/
private noncomputable def alternatingDiscoveryScale (d : ℝ) (t : ℕ) : ℝ :=
  if t % 2 = 0 then max 1 (Fintype.card α / d) else max 1 (Fintype.card β / d)

private theorem alternatingDiscoveryScale_bounds (d : ℝ) (t : ℕ) :
    let q := alternatingDiscoveryScale (α := α) (β := β) d t
    1 ≤ q ∧ q ≤ max 1 (max (Fintype.card α / d) (Fintype.card β / d)) := by
  simp only [alternatingDiscoveryScale]
  split_ifs
  · exact ⟨le_max_left _ _, max_le_max_left _ (le_max_left _ _)⟩
  · exact ⟨le_max_left _ _, max_le_max_left _ (le_max_right _ _)⟩

/-- The total weight of a discovery is the ratio of the scale at the new and old positions. -/
private theorem card_bipartiteVertexFinset_div_le {r l : ℕ} (hl : Even l) {d : ℝ}
    (hmul : (Fintype.card α / d : ℝ) * (Fintype.card β / d) = 1) (b : Fin r) (i : Fin l) :
    let q := alternatingDiscoveryScale (α := α) (β := β) d
    #(bipartiteVertexFinset (α := α) (β := β) (finRotate (r * l) (finProdFinEquiv (b, i))).val)
      / d ≤ q (i.val + 1) / q i.val := by
  have hpar : (finRotate (r * l) (finProdFinEquiv (b, i))).val % 2 = (i.val + 1) % 2 := by
    have ht : (finProdFinEquiv (b, i)).val = i.val + l * b.val := finProdFinEquiv_apply_val _
    rw [Fin.coe_finRotate_eq_ite, ht]
    have hblock : (l * b.val) % 2 = 0 :=
      Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp (hl.mul_right _))
    have htotal : (r * l) % 2 = 0 :=
      Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp (hl.mul_left _))
    split_ifs <;> omega
  have le_ratio {x y : ℝ} (hxy : x * y = 1) : y ≤ max 1 y / max 1 x := by
    rcases le_or_gt y 0 with hy | hy
    · exact hy.trans (by positivity)
    rw [le_div_iff₀ (zero_lt_one.trans_le (le_max_left _ _)), mul_max_of_nonneg _ _ hy.le,
      mul_one, mul_comm y, hxy, max_comm y 1]
  rw [card_bipartiteVertexFinset, hpar]
  by_cases hi : i.val % 2 = 0
  · have hn : (i.val + 1) % 2 ≠ 0 := by omega
    simpa [alternatingDiscoveryScale, hi, hn] using le_ratio hmul
  · have hn : (i.val + 1) % 2 = 0 := by omega
    simpa [alternatingDiscoveryScale, hi, hn] using
      le_ratio (mul_comm (Fintype.card α / d : ℝ) (Fintype.card β / d) ▸ hmul)

open Classical in
/-- The pairs of row and column words joined from non-backtracking blocks, with every edge
traversed at least twice. -/
noncomputable def bipartiteNonbacktrackingWords (r k : ℕ) :
    Finset ((Fin (r * (k + 1)) → α) × (Fin (r * (k + 1)) → β)) :=
  univ.filter fun uv ↦ BipartiteNonbacktracking k uv.1 uv.2 ∧
    (∀ t, ∃ s ≠ t, bipartiteEdge uv.1 uv.2 s = bipartiteEdge uv.1 uv.2 t)

/-- A word is admissible when it has no reversal inside any block and no single-use edge. -/
@[simp]
theorem mem_bipartiteNonbacktrackingWords {r k : ℕ}
    {uv : (Fin (r * (k + 1)) → α) × (Fin (r * (k + 1)) → β)} :
    uv ∈ bipartiteNonbacktrackingWords r k ↔
      BipartiteNonbacktracking k uv.1 uv.2 ∧
      (∀ t, ∃ s ≠ t, bipartiteEdge uv.1 uv.2 s = bipartiteEdge uv.1 uv.2 t) := by
  simp only [bipartiteNonbacktrackingWords, mem_filter, mem_univ, true_and]

variable [DecidableEq α] [DecidableEq β]

open Classical in
/-- Interleaving an admissible row and column word preserves repeated edges and the
non-backtracking condition within each block. -/
private theorem image_bipartiteNonbacktrackingWords_subset {r k : ℕ} :
    let l := 2 * (k + 1)
    let m := r * (k + 1)
    let e : Fin (r * l) ≃ Fin (2 * m) := finCongr (by dsimp [l, m]; ac_rfl)
    let w (uv : (Fin m → α) × (Fin m → β)) := bipartiteWord uv.1 uv.2 ∘ e
    (bipartiteNonbacktrackingWords (α := α) (β := β) r k).image w ⊆
      (Fintype.piFinset fun t : Fin (r * l) ↦ bipartiteVertexFinset t.val).filter fun f ↦
        (∀ t, ∃ s ≠ t, s(f s, f (finRotate _ s)) = s(f t, f (finRotate _ t))) ∧
        (∀ (b : Fin r) (i j : Fin l), i.val + 1 = j.val →
          f (finProdFinEquiv (b, i)) ≠ f (finRotate _ (finProdFinEquiv (b, j)))) := by
  intro l m e w
  have hlength : r * l = 2 * m := by dsimp [l, m]; ac_rfl
  have he (t : Fin (r * l)) : e (finRotate _ t) = finRotate _ (e t) := by
    simpa only [e] using t.finCongr_finRotate hlength
  intro f hf
  obtain ⟨uv, huv, rfl⟩ := mem_image.mp hf
  obtain ⟨hn, hrep⟩ := mem_bipartiteNonbacktrackingWords.mp huv
  refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, ?_, ?_⟩
  · intro t
    simpa only [w, Function.comp_apply, e, finCongr_apply, Fin.val_cast] using
      bipartiteWord_mem_bipartiteVertexFinset uv.1 uv.2 (e t)
  · intro t
    obtain ⟨s, hs, hedge⟩ := bipartiteWord_no_singleton_edge hrep (e t)
    refine ⟨e.symm s, ?_, ?_⟩
    · simpa only [Equiv.symm_apply_apply] using e.symm.injective.ne hs
    · simpa only [w, Function.comp_apply, he, Equiv.apply_symm_apply] using hedge
  · intro b i j hij
    have hrj : finRotate (r * l) (finProdFinEquiv (b, i)) = finProdFinEquiv (b, j) := by
      apply Fin.ext
      have hlt := (finProdFinEquiv (b, j)).isLt
      simp only [Fin.coe_finRotate_eq_ite, finProdFinEquiv_apply_val] at hlt ⊢
      split_ifs <;> omega
    have hmod : (e (finProdFinEquiv (b, i))).val % l = i.val := by
      simp only [e, finCongr_apply, Fin.val_cast, finProdFinEquiv_apply_val,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
    simpa only [w, Function.comp_apply, ← hrj, he] using
      (bipartiteNonbacktracking_iff_bipartiteWord _ _).mp hn (e (finProdFinEquiv (b, i))) (by
        rw [hmod, hij]
        exact j.isLt)

private theorem sum_pow_div_sqrt_mul_pow_le_of_nonbacktracking [Nonempty α] [Nonempty β]
    {r : ℕ} (hr : r ≠ 0) (k : ℕ) {γ : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) :
    let d : ℝ := √(Fintype.card α * Fintype.card β)
    let a : ℝ := max 1 (max (Fintype.card α / d) (Fintype.card β / d))
    let m := r * (k + 1)
    let l := 2 * (k + 1)
    ∑ uv ∈ bipartiteNonbacktrackingWords (α := α) (β := β) r k,
      γ ^ (2 * (2 * m + 2 - 2 * (#(univ.image uv.1) + #(univ.image uv.2)))) /
        d ^ (#(univ.image uv.1) + #(univ.image uv.2)) ≤
      (Fintype.card α / d) * ((((l : ℝ) + 1) * a) *
        (1 + ((l : ℝ) + 1) * a * ((2 * m : ℕ) * γ)) ^ l) ^ r := by
  classical
  dsimp only
  let m := r * (k + 1)
  let l := 2 * (k + 1)
  let d : ℝ := √(Fintype.card α * Fintype.card β)
  have hpos : 0 < (Fintype.card α : ℝ) * Fintype.card β :=
    mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos)
  have hd : 0 < d := Real.sqrt_pos.mpr hpos
  have hlength : r * l = 2 * m := by dsimp [l, m]; ac_rfl
  have : NeZero (r * l) := ⟨Nat.mul_ne_zero hr (by dsimp [l]; omega)⟩
  let e := finCongr hlength
  let q (i : Fin (l + 1)) := alternatingDiscoveryScale (α := α) (β := β) d i.val
  have hmul : (Fintype.card α / d : ℝ) * (Fintype.card β / d) = 1 := by
    rw [div_mul_div_comm, ← sq, Real.sq_sqrt hpos.le, div_self hpos.ne']
  let w (uv : (Fin m → α) × (Fin m → β)) := bipartiteWord uv.1 uv.2 ∘ e
  have hcard (uv) : #(univ.image (w uv)) = #(univ.image uv.1) + #(univ.image uv.2) := by
    simp only [w, ← image_image, image_univ_of_surjective e.surjective, card_image_bipartiteWord]
  have hw : Function.Injective w := fun uv uv' h ↦
    Prod.ext_iff.mpr (bipartiteWord_inj.mp (e.surjective.injective_comp_right h))
  let weight (f : Fin (r * l) → α ⊕ β) :=
    γ ^ (2 * (r * l + 2 - 2 * #(univ.image f))) / d ^ #(univ.image f)
  let W := bipartiteNonbacktrackingWords (α := α) (β := β) r k
  calc
    _ = ∑ f ∈ W.image w, weight f := by
      rw [sum_image hw.injOn]
      refine sum_congr rfl fun uv _ ↦ ?_
      simp only [weight, hcard, hlength, m, d]
    _ ≤ ∑ f ∈ Fintype.piFinset (fun t : Fin (r * l) ↦ bipartiteVertexFinset t.val) with
          (∀ t, ∃ s ≠ t, s(f s, f (finRotate _ s)) = s(f t, f (finRotate _ t))) ∧
          (∀ (b : Fin r) (i j : Fin l), i.val + 1 = j.val →
            f (finProdFinEquiv (b, i)) ≠ f (finRotate _ (finProdFinEquiv (b, j)))),
        weight f := sum_le_sum_of_subset_of_nonneg image_bipartiteNonbacktrackingWords_subset
          (fun f _ _ ↦ div_nonneg (pow_nonneg hγ₀ _) (pow_nonneg hd.le _))
    _ ≤ _ := by
      have hbound := sum_piFinset_pow_div_pow_card_image_le_of_nonbacktracking (B := r) (M := l)
        hγ₀ hγ₁ hd.le (fun t ↦ bipartiteVertexFinset t.val) (fun _ ↦ q)
        (fun _ i ↦ alternatingDiscoveryScale_bounds d i.val)
        (card_bipartiteVertexFinset_div_le ⟨k + 1, two_mul _⟩ hmul)
      have hA₀ : #(bipartiteVertexFinset (α := α) (β := β) 0) = Fintype.card α := by
        simp
      simpa only [weight, Fin.val_zero, hA₀, hlength] using hbound

/-- **Weighted enumeration of bipartite non-backtracking words.** For `p` row labels and
`n` column labels put `d = √(p * n)` and `a = max 1 (max (p / d) (n / d))`. Consider
closed words formed by joining `r > 0` alternating walks of length `l = 2 * (k + 1)` that
start and end on the row side. Each walk is non-backtracking internally, and each distinct
edge of the closed word is traversed at least twice.

If `0 ≤ γ ≤ 1`, `0 ≤ c` and `b² ≤ c * d * γ⁴`, the sum of the entry moment bounds
`(min c (b²))^e * b^(r*l - 2*e)`, where `e` is the number of distinct edges, is at most
`p * (c*d)^(r*(k+1)) * ((l+1)*a * (1 + (l+1)*a*r*l*γ)^l)^r`. -/
theorem sum_pow_card_bipartiteEdge_mul_pow_le_of_nonbacktracking {r : ℕ} (hr : r ≠ 0) (k : ℕ)
    {γ b c : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (hc : 0 ≤ c)
    (hbc : b ^ 2 ≤ c * √(Fintype.card α * Fintype.card β) * γ ^ 4) :
    let d : ℝ := √(Fintype.card α * Fintype.card β)
    let a : ℝ := max 1 (max (Fintype.card α / d) (Fintype.card β / d))
    let m := r * (k + 1)
    let l := 2 * (k + 1)
    ∑ uv ∈ bipartiteNonbacktrackingWords (α := α) (β := β) r k,
      min c (b ^ 2) ^ #(univ.image (bipartiteEdge uv.1 uv.2)) *
        b ^ (2 * m - 2 * #(univ.image (bipartiteEdge uv.1 uv.2))) ≤
      Fintype.card α * (c * d) ^ m * ((((l : ℝ) + 1) * a) *
        (1 + ((l : ℝ) + 1) * a * ((2 * m : ℕ) * γ)) ^ l) ^ r := by
  classical
  dsimp only
  let m := r * (k + 1)
  let d : ℝ := √(Fintype.card α * Fintype.card β)
  have : Nonempty (Fin m) := ⟨⟨0, Nat.mul_pos (Nat.pos_of_ne_zero hr) (Nat.succ_pos k)⟩⟩
  rcases isEmpty_or_nonempty α with hα | hα
  · have : IsEmpty ((Fin m → α) × (Fin m → β)) := inferInstance
    simp [bipartiteNonbacktrackingWords, m]
  rcases isEmpty_or_nonempty β with hβ | hβ
  · have : IsEmpty ((Fin m → α) × (Fin m → β)) := inferInstance
    simp only [bipartiteNonbacktrackingWords, m, univ_eq_empty, filter_empty, sum_empty]
    positivity
  have hd : 0 < d := Real.sqrt_pos.mpr
    (mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos))
  have henum := sum_pow_div_sqrt_mul_pow_le_of_nonbacktracking (α := α) (β := β) hr k hγ₀ hγ₁
  dsimp only at henum
  refine (sum_le_sum fun uv huv ↦
    pow_card_bipartiteEdge_mul_pow_le_of_no_singleton_edge (Nat.mul_ne_zero hr (Nat.succ_ne_zero k))
      (mem_bipartiteNonbacktrackingWords.mp huv).2 hc hbc).trans ?_
  rw [← mul_sum, mul_comm ((c * d) ^ m) d]
  refine (mul_le_mul_of_nonneg_left henum
    (mul_nonneg hd.le (pow_nonneg (mul_nonneg hc hd.le) _))).trans_eq ?_
  have hcancel : d * (c * d) ^ m * (Fintype.card α / d) =
      Fintype.card α * (c * d) ^ m := by field_simp
  rw [← mul_assoc, hcancel]

end TauCeti
