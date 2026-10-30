/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Analysis.Normed.Lp.lpSpace
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Normed.Lp.Dual
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Schur's theorem for ℓ¹

Over real or complex scalars, a sequence in ℓ¹ that converges weakly converges in norm
(`lp.tendsto_of_tendsto_toWeakSpace_one`). Thus weak and norm convergence agree for sequences
in ℓ¹, and more generally along every countably generated filter
(`lp.tendsto_toWeakSpace_iff_one`). This is the *Schur property* of ℓ¹: the basic example of a
space in which weakly convergent sequences converge in norm. Through the duality `c₀* = ℓ¹` it is
the input for the Dunford–Pettis property of `c₀`.

The index type is arbitrary, so the theorem covers ℓ¹ over uncountable index sets as well.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Theorem 2.3.6.
-/

public section

open Filter Topology

namespace lp

variable {𝕜 ι : Type*} [RCLike 𝕜]

/-- The gliding hump: if the mass of `x n` on every finite set of coordinates tends to zero while
`ε ≤ ‖x n‖` for infinitely many `n`, then there are indices `m 0 < m 1 < ⋯` and finite sets
`A 0 ⊆ A 1 ⊆ ⋯` such that `x (m k)` has mass less than `δ` on `A k` and more than `‖x (m k)‖ - δ`
on `A (k + 1)`. -/
private theorem exists_strictMono_monotone_of_frequently_le {x : ℕ → lp (fun _ : ι ↦ 𝕜) 1}
    (hcoord : ∀ A : Finset ι, Tendsto (fun n ↦ ∑ i ∈ A, ‖x n i‖) atTop (𝓝 0))
    {ε δ : ℝ} (hδ : 0 < δ) (hlarge : ∃ᶠ n in atTop, ε ≤ ‖x n‖) :
    ∃ (m : ℕ → ℕ) (A : ℕ → Finset ι), StrictMono m ∧ Monotone A ∧ ∀ k, ε ≤ ‖x (m k)‖ ∧
      ∑ i ∈ A k, ‖x (m k) i‖ < δ ∧ ‖x (m k)‖ - δ < ∑ i ∈ A (k + 1), ‖x (m k) i‖ := by
  -- One step: a late index of large norm with little mass on `A`, and a finite set `B ⊇ A`
  -- carrying all but `δ` of its mass.
  have hstep (A : Finset ι) (N : ℕ) : ∃ n, N < n ∧ ε ≤ ‖x n‖ ∧ ∑ i ∈ A, ‖x n i‖ < δ ∧
      ∃ B : Finset ι, A ⊆ B ∧ ‖x n‖ - δ < ∑ i ∈ B, ‖x n i‖ := by
    obtain ⟨n, hn, hnN, hnA⟩ :=
      (hlarge.and_eventually ((eventually_gt_atTop N).and
        ((hcoord A).eventually (gt_mem_nhds hδ)))).exists
    obtain ⟨B, hB, hAB⟩ :=
      (((hasSum_norm_one (x n)).eventually (Ioi_mem_nhds (sub_lt_self _ hδ))).and
      (eventually_ge_atTop A)).exists
    exact ⟨n, hnN, hn, hnA, B, hAB, hB⟩
  choose n hnN hn hnA B hAB hB using hstep
  -- Iterate the step from the empty set.
  let T : Finset ι × ℕ → Finset ι × ℕ := fun p ↦ (B p.1 p.2, n p.1 p.2)
  let A : ℕ → Finset ι := fun k ↦ (T^[k] (∅, 0)).1
  let m : ℕ → ℕ := fun k ↦ (T^[k + 1] (∅, 0)).2
  have hA_succ (k : ℕ) : A (k + 1) = B (A k) (T^[k] (∅, 0)).2 := by
    simp only [A, Function.iterate_succ_apply', T]
  have hm (k : ℕ) : m k = n (A k) (T^[k] (∅, 0)).2 := by
    simp only [m, A, Function.iterate_succ_apply', T]
  refine ⟨m, A, strictMono_nat_of_lt_succ fun k ↦ ?_, monotone_nat_of_le_succ fun k ↦ ?_,
    fun k ↦ ?_⟩
  · rw [hm (k + 1)]
    exact hnN _ _
  · rw [hA_succ]
    exact hAB _ _
  · rw [hA_succ, hm]
    exact ⟨hn _ _, hnA _ _, hB _ _⟩

/-- The block estimate: if `‖a i‖ ≤ 1` for all `i` and `a i * y i = ‖y i‖` on a finite set `D`,
then `∑ i, a i * y i` has norm at least `2 * ∑ i ∈ D, ‖y i‖ - ‖y‖`. -/
private theorem two_mul_sum_norm_sub_norm_le_of_hasSum {y : lp (fun _ : ι ↦ 𝕜) 1} {a : ι → 𝕜}
    {s : 𝕜} {D : Finset ι} (ha : ∀ i, ‖a i‖ ≤ 1) (hD : ∀ i ∈ D, a i * y i = ‖y i‖)
    (hs : HasSum (fun i ↦ a i * y i) s) :
    2 * ∑ i ∈ D, ‖y i‖ - ‖y‖ ≤ ‖s‖ := by
  classical
  -- Off `D`, `s` and `‖y‖` differ from their parts on `D` by at most the remaining mass.
  have hrest : ‖s - ((∑ i ∈ D, ‖y i‖ : ℝ) : 𝕜)‖ ≤ ‖y‖ - ∑ i ∈ D, ‖y i‖ := by
    have h := (hs.sub (hasSum_sum_of_ne_finset_zero (s := D)
        (f := fun i ↦ if i ∈ D then ((‖y i‖ : ℝ) : 𝕜) else 0)
        (by intro i hi; simp [hi]))).norm_le_of_bounded
      ((hasSum_norm_one y).sub (hasSum_sum_of_ne_finset_zero (s := D)
        (f := fun i ↦ if i ∈ D then ‖y i‖ else 0) (by intro i hi; simp [hi]))) fun i ↦ by
      split_ifs with hi
      · simpa using sub_eq_zero.2 (hD i hi)
      · simpa using mul_le_of_le_one_left (norm_nonneg _) (ha i)
    rw [Finset.sum_ite_of_true (fun _ hi ↦ hi), Finset.sum_ite_of_true (fun _ hi ↦ hi)] at h
    simpa using h
  have hnorm_cast : ‖((∑ i ∈ D, ‖y i‖ : ℝ) : 𝕜)‖ = ∑ i ∈ D, ‖y i‖ := by
    rw [RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
  have hlow := norm_sub_norm_le ((∑ i ∈ D, ‖y i‖ : ℝ) : 𝕜) (((∑ i ∈ D, ‖y i‖ : ℝ) : 𝕜) - s)
  rw [sub_sub_cancel, norm_sub_rev, hnorm_cast] at hlow
  linarith

/-- **Schur's theorem**, in the weakly null sequential form: a sequence in ℓ¹ on which every
continuous linear functional tends to zero tends to zero in norm. -/
private theorem tendsto_zero_of_forall_eval_tendsto {x : ℕ → lp (fun _ : ι ↦ 𝕜) 1}
    (hx : ∀ f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) 1), Tendsto (fun n ↦ f (x n)) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) := by
  -- If `ε ≤ ‖x n‖` for infinitely many `n`, the gliding hump gives a subsequence `x (m k)` with
  -- almost all its mass on the block `A (k + 1) \ A k`. The phase of `x (m k)` on that block, for
  -- every `k`, is a bounded family, hence a functional on ℓ¹ whose values on `x (m k)` stay at
  -- least `ε / 2` in norm, contradicting weak nullity.
  classical
  by_contra hnot
  obtain ⟨s, hs, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.1 hnot
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
  have hlarge : ∃ᶠ n in atTop, ε ≤ ‖x n‖ := hfreq.mono fun n hn ↦ by
    by_contra h
    exact hn (hball (by simpa using h))
  -- Weak nullity makes the mass of `x n` on any finite set of coordinates tend to zero.
  have hcoord (A : Finset ι) : Tendsto (fun n ↦ ∑ i ∈ A, ‖x n i‖) atTop (𝓝 0) := by
    simpa using
      tendsto_finsetSum A fun i _ ↦ (hx (lp.evalCLM 𝕜 (fun _ : ι ↦ 𝕜) 1 i)).norm
  obtain ⟨m, A, hmono, hAmono, hmA⟩ :=
    exists_strictMono_monotone_of_frequently_le hcoord (δ := ε / 8) (by positivity) hlarge
  -- The bounded family: on the block `A (k + 1) \ A k` it is the phase of `x (m k)`.
  choose c hc_norm hc_mul using RCLike.exists_norm_eq_mul_self (K := 𝕜)
  let a : ι → 𝕜 := fun i ↦ if h : ∃ k, i ∈ A (k + 1) then c (x (m (Nat.find h)) i) else 0
  have ha_norm (i : ι) : ‖a i‖ ≤ 1 := by
    simp only [a]
    split_ifs
    · exact (hc_norm _).le
    · simp
  have ha_block (k : ℕ) {i : ι} (hi : i ∈ A (k + 1) \ A k) : a i * x (m k) i = ‖x (m k) i‖ := by
    rw [Finset.mem_sdiff] at hi
    have h : ∃ k, i ∈ A (k + 1) := ⟨k, hi.1⟩
    have hfind : Nat.find h = k := (Nat.find_eq_iff h).2
      ⟨hi.1, fun j hj hij ↦ hi.2 (hAmono (Nat.succ_le_of_lt hj) hij)⟩
    have ha : a i = c (x (m (Nat.find h)) i) := dite_eq_left_of_eq_true (eq_true h)
    rw [ha, hfind, ← hc_mul]
  let F : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) 1) :=
    dualOneEquiv 𝕜 ι ⟨a, memℓp_infty ⟨1, by rintro _ ⟨i, rfl⟩; exact ha_norm i⟩⟩
  -- Every `F (x (m k))` stays at least `ε / 2` in norm.
  have hF (k : ℕ) : ε / 2 < ‖F (x (m k))‖ := by
    obtain ⟨h1, h2, h3⟩ := hmA k
    have hblock := two_mul_sum_norm_sub_norm_le_of_hasSum ha_norm (fun i hi ↦ ha_block k hi)
      (by simpa [F] using (F.hasSum_lp_single_mul (x (m k))))
    rw [Finset.sum_sdiff_eq_sub (hAmono k.le_succ)] at hblock
    linarith
  have hlim : Tendsto (fun k ↦ ‖F (x (m k))‖) atTop (𝓝 0) := by
    simpa using ((hx F).comp hmono.tendsto_atTop).norm
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds (half_pos hε))).exists
  exact (hF k).not_gt hk

/-- **Schur's theorem**: along a countably generated filter, in particular for sequences, weak
convergence in ℓ¹ implies norm convergence. -/
theorem tendsto_of_tendsto_toWeakSpace_one {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {x : α → lp (fun _ : ι ↦ 𝕜) 1} {y : lp (fun _ : ι ↦ 𝕜) 1}
    (hx : Tendsto (fun n ↦ toWeakSpace 𝕜 _ (x n)) l (𝓝 (toWeakSpace 𝕜 _ y))) :
    Tendsto x l (𝓝 y) := by
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  rw [← tendsto_sub_nhds_zero_iff]
  refine tendsto_zero_of_forall_eval_tendsto fun f ↦ ?_
  have hf : Tendsto (fun n ↦ f (x (u n))) atTop (𝓝 (f y)) :=
    TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto.1 (hx.comp hu) f
  simpa only [map_sub, Function.comp_apply] using tendsto_sub_nhds_zero_iff.2 hf

/-- Along a countably generated filter, weak and norm convergence agree in ℓ¹. -/
theorem tendsto_toWeakSpace_iff_one {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {x : α → lp (fun _ : ι ↦ 𝕜) 1} {y : lp (fun _ : ι ↦ 𝕜) 1} :
    Tendsto (fun n ↦ toWeakSpace 𝕜 _ (x n)) l (𝓝 (toWeakSpace 𝕜 _ y)) ↔ Tendsto x l (𝓝 y) :=
  ⟨tendsto_of_tendsto_toWeakSpace_one, fun h ↦
    ((toWeakSpaceCLM 𝕜 _).continuous.tendsto y).comp h⟩

end lp
