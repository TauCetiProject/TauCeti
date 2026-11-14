/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
import TauCeti.Algebra.BigOperators.Group.Finset.Indicator
import TauCeti.Algebra.BigOperators.Intervals

/-!
# Reindexing sequences in `ℓᵖ`

Let `f : ι → G` be a sequence in `ℓᵖ` and let `g : ι' → ι` be injective on a set `s ⊆ ι'`. The
sequence `s.indicator (f ∘ g)`, which reads `f` along `g` on `s` and vanishes off `s`, takes each
value of `f` at most once, so it again lies in `ℓᵖ`, with no larger norm
(`Memℓp.indicator_comp`, `lp.norm_le_of_forall_eq_indicator_comp`). Shifts of a sequence indexed
by `ℕ` are the basic examples: `j ↦ f (j + d)` and, on `{j | d ≤ j}`, `j ↦ f (j - d)`. In
particular a sequence indexed by `ℕ` lies in `ℓᵖ` exactly when its tail `j ↦ f (j + d)` does
(`TauCeti.memℓp_nat_add_iff`).

Consequently the **window sums** `j ↦ ∑_{j - L ≤ k < j + L} f k` of a sequence indexed by `ℕ`,
a sum of `2 L` shifts, lie in `ℓᵖ`, and for `1 ≤ p` their norm is at most `2 L ‖f‖`
(`Memℓp.sum_Ico_sub_add`, `lp.norm_le_of_forall_eq_sum_Ico_sub_add`). Such sums arise when a
sequence of dyadic pieces is replaced by another one in which each piece only interacts with the
pieces of nearby index, as for two Littlewood–Paley decompositions of the same function.

More generally, a matrix `w j k` dominated by a summable kernel `a : ℤ → ℝ` of the offset,
`‖w j k‖ ≤ c a(k - j) ‖x k‖`, has row sums `∑ₖ w j k` forming a sequence in `ℓᵖ` of norm at most
`c (∑_{d ∈ ℤ} a d) ‖x‖`: it is a sum over the offsets `d = k - j` of shifts weighted by `a d`
(`lp.exists_hasSum_and_norm_le_of_summable`). With the geometric kernel `a d = r^{|d|}`, `r < 1`,
this is how an operator that moves the Littlewood–Paley blocks of a function to blocks of nearby
index, with geometric decay in the distance, is bounded on dyadic sequence spaces.

Similarly, for `0 ≤ r < 1` the **geometric tail sums** `j ↦ ∑_{d ≥ 0} r ^ d f (j + d)` and
**geometric prefix sums** `m ↦ ∑_{k < m} r ^ (m - k) f k` of a sequence in `ℓᵖ`, `1 ≤ p`, form
sequences in `ℓᵖ` of norm at most `(1 - r)⁻¹ ‖f‖` and `r (1 - r)⁻¹ ‖f‖`
(`lp.exists_forall_hasSum_pow_smul_add_and_norm_le`,
`lp.exists_forall_eq_sum_pow_smul_and_norm_le`): both are absolutely convergent series of shifts,
arising when each dyadic piece interacts with all pieces of higher or lower index with
geometrically decaying weights.
-/

public section

open scoped ENNReal

variable {ι ι' G : Type*} [NormedAddCommGroup G] {p : ℝ≥0∞}

/-- **Reindexing in `ℓᵖ`.** If `f ∈ ℓᵖ` and `g` is injective on `s`, then the sequence that reads
`f` along `g` on `s` and vanishes off `s` lies in `ℓᵖ`. -/
theorem Memℓp.indicator_comp {f : ι → G} (hf : Memℓp f p) {g : ι' → ι} {s : Set ι'}
    (hg : s.InjOn g) : Memℓp (s.indicator (f ∘ g)) p := by
  rcases p.trichotomy with rfl | rfl | hp
  · refine memℓp_zero (Set.Finite.of_finite_image (hf.finite_dsupport.subset ?_) (hg.mono ?_))
    · rintro _ ⟨j, hj, rfl⟩
      by_cases hjs : j ∈ s
      · simpa [hjs] using hj
      · simp [hjs] at hj
    · intro j hj
      by_contra hjs
      simp [hjs] at hj
  · obtain ⟨C, hC⟩ := hf.bddAbove
    refine memℓp_infty ⟨max C 0, ?_⟩
    rintro _ ⟨j, rfl⟩
    by_cases hj : j ∈ s
    · simp [hj, hC ⟨g j, rfl⟩]
    · simp [hj]
  · classical
    refine memℓp_gen' (C := ∑' k, ‖f k‖ ^ p.toReal) fun t ↦ ?_
    exact (Finset.sum_apply_indicator_comp_eq_sum_image (h := fun x : G ↦ ‖x‖ ^ p.toReal)
      (by simp [Real.zero_rpow hp.ne']) hg t).trans_le
      ((hf.summable hp).sum_le_tsum _ fun k _ ↦ by positivity)

/-- **Reindexing in `ℓᵖ` does not increase the norm.** If `g` is injective on `s` and `f'` reads
`f` along `g` on `s` and vanishes off `s`, then `‖f'‖ ≤ ‖f‖`. -/
theorem lp.norm_le_of_forall_eq_indicator_comp (hp : p ≠ 0) {f : lp (fun _ : ι ↦ G) p}
    {f' : lp (fun _ : ι' ↦ G) p} {g : ι' → ι} {s : Set ι'} (hg : s.InjOn g)
    (h : ∀ j, f' j = s.indicator (f ∘ g) j) : ‖f'‖ ≤ ‖f‖ := by
  rcases p.trichotomy with rfl | rfl | hp'
  · exact absurd rfl hp
  · refine lp.norm_le_of_forall_le (lp.norm_nonneg' f) fun j ↦ ?_
    rw [h j]
    by_cases hj : j ∈ s
    · simpa [hj] using lp.norm_apply_le_norm hp f (g j)
    · simp [hj, lp.norm_nonneg' f]
  · classical
    refine lp.norm_le_of_forall_sum_le hp' (lp.norm_nonneg' f) fun t ↦ ?_
    simp_rw [h]
    exact (Finset.sum_apply_indicator_comp_eq_sum_image (h := fun x : G ↦ ‖x‖ ^ p.toReal)
      (by simp [Real.zero_rpow hp'.ne']) hg t).trans_le (lp.sum_rpow_le_norm_rpow hp' f _)

namespace TauCeti

/-- **Dropping the first terms.** A sequence indexed by `ℕ` lies in `ℓᵖ` exactly when its tail
`j ↦ f (j + d)` does. -/
theorem memℓp_nat_add_iff {f : ℕ → G} (d : ℕ) : Memℓp (fun j ↦ f (j + d)) p ↔ Memℓp f p := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · -- `f` is its first `d` terms plus its tail shifted back by `d`.
    have h0 : Memℓp ({j | j < d}.indicator f) p :=
      (memℓp_zero ((Set.finite_lt_nat d).subset fun j hj ↦
        by_contra fun h ↦ hj (Set.indicator_of_notMem h _))).of_exponent_ge zero_le
    have h1 := hf.indicator_comp (g := fun j ↦ j - d) (s := {j | d ≤ j})
      fun a ha b hb h ↦ by simp only [Set.mem_ofPred_eq] at ha hb h; omega
    convert h0.add h1 using 1
    funext j
    by_cases hj : j < d
    · simp [hj]
    · have hj' : d ≤ j := not_lt.1 hj
      simp [hj, Set.indicator_of_mem (s := {j | d ≤ j}) hj', Nat.sub_add_cancel hj']
  · simpa [Function.comp_def] using hf.indicator_comp (g := fun j ↦ j + d) (s := Set.univ)
      fun a _ b _ h ↦ add_right_cancel h

end TauCeti

/-- **Window sums in `ℓᵖ`.** If `f ∈ ℓᵖ`, then so is `j ↦ ∑_{j - L ≤ k < j + L} f k`. -/
theorem Memℓp.sum_Ico_sub_add {f : ℕ → G} (hf : Memℓp f p) (L : ℕ) :
    Memℓp (fun j ↦ ∑ k ∈ Finset.Ico (j - L) (j + L), f k) p := by
  simp_rw [Finset.sum_Ico_sub_add_eq_sum_range_indicator]
  exact Memℓp.finsetSum _ fun d _ ↦
    hf.indicator_comp fun _ hi _ hi' h ↦ add_right_cancel (tsub_inj_left hi hi' h)

/-- **The norm of window sums.** For `1 ≤ p`, the sequence `j ↦ ∑_{j - L ≤ k < j + L} f k` has
`ℓᵖ` norm at most `2 L ‖f‖`. -/
theorem lp.norm_le_of_forall_eq_sum_Ico_sub_add [Fact (1 ≤ p)] {f f' : lp (fun _ : ℕ ↦ G) p}
    (L : ℕ) (h : ∀ j, f' j = ∑ k ∈ Finset.Ico (j - L) (j + L), f k) : ‖f'‖ ≤ 2 * L * ‖f‖ := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hg : ∀ d, {i | L ≤ i + d}.InjOn fun i ↦ i + d - L :=
    fun _ _ hi _ hi' h ↦ add_right_cancel (tsub_inj_left hi hi' h)
  set T : ℕ → lp (fun _ : ℕ ↦ G) p := fun d ↦
    ⟨{i | L ≤ i + d}.indicator (f ∘ fun i ↦ i + d - L),
      (lp.memℓp f).indicator_comp (hg d)⟩
  have hT : ∀ d, ‖T d‖ ≤ ‖f‖ := fun d ↦
    lp.norm_le_of_forall_eq_indicator_comp hp (hg d) fun _ ↦ rfl
  have hf' : f' = ∑ d ∈ Finset.range (2 * L), T d := by
    ext j
    rw [h, Finset.sum_Ico_sub_add_eq_sum_range_indicator, lp.coeFn_sum, Finset.sum_apply]
  calc ‖f'‖ ≤ ∑ d ∈ Finset.range (2 * L), ‖T d‖ := hf' ▸ norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.range (2 * L), ‖f‖ := Finset.sum_le_sum fun d _ ↦ hT d
    _ = 2 * L * ‖f‖ := by simp

/-- **Interactions dominated by a summable kernel in `ℓᵖ`.** Let `1 ≤ p`, `0 ≤ c`,
`x ∈ ℓᵖ(ℕ, G)` with `G` complete, and `a : ℤ → ℝ` nonnegative and summable. If
`‖w j k‖ ≤ c a(k - j) ‖x k‖` for all `j, k`, then for every `j` the series `∑ₖ w j k` converges,
and its sums form a sequence `y ∈ ℓᵖ` with `‖y‖ ≤ c (∑_{d ∈ ℤ} a d) ‖x‖`. This is Young's
inequality for the convolution of a sequence in `ℓᵖ` with the summable kernel `a`, for a matrix
dominated by it. -/
theorem lp.exists_hasSum_and_norm_le_of_summable [Fact (1 ≤ p)] [CompleteSpace G]
    (x : lp (fun _ : ℕ ↦ G) p) {a : ℤ → ℝ} (ha0 : ∀ d, 0 ≤ a d) (ha : Summable a) {c : ℝ}
    (hc : 0 ≤ c) (w : ℕ → ℕ → G) (hw : ∀ j k, ‖w j k‖ ≤ c * a ((k : ℤ) - j) * ‖x k‖) :
    ∃ y : lp (fun _ : ℕ ↦ G) p, (∀ j, HasSum (w j) (y j)) ∧ ‖y‖ ≤ c * (∑' d, a d) * ‖x‖ := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  -- Group the entries by the offset `d = k - j`: the `d`-th group is `j ↦ w j (j + d)`, defined
  -- where `j + d ≥ 0`, and is dominated by `c a(d)` times a shift of `x`.
  have hinj (d : ℤ) : {j : ℕ | 0 ≤ (j : ℤ) + d}.InjOn fun j : ℕ ↦ ((j : ℤ) + d).toNat :=
    fun i hi j hj hij ↦ by
      have := congrArg (fun n : ℕ ↦ (n : ℤ)) hij
      simp only [Int.toNat_of_nonneg hi, Int.toNat_of_nonneg hj] at this
      exact_mod_cast add_right_cancel this
  set z : ℤ → lp (fun _ : ℕ ↦ G) p := fun d ↦
    ⟨{j : ℕ | 0 ≤ (j : ℤ) + d}.indicator (x ∘ fun j : ℕ ↦ ((j : ℤ) + d).toNat),
      (lp.memℓp x).indicator_comp (hinj d)⟩
  have hz (d : ℤ) : ‖z d‖ ≤ ‖x‖ :=
    lp.norm_le_of_forall_eq_indicator_comp hp (hinj d) fun _ ↦ rfl
  set t : ℤ → ℕ → G := fun d j ↦ if 0 ≤ (j : ℤ) + d then w j ((j : ℤ) + d).toNat else 0
  have ht (d : ℤ) (j : ℕ) : ‖t d j‖ ≤ c * a d * ‖(z d : ℕ → G) j‖ := by
    by_cases hj : 0 ≤ (j : ℤ) + d
    · have hk : (((j : ℤ) + d).toNat : ℤ) - j = d := by rw [Int.toNat_of_nonneg hj]; ring
      simp only [t, z, hj, ↓reduceIte]
      rw [Set.indicator_of_mem (show j ∈ {j : ℕ | 0 ≤ (j : ℤ) + d} from hj)]
      refine (hw j _).trans_eq ?_
      rw [hk, Function.comp_apply]
    · have h0 : 0 ≤ c * a d * ‖(z d : ℕ → G) j‖ := by have := ha0 d; positivity
      simpa [t, hj] using h0
  set T : ℤ → lp (fun _ : ℕ ↦ G) p := fun d ↦
    ⟨t d, ((lp.memℓp (z d)).norm.const_mul (c * a d)).mono (ht d)⟩
  have hT (d : ℤ) : ‖T d‖ ≤ c * ‖x‖ * a d := by
    -- Compare with the real sequence of the norms of `z d`.
    have had := ha0 d
    set n : lp (fun _ : ℕ ↦ ℝ) p := ⟨fun j ↦ ‖(z d : ℕ → G) j‖, (lp.memℓp (z d)).norm⟩
    calc ‖T d‖ ≤ ‖(c * a d) • n‖ := lp.norm_mono hp fun j ↦ by
          rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
          exact ht d j
      _ ≤ c * a d * ‖x‖ := by
          rw [lp.norm_const_smul hp, Real.norm_of_nonneg (by positivity)]
          gcongr
          exact (lp.norm_mono hp fun j ↦ (norm_norm _).le).trans (hz d)
      _ = _ := by ring
  have hTs : Summable T := Summable.of_norm_bounded (ha.mul_left (c * ‖x‖)) hT
  refine ⟨∑' d, T d, fun j ↦ ?_, ?_⟩
  · -- The `j`-th entry of the sum is `∑_d w j (j + d)`, reindexed by `k = j + d`.
    have h₁ : HasSum (fun d ↦ t d j) ((∑' d, T d) j) :=
      hTs.hasSum.map ((Pi.evalAddMonoidHom (fun _ : ℕ ↦ G) j).comp (lp (fun _ ↦ G) p).subtype)
        (lipschitzWith_one_eval p j).continuous
    have hg : Function.Injective fun k : ℕ ↦ (k : ℤ) - j := fun a b hab ↦ by simpa using hab
    have hsupp (d : ℤ) (hd : d ∉ Set.range fun k : ℕ ↦ (k : ℤ) - j) : t d j = 0 := by
      have hd' : ¬ 0 ≤ (j : ℤ) + d := fun h ↦ hd ⟨((j : ℤ) + d).toNat, by
        simp only [Int.toNat_of_nonneg h]; ring⟩
      simp only [t, hd', ↓reduceIte]
    convert (hg.hasSum_iff hsupp).2 h₁ using 1
    funext k
    simp [t]
  · calc ‖∑' d, T d‖ ≤ c * ‖x‖ * ∑' d, a d := tsum_of_norm_bounded (ha.hasSum.mul_left _) hT
      _ = _ := by ring

/-- **Geometric tail sums in `ℓᵖ`.** For `1 ≤ p` and `0 ≤ r < 1`, the tail sums
`j ↦ ∑_{d ≥ 0} r ^ d f (d + j)` of a sequence `f ∈ ℓᵖ` converge and form a sequence in `ℓᵖ` of norm
at most `(1 - r)⁻¹ ‖f‖`. -/
theorem lp.exists_forall_hasSum_pow_smul_add_and_norm_le [Fact (1 ≤ p)] [NormedSpace ℝ G]
    [CompleteSpace G] (f : lp (fun _ : ℕ ↦ G) p) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ g : lp (fun _ : ℕ ↦ G) p, (∀ j, HasSum (fun d ↦ r ^ d • f (d + j)) (g j)) ∧
      ‖g‖ ≤ (1 - r)⁻¹ * ‖f‖ := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hinj (d : ℕ) : (Set.univ : Set ℕ).InjOn fun j ↦ d + j :=
    fun _ _ _ _ h ↦ add_left_cancel h
  -- The shift `T d = (f (d + j))ⱼ`, of norm at most `‖f‖`.
  set T : ℕ → lp (fun _ : ℕ ↦ G) p := fun d ↦
    ⟨Set.univ.indicator (f ∘ fun j ↦ d + j), (lp.memℓp f).indicator_comp (hinj d)⟩
  have hT (d j : ℕ) : T d j = f (d + j) := by simp [T]
  have hbound (d : ℕ) : ‖r ^ d • T d‖ ≤ ‖f‖ * r ^ d := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_right
      (lp.norm_le_of_forall_eq_indicator_comp hp (hinj d) fun _ ↦ rfl) (by positivity)
  have hgeom := (summable_geometric_of_lt_one hr0 hr1).mul_left ‖f‖
  have hsum : Summable fun d ↦ r ^ d • T d := Summable.of_norm_bounded hgeom hbound
  refine ⟨∑' d, r ^ d • T d, fun j ↦ ?_, ?_⟩
  · have h := Pi.hasSum.1 (hsum.hasSum.map (lp.coeFnAddMonoidHom (fun _ : ℕ ↦ G) p)
      lp.uniformContinuous_coe.continuous) j
    simpa [lp.coeFnAddMonoidHom_apply, lp.coeFn_smul, hT] using h
  · calc ‖∑' d, r ^ d • T d‖ ≤ ∑' d, ‖f‖ * r ^ d := tsum_of_norm_bounded hgeom.hasSum hbound
      _ = (1 - r)⁻¹ * ‖f‖ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, mul_comm]

/-- **Geometric prefix sums in `ℓᵖ`.** For `1 ≤ p` and `0 ≤ r < 1`, the prefix sums
`m ↦ ∑_{k < m} r ^ (m - k) • f k` of a sequence `f ∈ ℓᵖ` form a sequence in `ℓᵖ` of norm at most
`r (1 - r)⁻¹ ‖f‖`. -/
theorem lp.exists_forall_eq_sum_pow_smul_and_norm_le [Fact (1 ≤ p)] [NormedSpace ℝ G]
    [CompleteSpace G] (f : lp (fun _ : ℕ ↦ G) p) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ g : lp (fun _ : ℕ ↦ G) p, (∀ m, g m = ∑ k ∈ Finset.range m, r ^ (m - k) • f k) ∧
      ‖g‖ ≤ r * (1 - r)⁻¹ * ‖f‖ := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hinj (d : ℕ) : {m | d + 1 ≤ m}.InjOn fun m ↦ m - (d + 1) :=
    fun _ hm _ hm' h ↦ tsub_inj_left hm hm' h
  -- The right-shift `T d` reads `f (m - d - 1)` for `d + 1 ≤ m` and has norm at most `‖f‖`.
  set T : ℕ → lp (fun _ : ℕ ↦ G) p := fun d ↦
    ⟨{m | d + 1 ≤ m}.indicator (f ∘ fun m ↦ m - (d + 1)), (lp.memℓp f).indicator_comp (hinj d)⟩
  have hT (d m : ℕ) : T d m = if d + 1 ≤ m then f (m - (d + 1)) else 0 := by
    by_cases hm : d + 1 ≤ m
    · simp only [T, hm, ↓reduceIte]
      exact Set.indicator_of_mem hm _
    · simp only [T, hm, ↓reduceIte]
      exact Set.indicator_of_notMem hm _
  have hbound (d : ℕ) : ‖r ^ (d + 1) • T d‖ ≤ r * ‖f‖ * r ^ d := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), pow_succ']
    calc r * r ^ d * ‖T d‖ ≤ r * r ^ d * ‖f‖ := by
          gcongr
          exact lp.norm_le_of_forall_eq_indicator_comp hp (hinj d) fun _ ↦ rfl
      _ = r * ‖f‖ * r ^ d := by ring
  have hgeom := (summable_geometric_of_lt_one hr0 hr1).mul_left (r * ‖f‖)
  have hsum : Summable fun d ↦ r ^ (d + 1) • T d := Summable.of_norm_bounded hgeom hbound
  refine ⟨∑' d, r ^ (d + 1) • T d, fun m ↦ ?_, ?_⟩
  · have h := Pi.hasSum.1 (hsum.hasSum.map (lp.coeFnAddMonoidHom (fun _ : ℕ ↦ G) p)
      lp.uniformContinuous_coe.continuous) m
    have hfin : HasSum (fun d ↦ r ^ (d + 1) • T d m)
        (∑ d ∈ Finset.range m, r ^ (d + 1) • T d m) :=
      hasSum_sum_of_ne_finset_zero fun d hd ↦ by
        rw [Finset.mem_range, not_lt] at hd
        simp [hT, Nat.not_le.2 (Nat.lt_succ_of_le hd)]
    rw [lp.coeFnAddMonoidHom_apply] at h
    have hval : (∑' d, r ^ (d + 1) • T d) m =
        ∑ d ∈ Finset.range m, r ^ (d + 1) • f (m - (d + 1)) := by
      rw [(h.congr_fun fun d ↦ by simp [lp.coeFn_smul]).unique hfin]
      exact Finset.sum_congr rfl fun d hd ↦ by simp [hT, Finset.mem_range.1 hd]
    rw [hval]
    refine Finset.sum_bij (fun d _ ↦ m - (d + 1)) (fun d hd ↦ ?_) (fun a ha b hb hab ↦ ?_)
      (fun k hk ↦ ⟨m - (k + 1), ?_, ?_⟩) fun d hd ↦ ?_
    · rw [Finset.mem_range] at hd ⊢; omega
    · rw [Finset.mem_range] at ha hb; omega
    · rw [Finset.mem_range] at hk ⊢; omega
    · rw [Finset.mem_range] at hk; omega
    · rw [Finset.mem_range] at hd
      have hd' : m - (m - (d + 1)) = d + 1 := by omega
      rw [hd']
  · calc ‖∑' d, r ^ (d + 1) • T d‖ ≤ ∑' d, r * ‖f‖ * r ^ d :=
          tsum_of_norm_bounded hgeom.hasSum hbound
      _ = r * (1 - r)⁻¹ * ‖f‖ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]; ring
