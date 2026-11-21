/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
import TauCeti.Algebra.BigOperators.Group.Finset.Indicator
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Reindexing sequences in `ℓᵖ`

Let `f : ι → G` be a sequence in `ℓᵖ` and let `g : ι' → ι` be injective on a set `s ⊆ ι'`. The
sequence `s.indicator (f ∘ g)`, which reads `f` along `g` on `s` and vanishes off `s`, takes each
value of `f` at most once, so it again lies in `ℓᵖ`, with no larger norm
(`Memℓp.indicator_comp`, `lp.norm_le_of_forall_eq_indicator_comp`). For a bijection `e : ι ≃ ι'`,
reindexing yields a norm-preserving additive equivalence between `ℓᵖ(ι, G)` and `ℓᵖ(ι', G)`
(`Memℓp.comp_equiv`, `AddEquiv.lpCongrLeft`), and a linear isometry equivalence for `1 ≤ p`
(`LinearIsometryEquiv.lpCongrLeft`). Shifts of a sequence indexed
by `ℕ` are the basic examples: `j ↦ f (j + d)` and, on `{j | d ≤ j}`, `j ↦ f (j - d)`. In
particular a sequence indexed by `ℕ` lies in `ℓᵖ` exactly when its tail `j ↦ f (j + d)` does
(`TauCeti.memℓp_nat_add_iff`), with no larger norm (`lp.norm_le_of_forall_eq_nat_add`). Two
sequences indexed by `ℕ` in `ℓᵖ` can be interleaved into a single one, `f 0, g 0, f 1, g 1, …`
(`Memℓp.interleave`).

Consequently the **window sums** `j ↦ ∑_{j - L ≤ k < j + L} f k` of a sequence indexed by `ℕ`,
a sum of `2 L` shifts, lie in `ℓᵖ`, and for `1 ≤ p` their norm is at most `2 L ‖f‖`
(`Memℓp.sum_Ico_sub_add`, `lp.norm_le_of_forall_eq_sum_Ico_sub_add`); together, for `f ∈ ℓᵖ`
they give an element of `ℓᵖ` with these entries and norm bound
(`lp.exists_eq_sum_Ico_sub_add_and_norm_le`). Such sums arise when a
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

When `g : ι' → ι` is injective, composing with `g` preserves `ℓᵖ` membership without increasing the
norm (`Memℓp.comp_injective`, `lp.norm_le_of_forall_eq_comp`). In particular, when `e : ι ≃ ι'` is
a bijection between index types (possibly in different universes), composing with `e` preserves `ℓᵖ`
membership (`Memℓp.comp_equiv`, `Equiv.memℓp_comp_iff`) and the `ℓᵖ` norm
(`lp.norm_eq_of_forall_eq_comp_equiv`), and for `1 ≤ p` induces the linear isometric equivalence
`LinearIsometryEquiv.lpCongrLeft` between `ℓᵖ(ι, G)` and `ℓᵖ(ι', G)`.
-/

public section

open scoped ENNReal

variable {ι ι' ι'' G : Type*} [NormedAddCommGroup G] {p : ℝ≥0∞}

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
theorem lp.norm_le_of_forall_eq_indicator_comp {f : lp (fun _ : ι ↦ G) p}
    {f' : lp (fun _ : ι' ↦ G) p} {g : ι' → ι} {s : Set ι'} (hg : s.InjOn g)
    (h : ∀ j, f' j = s.indicator (f ∘ g) j) : ‖f'‖ ≤ ‖f‖ := by
  rcases p.trichotomy with rfl | rfl | hp'
  · rw [lp.norm_eq_card_dsupport, lp.norm_eq_card_dsupport]
    have hmem : ∀ j ∈ (lp.memℓp f').finite_dsupport.toFinset, j ∈ s ∧ f (g j) ≠ 0 :=
      fun j hj ↦ by simpa [h j] using hj
    exact_mod_cast Finset.card_le_card_of_injOn g
      (fun j hj ↦ by simpa using (hmem j hj).2)
      (fun j₁ hj₁ j₂ hj₂ hij ↦ hg (hmem j₁ hj₁).1 (hmem j₂ hj₂).1 hij)
  · refine lp.norm_le_of_forall_le (lp.norm_nonneg' f) fun j ↦ ?_
    rw [h j]
    by_cases hj : j ∈ s
    · simpa [hj] using lp.norm_apply_le_norm ENNReal.top_ne_zero f (g j)
    · simp [hj, lp.norm_nonneg' f]
  · classical
    refine lp.norm_le_of_forall_sum_le hp' (lp.norm_nonneg' f) fun t ↦ ?_
    simp_rw [h]
    exact (Finset.sum_apply_indicator_comp_eq_sum_image (h := fun x : G ↦ ‖x‖ ^ p.toReal)
      (by simp [Real.zero_rpow hp'.ne']) hg t).trans_le (lp.sum_rpow_le_norm_rpow hp' f _)

/-- **Interleaving in `ℓᵖ`.** The sequence `f 0, g 0, f 1, g 1, …` alternating the terms of two
sequences in `ℓᵖ` lies in `ℓᵖ`. -/
theorem Memℓp.interleave {f g : ℕ → G} (hf : Memℓp f p) (hg : Memℓp g p) :
    Memℓp (fun n ↦ if Even n then f (n / 2) else g (n / 2)) p := by
  -- the even and the odd terms are reindexings of `f` and `g` along `n ↦ n / 2`
  have h₁ := hf.indicator_comp (g := (· / 2)) (s := {n | Even n}) (by
    rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩ h
    simp only at h
    omega)
  have h₂ := hg.indicator_comp (g := (· / 2)) (s := {n | ¬Even n}) (by
    intro a ha b hb h
    simp only [Set.mem_ofPred_eq, Nat.not_even_iff_odd] at ha hb h
    obtain ⟨k, rfl⟩ := ha
    obtain ⟨l, rfl⟩ := hb
    omega)
  convert h₁.add h₂ using 1
  funext n
  by_cases hn : Even n <;> simp [Set.indicator, hn]

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

/-- **Dropping the first terms does not increase the norm.** A sequence in `ℓᵖ` that reads `f`
shifted by `d` has norm at most `‖f‖`. -/
theorem lp.norm_le_of_forall_eq_nat_add {f f' : lp (fun _ : ℕ ↦ G) p} (d : ℕ)
    (h : ∀ j, f' j = f (j + d)) : ‖f'‖ ≤ ‖f‖ :=
  lp.norm_le_of_forall_eq_indicator_comp (g := fun j ↦ j + d) (s := Set.univ)
    (fun _ _ _ _ hab ↦ Nat.add_right_cancel hab) fun j ↦ by simp [h j]

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
  have hg : ∀ d, {i | L ≤ i + d}.InjOn fun i ↦ i + d - L :=
    fun _ _ hi _ hi' h ↦ add_right_cancel (tsub_inj_left hi hi' h)
  set T : ℕ → lp (fun _ : ℕ ↦ G) p := fun d ↦
    ⟨{i | L ≤ i + d}.indicator (f ∘ fun i ↦ i + d - L),
      (lp.memℓp f).indicator_comp (hg d)⟩
  have hT : ∀ d, ‖T d‖ ≤ ‖f‖ := fun d ↦
    lp.norm_le_of_forall_eq_indicator_comp (hg d) fun _ ↦ rfl
  have hf' : f' = ∑ d ∈ Finset.range (2 * L), T d := by
    ext j
    rw [h, Finset.sum_Ico_sub_add_eq_sum_range_indicator, lp.coeFn_sum, Finset.sum_apply]
  calc ‖f'‖ ≤ ∑ d ∈ Finset.range (2 * L), ‖T d‖ := hf' ▸ norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.range (2 * L), ‖f‖ := Finset.sum_le_sum fun d _ ↦ hT d
    _ = 2 * L * ‖f‖ := by simp

/-- **Window sums as an element of `ℓᵖ`.** For `1 ≤ p` and `f ∈ ℓᵖ`, the window sums
`j ↦ ∑_{j - L ≤ k < j + L} f k` are the entries of an element of `ℓᵖ` of norm at most
`2 L ‖f‖`. -/
theorem lp.exists_eq_sum_Ico_sub_add_and_norm_le [Fact (1 ≤ p)] (f : lp (fun _ : ℕ ↦ G) p)
    (L : ℕ) : ∃ f' : lp (fun _ : ℕ ↦ G) p,
      (∀ j, f' j = ∑ k ∈ Finset.Ico (j - L) (j + L), f k) ∧ ‖f'‖ ≤ 2 * L * ‖f‖ := by
  set f' : lp (fun _ : ℕ ↦ G) p :=
    ⟨fun j ↦ ∑ k ∈ Finset.Ico (j - L) (j + L), f k, (lp.memℓp f).sum_Ico_sub_add L⟩
  -- The entries of the anonymous `lp` element `f'` are its defining sequence by definition: `lp`
  -- coerces through `Subtype.val` and has no lemma evaluating an anonymous constructor.
  have h (j : ℕ) : f' j = ∑ k ∈ Finset.Ico (j - L) (j + L), f k := rfl
  exact ⟨f', h, lp.norm_le_of_forall_eq_sum_Ico_sub_add L h⟩

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
    lp.norm_le_of_forall_eq_indicator_comp (hinj d) fun _ ↦ rfl
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
    set n := lp.normSeq (z d)
    calc ‖T d‖ ≤ ‖(c * a d) • n‖ := lp.norm_mono hp fun j ↦ by
          rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.normSeq_apply,
            Real.norm_of_nonneg (by positivity)]
          exact ht d j
      _ ≤ c * a d * ‖x‖ := by
          rw [lp.norm_const_smul hp, Real.norm_of_nonneg (by positivity)]
          gcongr
          exact (lp.norm_normSeq _).le.trans (hz d)
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
  have hinj (d : ℕ) : (Set.univ : Set ℕ).InjOn fun j ↦ d + j :=
    fun _ _ _ _ h ↦ add_left_cancel h
  -- The shift `T d = (f (d + j))ⱼ`, of norm at most `‖f‖`.
  set T : ℕ → lp (fun _ : ℕ ↦ G) p := fun d ↦
    ⟨Set.univ.indicator (f ∘ fun j ↦ d + j), (lp.memℓp f).indicator_comp (hinj d)⟩
  have hT (d j : ℕ) : T d j = f (d + j) := by simp [T]
  have hbound (d : ℕ) : ‖r ^ d • T d‖ ≤ ‖f‖ * r ^ d := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_right
      (lp.norm_le_of_forall_eq_indicator_comp (hinj d) fun _ ↦ rfl) (by positivity)
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
    (f : lp (fun _ : ℕ ↦ G) p) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ g : lp (fun _ : ℕ ↦ G) p, (∀ m, g m = ∑ k ∈ Finset.range m, r ^ (m - k) • f k) ∧
      ‖g‖ ≤ r * (1 - r)⁻¹ * ‖f‖ := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set a : ℤ → ℝ := fun d ↦ if d < 0 then r ^ d.natAbs else 0
  have ha0 (d : ℤ) : 0 ≤ a d := by simp only [a]; split_ifs <;> positivity
  have hneg : Function.Injective (fun n : ℕ ↦ -((n + 1 : ℕ) : ℤ)) := fun _ _ h ↦ by
    dsimp at h; omega
  have ha_hasSum : HasSum a (r * (1 - r)⁻¹) :=
    (hneg.hasSum_iff fun d hd ↦ by
      have : ¬ d < 0 := fun hlt ↦ hd ⟨(-d - 1).toNat, by dsimp; omega⟩
      simp [a, this]).1 <|
    ((hasSum_geometric_of_lt_one hr0 hr1).mul_left r |>.congr_fun fun n ↦ by
      have hlt : -((n + 1 : ℕ) : ℤ) < 0 := by omega
      simp only [Function.comp_def, a, hlt, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast,
        pow_succ'])
  set w : ℕ → ℕ → ℝ := fun m k ↦ if k < m then r ^ (m - k) * ‖f k‖ else 0
  obtain ⟨y, hy, hyn⟩ := lp.exists_hasSum_and_norm_le_of_summable (lp.toNorm f) ha0
    ha_hasSum.summable zero_le_one w fun m k ↦ by
      simp only [one_mul, lp.toNorm_coe, norm_norm]
      by_cases hkm : k < m
      · have hlt : (k : ℤ) - m < 0 := by omega
        have hnat : ((k : ℤ) - m).natAbs = m - k := by omega
        simp only [w, a, hkm, hlt, hnat, ↓reduceIte]; rw [Real.norm_of_nonneg (by positivity)]
      · simpa [w, hkm] using mul_nonneg (ha0 ((k : ℤ) - m)) (norm_nonneg (f k))
  have hle (m : ℕ) : ‖∑ k ∈ Finset.range m, r ^ (m - k) • f k‖ ≤ ‖y m‖ := by
    have hym : y m = ∑ k ∈ Finset.range m, r ^ (m - k) * ‖f k‖ := by
      rw [(hy m).unique (hasSum_sum_of_ne_finset_zero (s := Finset.range m) fun k hk ↦ by
        simp [w, Finset.mem_range.not.1 hk])]
      exact Finset.sum_congr rfl fun k hk ↦ by simp [w, Finset.mem_range.1 hk]
    rw [hym, Real.norm_of_nonneg (Finset.sum_nonneg fun k _ ↦ by positivity)]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)])
  exact ⟨⟨fun m ↦ ∑ k ∈ Finset.range m, r ^ (m - k) • f k, (lp.memℓp y).mono' hle⟩,
    fun _ ↦ rfl, (lp.norm_mono hp hle).trans <| by
      simpa [ha_hasSum.tsum_eq, lp.norm_toNorm] using hyn⟩

section Equiv

/-- Composing a sequence in `ℓᵖ` with an injective map (possibly between different universes)
preserves membership in `ℓᵖ`. -/
theorem Memℓp.comp_injective {α : Type*} {β : Type*} {H : Type*} [NormedAddCommGroup H] {q : ℝ≥0∞}
    {f : β → H} (hf : Memℓp f q) {g : α → β} (hg : Function.Injective g) : Memℓp (f ∘ g) q := by
  simpa only [Set.indicator_univ] using hf.indicator_comp (s := Set.univ) hg.injOn

/-- Composing a sequence in `ℓᵖ` with an equivalence of index types (possibly in different
universes) preserves membership in `ℓᵖ`. -/
theorem Memℓp.comp_equiv {α : Type*} {β : Type*} {H : Type*} [NormedAddCommGroup H] {q : ℝ≥0∞}
    {f : β → H} (hf : Memℓp f q) (e : α ≃ β) : Memℓp (f ∘ e) q :=
  hf.comp_injective e.injective

/-- Composing with an equivalence of index types preserves `ℓᵖ` membership in both directions. -/
@[simp]
theorem Equiv.memℓp_comp_iff {α : Type*} {β : Type*} {H : Type*} [NormedAddCommGroup H]
    {q : ℝ≥0∞} {f : β → H} (e : α ≃ β) : Memℓp (f ∘ e) q ↔ Memℓp f q :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.comp_equiv e.symm, fun h ↦ h.comp_equiv e⟩

/-- Reindexing a sequence in `ℓᵖ` along an injective map does not increase the `ℓᵖ` norm. -/
theorem lp.norm_le_of_forall_eq_comp {α : Type*} {β : Type*} {H : Type*}
    [NormedAddCommGroup H] {q : ℝ≥0∞} {f : lp (fun _ : β ↦ H) q}
    {g : lp (fun _ : α ↦ H) q} {e : α → β} (he : Function.Injective e) (h : ∀ i, g i = f (e i)) :
    ‖g‖ ≤ ‖f‖ :=
  lp.norm_le_of_forall_eq_indicator_comp (s := Set.univ) he.injOn fun i ↦ by simpa using h i

/-- Reindexing a sequence in `ℓᵖ` along an equivalence preserves the `ℓᵖ` norm. -/
theorem lp.norm_eq_of_forall_eq_comp_equiv {α : Type*} {β : Type*} {H : Type*}
    [NormedAddCommGroup H] {q : ℝ≥0∞} {f : lp (fun _ : β ↦ H) q}
    {g : lp (fun _ : α ↦ H) q} (e : α ≃ β) (h : ∀ i, g i = f (e i)) : ‖g‖ = ‖f‖ :=
  le_antisymm (lp.norm_le_of_forall_eq_comp e.injective h)
    (lp.norm_le_of_forall_eq_comp e.symm.injective fun j ↦ by simp [h (e.symm j)])

namespace AddEquiv

/-- Reindexing `ℓᵖ` along an equivalence `e : ι ≃ ι'` as an additive equivalence, for every
exponent `p`, sending `f` to `j ↦ f (e.symm j)` so that `lp.single p i v` goes to
`lp.single p (e i) v`. -/
def lpCongrLeft (p : ℝ≥0∞) (G : Type*) [NormedAddCommGroup G] (e : ι ≃ ι') :
    lp (fun _ : ι ↦ G) p ≃+ lp (fun _ : ι' ↦ G) p where
  toFun f := ⟨f ∘ e.symm, (lp.memℓp f).comp_equiv e.symm⟩
  invFun g := ⟨g ∘ e, (lp.memℓp g).comp_equiv e⟩
  left_inv f := lp.ext (funext fun i ↦ by simp)
  right_inv g := lp.ext (funext fun j ↦ by simp)
  map_add' _ _ := rfl

/-- Function-coercion form of `AddEquiv.lpCongrLeft_apply`. -/
theorem coeFn_lpCongrLeft (e : ι ≃ ι') (f : lp (fun _ : ι ↦ G) p) :
    ⇑(lpCongrLeft p G e f) = f ∘ e.symm := by
  rfl

/-- Evaluating `AddEquiv.lpCongrLeft` at an index `j` reads `f` at `e.symm j`. -/
@[simp]
theorem lpCongrLeft_apply (e : ι ≃ ι') (f : lp (fun _ : ι ↦ G) p) (j : ι') :
    lpCongrLeft p G e f j = f (e.symm j) := by
  rfl

/-- Reindexing along the identity equivalence is the identity additive equivalence. -/
@[simp]
theorem lpCongrLeft_refl : lpCongrLeft p G (Equiv.refl ι) = AddEquiv.refl _ := by
  ext f i
  rfl

/-- The inverse of `AddEquiv.lpCongrLeft` is induced by the inverse equivalence. -/
@[simp]
theorem lpCongrLeft_symm (e : ι ≃ ι') :
    (lpCongrLeft p G e).symm = lpCongrLeft p G e.symm := by
  rfl

/-- Reindexing along a composition of equivalences is the composition of the reindexing additive
equivalences. -/
@[simp]
theorem lpCongrLeft_trans (e₁ : ι ≃ ι') (e₂ : ι' ≃ ι'') :
    (lpCongrLeft p G e₁).trans (lpCongrLeft p G e₂) = lpCongrLeft p G (e₁.trans e₂) := by
  ext f k
  rfl

/-- `AddEquiv.lpCongrLeft` transports single-coordinate vectors along `e`. -/
@[simp]
theorem lpCongrLeft_single [DecidableEq ι] [DecidableEq ι'] (e : ι ≃ ι') (i : ι) (v : G) :
    lpCongrLeft p G e (lp.single p i v) = lp.single p (e i) v := by
  ext j
  simp [lp.single_apply, Pi.single_apply, Equiv.symm_apply_eq]

/-- Reindexing `ℓᵖ` along an equivalence preserves the `ℓᵖ` norm for every exponent `p`. -/
@[simp]
theorem norm_lpCongrLeft (e : ι ≃ ι') (f : lp (fun _ : ι ↦ G) p) :
    ‖lpCongrLeft p G e f‖ = ‖f‖ :=
  lp.norm_eq_of_forall_eq_comp_equiv e.symm fun _ ↦ rfl

end AddEquiv

namespace LinearIsometryEquiv

variable (q : ℝ≥0∞) (𝕜 : Type*) (H : Type*) [NormedRing 𝕜] [NormedAddCommGroup H]
  [Module 𝕜 H] [IsBoundedSMul 𝕜 H] [Fact (1 ≤ q)]
  {α : Type*} {β : Type*} {γ : Type*}

/-- An equivalence of index types (possibly in different universes) induces a linear isometric
equivalence between the `ℓᵖ` spaces `lp (fun _ : α ↦ H) q` and `lp (fun _ : β ↦ H) q`.

This is the `lp` counterpart of `LinearIsometryEquiv.piLpCongrLeft`. -/
def lpCongrLeft (e : α ≃ β) : lp (fun _ : α ↦ H) q ≃ₗᵢ[𝕜] lp (fun _ : β ↦ H) q where
  toFun v := ⟨v ∘ e.symm, (lp.memℓp v).comp_equiv e.symm⟩
  invFun w := ⟨w ∘ e, (lp.memℓp w).comp_equiv e⟩
  map_add' _ _ := lp.ext <| funext fun _ ↦ by
    simp only [lp.coeFn_add, Pi.add_apply, Function.comp_apply]
  map_smul' _ _ := lp.ext <| funext fun _ ↦ by
    simp only [lp.coeFn_smul, Pi.smul_apply, Function.comp_apply, RingHom.id_apply]
  left_inv v := lp.ext (funext fun i ↦ by simp)
  right_inv w := lp.ext (funext fun j ↦ by simp)
  norm_map' _ := lp.norm_eq_of_forall_eq_comp_equiv e.symm fun _ ↦ rfl

variable {q 𝕜 H}

/-- Evaluating `LinearIsometryEquiv.lpCongrLeft` at an index `j` reads `v` at `e.symm j`. -/
@[simp]
theorem lpCongrLeft_apply (e : α ≃ β) (v : lp (fun _ : α ↦ H) q) (j : β) :
    lpCongrLeft q 𝕜 H e v j = v (e.symm j) :=
  (rfl)

/-- Function-coercion form of `LinearIsometryEquiv.lpCongrLeft_apply`. -/
theorem coeFn_lpCongrLeft (e : α ≃ β) (v : lp (fun _ : α ↦ H) q) :
    ⇑(lpCongrLeft q 𝕜 H e v) = v ∘ e.symm :=
  (rfl)

/-- The inverse of `LinearIsometryEquiv.lpCongrLeft` is induced by the inverse equivalence. -/
@[simp]
theorem lpCongrLeft_symm (e : α ≃ β) :
    (lpCongrLeft q 𝕜 H e).symm = lpCongrLeft q 𝕜 H e.symm := by
  refine LinearIsometryEquiv.ext fun v ↦ ?_
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext j
  simp

/-- Reindexing along the identity equivalence is the identity linear isometric equivalence. -/
@[simp]
theorem lpCongrLeft_refl :
    lpCongrLeft q 𝕜 H (Equiv.refl α) = LinearIsometryEquiv.refl 𝕜 (lp (fun _ : α ↦ H) q) := by
  ext v i
  simp

/-- Reindexing along a composition of equivalences is the composition of the reindexing linear
isometric equivalences. -/
@[simp]
theorem lpCongrLeft_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    (lpCongrLeft q 𝕜 H e₁).trans (lpCongrLeft q 𝕜 H e₂) = lpCongrLeft q 𝕜 H (e₁.trans e₂) := by
  ext v k
  simp

/-- Applying two `LinearIsometryEquiv.lpCongrLeft` equivalences in succession reindexes along the
composed equivalence. -/
@[simp]
theorem lpCongrLeft_trans_apply (e₁ : α ≃ β) (e₂ : β ≃ γ) (v : lp (fun _ : α ↦ H) q) :
    lpCongrLeft q 𝕜 H e₂ (lpCongrLeft q 𝕜 H e₁ v) = lpCongrLeft q 𝕜 H (e₁.trans e₂) v := by
  rw [← LinearIsometryEquiv.trans_apply, lpCongrLeft_trans]

/-- `LinearIsometryEquiv.lpCongrLeft` transports single-coordinate vectors along `e`. -/
@[simp high]
theorem lpCongrLeft_single [DecidableEq α] [DecidableEq β] (e : α ≃ β) (i : α) (v : H) :
    lpCongrLeft q 𝕜 H e (lp.single q i v) = lp.single q (e i) v := by
  ext j
  simp [lp.single_apply, Pi.single_apply, e.symm_apply_eq]

/-- The additive equivalence underlying `LinearIsometryEquiv.lpCongrLeft` is
`AddEquiv.lpCongrLeft`. -/
@[simp]
theorem toAddEquiv_lpCongrLeft (e : α ≃ β) :
    (lpCongrLeft q 𝕜 H e).toLinearEquiv.toAddEquiv = AddEquiv.lpCongrLeft q H e := by
  ext f i
  simp

/-- As a function, `LinearIsometryEquiv.lpCongrLeft` is `AddEquiv.lpCongrLeft`. -/
theorem coe_lpCongrLeft (e : α ≃ β) :
    ⇑(lpCongrLeft q 𝕜 H e) = AddEquiv.lpCongrLeft q H e := by
  ext f i
  simp

end LinearIsometryEquiv

end Equiv
