/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Module.Bases.TOrthogonal
public import TauCeti.Analysis.Normed.Module.RieszLemma

/-!
# Nonarchimedean normed spaces of countable type

A topological module `E` over `K` is of *countable type* (`TauCeti.IsCountableType K E`) if some
countable subset of `E` has dense span. Separable spaces and finite-dimensional spaces are of
countable type. Over a nonarchimedean field this, rather than separability, is the natural
countability condition: a field such as a spherical completion of `ℂ_p` is not separable, yet
`K` itself is of countable type over `K`.

The main result is the existence of almost orthogonal bases. For a complete nontrivially normed
field `K` and an ultrametric normed `K`-space `E` of countable type,

* `TauCeti.exists_isTOrthogonalBasis`: for every `t < 1` there is a `t`-orthogonal basis of `E`
  indexed by a subset of `ℕ`;
* `TauCeti.exists_isTOrthogonalBasis_nat`: if `E` is infinite-dimensional, there is a
  `t`-orthogonal basis indexed by `ℕ`;
* `TauCeti.exists_isTOrthogonalBasis_fin`: if `E` is finite-dimensional and `0 < t < 1`, there is a
  `t`-orthogonal basis indexed by `Fin (Module.finrank K E)`.

Conversely `TauCeti.isCountableType_iff_exists_isTOrthogonalBasis` shows that for `t < 1` a space
is of countable type exactly when it has a `t`-orthogonal basis indexed by a subset of `ℕ`.
Neither completeness of `E` nor a discrete valuation on `K` is needed: the basis is built by
applying Riesz's lemma along the increasing chain of finite-dimensional subspaces spanned by an
enumeration of a countable set with dense span. In general `t = 1` cannot be reached, since
orthogonal bases need not exist when `K` is not spherically complete.

## References

* C. Perez-Garcia and W. H. Schikhof, *Locally Convex Spaces over Non-Archimedean Valued
  Fields*, Cambridge Studies in Advanced Mathematics 119, Cambridge University Press, 2010,
  Theorem 2.3.13.
* P. Schneider, *Nonarchimedean Functional Analysis*, Springer Monographs in Mathematics,
  Springer, 2002, Proposition 10.4.
-/

public section

open Set Submodule
open scoped NNReal

namespace TauCeti

variable {K E : Type*}

/-- A topological module is of **countable type** if some countable subset has dense span. -/
class IsCountableType (K E : Type*) [Semiring K] [AddCommMonoid E] [Module K E]
    [TopologicalSpace E] : Prop where
  /-- A module of countable type has a countable subset with dense span. -/
  exists_countable_dense_span : ∃ s : Set E, s.Countable ∧ Dense (span K s : Set E)

section Basic

variable [Semiring K] [AddCommMonoid E] [Module K E] [TopologicalSpace E]

variable (K E) in
/-- A module is of countable type exactly when some countable subset has dense span. -/
theorem isCountableType_iff :
    IsCountableType K E ↔ ∃ s : Set E, s.Countable ∧ Dense (span K s : Set E) :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

/-- A module with a countable family whose span is dense is of countable type. -/
theorem IsCountableType.of_dense_span_range {I : Type*} [Countable I] {e : I → E}
    (he : Dense (span K (range e) : Set E)) : IsCountableType K E :=
  ⟨⟨range e, countable_range e, he⟩⟩

/-- A separable topological module is of countable type. -/
instance (priority := 100) IsCountableType.of_separableSpace [TopologicalSpace.SeparableSpace E] :
    IsCountableType K E := by
  obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense E
  exact ⟨⟨s, hs, hd.mono subset_span⟩⟩

/-- A finitely generated topological module is of countable type. -/
instance (priority := 100) IsCountableType.of_finite [Module.Finite K E] : IsCountableType K E := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := E)
  exact ⟨⟨s, s.countable_toSet, by simp [hs]⟩⟩

end Basic

section AlmostOrthogonal

variable [NormedField K] [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]

/-- In an ultrametric normed space, let `x` be almost orthogonal to a subspace `F`, in the sense
that `s * ‖x‖ ≤ ‖x - y‖` for all `y ∈ F`, where `s ≤ 1`. Then for every scalar `a` and every
`y ∈ F`, the norm of `a • x + y` is at least `s` times the larger of `‖a • x‖` and `‖y‖`. -/
theorem mul_max_nnnorm_le_nnnorm_smul_add {F : Submodule K E} {x : E} {s : ℝ≥0} (hs : s ≤ 1)
    (hx : ∀ y ∈ F, s * ‖x‖₊ ≤ ‖x - y‖₊) (a : K) {y : E} (hy : y ∈ F) :
    s * max ‖a • x‖₊ ‖y‖₊ ≤ ‖a • x + y‖₊ := by
  have hax : s * ‖a • x‖₊ ≤ ‖a • x + y‖₊ := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    calc s * ‖a • x‖₊ = ‖a‖₊ * (s * ‖x‖₊) := by rw [nnnorm_smul, mul_left_comm]
      _ ≤ ‖a‖₊ * ‖x - -(a⁻¹ • y)‖₊ := by gcongr; exact hx _ (F.neg_mem (F.smul_mem _ hy))
      _ = ‖a • x + y‖₊ := by rw [← nnnorm_smul, smul_sub, smul_neg, smul_inv_smul₀ ha,
          sub_neg_eq_add]
  have hy' : ‖y‖₊ ≤ max ‖a • x + y‖₊ ‖a • x‖₊ := by
    simpa using IsUltrametricDist.nnnorm_add_le_max (a • x + y) (-(a • x))
  rw [mul_max]
  refine max_le hax ((mul_le_mul_of_nonneg_left hy' (by positivity)).trans ?_)
  rw [mul_max]
  exact max_le ((mul_le_of_le_one_left' hs).trans le_rfl) hax

/-- The estimate behind almost orthogonal bases. Let `V` be an increasing chain of subspaces and
`τ` a strictly decreasing sequence in `[0, 1]`. If each `g n` lies in `V (n + 1)` and, when
nonzero, is almost orthogonal to `V n` with constant `τ (n + 1) / τ n`, then every finite
combination of `g 0, …, g (N - 1)` has norm at least `τ N` times the largest norm of its terms. -/
private theorem mul_sup_nnnorm_smul_le_of_chain {V : ℕ → Submodule K E} (hV : Monotone V)
    {τ : ℕ → ℝ≥0} (hτ : StrictAnti τ) (hτ1 : ∀ n, τ n ≤ 1) {g : ℕ → E}
    (hgV : ∀ n, g n ∈ V (n + 1))
    (hg : ∀ n, g n ≠ 0 → ∀ y ∈ V n, τ (n + 1) / τ n * ‖g n‖₊ ≤ ‖g n - y‖₊)
    (N : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n < N) (a : ℕ → K) :
    τ N * (s.sup fun n ↦ ‖a n • g n‖₊) ≤ ‖∑ n ∈ s, a n • g n‖₊ := by
  induction N generalizing s with
  | zero => simp [Finset.eq_empty_of_forall_notMem fun n hn ↦ Nat.not_lt_zero n (hs n hn)]
  | succ N ih =>
    have hτN : τ (N + 1) ≤ τ N := (hτ N.lt_succ_self).le
    by_cases hNs : N ∈ s
    swap
    · exact (mul_le_mul_of_nonneg_right hτN (by positivity)).trans
        (ih s fun n hn ↦ Nat.lt_of_le_of_ne (Nat.lt_succ_iff.1 (hs n hn)) fun h ↦ hNs (h ▸ hn))
    -- Split off the last term `a N • g N` from the combination `y` of the earlier ones.
    have hs' : ∀ n ∈ s.erase N, n < N := fun n hn ↦ Nat.lt_of_le_of_ne
      (Nat.lt_succ_iff.1 (hs n (Finset.mem_of_mem_erase hn))) (Finset.ne_of_mem_erase hn)
    have hy : ∑ n ∈ s.erase N, a n • g n ∈ V N :=
      sum_mem fun n hn ↦ smul_mem _ _ (hV (hs' n hn) (hgV n))
    have ih' := ih (s.erase N) hs'
    rw [← Finset.insert_erase hNs, Finset.sum_insert (Finset.notMem_erase N s),
      Finset.sup_insert]
    by_cases hgN : g N = 0
    · rw [hgN, smul_zero, nnnorm_zero, zero_add, max_eq_right zero_le]
      exact (mul_le_mul_of_nonneg_right hτN (by positivity)).trans ih'
    have hτpos : 0 < τ N := zero_le.trans_lt (hτ N.lt_succ_self)
    calc _ = τ (N + 1) / τ N * max (τ N * ‖a N • g N‖₊)
            (τ N * (s.erase N).sup fun n ↦ ‖a n • g n‖₊) := by
          rw [← mul_max, ← mul_assoc, div_mul_cancel₀ _ hτpos.ne']
      _ ≤ τ (N + 1) / τ N * max ‖a N • g N‖₊ ‖∑ n ∈ s.erase N, a n • g n‖₊ := by
          gcongr
          exact mul_le_of_le_one_left' (hτ1 N)
      _ ≤ ‖a N • g N + ∑ n ∈ s.erase N, a n • g n‖₊ :=
          mul_max_nnnorm_le_nnnorm_smul_add (div_le_one_of_le₀ hτN (by positivity))
            (hg N hgN) (a N) hy

end AlmostOrthogonal

section Existence

variable [NontriviallyNormedField K] [CompleteSpace K] [NormedAddCommGroup E] [NormedSpace K E]
  [IsUltrametricDist E]

/-- For `t < 1`, a sequence of nonnegative reals decreasing strictly from `1` and bounded below by
`t`. Its successive ratios are the constants used in the almost orthogonal construction. -/
private theorem exists_strictAnti_of_lt_one {t : ℝ≥0} (ht : t < 1) :
    ∃ τ : ℕ → ℝ≥0, τ 0 = 1 ∧ StrictAnti τ ∧ ∀ n, t ≤ τ n := by
  refine ⟨fun n ↦ t + (1 - t) / 2 ^ n, by simp [add_tsub_cancel_of_le ht.le],
    strictAnti_nat_of_succ_lt fun n ↦ ?_, fun n ↦ le_self_add⟩
  have h1t : 0 < 1 - t := tsub_pos_of_lt ht
  gcongr
  · exact one_lt_two
  · exact n.lt_succ_self

/-- The almost orthogonal construction: if the vectors `u n` span a dense subspace, then for
every `t < 1` there is a `t`-orthogonal basis indexed by a subset of `ℕ`. -/
private theorem exists_isTOrthogonalBasis_of_dense_span_range {u : ℕ → E}
    (hu : Dense (span K (range u) : Set E)) {t : ℝ≥0} (ht : t < 1) :
    ∃ (I : Set ℕ) (e : I → E), IsTOrthogonalBasis K t e := by
  classical
  obtain ⟨τ, hτ0, hτ, htτ⟩ := exists_strictAnti_of_lt_one ht
  have hτpos (n : ℕ) : 0 < τ n := zero_le.trans_lt (hτ n.lt_succ_self)
  have hτle (n : ℕ) : τ n ≤ 1 := hτ0 ▸ hτ.antitone (Nat.zero_le n)
  -- The chain of finite-dimensional, hence closed, subspaces spanned by `u 0, …, u (n - 1)`.
  set V : ℕ → Submodule K E := fun n ↦ span K (u '' Iio n) with hV
  have hVmono : Monotone V := fun m n h ↦ span_mono (image_mono (Iio_subset_Iio h))
  have hVsucc (n : ℕ) : V (n + 1) = span K (insert (u n) (u '' Iio n)) := by
    simp only [hV]
    rw [← Order.succ_eq_add_one, Order.Iio_succ_eq_insert, image_insert_eq]
  have hVc (n : ℕ) : IsClosed (V n : Set E) := by
    have : FiniteDimensional K (V n) := FiniteDimensional.span_of_finite K ((finite_Iio n).image u)
    exact (V n).closed_of_finiteDimensional
  -- Whenever the chain grows, choose an almost orthogonal new vector.
  have hstep (n : ℕ) (hn : u n ∉ V n) : ∃ x ∈ V (n + 1), x ∉ V n ∧
      ∀ y ∈ V n, ((τ (n + 1) / τ n : ℝ≥0) : ℝ) * ‖x‖ ≤ ‖x - y‖ := by
    refine riesz_lemma_of_lt (hVc n) (lt_of_le_of_ne (hVmono n.le_succ) fun h ↦ hn ?_) ?_
    · rw [h, hVsucc]
      exact subset_span (mem_insert _ _)
    · exact_mod_cast (div_lt_one (hτpos n)).2 (hτ n.lt_succ_self)
  choose! f hfV hfV' hfR using hstep
  set I : Set ℕ := {n | u n ∉ V n} with hI
  set g : ℕ → E := I.indicator f with hg
  have hgV (n : ℕ) : g n ∈ V (n + 1) := by
    by_cases hn : n ∈ I
    · simpa [hg, hn] using hfV n hn
    · simp [hg, hn]
  -- The span of the chosen vectors contains the whole chain.
  have hVW (n : ℕ) : V n ≤ span K (f '' I) := by
    induction n with
    | zero => simp [hV]
    | succ n ih =>
      rw [hVsucc, span_le, insert_subset_iff]
      refine ⟨?_, subset_span.trans ih⟩
      by_cases hn : n ∈ I
      · have hex := mem_span_insert_exchange (hVsucc n ▸ hfV n hn) (hfV' n hn)
        exact span_le.2 (insert_subset_iff.2 ⟨subset_span (mem_image_of_mem f hn),
          subset_span.trans ih⟩) hex
      · exact ih (by simpa [hI] using hn)
  have hgR (n : ℕ) (hn : g n ≠ 0) : ∀ y ∈ V n, τ (n + 1) / τ n * ‖g n‖₊ ≤ ‖g n - y‖₊ := by
    have hnI : n ∈ I := by_contra fun h ↦ hn (indicator_of_notMem h f)
    rw [show g n = f n from indicator_of_mem hnI f]
    exact fun y hy ↦ by exact_mod_cast hfR n hnI y hy
  have horth := mul_sup_nnnorm_smul_le_of_chain hVmono hτ hτle hgV hgR
  have hgorth : IsTOrthogonalFamily K t g := isTOrthogonalFamily_def.2 fun s a ↦
    (mul_le_mul_of_nonneg_right (htτ (s.sup id + 1)) (by positivity)).trans
      (horth _ s (fun n hn ↦ Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)) a)
  refine ⟨I, fun n ↦ f n, ?_, fun n hn ↦ hfV' n n.2 (hn ▸ zero_mem _), ?_⟩
  · have heq : g ∘ Subtype.val = fun n : I ↦ f n := funext fun n ↦ indicator_of_mem n.2 f
    exact heq ▸ hgorth.comp Subtype.val_injective
  · rw [← image_eq_range]
    refine hu.mono (span_le.2 ?_)
    rintro _ ⟨n, rfl⟩
    exact hVW (n + 1) (subset_span (mem_image_of_mem u n.lt_succ_self))

variable (K E) in
/-- **Almost orthogonal bases of spaces of countable type**: over a complete nontrivially normed
field, an ultrametric normed space of countable type has, for every `t < 1`, a `t`-orthogonal
basis indexed by a subset of `ℕ`. -/
theorem exists_isTOrthogonalBasis [IsCountableType K E] {t : ℝ≥0} (ht : t < 1) :
    ∃ (I : Set ℕ) (e : I → E), IsTOrthogonalBasis K t e := by
  obtain ⟨s, hs, hd⟩ := IsCountableType.exists_countable_dense_span (K := K) (E := E)
  obtain ⟨u, hu⟩ := (hs.insert 0).exists_eq_range (insert_nonempty 0 s)
  exact exists_isTOrthogonalBasis_of_dense_span_range (by rwa [← hu, span_insert_zero]) ht

variable (K E) in
/-- For `t < 1`, an ultrametric normed space over a complete nontrivially normed field is of
countable type exactly when it has a `t`-orthogonal basis indexed by a subset of `ℕ`. -/
theorem isCountableType_iff_exists_isTOrthogonalBasis {t : ℝ≥0} (ht : t < 1) :
    IsCountableType K E ↔ ∃ (I : Set ℕ) (e : I → E), IsTOrthogonalBasis K t e :=
  ⟨fun _ ↦ exists_isTOrthogonalBasis K E ht,
    fun ⟨_, _, he⟩ ↦ .of_dense_span_range he.dense_span⟩

variable (K) in
/-- **Almost orthogonal bases in infinite dimension**: an infinite-dimensional ultrametric
normed space of countable type over a complete nontrivially normed field has, for every `t < 1`,
a `t`-orthogonal basis indexed by `ℕ`. -/
theorem exists_isTOrthogonalBasis_nat [IsCountableType K E] (hE : ¬FiniteDimensional K E)
    {t : ℝ≥0} (ht : t < 1) : ∃ e : ℕ → E, IsTOrthogonalBasis K t e := by
  obtain ⟨I, e, he⟩ := exists_isTOrthogonalBasis K E ht
  have : Infinite I := by
    refine infinite_coe_iff.2 fun hI ↦ hE ?_
    have : Finite I := hI.to_subtype
    have : FiniteDimensional K (span K (range e)) :=
      FiniteDimensional.span_of_finite K (finite_range e)
    have htop : span K (range e) = ⊤ :=
      coe_eq_univ.1 ((span K (range e)).closed_of_finiteDimensional.closure_eq ▸
        he.dense_span.closure_eq)
    exact ⟨htop ▸ fg_span (finite_range e)⟩
  obtain ⟨σ⟩ := nonempty_equiv_of_countable (α := ℕ) (β := I)
  exact ⟨e ∘ σ, he.comp_equiv σ⟩

variable (K E) in
/-- **Almost orthogonal bases in finite dimension**: a finite-dimensional ultrametric normed
space over a complete nontrivially normed field has, for every `0 < t < 1`, a `t`-orthogonal
basis indexed by `Fin (Module.finrank K E)`. -/
theorem exists_isTOrthogonalBasis_fin [FiniteDimensional K E] {t : ℝ≥0} (ht₀ : 0 < t)
    (ht : t < 1) : ∃ e : Fin (Module.finrank K E) → E, IsTOrthogonalBasis K t e := by
  obtain ⟨I, e, he⟩ := exists_isTOrthogonalBasis K E ht
  have htop : span K (range e) = ⊤ :=
    coe_eq_univ.1 ((span K (range e)).closed_of_finiteDimensional.closure_eq ▸
      he.dense_span.closure_eq)
  let b := Module.Basis.mk (he.isTOrthogonalFamily.linearIndependent ht₀ he.ne_zero) htop.ge
  exact ⟨e ∘ (Module.finBasis K E).indexEquiv b, he.comp_equiv _⟩

end Existence

end TauCeti

end
