/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Degenerate-domain lemmas and uniform-tail criteria for `SummableUniformlyOn`

This file supplements `Mathlib.Topology.Algebra.InfiniteSum.UniformOn` along two axes:

1. **Empty-domain, finite-index, and cofinite-support lemmas** (`hasProdUniformlyOn_empty`,
   `hasProdLocallyUniformlyOn_empty`, `hasProdUniformlyOn_prod_of_ne_finset_one`,
   `hasProdUniformlyOn_fintype`, `multipliableUniformlyOn_of_finite`,
   `hasProdUniformlyOn_of_cofinite_eq_one`, together with their `Multipliable*` and
   `@[to_additive]` counterparts) and **subtype restriction** (`MultipliableUniformlyOn.subtype`,
   `SummableUniformlyOn.subtype`).
2. **Cauchy and uniform-tail characterizations** of `SummableUniformlyOn` in complete seminormed
   additive groups (`TauCeti.summableUniformlyOn_iff_vanishing_norm`) and for nonnegative real
   series (`TauCeti.summableUniformlyOn_of_nonneg_iff`,
   `TauCeti.summableUniformlyOn_iff_tsum_compl_of_nonneg`,
   `TauCeti.summableUniformlyOn_nat_of_nonneg_iff`), together with the comparison test
   `SummableUniformlyOn.of_norm_bounded` and the uniform full-sum bound
   `SummableUniformlyOn.exists_tsum_le_of_nonneg`.
-/

public section

open Filter Function Set
open scoped Topology UniformConvergence

section Subtype

/-- Restricting the index type of a uniformly multipliable family in a complete uniform commutative
group preserves `MultipliableUniformlyOn`. -/
@[to_additive /-- Restricting the index type of a uniformly summable family in a complete uniform
additive commutative group preserves `SummableUniformlyOn`. -/]
theorem MultipliableUniformlyOn.subtype {ι β α : Type*} [CommGroup α] [UniformSpace α]
    [IsUniformGroup α] [CompleteSpace α] {f : ι → β → α} {s : Set β}
    (hf : MultipliableUniformlyOn f s) (p : ι → Prop) :
    MultipliableUniformlyOn (fun i : Subtype p ↦ f i) s :=
  Multipliable.subtype hf p

end Subtype

namespace TauCeti

section DegenerateAndFinite

variable {ι β α : Type*} [CommMonoid α] [UniformSpace α] {f : ι → β → α} {g : β → α} {s : Set β}

/-- Every family has uniform product equal to any target function on the empty set. -/
@[to_additive (attr := simp) /-- Every family has uniform sum equal to any target function on the
empty set. -/]
theorem hasProdUniformlyOn_empty : HasProdUniformlyOn f g ∅ :=
  hasProdUniformlyOn_iff_tendstoUniformlyOn.2 tendstoUniformlyOn_empty

/-- Every family is uniformly multipliable on the empty set. -/
@[to_additive (attr := simp) /-- Every family is uniformly summable on the empty set. -/]
theorem multipliableUniformlyOn_empty : MultipliableUniformlyOn f ∅ :=
  ⟨1, hasProdUniformlyOn_empty⟩

/-- Every family has locally uniform product equal to any target function on the empty set. -/
@[to_additive (attr := simp) /-- Every family has locally uniform sum equal to any target function
on the empty set. -/]
theorem hasProdLocallyUniformlyOn_empty [TopologicalSpace β] :
    HasProdLocallyUniformlyOn f g ∅ :=
  hasProdUniformlyOn_empty.hasProdLocallyUniformlyOn

/-- Every family is locally uniformly multipliable on the empty set. -/
@[to_additive (attr := simp) /-- Every family is locally uniformly summable on the empty set. -/]
theorem multipliableLocallyUniformlyOn_empty [TopologicalSpace β] :
    MultipliableLocallyUniformlyOn f ∅ :=
  ⟨1, hasProdLocallyUniformlyOn_empty⟩

/-- If `f i x = 1` on `s` outside a finite index set `I`, then `f` converges uniformly on `s` to
the finite product `∏ i ∈ I, f i x`. -/
@[to_additive /-- If `f i x = 0` on `s` outside a finite index set `I`, then `f` converges
uniformly on `s` to the finite sum `∑ i ∈ I, f i x`. -/]
theorem hasProdUniformlyOn_prod_of_ne_finset_one {I : Finset ι}
    (hf : ∀ i ∉ I, ∀ x ∈ s, f i x = 1) :
    HasProdUniformlyOn f (fun x ↦ ∏ i ∈ I, f i x) s := by
  classical
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
  have hconst : TendstoUniformlyOn (fun _ : Finset ι ↦ fun x ↦ ∏ i ∈ I, f i x)
      (fun x ↦ ∏ i ∈ I, f i x) atTop s :=
    fun u hu ↦ Eventually.of_forall fun _ _ _ ↦ refl_mem_uniformity hu
  refine hconst.congr ?_
  filter_upwards [eventually_ge_atTop I] with J hIJ x hx
  exact Finset.prod_subset hIJ fun i _ hiI ↦ hf i hiI x hx

/-- If `f i x = 1` on `s` outside a finite index set `I`, then `f` is uniformly multipliable on
`s`. -/
@[to_additive /-- If `f i x = 0` on `s` outside a finite index set `I`, then `f` is uniformly
summable on `s`. -/]
theorem multipliableUniformlyOn_of_ne_finset_one {I : Finset ι}
    (hf : ∀ i ∉ I, ∀ x ∈ s, f i x = 1) :
    MultipliableUniformlyOn f s :=
  (hasProdUniformlyOn_prod_of_ne_finset_one hf).multipliableUniformlyOn

/-- Every family indexed by a `Fintype` converges uniformly on `s` to `∏ i, f i x`. -/
@[to_additive /-- Every family indexed by a `Fintype` converges uniformly on `s` to
`∑ i, f i x`. -/]
theorem hasProdUniformlyOn_fintype [Fintype ι] :
    HasProdUniformlyOn f (fun x ↦ ∏ i, f i x) s :=
  hasProdUniformlyOn_prod_of_ne_finset_one (I := Finset.univ) (by simp)

/-- Every family indexed by a finite type is uniformly multipliable on `s`. -/
@[to_additive /-- Every family indexed by a finite type is uniformly summable on `s`. -/]
theorem multipliableUniformlyOn_of_finite [Finite ι] :
    MultipliableUniformlyOn f s := by
  cases nonempty_fintype ι
  exact hasProdUniformlyOn_fintype.multipliableUniformlyOn

/-- If all but finitely many factors equal `1` identically on `s`, then the infinite product
converges uniformly on `s` to `∏' i, f i x`. -/
@[to_additive /-- If all but finitely many terms vanish identically on `s`, then the infinite sum
converges uniformly on `s` to `∑' i, f i x`. -/]
theorem hasProdUniformlyOn_of_cofinite_eq_one (hf : ∀ᶠ i in cofinite, ∀ x ∈ s, f i x = 1) :
    HasProdUniformlyOn f (fun x ↦ ∏' i, f i x) s := by
  have hfin : {i : ι | ¬ ∀ x ∈ s, f i x = 1}.Finite := hf
  have hmem : ∀ i ∉ hfin.toFinset, ∀ x ∈ s, f i x = 1 := by
    intro i hi
    simpa [Set.Finite.mem_toFinset] using hi
  refine (hasProdUniformlyOn_prod_of_ne_finset_one hmem).congr_right fun x hx ↦ ?_
  exact (tprod_eq_prod fun i hi ↦ hmem i hi x hx).symm

/-- If all but finitely many factors equal `1` identically on `s`, then `f` is uniformly
multipliable on `s`. -/
@[to_additive /-- If all but finitely many terms vanish identically on `s`, then `f` is uniformly
summable on `s`. -/]
theorem multipliableUniformlyOn_of_cofinite_eq_one (hf : ∀ᶠ i in cofinite, ∀ x ∈ s, f i x = 1) :
    MultipliableUniformlyOn f s :=
  (hasProdUniformlyOn_of_cofinite_eq_one hf).multipliableUniformlyOn

end DegenerateAndFinite

section CauchyNorm

variable {ι β E : Type*} [SeminormedAddCommGroup E] [CompleteSpace E]

/-- **Cauchy criterion for `SummableUniformlyOn` in a complete seminormed group.** A family
`f : ι → β → E` is uniformly summable on `s` if and only if finite partial sums over index sets
disjoint from a sufficiently large finite set are uniformly small in norm on `s`. -/
theorem summableUniformlyOn_iff_vanishing_norm {f : ι → β → E} {s : Set β} :
    SummableUniformlyOn f s ↔
      ∀ ε > 0, ∃ I : Finset ι, ∀ J : Finset ι, Disjoint J I → ∀ x ∈ s, ‖∑ i ∈ J, f i x‖ < ε := by
  have hdir : DirectedOn (fun a b : Set β ↦ a ⊆ b) {s} :=
    fun _ ha _ hb ↦ ⟨s, mem_singleton s, ha.subset, hb.subset⟩
  have hbasis := UniformOnFun.hasBasis_nhds_zero_of_basis {s} (singleton_nonempty s) hdir
    (Metric.nhds_basis_ball (x := (0 : E)))
  rw [SummableUniformlyOn, summable_iff_vanishing,
    hbasis.forall_iff fun _ _ hst ⟨I, hI⟩ ↦ ⟨I, fun J hJI ↦ hst (hI J hJI)⟩]
  simp only [Prod.forall, mem_singleton_iff, and_imp, Metric.mem_ball,
    dist_zero_right, mem_ofPred_eq, Function.comp_apply, ← UniformOnFun.ofFun_sum,
    UniformOnFun.toFun_ofFun, Finset.sum_apply]
  exact ⟨fun h ε hε ↦ h s ε rfl hε, by rintro h _ ε rfl hε; exact h ε hε⟩

end CauchyNorm

end TauCeti

namespace SummableUniformlyOn

/-- **Comparison test for `SummableUniformlyOn`.** If `g : ι → β → ℝ` is uniformly summable on `s`
and `‖f i x‖ ≤ g i x` on `s`, then `f` is uniformly summable on `s`. -/
theorem of_norm_bounded {ι β E : Type*} [SeminormedAddCommGroup E] [CompleteSpace E]
    {f : ι → β → E} {g : ι → β → ℝ} {s : Set β}
    (hg : SummableUniformlyOn g s) (hfg : ∀ i, ∀ x ∈ s, ‖f i x‖ ≤ g i x) :
    SummableUniformlyOn f s := by
  rw [TauCeti.summableUniformlyOn_iff_vanishing_norm] at hg ⊢
  intro ε hε
  obtain ⟨I, hI⟩ := hg ε hε
  refine ⟨I, fun J hJI x hx ↦ ?_⟩
  calc
    ‖∑ i ∈ J, f i x‖ ≤ ∑ i ∈ J, ‖f i x‖ := norm_sum_le J _
    _ ≤ ∑ i ∈ J, g i x := Finset.sum_le_sum fun i _ ↦ hfg i x hx
    _ ≤ ‖∑ i ∈ J, g i x‖ := Real.le_norm_self _
    _ < ε := hI J hJI x hx

/-- Nonnegative real comparison test for `SummableUniformlyOn`. -/
theorem of_nonneg_of_le {ι β : Type*} {f g : ι → β → ℝ} {s : Set β}
    (hg : SummableUniformlyOn g s) (hf0 : ∀ i, ∀ x ∈ s, 0 ≤ f i x)
    (hfg : ∀ i, ∀ x ∈ s, f i x ≤ g i x) :
    SummableUniformlyOn f s :=
  hg.of_norm_bounded fun i x hx ↦ by rw [Real.norm_of_nonneg (hf0 i x hx)]; exact hfg i x hx

end SummableUniformlyOn

namespace TauCeti

section NonnegReal

variable {ι β : Type*} {g : ι → β → ℝ} {s : Set β}

/-- For a family of real functions that are nonnegative on `s`, `SummableUniformlyOn g s` holds if
and only if finite sums over index sets disjoint from a large finite set are uniformly `< ε` on
`s`. -/
theorem summableUniformlyOn_of_nonneg_iff (hg0 : ∀ i, ∀ x ∈ s, 0 ≤ g i x) :
    SummableUniformlyOn g s ↔
      ∀ ε > 0, ∃ I : Finset ι, ∀ J : Finset ι, Disjoint J I → ∀ x ∈ s, ∑ i ∈ J, g i x < ε := by
  rw [summableUniformlyOn_iff_vanishing_norm]
  refine forall₂_congr fun ε _ ↦ exists_congr fun I ↦ forall₂_congr fun J _ ↦
    forall₂_congr fun x hx ↦ ?_
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ ↦ hg0 i x hx)]

/-- For a family of real functions that are nonnegative on `s`, `SummableUniformlyOn g s` is
equivalent to pointwise summability on `s` together with uniformly vanishing complement tails
`∑' i : {i // i ∉ I}, g i x`. -/
theorem summableUniformlyOn_iff_tsum_compl_of_nonneg (hg0 : ∀ i, ∀ x ∈ s, 0 ≤ g i x) :
    SummableUniformlyOn g s ↔
      (∀ x ∈ s, Summable (g · x)) ∧
        ∀ ε > 0, ∃ I : Finset ι, ∀ x ∈ s, (∑' i : {i // i ∉ I}, g i x) < ε := by
  rw [summableUniformlyOn_of_nonneg_iff hg0]
  constructor
  · intro h
    have hvan := (summableUniformlyOn_of_nonneg_iff hg0).2 h
    refine ⟨fun x hx ↦ hvan.summable hx, fun ε hε ↦ ?_⟩
    obtain ⟨I, hI⟩ := h (ε / 2) (half_pos hε)
    refine ⟨I, fun x hx ↦ ?_⟩
    have hle : (∑' i : {i // i ∉ I}, g i x) ≤ ε / 2 := by
      refine Real.tsum_le_of_sum_le (fun i ↦ hg0 i x hx) fun J ↦ ?_
      classical
      have hdisj : Disjoint (J.map (Embedding.subtype fun i ↦ i ∉ I)) I := by
        rw [Finset.disjoint_left]
        rintro i hi hiI
        rcases Finset.mem_map.1 hi with ⟨j, -, rfl⟩
        exact j.2 hiI
      simpa using (hI _ hdisj x hx).le
    exact hle.trans_lt (half_lt_self hε)
  · rintro ⟨hsum, htail⟩ ε hε
    obtain ⟨I, hI⟩ := htail ε hε
    refine ⟨I, fun J hJI x hx ↦ ?_⟩
    classical
    have hsub : ∑ i ∈ J, g i x = ∑ i ∈ J.subtype (· ∉ I), g i x :=
      (Finset.sum_subtype_of_mem (fun i ↦ g i x) fun i hi ↦ Finset.disjoint_left.1 hJI hi).symm
    have hsub_sum : Summable fun i : {i // i ∉ I} ↦ g i x := (hsum x hx).subtype (· ∉ I)
    rw [hsub]
    exact (hsub_sum.sum_le_tsum (J.subtype (· ∉ I)) fun i _ ↦ hg0 i x hx).trans_lt (hI x hx)

/-- **Uniform-tail characterization of `SummableUniformlyOn` over `ℕ`.** For nonnegative real
functions on `s`, uniform summability on `s` is equivalent to pointwise summability on `s` together
with uniformly vanishing sequential tails `∑' k, g (N + k) x`. -/
theorem summableUniformlyOn_nat_of_nonneg_iff {g : ℕ → β → ℝ} (hg0 : ∀ n, ∀ x ∈ s, 0 ≤ g n x) :
    SummableUniformlyOn g s ↔
      (∀ x ∈ s, Summable (g · x)) ∧
        ∀ ε > 0, ∃ N : ℕ, ∀ x ∈ s, (∑' k, g (N + k) x) < ε := by
  rw [summableUniformlyOn_of_nonneg_iff hg0]
  constructor
  · intro h
    have hvan := (summableUniformlyOn_of_nonneg_iff hg0).2 h
    refine ⟨fun x hx ↦ hvan.summable hx, fun ε hε ↦ ?_⟩
    obtain ⟨I, hI⟩ := h (ε / 2) (half_pos hε)
    refine ⟨I.sup id + 1, fun x hx ↦ ?_⟩
    have hle : (∑' k, g (I.sup id + 1 + k) x) ≤ ε / 2 := by
      refine Real.tsum_le_of_sum_range_le (fun k ↦ hg0 _ x hx) fun M ↦ ?_
      have hdisj : Disjoint ((Finset.range M).map (addLeftEmbedding (I.sup id + 1))) I := by
        rw [Finset.disjoint_left]
        rintro n hn hnI
        rcases Finset.mem_map.1 hn with ⟨k, -, rfl⟩
        have hleI : I.sup id + 1 + k ≤ I.sup id := I.le_sup (f := id) hnI
        omega
      simpa [addLeftEmbedding] using (hI _ hdisj x hx).le
    exact hle.trans_lt (half_lt_self hε)
  · rintro ⟨hsum, htail⟩ ε hε
    obtain ⟨N, hN⟩ := htail ε hε
    refine ⟨Finset.range N, fun J hJN x hx ↦ ?_⟩
    have hJ : J ⊆ (Finset.range (J.sup id + 1)).map (addLeftEmbedding N) := by
      intro n hn
      have hnN : N ≤ n := by
        have := Finset.disjoint_left.1 hJN hn
        simpa [Finset.mem_range] using this
      refine Finset.mem_map.2 ⟨n - N, Finset.mem_range.2 ?_, ?_⟩
      · have hleJ : n ≤ J.sup id := J.le_sup (f := id) hn
        omega
      · simp [addLeftEmbedding, Nat.add_sub_of_le hnN]
    have hsum_shift : Summable fun k ↦ g (N + k) x := by
      simpa [Nat.add_comm] using (summable_nat_add_iff N).2 (hsum x hx)
    calc
      ∑ n ∈ J, g n x ≤ ∑ n ∈ (Finset.range (J.sup id + 1)).map (addLeftEmbedding N), g n x :=
        Finset.sum_le_sum_of_subset_of_nonneg hJ fun n _ _ ↦ hg0 n x hx
      _ = ∑ k ∈ Finset.range (J.sup id + 1), g (N + k) x := by simp [addLeftEmbedding]
      _ ≤ ∑' k, g (N + k) x :=
        hsum_shift.sum_le_tsum _ fun k _ ↦ hg0 _ x hx
      _ < ε := hN x hx

end NonnegReal

end TauCeti

namespace SummableUniformlyOn

/-- If a nonnegative family `g : ι → β → ℝ` is uniformly summable on `s` and each `g i` is bounded
above on `s`, then the full sums `∑' i, g i x` and all finite partial sums `∑ i ∈ J, g i x` are
uniformly bounded on `s` by a single nonnegative constant `C`. -/
theorem exists_tsum_le_of_nonneg {ι β : Type*} {g : ι → β → ℝ} {s : Set β}
    (hg : SummableUniformlyOn g s) (hg0 : ∀ i, ∀ x ∈ s, 0 ≤ g i x)
    (hbd : ∀ i, BddAbove (g i '' s)) :
    ∃ C ≥ 0, (∀ x ∈ s, (∑' i, g i x) ≤ C) ∧ ∀ J : Finset ι, ∀ x ∈ s, ∑ i ∈ J, g i x ≤ C := by
  classical
  obtain ⟨I, hI⟩ := (TauCeti.summableUniformlyOn_iff_tsum_compl_of_nonneg hg0).1 hg
    |>.2 1 one_pos
  have hM : ∀ i, ∃ M ≥ 0, ∀ x ∈ s, g i x ≤ M := fun i ↦ by
    obtain ⟨M, hM⟩ := hbd i
    exact ⟨max M 0, le_max_right M 0, fun x hx ↦ (hM ⟨x, hx, rfl⟩).trans (le_max_left M 0)⟩
  choose M hM0 hMle using hM
  refine ⟨(∑ i ∈ I, M i) + 1,
    add_nonneg (Finset.sum_nonneg fun i _ ↦ hM0 i) zero_le_one,
    fun x hx ↦ ?_, fun J x hx ↦ ?_⟩
  · have hsum : Summable (g · x) := hg.summable hx
    rw [← hsum.sum_add_tsum_subtype_compl I]
    have hhead : ∑ i ∈ I, g i x ≤ ∑ i ∈ I, M i := Finset.sum_le_sum fun i _ ↦ hMle i x hx
    linarith [hI x hx]
  · have hsum : Summable (g · x) := hg.summable hx
    exact (hsum.sum_le_tsum J fun i _ ↦ hg0 i x hx).trans (by
      rw [← hsum.sum_add_tsum_subtype_compl I]
      have hhead : ∑ i ∈ I, g i x ≤ ∑ i ∈ I, M i := Finset.sum_le_sum fun i _ ↦ hMle i x hx
      linarith [hI x hx])

end SummableUniformlyOn
