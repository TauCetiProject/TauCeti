/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.WeakSpace.SeqCompact
public import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded
public import Mathlib.Topology.Sequences
import TauCeti.Analysis.Normed.Operator.Norming
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.LocallyConvex.Mazur
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# The Eberlein–Šmulian theorem and sequential weak closure

Weak compactness and weak sequential compactness agree in real and complex normed spaces,
without completeness or separability assumptions. The relative version allows subsequential
limits to lie outside the original set.

The separable reduction uses finite predual norming sets. Given a weak-star bidual cluster
point, recursively choose vectors and finite norming sets for their finite-dimensional spans
together with that point. Any weak subsequential limit of the resulting sequence represents
the original bidual point. Banach–Alaoglu then supplies compactness.

Combined with relative weak sequential compactness, the same sequence construction yields the
sequential-closure form of Eberlein–Šmulian (Kaplansky–Eberlein–Šmulian): for any set `A` with
weakly compact closure in a real or complex seminormed space — in particular, any subset of a
weakly compact set — its weak closure equals its sequential weak closure
(`TauCeti.seqClosure_toWeakSpace_eq_closure`). Every weakly compact set is therefore a
Fréchet–Urysohn space in the weak topology (`TauCeti.frechetUrysohnSpace_toWeakSpace_of_isCompact`),
and weak closedness agrees with sequential weak closedness on subsets with weakly compact closure.
Relative weak compactness is essential: in `ℓ²`, von Neumann's set `{e_m + m • e_n | 1 ≤ m < n}`
contains `0` in its weak closure while every weakly convergent sequence in it is norm bounded and
hence cannot converge weakly to `0`.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.8, Theorem 2.8.6 and
  Corollary 2.8.9.
-/

public section

open Bornology Filter Metric Set Topology

namespace TauCeti

section Normed

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The sequence used in the separable reduction: every weak subsequential limit represents
the prescribed weak-star cluster point in the bidual. -/
theorem exists_seq_inclusionInDoubleDualWeak_eq_of_mem_closure {K : Set E}
    {φ : WeakDual 𝕜 (StrongDual 𝕜 E)}
    (hφ : φ ∈ closure (NormedSpace.inclusionInDoubleDualWeak 𝕜 E ''
      (toWeakSpace 𝕜 E '' K))) :
    ∃ u : ℕ → E, (∀ n, u n ∈ K) ∧
      ∀ (x : E) (σ : ℕ → ℕ), StrictMono σ →
        Tendsto (fun n ↦ toWeakSpace 𝕜 E (u (σ n))) atTop (𝓝 (toWeakSpace 𝕜 E x)) →
        NormedSpace.inclusionInDoubleDualWeak 𝕜 E (toWeakSpace 𝕜 E x) = φ := by
  -- Recursively choose `p` and `u`, prove agreement on accumulated tests in `heval`,
  -- then close by norming the difference in the closure of the accumulated spans.
  classical
  let : NormedAddCommGroup (StrongDual 𝕜 E) := ContinuousLinearMap.normedAddCommGroup
  let : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
    ContinuousLinearMap.normedAddCommGroup
  let J := NormedSpace.inclusionInDoubleDual 𝕜 E
  let Φ := WeakDual.toStrongDual φ
  let M (s : Finset E) : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
    Submodule.span 𝕜 (insert Φ (J '' (s : Set E)))
  have hfinite (s : Finset E) : FiniteDimensional 𝕜 (M s) :=
    FiniteDimensional.span_of_finite 𝕜 ((s.finite_toSet.image J).insert Φ)
  have hnorming (s : Finset E) : ∃ t : Finset (StrongDual 𝕜 E),
      (∀ f ∈ t, ‖f‖ ≤ 1) ∧ ∀ ψ ∈ M s, ∃ f ∈ t, ‖ψ‖ ≤ 2 * ‖ψ f‖ := by
    let := hfinite s
    exact (M s).exists_finset_norming (by norm_num)
  choose t ht hnorm using hnorming
  have happ (n : ℕ) (p : Finset E × Finset (StrongDual 𝕜 E)) :
      ∃ x ∈ K, ∀ f ∈ p.2 ∪ t p.1, ‖f x - Φ f‖ < 1 / ((n : ℝ) + 1) := by
    let U : Set (WeakDual 𝕜 (StrongDual 𝕜 E)) :=
      ⋂ f ∈ p.2 ∪ t p.1, {ψ | ‖ψ f - φ f‖ < 1 / ((n : ℝ) + 1)}
    have hU : IsOpen U := isOpen_biInter_finset fun f _ ↦
      isOpen_lt ((WeakDual.eval_continuous f).sub continuous_const).norm continuous_const
    have hφU : φ ∈ U := by
      simp only [U, mem_iInter, mem_ofPred_eq, sub_self, norm_zero]
      intro f _
      positivity
    obtain ⟨_, hxU, ⟨_, ⟨x, hx, rfl⟩, rfl⟩⟩ :=
      mem_closure_iff.mp hφ U hU hφU
    exact ⟨x, hx, by simpa [U, Φ, NormedSpace.inclusionInDoubleDualWeak_apply] using hxU⟩
  choose a ha happly using happ
  -- Keep both the previously chosen vectors and all the tests accumulated so far.
  let p : ℕ → Finset E × Finset (StrongDual 𝕜 E) :=
    Nat.rec (∅, ∅) (fun n q ↦ (insert (a n q) q.1, q.2 ∪ t q.1))
  let u (n : ℕ) := a n (p n)
  have hp (n : ℕ) : p (n + 1) = (insert (u n) (p n).1, (p n).2 ∪ t (p n).1) := rfl
  have hmono₁ : Monotone (fun n ↦ (p n).1) := monotone_nat_of_le_succ fun n ↦ by
    rw [hp]; exact Finset.subset_insert _ _
  have hmono₂ : Monotone (fun n ↦ (p n).2) := monotone_nat_of_le_succ fun n ↦ by
    rw [hp]; exact Finset.subset_union_left
  refine ⟨u, fun n ↦ ha n (p n), fun x σ hσ hlim ↦ ?_⟩
  -- Each fixed test eventually occurs in every approximation condition.
  have heval (n : ℕ) (f : StrongDual 𝕜 E) (hf : f ∈ t (p n).1) : Φ f = f x := by
    have happrox : Tendsto (fun m ↦ f (u m) - Φ f) atTop (𝓝 0) := by
      apply squeeze_zero_norm' _ tendsto_one_div_add_atTop_nhds_zero_nat
      filter_upwards [eventually_ge_atTop (n + 1)] with m hm
      have hf' : f ∈ (p m).2 := hmono₂ hm
        (by simpa only [hp] using Finset.mem_union_right (p n).2 hf)
      exact (happly m (p m) f (Finset.mem_union_left _ hf')).le
    have h₁ := ((WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip f).tendsto
      (toWeakSpace 𝕜 E x)).comp hlim
    have h₂ := happrox.comp hσ.tendsto_atTop
    have : f x - Φ f = 0 := tendsto_nhds_unique (h₁.sub_const (Φ f)) h₂
    exact (sub_eq_zero.mp this).symm
  let ψ := Φ - J x
  have hzero (n : ℕ) (f : StrongDual 𝕜 E) (hf : f ∈ t (p n).1) : ψ f = 0 := by
    simp [ψ, J, heval n f hf]
  -- The accumulated finite spans are normed by the chosen tests.
  have hMmono : Monotone (fun n ↦ M (p n).1) := fun i j hij ↦
    Submodule.span_mono (insert_subset_insert (image_mono (hmono₁ hij)))
  let L : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
    (⨆ n, M (p n).1).topologicalClosure
  have hL : ψ ∈ L := by
    have hΦ : Φ ∈ L := Submodule.le_topologicalClosure _
      ((le_iSup (fun n ↦ M (p n).1) 0) (Submodule.subset_span (mem_insert _ _)))
    have hJu (n : ℕ) : J (u n) ∈ L := Submodule.le_topologicalClosure _
      ((le_iSup (fun n ↦ M (p n).1) (n + 1))
        (Submodule.subset_span (mem_insert_of_mem _ ⟨u n, by simp [hp], rfl⟩)))
    -- A norm-closed subspace is weakly closed, so it contains the weak limit `x`.
    let N := L.comap J.toLinearMap
    have hNclosed : IsClosed (N : Set E) :=
      (⨆ n, M (p n).1).isClosed_topologicalClosure.preimage J.continuous
    have hxN : x ∈ N := by
      let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
      let : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
      exact (N.restrictScalars ℝ).convex.mem_of_tendsto_weak hNclosed
        (fun n ↦ hJu (σ n)) hlim
    exact L.sub_mem hΦ hxN
  have hψ : ψ = 0 := ψ.eq_zero_of_mem_topologicalClosure_iSup_of_norming hMmono
    (by norm_num) (fun n ↦ ht (p n).1) (fun n ↦ hnorm (p n).1) hL hzero
  have hJ : NormedSpace.inclusionInDoubleDual 𝕜 E x = WeakDual.toStrongDual φ :=
    (sub_eq_zero.mp hψ).symm
  simpa only [NormedSpace.inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply,
    WeakDual.toWeakDual_toStrongDual] using congrArg StrongDual.toWeakDual hJ

/-- **Eberlein–Šmulian, relative form.** A set in a real or complex normed space has
weakly compact closure exactly when every sequence in it has a weakly convergent subsequence
with limit in the ambient space. -/
theorem isCompact_closure_toWeakSpace_iff {K : Set E} :
    IsCompact (closure (toWeakSpace 𝕜 E '' K)) ↔
      ∀ u : ℕ → E, (∀ n, u n ∈ K) → ∃ x : E, ∃ σ : ℕ → ℕ,
        StrictMono σ ∧
          Tendsto (fun n ↦ toWeakSpace 𝕜 E (u (σ n))) atTop (𝓝 (toWeakSpace 𝕜 E x)) := by
  refine ⟨fun hK _ hu ↦ tendsto_subseq_toWeakSpace_of_isCompact_closure hK hu, fun hK ↦ ?_⟩
  apply NormedSpace.isCompact_closure_of_isBounded
  · rw [Set.preimage_image_eq _ (toWeakSpace 𝕜 E).injective]
    exact isBounded_of_forall_tendsto_subseq_toWeakSpace hK
  · intro φ hφ
    obtain ⟨u, hu, huniq⟩ := exists_seq_inclusionInDoubleDualWeak_eq_of_mem_closure hφ
    obtain ⟨x, σ, hσ, hlim⟩ := hK u hu
    exact ⟨toWeakSpace 𝕜 E x, huniq x σ hσ hlim⟩

/-- **Eberlein–Šmulian.** Weak compactness is equivalent to weak sequential compactness,
without completeness or separability assumptions. -/
theorem isCompact_toWeakSpace_iff_isSeqCompact {K : Set E} :
    IsCompact (toWeakSpace 𝕜 E '' K) ↔ IsSeqCompact (toWeakSpace 𝕜 E '' K) := by
  refine ⟨isSeqCompact_toWeakSpace_of_isCompact, fun hK ↦ ?_⟩
  have hrelative : ∀ u : ℕ → E, (∀ n, u n ∈ K) → ∃ x : E, ∃ σ : ℕ → ℕ,
      StrictMono σ ∧
        Tendsto (fun n ↦ toWeakSpace 𝕜 E (u (σ n))) atTop (𝓝 (toWeakSpace 𝕜 E x)) := by
    intro u hu
    obtain ⟨_, ⟨x, _, rfl⟩, σ, hσ, hlim⟩ :=
      hK (fun n ↦ mem_image_of_mem (toWeakSpace 𝕜 E) (hu n))
    exact ⟨x, σ, hσ, hlim⟩
  have hclosed : IsClosed (toWeakSpace 𝕜 E '' K) := by
    apply isClosed_of_closure_subset
    intro z hz
    have hφ := mem_closure_image
      (NormedSpace.inclusionInDoubleDualWeak 𝕜 E).continuous.continuousAt hz
    obtain ⟨u, hu, huniq⟩ := exists_seq_inclusionInDoubleDualWeak_eq_of_mem_closure hφ
    obtain ⟨_, ⟨x, hx, rfl⟩, σ, hσ, hlim⟩ :=
      hK (fun n ↦ mem_image_of_mem (toWeakSpace 𝕜 E) (hu n))
    have hxz : toWeakSpace 𝕜 E x = z := by
      apply (NormedSpace.isEmbedding_inclusionInDoubleDualWeak 𝕜 E).injective
      exact huniq x σ hσ hlim
    exact hxz ▸ mem_image_of_mem (toWeakSpace 𝕜 E) hx
  simpa only [hclosed.closure_eq] using isCompact_closure_toWeakSpace_iff.mpr hrelative

private theorem exists_seq_tendsto_toWeakSpace_of_mem_closure_normed {A : Set E}
    (hA : IsCompact (closure (toWeakSpace 𝕜 E '' A))) {z : WeakSpace 𝕜 E}
    (hz : z ∈ closure (toWeakSpace 𝕜 E '' A)) :
    ∃ u : ℕ → E, (∀ n, u n ∈ A) ∧ Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 z) := by
  have hφ := mem_closure_image
    (NormedSpace.inclusionInDoubleDualWeak 𝕜 E).continuous.continuousAt hz
  obtain ⟨u, hu, huniq⟩ := exists_seq_inclusionInDoubleDualWeak_eq_of_mem_closure hφ
  refine ⟨u, hu, ?_⟩
  by_contra hnot
  obtain ⟨s, hs, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.mp hnot
  obtain ⟨φ, hφ_mono, hφ_not⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨y, ψ, hψ_mono, hlim⟩ :=
    tendsto_subseq_toWeakSpace_of_isCompact_closure hA (fun n ↦ hu (φ n))
  have hyz : toWeakSpace 𝕜 E y = z :=
    (NormedSpace.isEmbedding_inclusionInDoubleDualWeak 𝕜 E).injective
      (huniq y (φ ∘ ψ) (hφ_mono.comp hψ_mono) hlim)
  obtain ⟨n, hn⟩ := ((hyz ▸ hlim).eventually_mem hs).exists
  exact hφ_not (ψ n) hn

end Normed

section Seminormed

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Eberlein–Šmulian, sequential-closure form.** If `A` has weakly compact closure in a real or
complex seminormed space, a vector lies in the weak closure of `A` if and only if it is the weak
limit of a sequence in `A`. -/
theorem mem_closure_toWeakSpace_iff_exists_seq_tendsto {A : Set E}
    (hA : IsCompact (closure (toWeakSpace 𝕜 E '' A))) {x : E} :
    toWeakSpace 𝕜 E x ∈ closure (toWeakSpace 𝕜 E '' A) ↔
      ∃ u : ℕ → E, (∀ n, u n ∈ A) ∧
        Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)) := by
  refine ⟨fun hx ↦ ?_, fun ⟨u, hu, hlim⟩ ↦
    mem_closure_of_tendsto hlim (.of_forall fun n ↦ mem_image_of_mem _ (hu n))⟩
  let π := WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E)
  have hπ (y : E) : WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E) (toWeakSpace 𝕜 E y) =
      toWeakSpace 𝕜 (SeparationQuotient E) (SeparationQuotient.mk y) := rfl
  have hpi : π '' (toWeakSpace 𝕜 E '' A) =
      toWeakSpace 𝕜 (SeparationQuotient E) '' (SeparationQuotient.mk '' A) := by
    simp_rw [π, ← image_comp, Function.comp_def, hπ]
  have hA' : IsCompact
      (closure (toWeakSpace 𝕜 (SeparationQuotient E) '' (SeparationQuotient.mk '' A))) := by
    rw [← hpi]
    exact (hA.image π.continuous).closure.of_isClosed_subset isClosed_closure
      (closure_mono (image_mono subset_closure))
  have hx' : toWeakSpace 𝕜 (SeparationQuotient E) (SeparationQuotient.mk x) ∈
      closure (toWeakSpace 𝕜 (SeparationQuotient E) '' (SeparationQuotient.mk '' A)) := by
    rw [← hπ x, ← hpi]
    exact mem_closure_image π.continuous.continuousAt hx
  obtain ⟨q, hq, hlim⟩ := exists_seq_tendsto_toWeakSpace_of_mem_closure_normed hA' hx'
  choose u hu hqu using hq
  refine ⟨u, hu, (WeakSpace.isInducing_map_mkCLM 𝕜 E).tendsto_nhds_iff.mpr ?_⟩
  simpa only [Function.comp_def, hπ, hqu] using hlim

/-- If `A` has weakly compact closure in a real or complex seminormed space, its sequential weak
closure equals its weak closure. -/
theorem seqClosure_toWeakSpace_eq_closure {A : Set E}
    (hA : IsCompact (closure (toWeakSpace 𝕜 E '' A))) :
    seqClosure (toWeakSpace 𝕜 E '' A) = closure (toWeakSpace 𝕜 E '' A) := by
  refine seqClosure_subset_closure.antisymm fun z hz ↦ ?_
  have hz' : toWeakSpace 𝕜 E ((toWeakSpace 𝕜 E).symm z) ∈ closure (toWeakSpace 𝕜 E '' A) := by
    simpa only [LinearEquiv.apply_symm_apply] using hz
  obtain ⟨u, hu, hlim⟩ := (mem_closure_toWeakSpace_iff_exists_seq_tendsto hA).mp hz'
  exact ⟨fun n ↦ toWeakSpace 𝕜 E (u n), fun n ↦ mem_image_of_mem _ (hu n),
    by simpa only [LinearEquiv.apply_symm_apply] using hlim⟩

/-- Every point in the weak closure of a subset `A` of a weakly compact set `K` is the weak limit
of a sequence in `A`. -/
theorem mem_closure_toWeakSpace_iff_exists_seq_tendsto_of_subset_isCompact {A K : Set E}
    (hAK : A ⊆ K) (hK : IsCompact (toWeakSpace 𝕜 E '' K)) {x : E} :
    toWeakSpace 𝕜 E x ∈ closure (toWeakSpace 𝕜 E '' A) ↔
      ∃ u : ℕ → E, (∀ n, u n ∈ A) ∧
        Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)) :=
  mem_closure_toWeakSpace_iff_exists_seq_tendsto
    (hK.closure.of_isClosed_subset isClosed_closure (closure_mono (image_mono hAK)))

/-- Every weakly compact subset of a real or complex seminormed space is a Fréchet–Urysohn space in
the induced weak topology, and hence a sequential space. -/
theorem frechetUrysohnSpace_toWeakSpace_of_isCompact {K : Set E}
    (hK : IsCompact (toWeakSpace 𝕜 E '' K)) :
    FrechetUrysohnSpace (toWeakSpace 𝕜 E '' K) := by
  refine ⟨fun S ⟨z, hz⟩ hmem ↦ ?_⟩
  let A : Set E := (toWeakSpace 𝕜 E) ⁻¹' ((↑) '' S)
  have hAK : A ⊆ K := by
    rintro x ⟨⟨w, hw⟩, -, hwx⟩
    obtain ⟨y, hy, rfl⟩ := hw
    exact (toWeakSpace 𝕜 E).injective hwx.symm ▸ hy
  have himg : toWeakSpace 𝕜 E '' A = (↑) '' S :=
    (toWeakSpace 𝕜 E).image_preimage _
  have hzA : toWeakSpace 𝕜 E ((toWeakSpace 𝕜 E).symm z) ∈ closure (toWeakSpace 𝕜 E '' A) := by
    rw [LinearEquiv.apply_symm_apply, himg, ← Subtype.coe_mk z hz]
    exact closure_subtype.mp hmem
  obtain ⟨u, hu, hlim⟩ :=
    (mem_closure_toWeakSpace_iff_exists_seq_tendsto_of_subset_isCompact hAK hK).mp hzA
  have huS (n : ℕ) : ∃ w ∈ S, (w : WeakSpace 𝕜 E) = toWeakSpace 𝕜 E (u n) := by
    obtain ⟨w, hwS, hwu⟩ := hu n
    exact ⟨w, hwS, hwu⟩
  choose w hwS hwu using huS
  refine ⟨w, hwS, tendsto_subtype_rng.mpr ?_⟩
  simpa only [hwu, LinearEquiv.apply_symm_apply] using hlim

/-- For a set with weakly compact closure in a real or complex seminormed space, weak closedness is
equivalent to sequential weak closedness. -/
theorem isClosed_toWeakSpace_iff_isSeqClosed {A : Set E}
    (hA : IsCompact (closure (toWeakSpace 𝕜 E '' A))) :
    IsClosed (toWeakSpace 𝕜 E '' A) ↔ IsSeqClosed (toWeakSpace 𝕜 E '' A) := by
  rw [← closure_eq_iff_isClosed, ← seqClosure_toWeakSpace_eq_closure hA, isSeqClosed_iff]

/-- Within a weakly compact set in a real or complex seminormed space, weak closedness of a subset
is equivalent to sequential weak closedness. -/
theorem isClosed_toWeakSpace_iff_isSeqClosed_of_subset_isCompact {A K : Set E}
    (hAK : A ⊆ K) (hK : IsCompact (toWeakSpace 𝕜 E '' K)) :
    IsClosed (toWeakSpace 𝕜 E '' A) ↔ IsSeqClosed (toWeakSpace 𝕜 E '' A) :=
  isClosed_toWeakSpace_iff_isSeqClosed
    (hK.closure.of_isClosed_subset isClosed_closure (closure_mono (image_mono hAK)))

end Seminormed

end TauCeti
