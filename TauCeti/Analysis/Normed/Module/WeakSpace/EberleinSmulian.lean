/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sequences
public import TauCeti.Analysis.Normed.Module.WeakSpace.SeqCompact
public import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded
import TauCeti.Analysis.Normed.Operator.Norming
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.Normed.Module.Mazur

/-!
# The Eberlein–Šmulian theorem and sequential weak closures

Weak compactness and weak sequential compactness agree in real and complex normed spaces,
without completeness or separability assumptions. The relative version allows subsequential
limits to lie outside the original set.

The separable reduction uses finite predual norming sets. Given a weak-star bidual cluster
point, recursively choose vectors and finite norming sets for their finite-dimensional spans
together with that point. Any weak subsequential limit of the resulting sequence represents
the original bidual point. Banach–Alaoglu then supplies compactness.

Combined with Šmulian's subsequential compactness, the same sequence converges weakly to the
prescribed closure point (`TauCeti.exists_seq_tendsto_toWeakSpace_of_mem_closure`), because
every subsequence has a further subsequence converging to that unique cluster point. Consequently,
for any relatively weakly compact set `A` (in particular, any `A ⊆ K` with `K` weakly compact),
the weak closure coincides with the weak sequential closure
(`TauCeti.seqClosure_toWeakSpace_eq_closure`), weak closedness agrees with weak sequential
closedness, and every weakly compact subspace is a Fréchet–Urysohn space
(`TauCeti.frechetUrysohnSpace_toWeakSpace_of_isCompact`).

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.8, Theorem 2.8.6 and
  Corollary 2.8.9.
-/

public section

open Bornology Filter Metric Set Topology

namespace TauCeti

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

/-- **Sequential-closure Eberlein–Šmulian, relative form.** If `A` has weakly compact closure in a
real or complex normed space, every point in the weak closure of `A` is the weak limit of a
sequence in `A`. -/
theorem exists_seq_tendsto_toWeakSpace_of_mem_closure {A : Set E}
    (hA : IsCompact (closure (toWeakSpace 𝕜 E '' A))) {x : E}
    (hx : toWeakSpace 𝕜 E x ∈ closure (toWeakSpace 𝕜 E '' A)) :
    ∃ u : ℕ → E, (∀ n, u n ∈ A) ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)) := by
  have hφ := mem_closure_image
    (NormedSpace.inclusionInDoubleDualWeak 𝕜 E).continuous.continuousAt hx
  obtain ⟨u, hu, huniq⟩ := exists_seq_inclusionInDoubleDualWeak_eq_of_mem_closure hφ
  refine ⟨u, hu, tendsto_of_subseq_tendsto fun ns hns ↦ ?_⟩
  obtain ⟨ψ, -, hnsψ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨y, θ, hθ, hlim⟩ :=
    tendsto_subseq_toWeakSpace_of_isCompact_closure hA (fun n ↦ hu (ns (ψ n)))
  have hyx : toWeakSpace 𝕜 E y = toWeakSpace 𝕜 E x :=
    (NormedSpace.isEmbedding_inclusionInDoubleDualWeak 𝕜 E).injective
      (huniq y ((ns ∘ ψ) ∘ θ) (hnsψ.comp hθ) hlim)
  exact ⟨ψ ∘ θ, hyx ▸ hlim⟩

/-- **Sequential-closure Eberlein–Šmulian.** If `K` is weakly compact in a real or complex normed
space and `A ⊆ K`, every point in the weak closure of `A` lies in `K` and is the weak limit of a
sequence in `A`. -/
theorem exists_seq_tendsto_toWeakSpace_of_mem_closure_of_subset {K A : Set E}
    (hK : IsCompact (toWeakSpace 𝕜 E '' K)) (hAK : A ⊆ K) {x : E}
    (hx : toWeakSpace 𝕜 E x ∈ closure (toWeakSpace 𝕜 E '' A)) :
    x ∈ K ∧ ∃ u : ℕ → E, (∀ n, u n ∈ A) ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)) := by
  have hsub : closure (toWeakSpace 𝕜 E '' A) ⊆ toWeakSpace 𝕜 E '' K :=
    closure_minimal (image_mono hAK) hK.isClosed
  have hxK : x ∈ K := (toWeakSpace 𝕜 E).injective.mem_set_image.mp (hsub hx)
  exact ⟨hxK, exists_seq_tendsto_toWeakSpace_of_mem_closure
    (hK.of_isClosed_subset isClosed_closure hsub) hx⟩

/-- For a relatively weakly compact subset of a real or complex normed space, the weak sequential
closure equals the weak closure. -/
theorem seqClosure_toWeakSpace_eq_closure {A : Set E}
    (hA : IsCompact (closure (toWeakSpace 𝕜 E '' A))) :
    seqClosure (toWeakSpace 𝕜 E '' A) = closure (toWeakSpace 𝕜 E '' A) := by
  refine seqClosure_subset_closure.antisymm fun w hw ↦ ?_
  have hw' : toWeakSpace 𝕜 E ((toWeakSpace 𝕜 E).symm w) ∈ closure (toWeakSpace 𝕜 E '' A) := by
    simpa only [LinearEquiv.apply_symm_apply] using hw
  obtain ⟨u, hu, hlim⟩ := exists_seq_tendsto_toWeakSpace_of_mem_closure hA hw'
  refine ⟨fun n ↦ toWeakSpace 𝕜 E (u n), fun n ↦ mem_image_of_mem _ (hu n), ?_⟩
  simpa only [LinearEquiv.apply_symm_apply] using hlim

/-- A relatively weakly compact subset of a real or complex normed space is weakly closed if and
only if it is weakly sequentially closed. -/
theorem isClosed_toWeakSpace_iff_isSeqClosed_of_isCompact_closure {A : Set E}
    (hA : IsCompact (closure (toWeakSpace 𝕜 E '' A))) :
    IsClosed (toWeakSpace 𝕜 E '' A) ↔ IsSeqClosed (toWeakSpace 𝕜 E '' A) :=
  ⟨IsClosed.isSeqClosed, fun hseq ↦ by
    rw [← closure_eq_iff_isClosed, ← seqClosure_toWeakSpace_eq_closure hA, hseq.seqClosure_eq]⟩

/-- A subset `A` of a weakly compact set `K` in a real or complex normed space is weakly closed if
and only if it is weakly sequentially closed. -/
theorem isClosed_toWeakSpace_iff_isSeqClosed_of_subset {K A : Set E}
    (hK : IsCompact (toWeakSpace 𝕜 E '' K)) (hAK : A ⊆ K) :
    IsClosed (toWeakSpace 𝕜 E '' A) ↔ IsSeqClosed (toWeakSpace 𝕜 E '' A) :=
  isClosed_toWeakSpace_iff_isSeqClosed_of_isCompact_closure <|
    hK.of_isClosed_subset isClosed_closure (closure_minimal (image_mono hAK) hK.isClosed)

/-- **Kaplansky's theorem.** Every weakly compact subset of a real or complex normed space is a
Fréchet–Urysohn space in the weak topology, hence in particular a sequential space. -/
theorem frechetUrysohnSpace_toWeakSpace_of_isCompact {K : Set E}
    (hK : IsCompact (toWeakSpace 𝕜 E '' K)) :
    FrechetUrysohnSpace (toWeakSpace 𝕜 E '' K) where
  closure_subset_seqClosure s z hz := by
    set A : Set E := toWeakSpace 𝕜 E ⁻¹' (Subtype.val '' s)
    have hAs : toWeakSpace 𝕜 E '' A = Subtype.val '' s :=
      (toWeakSpace 𝕜 E).surjective.image_preimage _
    have hAK : A ⊆ K := by
      rintro y ⟨w, -, hw⟩
      exact (toWeakSpace 𝕜 E).injective.mem_set_image.mp (hw ▸ w.2)
    have hz' : toWeakSpace 𝕜 E ((toWeakSpace 𝕜 E).symm z.1) ∈ closure (toWeakSpace 𝕜 E '' A) := by
      rw [LinearEquiv.apply_symm_apply, hAs]
      exact mem_closure_image continuous_subtype_val.continuousAt hz
    obtain ⟨-, u, huA, hlim⟩ := exists_seq_tendsto_toWeakSpace_of_mem_closure_of_subset hK hAK hz'
    choose v hvs hvu using fun n ↦ (huA n : toWeakSpace 𝕜 E (u n) ∈ Subtype.val '' s)
    refine ⟨v, hvs, IsInducing.subtypeVal.tendsto_nhds_iff.2 ?_⟩
    simpa only [Function.comp_def, hvu, LinearEquiv.apply_symm_apply] using hlim

end TauCeti
