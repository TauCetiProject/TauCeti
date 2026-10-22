/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import TauCeti.Analysis.Normed.Module.Dual.Norming
public import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
public import Mathlib.Topology.Compactness.CountablyCompact
public import Mathlib.Topology.MetricSpace.PiNat

/-!
# Weakly compact sets are weakly sequentially compact

In a real or complex normed space, every weakly compact set is weakly sequentially compact:
each sequence in it has a subsequence converging weakly to a point of the set. This is the
Šmulian half of the Eberlein–Šmulian theorem. No separability or completeness of the space is
assumed, and the weak topology need not be first countable on the set.

The proof reduces to a separable subspace. The closed linear span `S` of the sequence is
separable, and it is weakly closed since it is convex and norm closed. So the given compact set
meets `S` in a weakly compact set containing the sequence. A norming sequence `(fₙ)` for `S`
is a countable family of weakly continuous functions separating the points of this compact set,
which is therefore metrizable (`TopologicalSpace.MetrizableSpace.of_countable_separating`), and
so sequentially compact.

## Main results

* `WeakSpace.isSeqCompact_of_isCompact`: weakly compact sets are weakly sequentially compact.
* `WeakSpace.tendsto_subseq_of_isCompact_closure`: the relative version; every sequence in a
  relatively weakly compact set has a weakly convergent subsequence, whose limit lies in the
  weak closure of the set.
* `TauCeti.tendsto_toWeakSpace_subseq_of_bounded`: in a reflexive space, every bounded
  sequence has a weakly convergent subsequence.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, Theorem 2.8.6.
-/

public section

open Bornology Filter Function Set Topology TopologicalSpace NormedSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace WeakSpace

/-- **Šmulian's theorem**: a weakly compact subset of a normed space is weakly sequentially
compact. -/
theorem isSeqCompact_of_isCompact {s : Set (WeakSpace 𝕜 E)} (hs : IsCompact s) :
    IsSeqCompact s := by
  intro u hu
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := .of_algebraMap_smul fun _ _ ↦ rfl
  -- The closed linear span `S` of the sequence is separable and weakly closed.
  let S : Submodule 𝕜 E :=
    (Submodule.span 𝕜 (range fun n ↦ (toWeakSpace 𝕜 E).symm (u n))).topologicalClosure
  have hSsep : IsSeparable (S : Set E) := by
    rw [Submodule.topologicalClosure_coe]
    exact (countable_range _).isSeparable.span.closure
  have hSclosed : IsClosed (toWeakSpace 𝕜 E '' S) := by
    have hconv : Convex ℝ (S : Set E) := (S.restrictScalars ℝ).convex
    rw [← (Submodule.isClosed_topologicalClosure _).closure_eq, hconv.toWeakSpace_closure 𝕜]
    exact isClosed_closure
  -- A norming sequence for `S` separates the points of the weakly compact set `s ∩ S`,
  -- which is therefore metrizable.
  obtain ⟨f, -, hf⟩ := hSsep.exists_norming_seq 𝕜
  let K := s ∩ toWeakSpace 𝕜 E '' S
  have : CompactSpace K := isCompact_iff_compactSpace.mp (hs.inter_right hSclosed)
  have : MetrizableSpace K := by
    -- The weak topology is induced by the pairing `(topDualPairing 𝕜 E).flip`, whose
    -- evaluation at `f n` is by definition `x ↦ f n x`.
    refine Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
      (fun n (x : K) ↦ f n ((toWeakSpace 𝕜 E).symm x)) (fun n ↦
        (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip (f n)).comp continuous_subtype_val)
      ?_
    rintro ⟨_, _, a, ha, rfl⟩ ⟨_, _, b, hb, rfl⟩ hne
    by_contra! hab
    replace hab (n : ℕ) : f n a = f n b := by simpa using hab n
    refine hne (Subtype.ext (?_ : toWeakSpace 𝕜 E a = toWeakSpace 𝕜 E b))
    rw [← sub_eq_zero, ← map_sub, LinearEquiv.map_eq_zero_iff, ← norm_eq_zero,
      hf (a - b) (S.sub_mem ha hb)]
    simp [hab]
  obtain ⟨a, φ, hφ, h⟩ := SeqCompactSpace.tendsto_subseq fun n ↦ (⟨u n, hu n, _,
    Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self n)),
    (toWeakSpace 𝕜 E).apply_symm_apply (u n)⟩ : K)
  exact ⟨a, a.2.1, φ, hφ, (continuous_subtype_val.tendsto a).comp h⟩

/-- Every sequence in a relatively weakly compact subset of a normed space has a weakly
convergent subsequence. The limit lies in the weak closure of the set, but need not lie in the
set itself. -/
theorem tendsto_subseq_of_isCompact_closure {s : Set (WeakSpace 𝕜 E)}
    (hs : IsCompact (closure s)) {x : ℕ → WeakSpace 𝕜 E} (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  isSeqCompact_of_isCompact hs fun n ↦ subset_closure (hx n)

end WeakSpace

namespace TauCeti

/-- In a reflexive normed space, every bounded sequence has a weakly convergent subsequence. -/
theorem tendsto_toWeakSpace_subseq_of_bounded (hE : Surjective (inclusionInDoubleDual 𝕜 E))
    {s : Set E} (hs : IsBounded s) {x : ℕ → E} (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ closure (toWeakSpace 𝕜 E '' s), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (toWeakSpace 𝕜 E ∘ x ∘ φ) atTop (𝓝 a) :=
  WeakSpace.tendsto_subseq_of_isCompact_closure (isCompact_closure_toWeakSpace hE hs)
    fun n ↦ mem_image_of_mem _ (hx n)

end TauCeti
