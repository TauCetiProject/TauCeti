/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Sequences

/-!
# Weakly compact sets are weakly sequentially compact

This file proves Šmulian's half of the Eberlein–Šmulian theorem: in a real or complex normed
space, a weakly compact set is weakly sequentially compact, and every sequence in a relatively
weakly compact set has a weakly convergent subsequence. No separability or completeness
assumption is made on the space.

The proof is a separable reduction. A norm-separable set `s` is separated by countably many
continuous linear functionals of norm at most one: choose norming functionals at the points of
a countable dense subset of `s - s`. On a weakly compact, norm-separable set these functionals
induce a continuous injection into a countable product of metric spaces, so the weak topology
there is metrizable and compactness gives convergent subsequences. A sequence in an arbitrary
weakly compact set `K` lies in the closed linear span of its terms, which is norm separable and,
being convex and norm closed, weakly closed; its intersection with `K` is therefore a weakly
compact, norm-separable set containing the sequence.

The separation argument is the one carried out inline in Mathlib's
`ae_eq_zero_of_forall_dual_of_isSeparable`, and the metrizability step follows Mathlib's
`WeakDual.metrizable_of_isCompact` for the weak-star topology.

## Main declarations

* `TauCeti.exists_seq_dual_injOn_of_isSeparable`: countably many functionals of norm at
  most one separate the points of a norm-separable set.
* `TauCeti.metrizableSpace_toWeakSpace_of_isSeparable_of_isCompact`: a weakly compact,
  norm-separable set is metrizable in the weak topology.
* `TauCeti.isSeqCompact_toWeakSpace_of_isCompact`: weakly compact sets are weakly sequentially
  compact.
* `TauCeti.tendsto_subseq_toWeakSpace_of_isCompact_closure`: every sequence in a relatively
  weakly compact set has a subsequence converging weakly to a point of the space.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.8 (Theorem 2.8.6).
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §1.6.
-/

public section

open Filter Set Topology TopologicalSpace

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable (𝕜) in
/-- Countably many continuous linear functionals of norm at most one separate the points of a
norm-separable set. -/
theorem exists_seq_dual_injOn_of_isSeparable {s : Set E} (hs : IsSeparable s) :
    ∃ f : ℕ → StrongDual 𝕜 E, (∀ n, ‖f n‖ ≤ 1) ∧ InjOn (fun x n ↦ f n x) s := by
  obtain ⟨c, -, hc, hsc⟩ :=
    ((hs.prod hs).image (continuous_fst.sub continuous_snd)).exists_countable_dense_subset
  obtain ⟨d, hd⟩ := (hc.insert 0).exists_eq_range (insert_nonempty 0 c)
  choose f hf_norm hf_apply using fun n ↦ exists_dual_vector'' 𝕜 (d n)
  refine ⟨f, hf_norm, fun x hx y hy hxy ↦ ?_⟩
  -- The difference `z = x - y` is annihilated by every `f n` and lies in the closure of `range d`.
  set z := x - y with hz_def
  have hfz (n : ℕ) : f n z = 0 := by simp [hz_def, congrFun hxy n]
  have hz : z ∈ closure (range d) :=
    closure_mono (hd ▸ subset_insert 0 c) (hsc ⟨(x, y), ⟨hx, hy⟩, rfl⟩)
  -- Each `‖d n‖ = ‖f n (d n - z)‖` is at most `‖d n - z‖`, so `‖z‖ ≤ 2 ‖z - d n‖`.
  have hle (n : ℕ) : ‖z‖ ≤ 2 * dist z (d n) := by
    have hdn : ‖d n‖ ≤ ‖d n - z‖ := by
      calc ‖d n‖ = ‖f n (d n - z)‖ := by simp [hf_apply, hfz]
        _ ≤ ‖f n‖ * ‖d n - z‖ := (f n).le_opNorm _
        _ ≤ 1 * ‖d n - z‖ := by gcongr; exact hf_norm n
        _ = ‖d n - z‖ := one_mul _
    rw [dist_eq_norm, ← norm_neg (z - d n), neg_sub]
    linarith [norm_le_insert' z (d n), norm_sub_rev z (d n)]
  by_contra hne
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := Metric.mem_closure_range_iff.mp hz (‖z‖ / 2) (half_pos hpos)
  linarith [hle n]

/-- A weakly compact, norm-separable set is metrizable in the weak topology. -/
theorem metrizableSpace_toWeakSpace_of_isSeparable_of_isCompact {K : Set E} (hsep : IsSeparable K)
    (hK : IsCompact (toWeakSpace 𝕜 E '' K)) : MetrizableSpace (toWeakSpace 𝕜 E '' K) := by
  have : CompactSpace (toWeakSpace 𝕜 E '' K) := isCompact_iff_compactSpace.mp hK
  obtain ⟨f, -, hf⟩ := exists_seq_dual_injOn_of_isSeparable 𝕜 hsep
  -- Evaluations at the `f n` are continuous for the weak topology, which they generate.
  refine Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
    (fun n (w : toWeakSpace 𝕜 E '' K) ↦ f n ((toWeakSpace 𝕜 E).symm w))
    (fun n ↦ (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip (f n)).comp
      continuous_subtype_val) ?_
  rintro ⟨-, x, hx, rfl⟩ ⟨-, y, hy, rfl⟩ hne
  by_contra! h
  exact hne <| Subtype.ext <| congrArg (toWeakSpace 𝕜 E) <|
    hf hx hy (funext fun n ↦ by simpa using h n)

/-- **Šmulian's theorem**: in a real or complex normed space, a weakly compact set is weakly
sequentially compact. Neither completeness nor separability of the space is assumed. -/
theorem isSeqCompact_toWeakSpace_of_isCompact {K : Set E}
    (hK : IsCompact (toWeakSpace 𝕜 E '' K)) : IsSeqCompact (toWeakSpace 𝕜 E '' K) := by
  intro u hu
  choose v hvK hv using hu
  -- The closed span `Y` of the sequence is norm separable and weakly closed.
  set Y : Set E := closure (Submodule.span 𝕜 (range v)) with hY
  have hYsep : IsSeparable Y := (countable_range v).isSeparable.span.closure
  have hYclosed : IsClosed (toWeakSpace 𝕜 E '' Y) := by
    -- The weak and norm closures of a convex set agree; convexity is over `ℝ`.
    let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    have : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
    have hconv : Convex ℝ (Submodule.span 𝕜 (range v) : Set E) :=
      ((Submodule.span 𝕜 (range v)).restrictScalars ℝ).convex
    rw [hY, hconv.toWeakSpace_closure 𝕜]
    exact isClosed_closure
  have hvY (n : ℕ) : v n ∈ Y := subset_closure (Submodule.subset_span (mem_range_self n))
  -- The sequence lies in `K ∩ Y`, which is weakly compact and norm separable, hence weakly
  -- compact metrizable and so weakly sequentially compact.
  have hKY : IsCompact (toWeakSpace 𝕜 E '' (K ∩ Y)) := by
    rw [image_inter (toWeakSpace 𝕜 E).injective]
    exact hK.inter_right hYclosed
  have : CompactSpace (toWeakSpace 𝕜 E '' (K ∩ Y)) := isCompact_iff_compactSpace.mp hKY
  have :=
    metrizableSpace_toWeakSpace_of_isSeparable_of_isCompact (hYsep.mono inter_subset_right) hKY
  obtain ⟨⟨a, ha⟩, φ, hφ, hlim⟩ := SeqCompactSpace.tendsto_subseq
    (fun n ↦ (⟨u n, v n, ⟨hvK n, hvY n⟩, hv n⟩ : toWeakSpace 𝕜 E '' (K ∩ Y)))
  exact ⟨a, image_mono inter_subset_left ha, φ, hφ, (continuous_subtype_val.tendsto _).comp hlim⟩

/-- **Šmulian's theorem**, relative form: every sequence in a relatively weakly compact subset of
a real or complex normed space has a subsequence converging weakly to some point of the space. -/
theorem tendsto_subseq_toWeakSpace_of_isCompact_closure {K : Set E}
    (hK : IsCompact (closure (toWeakSpace 𝕜 E '' K))) {u : ℕ → E} (hu : ∀ n, u n ∈ K) :
    ∃ x : E, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 E (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 E x)) := by
  set L : Set E := (toWeakSpace 𝕜 E).symm '' closure (toWeakSpace 𝕜 E '' K)
  have hL : toWeakSpace 𝕜 E '' L = closure (toWeakSpace 𝕜 E '' K) :=
    (toWeakSpace 𝕜 E).image_symm_image _
  obtain ⟨-, ⟨x, -, rfl⟩, φ, hφ, hlim⟩ := isSeqCompact_toWeakSpace_of_isCompact (hL ▸ hK)
    (x := fun n ↦ toWeakSpace 𝕜 E (u n))
    (fun n ↦ hL ▸ subset_closure (mem_image_of_mem _ (hu n)))
  exact ⟨x, φ, hφ, hlim⟩

end TauCeti
