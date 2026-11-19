/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
public import TauCeti.Analysis.Variational.BoundedSublevels
public import TauCeti.Topology.Semicontinuity.Sequential
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Topology.Order.IsLUB

/-!
# The direct method along weakly convergent sequences

In a reflexive real or complex normed space, a norm-bounded sequence has a weakly convergent
subsequence (`TauCeti.tendsto_subseq_toWeakSpace_of_isBounded`). Hence a bounded minimizing
sequence of an energy, lying in a weakly sequentially closed set on which the energy is weakly
sequentially lower semicontinuous, has a subsequence converging weakly to a minimizer
(`TauCeti.exists_isMinOn_of_bounded_minimizing_sequence`).
Closedness and semicontinuity are only required along sequences. This matters for constraint
sets such as the sphere `{u | ‖j u‖ = 1}` of a compact operator `j`: it is weakly sequentially
closed (`IsCompactOperator.isSeqClosed_toWeakSpace_preimage`), but not weakly closed when `j` is
injective and the space is infinite dimensional (`TauCeti.not_isClosed_toWeakSpace_setOf_norm_eq`).

A sequence `u` is minimizing for `E` on `S` when its energies are eventually below every number
exceeding a value of `E` on `S`. For real energies bounded below on `S` this holds when
`E (u n) → sInf (E '' S)`, and minimizing sequences of points of a nonempty `S` always exist
(`TauCeti.exists_seq_forall_gt_eventually_lt`).

Compared with the direct method in the weak topology (`TauCeti.exists_isMinOn_of_weak_closed`),
the sequential version weakens closedness and semicontinuity to their sequential forms, at the
price of Šmulian's theorem, which extracts weakly convergent subsequences from weakly compact sets.
For a real energy bounded below and a sequence whose energies converge to the infimum, only the
finite-limit form of semicontinuity is needed: the energy at a weak limit of admissible points is
at most every limit of their energies.

## Main results

* `TauCeti.exists_isMinOn_of_bounded_minimizing_sequence`: a bounded minimizing sequence in a
  weakly sequentially closed set has a subsequence converging weakly to a minimizer.
* `TauCeti.exists_isMinOn_of_bounded_tendsto_sInf`: a real energy bounded below attains its
  infimum if a bounded sequence of admissible points has energies converging to the infimum.
* `TauCeti.exists_isMinOn_of_weak_seqClosed`: a weakly sequentially lower semicontinuous real
  energy with bounded sublevels on a nonempty weakly sequentially closed set attains its minimum.

## References

* V. Ivrii, *Partial Differential Equations*, §13.1, proof of Theorem 4, step 1.
* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2.
-/

public section

open Set Filter Topology Bornology NormedSpace

namespace TauCeti

/-- Every real function on a nonempty set admits a minimizing sequence of points of the set: its
values are eventually below every number exceeding a value of the function on the set. -/
theorem exists_seq_forall_gt_eventually_lt {X : Type*} {E : X → ℝ} {S : Set X}
    (hS : S.Nonempty) :
    ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧ ∀ v ∈ S, ∀ c > E v, ∀ᶠ n in atTop, E (u n) < c := by
  by_cases hbdd : BddBelow (E '' S)
  · -- The values converge to the infimum, which lies below every value.
    obtain ⟨w, -, hw, hwS⟩ := exists_seq_tendsto_sInf (hS.image E) hbdd
    choose u hu hEu using hwS
    refine ⟨u, hu, fun v hv c hc ↦ ?_⟩
    simpa only [hEu] using
      hw.eventually (Iio_mem_nhds ((csInf_le hbdd (mem_image_of_mem E hv)).trans_lt hc))
  · -- The values tend to `-∞`.
    have hlt (n : ℕ) : ∃ x ∈ S, E x < -n := by
      obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := not_bddBelow_iff.1 hbdd (-n)
      exact ⟨x, hx, hlt⟩
    choose u hu hEu using hlt
    have hbot : Tendsto (fun n ↦ E (u n)) atTop atBot :=
      tendsto_atBot_mono (fun n ↦ (hEu n).le)
        (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    exact ⟨u, hu, fun _ _ c _ ↦ hbot.eventually_lt_atBot c⟩

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **The direct method along sequences.** In a reflexive space, let `u` be a norm-bounded
sequence in `K` that is minimizing for `E` on `S`: its energies are eventually below every number
exceeding a value of `E` on `S`. If `K` is weakly sequentially closed and `E` is weakly
sequentially lower semicontinuous on `K`, then a subsequence of `u` converges weakly to a point of
`K` minimizing `E` on `S`.

Taking for `K` a bounded sublevel of `E` on `S` containing the sequence, closedness and
semicontinuity are only needed within that sublevel. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence {β : Type*} [LinearOrder β]
    {E : V → β} {S K : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hK : IsSeqClosed (toWeakSpace 𝕜 V '' K))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' K))
    {u : ℕ → V} (hu : ∀ n, u n ∈ K) (hb : IsBounded (range u))
    (hmin : ∀ v ∈ S, ∀ c > E v, ∀ᶠ n in atTop, E (u n) < c) :
    ∃ x ∈ K, IsMinOn E S x ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V x)) := by
  obtain ⟨x, φ, hφ, hlim⟩ := tendsto_subseq_toWeakSpace_of_isBounded hV hb
  have huK (n : ℕ) : toWeakSpace 𝕜 V (u (φ n)) ∈ toWeakSpace 𝕜 V '' K :=
    mem_image_of_mem _ (hu _)
  have hxK : toWeakSpace 𝕜 V x ∈ toWeakSpace 𝕜 V '' K := hK huK hlim
  refine ⟨x, (toWeakSpace 𝕜 V).injective.mem_set_image.1 hxK, isMinOn_iff.2 fun v hv ↦ ?_, φ, hφ,
    hlim⟩
  simpa only [LinearEquiv.symm_apply_apply] using
    hE.le_of_forall_gt_eventually_lt hxK huK hlim (b := E v) fun c hc ↦ by
      simpa only [LinearEquiv.symm_apply_apply] using
        hφ.tendsto_atTop.eventually (hmin v hv c hc)

/-- **The direct method along sequences, for real energies bounded below.** In a reflexive space,
let `E` be a real energy bounded below on a weakly sequentially closed set `S` such that, whenever
points of `S` converge weakly to `x ∈ S` and their energies converge to `r`, `E x ≤ r`. Then `E`
attains its infimum on `S` as soon as some norm-bounded sequence of points of `S` has energies
converging to that infimum. Weak sequential lower semicontinuity gives the hypothesis on `E`
(`TauCeti.SeqLowerSemicontinuousOn.le_of_tendsto`). -/
theorem exists_isMinOn_of_bounded_tendsto_sInf {E : V → ℝ} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : ∀ ⦃x⦄, x ∈ S → ∀ ⦃u : ℕ → V⦄, (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V x)) →
      ∀ ⦃r : ℝ⦄, Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E x ≤ r)
    (hbdd : BddBelow (E '' S)) {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hlim : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ x ∈ S, IsMinOn E S x := by
  obtain ⟨x, φ, hφ, hx⟩ := tendsto_subseq_toWeakSpace_of_isBounded hV hb
  have hxS : x ∈ S := (toWeakSpace 𝕜 V).injective.mem_set_image.1 <|
    hS (fun n ↦ mem_image_of_mem _ (hu (φ n))) hx
  exact ⟨x, hxS, isMinOn_iff.2 fun v hv ↦ (hE hxS (fun n ↦ hu (φ n)) hx
    (hlim.comp hφ.tendsto_atTop)).trans (csInf_le hbdd (mem_image_of_mem E hv))⟩

/-- **The direct method along sequences, with bounded sublevels.** In a reflexive space, a real
energy that is weakly sequentially lower semicontinuous on a nonempty weakly sequentially closed
set, with norm-bounded sublevels there, attains its minimum. No lower bound on the energy is
assumed. -/
theorem exists_isMinOn_of_weak_seqClosed {E : V → ℝ} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ x ∈ S, IsMinOn E S x := by
  obtain ⟨v, hv⟩ := hne
  obtain ⟨u, hu, hmin⟩ := exists_seq_forall_gt_eventually_lt (E := E) ⟨v, hv⟩
  -- A tail of the minimizing sequence lies in the bounded sublevel at `E v + 1`.
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hmin v hv (E v + 1) (lt_add_one _))
  have hbN : IsBounded (range fun n ↦ u (n + N)) :=
    (hb.isBounded_sublevel (E v + 1)).subset <| range_subset_iff.2 fun n ↦
      ⟨hu _, (hN _ (Nat.le_add_left N n)).le⟩
  obtain ⟨x, hx, hxmin, -⟩ := exists_isMinOn_of_bounded_minimizing_sequence hV hS hE
    (fun n ↦ hu (n + N)) hbN fun w hw c hc ↦ (tendsto_add_atTop_nat N).eventually (hmin w hw c hc)
  exact ⟨x, hx, hxmin⟩

end TauCeti
