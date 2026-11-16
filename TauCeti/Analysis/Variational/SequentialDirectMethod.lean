/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Filter.Extr
public import TauCeti.Topology.Semicontinuity.Sequential
public import TauCeti.Analysis.Variational.BoundedSublevels
public import TauCeti.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The sequential direct method and weak sequential lower semicontinuity

In a real or complex reflexive normed space, an energy attains its infimum on a sequentially
weakly closed admissible set whenever it is sequentially weakly lower semicontinuous and admits
a norm-bounded minimizing sequence. Unlike the purely topological direct method, this applies to
admissible sets that are sequentially weakly closed without being weakly closed, such as spheres
constrained by a compact operator.

Two formulations are proved:

* **Bounded minimizing sequence.** Given a lower bound on the energy, sequential weak closedness,
  the finite-limit sequential weak lower semicontinuity inequality, and a norm-bounded minimizing
  sequence, Eberlein–Šmulian extracts a weakly convergent subsequence whose limit minimizes the
  energy and attains `sInf (E '' S)`. A localized variant requires closedness and semicontinuity
  only inside a single sublevel containing the sequence. If the minimizer is unique, the entire
  bounded minimizing sequence converges weakly to it.
* **Bounded sublevels.** For an energy valued in an arbitrary linear order with
  `HasBoundedSublevelsOn` (or a single nonempty bounded sublevel), no a priori lower bound is
  needed: the bounded sublevel is weakly compact by the sequential-closure form of
  Eberlein–Šmulian, on which sequential and topological weak lower semicontinuity coincide.
  The set of all minimizers is weakly compact.

Reflexivity means surjectivity of the continuous bidual inclusion
`NormedSpace.inclusionInDoubleDual`, and completeness is not assumed separately.

## Main declarations

* `TauCeti.lowerSemicontinuousOn_toWeakSpace_iff_seqLowerSemicontinuousOn`: on a relatively
  weakly compact set, topological and sequential weak lower semicontinuity coincide.
* `TauCeti.exists_minimizing_seq`: constructs an admissible minimizing sequence with
  `E (u n) < sInf (E '' S) + 1 / (n + 1)`.
* `TauCeti.exists_subseq_tendsto_toWeakSpace_isMinOn`: subsequential weak convergence of a
  bounded minimizing sequence to a minimizer.
* `TauCeti.exists_isMinOn_of_bounded_minimizing_sequence`: the sequential direct method from a
  bounded minimizing sequence.
* `TauCeti.tendsto_toWeakSpace_of_unique_isMinOn`: full weak convergence of bounded minimizing
  sequences when the minimizer is unique.
* `TauCeti.exists_isMinOn_of_isSeqClosed`: the sequential direct method from bounded sublevels.
* `TauCeti.isCompact_toWeakSpace_minimizers_of_isSeqClosed`: weak compactness of the minimizer
  set under sequential hypotheses.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2 (the direct method).
* V. Ivrii, *Partial Differential Equations*, §13.1, proof of Theorem 4.
-/

public section

open Bornology Filter Function NormedSpace Set Topology

namespace TauCeti

/-! ### Weak sequential closedness and weak sequential lower semicontinuity -/

section WeakSequential

variable {𝕜 V : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V]

/-- Sequential closedness of `toWeakSpace 𝕜 V '' S` unpacked as a statement about weakly
convergent sequences in `V`. -/
theorem isSeqClosed_toWeakSpace_iff {S : Set V} :
    IsSeqClosed (toWeakSpace 𝕜 V '' S) ↔
      ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S := by
  constructor
  · intro hS u v hu hlim
    have hv := hS (fun n ↦ mem_image_of_mem (toWeakSpace 𝕜 V) (hu n)) hlim
    rwa [(toWeakSpace 𝕜 V).injective.mem_set_image] at hv
  · intro hS u w hu hlim
    have hu' : ∀ n, (toWeakSpace 𝕜 V).symm (u n) ∈ S := fun n ↦ by
      simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using hu n
    have hlim' : Tendsto (fun n ↦ toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm (u n))) atTop
        (𝓝 (toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm w))) := by
      simpa only [LinearEquiv.apply_symm_apply] using hlim
    have hw : (toWeakSpace 𝕜 V).symm w ∈ S := hS _ _ hu' hlim'
    simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using hw

/-- Sequential weak lower semicontinuity of `E` on `S` unpacked in terms of weakly convergent
sequences in `V`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff {β : Type*} [LT β] {E : V → β} {S : Set V} :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S) → v ∈ S →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        ∀ b < E v, ∀ᶠ n in atTop, b < E (u n) := by
  rw [seqLowerSemicontinuousOn_iff]
  constructor
  · intro hE u v hu hv hlim b hb
    have h := hE (toWeakSpace 𝕜 V v) (mem_image_of_mem _ hv)
      (fun n ↦ toWeakSpace 𝕜 V (u n)) (fun n ↦ mem_image_of_mem _ (hu n)) hlim b
      (by simpa only [LinearEquiv.symm_apply_apply] using hb)
    simpa only [LinearEquiv.symm_apply_apply] using h
  · intro hE w hw u hu hlim b hb
    have hu' : ∀ n, (toWeakSpace 𝕜 V).symm (u n) ∈ S := fun n ↦ by
      simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using hu n
    have hw' : (toWeakSpace 𝕜 V).symm w ∈ S := by
      simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using hw
    have hlim' : Tendsto (fun n ↦ toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm (u n))) atTop
        (𝓝 (toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm w))) := by
      simpa only [LinearEquiv.apply_symm_apply] using hlim
    exact hE _ _ hu' hw' hlim' b hb

/-- Sequential weak lower semicontinuity of a real-valued energy on `S`, expressed via the
`EReal` lower limit along weakly convergent sequences in `S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_le_liminf_ereal {E : V → ℝ} {S : Set V} :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S) → v ∈ S →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuousOn_coe_ereal_iff,
    seqLowerSemicontinuousOn_toWeakSpace_iff (E := fun x ↦ (E x : EReal))]
  refine forall₂_congr fun u v ↦ imp_congr_right fun _ ↦ imp_congr_right fun _ ↦
    imp_congr_right fun _ ↦ ?_
  exact (le_liminf_iff (u := fun n ↦ (E (u n) : EReal)) (f := atTop)).symm

/-- For a real-valued energy bounded below on `S`, sequential weak lower semicontinuity on `S`
is equivalent to the finite-limit inequality `E v ≤ r` whenever `u n ⇀ v` in `S` and
`E (u n) → r`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_forall_le_of_tendsto {E : V → ℝ} {S : Set V}
    (hb : BddBelow (E '' S)) :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ (u : ℕ → V) (v : V) (r : ℝ), (∀ n, u n ∈ S) → v ∈ S →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        Tendsto (E ∘ u) atTop (𝓝 r) → E v ≤ r := by
  have hb' : BddBelow ((fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ''
      (toWeakSpace 𝕜 V '' S)) := by
    simpa only [image_image, LinearEquiv.symm_apply_apply] using hb
  rw [seqLowerSemicontinuousOn_iff_forall_le_of_tendsto hb']
  constructor
  · intro hE u v r hu hv hlim hEr
    have h := hE (fun n ↦ toWeakSpace 𝕜 V (u n)) (toWeakSpace 𝕜 V v) r
      (fun n ↦ mem_image_of_mem _ (hu n)) (mem_image_of_mem _ hv) hlim
      (by simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using hEr)
    simpa only [LinearEquiv.symm_apply_apply] using h
  · intro hE u w r hu hw hlim hEr
    have hu' : ∀ n, (toWeakSpace 𝕜 V).symm (u n) ∈ S := fun n ↦ by
      simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using hu n
    have hw' : (toWeakSpace 𝕜 V).symm w ∈ S := by
      simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using hw
    have hlim' : Tendsto (fun n ↦ toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm (u n))) atTop
        (𝓝 (toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm w))) := by
      simpa only [LinearEquiv.apply_symm_apply] using hlim
    exact hE _ _ r hu' hw' hlim' hEr

end WeakSequential

section WeakCompactEquiv

variable {𝕜 V β : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [LinearOrder β]
  {E : V → β} {K : Set V}

/-- On a relatively weakly compact subset of a real or complex normed space, topological and
sequential weak lower semicontinuity coincide. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_seqLowerSemicontinuousOn
    (hK : IsCompact (closure (toWeakSpace 𝕜 V '' K))) :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' K) ↔
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' K) := by
  have : FrechetUrysohnSpace (toWeakSpace 𝕜 V '' K) :=
    frechetUrysohnSpace_of_isCompact_closure_weakSpace hK
  exact lowerSemicontinuousOn_iff_seqLowerSemicontinuousOn

/-- On a weakly compact subset of a real or complex normed space, topological and sequential
weak lower semicontinuity coincide. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_seqLowerSemicontinuousOn_of_isCompact
    (hK : IsCompact (toWeakSpace 𝕜 V '' K)) :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' K) ↔
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' K) :=
  lowerSemicontinuousOn_toWeakSpace_iff_seqLowerSemicontinuousOn
    (hK.isClosed.closure_eq.symm ▸ hK)

end WeakCompactEquiv

/-! ### Minimizing sequences -/

/-- Any real-valued energy bounded below on a nonempty set `S` admits a minimizing sequence
`u : ℕ → X` in `S` with `E (u n) < sInf (E '' S) + 1 / (n + 1)` and
`E (u n) → sInf (E '' S)`. -/
theorem exists_minimizing_seq {X : Type*} {E : X → ℝ} {S : Set X}
    (hne : S.Nonempty) (hb : BddBelow (E '' S)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧
      (∀ n, E (u n) < sInf (E '' S) + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (E ∘ u) atTop (𝓝 (sInf (E '' S))) := by
  have hchoose (n : ℕ) : ∃ x ∈ S, E x < sInf (E '' S) + 1 / ((n : ℝ) + 1) := by
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hne.image E)
      (lt_add_of_pos_right (sInf (E '' S)) (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
    exact ⟨x, hx, hlt⟩
  choose u hu hlt using hchoose
  refine ⟨u, hu, hlt, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_add (sInf (E '' S)))
    (fun n ↦ csInf_le hb (mem_image_of_mem E (hu n)))
    (fun n ↦ (hlt n).le)⟩

/-! ### The sequential direct method from a bounded minimizing sequence -/

section BoundedMinimizingSeq

variable {𝕜 V β : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [ConditionallyCompleteLattice β] [TopologicalSpace β] {E : V → β} {S : Set V}

/-- Sublevel-localized subsequential weak convergence of a bounded minimizing sequence:
if a norm-bounded minimizing sequence lies in a sublevel `{x ∈ S | E x ≤ b}` on which
sequential weak closedness and the finite-limit sequential weak lower semicontinuity inequality
hold, then a subsequence converges weakly to a minimizer of `E` on `S`. -/
theorem exists_subseq_tendsto_toWeakSpace_isMinOn_sublevel
    (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S)) (b : β)
    (hseqclosed : ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S ∧ E (u n) ≤ b) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      v ∈ S ∧ E v ≤ b)
    (hseqlsc : ∀ (u : ℕ → V) (v : V) (r : β), (∀ n, u n ∈ S ∧ E (u n) ≤ b) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S ∧ E (u n) ≤ b) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (σ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
  obtain ⟨v, σ, hσ, hlim⟩ := tendsto_subseq_toWeakSpace_of_isCompact_closure
    (isCompact_closure_toWeakSpace_of_isBounded hV hb) (fun n ↦ mem_range_self n)
  have hv : v ∈ S ∧ E v ≤ b := hseqclosed (u ∘ σ) v (fun n ↦ hu (σ n)) hlim
  have hle : E v ≤ sInf (E '' S) :=
    hseqlsc (u ∘ σ) v (sInf (E '' S)) (fun n ↦ hu (σ n)) hlim (hminseq.comp hσ.tendsto_atTop)
  refine ⟨v, hv.1, fun x hx ↦ hle.trans (csInf_le hbelow (mem_image_of_mem E hx)), σ, hσ, hlim⟩

/-- Sublevel-localized sequential direct method: sequential weak closedness and finite-limit
sequential weak lower semicontinuity are needed only on a single sublevel containing the
bounded minimizing sequence. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence_sublevel
    (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S)) (b : β)
    (hseqclosed : ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S ∧ E (u n) ≤ b) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      v ∈ S ∧ E v ≤ b)
    (hseqlsc : ∀ (u : ℕ → V) (v : V) (r : β), (∀ n, u n ∈ S ∧ E (u n) ≤ b) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S ∧ E (u n) ≤ b) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v :=
  let ⟨v, hv, hmin, _⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn_sublevel hV hbelow b hseqclosed hseqlsc hu hb hminseq
  ⟨v, hv, hmin⟩

/-- Every norm-bounded minimizing sequence in a sequentially weakly closed subset of a reflexive
normed space has a subsequence converging weakly to a minimizer of `E` on `S`. -/
theorem exists_subseq_tendsto_toWeakSpace_isMinOn
    (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hseqlsc : ∀ (u : ℕ → V) (v : V) (r : β), (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (σ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
  obtain ⟨v, σ, hσ, hlim⟩ := tendsto_subseq_toWeakSpace_of_isCompact_closure
    (isCompact_closure_toWeakSpace_of_isBounded hV hb) (fun n ↦ mem_range_self n)
  have hv : v ∈ S := hseqclosed (u ∘ σ) v (fun n ↦ hu (σ n)) hlim
  have hle : E v ≤ sInf (E '' S) :=
    hseqlsc (u ∘ σ) v (sInf (E '' S)) (fun n ↦ hu (σ n)) hlim (hminseq.comp hσ.tendsto_atTop)
  refine ⟨v, hv, fun x hx ↦ hle.trans (csInf_le hbelow (mem_image_of_mem E hx)), σ, hσ, hlim⟩

/-- **The sequential direct method.** On a reflexive normed space, an energy bounded below on a
sequentially weakly closed set and satisfying the finite-limit sequential weak lower
semicontinuity inequality attains its infimum as soon as a norm-bounded minimizing sequence
exists. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence
    (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hseqlsc : ∀ (u : ℕ → V) (v : V) (r : β), (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v :=
  let ⟨v, hv, hmin, _⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn hV hbelow hseqclosed hseqlsc hu hb hminseq
  ⟨v, hv, hmin⟩

/-- When the minimizer `v₀` on `S` is unique, every norm-bounded minimizing sequence converges
weakly to `v₀`. -/
theorem tendsto_toWeakSpace_of_unique_isMinOn
    (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hseqlsc : ∀ (u : ℕ → V) (v : V) (r : β), (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r)
    {v₀ : V} (huniq : ∀ v ∈ S, IsMinOn E S v → v = v₀)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v₀)) := by
  by_contra hnot
  obtain ⟨U, hU, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.mp hnot
  obtain ⟨φ, hφ_mono, hφ_not⟩ := extraction_of_frequently_atTop hfreq
  have hsub_bdd : IsBounded (range (u ∘ φ)) := hb.subset (range_comp_subset_range φ u)
  obtain ⟨v, hv, hmin, σ, _, hlim⟩ := exists_subseq_tendsto_toWeakSpace_isMinOn hV hbelow
    hseqclosed hseqlsc (fun n ↦ hu (φ n)) hsub_bdd (hminseq.comp hφ_mono.tendsto_atTop)
  rw [huniq v hv hmin] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually hU).exists
  exact hφ_not (σ n) hn

end BoundedMinimizingSeq

/-! ### The sequential direct method from bounded sublevels -/

section BoundedSublevels

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}

/-- On a sequentially weakly closed set in a reflexive normed space, a norm-bounded sublevel of
a sequentially weakly lower semicontinuous energy is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel_of_isSeqClosed
    (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  have heq : toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} =
      {w ∈ toWeakSpace 𝕜 V '' S | E ((toWeakSpace 𝕜 V).symm w) ≤ b} := by
    ext w
    simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage, mem_ofPred_eq]
  have hseq : IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
    rw [heq]
    exact hE.isSeqClosed_sublevel hS b
  exact isCompact_toWeakSpace_of_isSeqClosed_of_isCompact_closure hseq
    (isCompact_closure_toWeakSpace_of_isBounded hV hb)

/-- Sublevel-localized sequential direct method without a lower bound: if a single nonempty
bounded sublevel `{u ∈ S | E u ≤ b}` is sequentially weakly closed and `E` is sequentially
weakly lower semicontinuous on it, then `E` attains its minimum on `S`. -/
theorem exists_isMinOn_of_isSeqClosed_sublevel
    (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b})
    (hclosed : IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b})) :
    ∃ u ∈ S, IsMinOn E S u := by
  have hcompact : IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    isCompact_toWeakSpace_of_isSeqClosed_of_isCompact_closure hclosed
      (isCompact_closure_toWeakSpace_of_isBounded hV hb)
  have hlsc :=
    (lowerSemicontinuousOn_toWeakSpace_iff_seqLowerSemicontinuousOn_of_isCompact hcompact).mpr hE
  obtain ⟨w, hw, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn (hne.image _) hcompact hlsc
  obtain ⟨u, hu, rfl⟩ := hw
  refine ⟨u, hu.1, (isMinOn_sublevel_iff hu.2).1 fun x hx ↦ ?_⟩
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    hmin (mem_image_of_mem (toWeakSpace 𝕜 V) hx)

/-- A single nonempty bounded sublevel suffices for the sequential direct method on a
sequentially weakly closed admissible set. -/
theorem exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel
    (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u := by
  have hcompact := isCompact_toWeakSpace_sublevel_of_isSeqClosed hV hS hE b hb
  exact exists_isMinOn_of_isSeqClosed_sublevel hV hne hb hcompact.isClosed.isSeqClosed
    (hE.mono (image_mono fun _ hx ↦ hx.1))

/-- **The sequential direct method (bounded-sublevels form).** A sequentially weakly lower
semicontinuous energy with bounded sublevels on a nonempty sequentially weakly closed set in a
reflexive normed space attains its minimum. No a priori lower bound on `E` is assumed. -/
theorem exists_isMinOn_of_isSeqClosed
    (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨v, hv⟩ := hne
  exact exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel hV hS hE
    ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v))

/-- If the minimizer set of a sequentially weakly lower semicontinuous energy on a sequentially
weakly closed set in a reflexive normed space is bounded, then that minimizer set is weakly
compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded
    (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : IsBounded {u ∈ S | IsMinOn E S u}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) := by
  obtain hempty | ⟨u, hu, hmin⟩ := {u ∈ S | IsMinOn E S u}.eq_empty_or_nonempty
  · simp [hempty]
  · rw [hmin.minimizers_eq_sublevel hu] at hb ⊢
    exact isCompact_toWeakSpace_sublevel_of_isSeqClosed hV hS hE (E u) hb

/-- For a sequentially weakly lower semicontinuous energy with bounded sublevels on a
sequentially weakly closed set in a reflexive normed space, the set of minimizers is weakly
compact, including when the admissible set is empty. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed
    (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded hV hS hE hb.isBounded_minimizers

end BoundedSublevels

/-- Under bounded sublevels, every minimizing sequence in a sequentially weakly closed set in a
reflexive normed space is norm-bounded and admits a subsequence converging weakly to a
minimizer, without assuming an a priori lower bound on `E`. -/
theorem exists_subseq_tendsto_toWeakSpace_isMinOn_of_hasBoundedSublevelsOn
    {𝕜 V β : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {E : V → β} {S : Set V}
    (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S)
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (σ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
  obtain ⟨w, _, hminw⟩ := exists_isMinOn_of_isSeqClosed hV ⟨u 0, hu 0⟩ hS hE hb
  exact exists_subseq_tendsto_toWeakSpace_isMinOn hV hminw.bddBelow
    (isSeqClosed_toWeakSpace_iff.mp hS)
    (fun v x r hv hlim hEr ↦
      hE.le_of_tendsto (fun n ↦ mem_image_of_mem _ (hv n))
        (hS (fun n ↦ mem_image_of_mem _ (hv n)) hlim) hlim
        (by simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using hEr))
    hu (hb.isBounded_range hu hminseq.bddAbove_range) hminseq

end TauCeti
