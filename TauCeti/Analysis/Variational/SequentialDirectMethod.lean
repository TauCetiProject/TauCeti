/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Variational.BoundedSublevels
public import TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian
public import TauCeti.Topology.Semicontinuity.Sequential
import TauCeti.Order.Filter.Extr
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# The sequential direct method in the weak topology

In any topological module over a topological commutative semiring, sequential weak lower
semicontinuity of `E : V → β` unfolds directly to weakly convergent sequences in `V`
(`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff`) and, into a linear order on a sequentially
weakly closed set `S`, is equivalent to sequential weak closedness of all relative sublevels
(`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel`).

In a real or complex seminormed space, every relatively weakly compact set is Fréchet–Urysohn in the
subspace weak topology (`TauCeti.frechetUrysohnSpace_toWeakSpace_of_isCompact_closure`), so
sequential weak lower semicontinuity and topological weak lower semicontinuity coincide on
relatively weakly compact sets — and, when the continuous bidual inclusion is surjective, on all
norm-bounded sets
(`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isBounded`).

Consequently, in a reflexive seminormed space over `ℝ` or `ℂ`, the direct method holds under purely
sequential weak hypotheses without assuming the admissible set `S` is topologically weakly closed:

* `TauCeti.isCompact_toWeakSpace_sublevel_of_isSeqClosed` and
  `TauCeti.exists_isMinOn_of_isSeqClosed`: without assuming the energy is bounded below, on a
  sequentially weakly closed set every norm-bounded sublevel of a sequentially weakly lower
  semicontinuous energy into a linear order is weakly compact, an energy with bounded sublevels on
  a nonempty sequentially weakly closed set attains its minimum, and its minimizer set is weakly
  compact (`TauCeti.isCompact_toWeakSpace_minimizers_of_isSeqClosed`).
* `TauCeti.exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence` and
  `TauCeti.exists_isMinOn_of_bounded_minimizing_sequence`: when `E '' S` is bounded below in a
  conditionally complete lattice equipped with a topology and a norm-bounded minimizing sequence in
  a sequentially weakly closed set `S` exists, the sequence has a weakly convergent subsequence
  whose limit is an admissible minimizer; when at most one admissible minimizer exists, the entire
  minimizing sequence converges weakly to it
  (`TauCeti.tendsto_toWeakSpace_of_unique_isMinOn_of_bounded_minimizing_sequence`).

Neither completeness of `V` nor point-separation of the seminorm is assumed.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2 (the direct method).
* V. Ivrii, *Partial Differential Equations*, §13.1, Theorem 4.
* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.8, Theorem 2.8.14.
-/

public section

open Bornology Filter NormedSpace Set Topology

namespace TauCeti

section WeakSemicontinuity

variable {𝕜 V : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V]

/-- Sequential weak lower semicontinuity of `E` on `S` is equivalent to persistence of strict lower
bounds along sequences in `S` converging weakly to a point of `S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff {β : Type*} [Preorder β]
    {E : V → β} {S : Set V} :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' S) ↔
      ∀ v ∈ S, ∀ b < E v, ∀ ⦃u : ℕ → V⦄, (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        ∀ᶠ n in atTop, b < E (u n) := by
  rw [seqLowerSemicontinuousOn_iff]
  refine ⟨fun h v hv b hb u hu hlim ↦ ?_, fun h w hw b hb u' hu' hlim ↦ ?_⟩
  · simpa only [LinearEquiv.symm_apply_apply] using
      h (toWeakSpace 𝕜 V v) (mem_image_of_mem _ hv) b
        (by simpa only [LinearEquiv.symm_apply_apply] using hb)
        (fun n ↦ mem_image_of_mem _ (hu n)) hlim
  · obtain ⟨v, hv, rfl⟩ := hw
    choose u hu huu' using hu'
    simpa only [← huu', LinearEquiv.symm_apply_apply] using
      h v hv b (by simpa only [LinearEquiv.symm_apply_apply] using hb) hu
        (by simpa only [huu'] using hlim)

/-- Global sequential weak lower semicontinuity of `E` is equivalent to persistence of strict lower
bounds along weakly convergent sequences in `V`. -/
theorem seqLowerSemicontinuous_toWeakSpace_iff {β : Type*} [Preorder β] {E : V → β} :
    SeqLowerSemicontinuous (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ↔
      ∀ v : V, ∀ b < E v, ∀ ⦃u : ℕ → V⦄,
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        ∀ᶠ n in atTop, b < E (u n) := by
  have huniv : toWeakSpace 𝕜 V '' (univ : Set V) = univ := by
    rw [image_univ, (toWeakSpace 𝕜 V).surjective.range_eq]
  simpa only [← seqLowerSemicontinuousOn_univ_iff, ← huniv, mem_univ, forall_const,
    true_implies] using
    seqLowerSemicontinuousOn_toWeakSpace_iff (𝕜 := 𝕜) (V := V) (E := E) (S := univ)

/-- If `E` is sequentially weakly lower semicontinuous on `S`, `v ∈ S`, `b < E v`, and `u n ∈ S`
converges weakly to `v`, then eventually `b < E (u n)`. -/
theorem SeqLowerSemicontinuousOn.eventually_lt_toWeakSpace {β : Type*} [Preorder β]
    {E : V → β} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {v : V} (hv : v ∈ S) {b : β} (hb : b < E v) {u : ℕ → V} (hu : ∀ n, u n ∈ S)
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v))) :
    ∀ᶠ n in atTop, b < E (u n) :=
  seqLowerSemicontinuousOn_toWeakSpace_iff.1 hE v hv b hb hu huv

/-- Global form of `TauCeti.SeqLowerSemicontinuousOn.eventually_lt_toWeakSpace`. -/
theorem SeqLowerSemicontinuous.eventually_lt_toWeakSpace {β : Type*} [Preorder β]
    {E : V → β}
    (hE : SeqLowerSemicontinuous (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)))
    {v : V} {b : β} (hb : b < E v) {u : ℕ → V}
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v))) :
    ∀ᶠ n in atTop, b < E (u n) :=
  seqLowerSemicontinuous_toWeakSpace_iff.1 hE v b hb huv

/-- Into a complete linear order, sequential weak lower semicontinuity of `E` on `S` is equivalent
to `E v ≤ liminf (E ∘ u) atTop` along sequences in `S` converging weakly to `v ∈ S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_le_liminf
    {β : Type*} [CompleteLinearOrder β] {E : V → β} {S : Set V} :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' S) ↔
      ∀ v ∈ S, ∀ ⦃u : ℕ → V⦄, (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        E v ≤ liminf (fun n ↦ E (u n)) atTop := by
  rw [seqLowerSemicontinuousOn_toWeakSpace_iff]
  refine ⟨fun h v hv u hu hlim ↦ ?_, fun h v hv b hb u hu hlim ↦ ?_⟩
  · rw [le_liminf_iff]
    exact fun b hb ↦ h v hv b hb hu hlim
  · exact eventually_lt_of_lt_liminf (hb.trans_le (h v hv hu hlim))

/-- Along any sequence in `S` converging weakly to `v ∈ S`, a sequentially weakly lower
semicontinuous function into a complete linear order satisfies `E v ≤ liminf (E ∘ u) atTop`. -/
theorem SeqLowerSemicontinuousOn.le_liminf_toWeakSpace
    {β : Type*} [CompleteLinearOrder β] {E : V → β} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {v : V} (hv : v ∈ S) {u : ℕ → V} (hu : ∀ n, u n ∈ S)
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v))) :
    E v ≤ liminf (fun n ↦ E (u n)) atTop :=
  seqLowerSemicontinuousOn_toWeakSpace_iff_le_liminf.1 hE v hv hu huv

/-- Into a complete linear order, global sequential weak lower semicontinuity of `E` is equivalent
to `E v ≤ liminf (E ∘ u) atTop` along weakly convergent sequences in `V`. -/
theorem seqLowerSemicontinuous_toWeakSpace_iff_le_liminf
    {β : Type*} [CompleteLinearOrder β] {E : V → β} :
    SeqLowerSemicontinuous (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ↔
      ∀ v : V, ∀ ⦃u : ℕ → V⦄,
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        E v ≤ liminf (fun n ↦ E (u n)) atTop := by
  rw [seqLowerSemicontinuous_toWeakSpace_iff]
  refine ⟨fun h v u hlim ↦ ?_, fun h v b hb u hlim ↦ ?_⟩
  · rw [le_liminf_iff]
    exact fun b hb ↦ h v b hb hlim
  · exact eventually_lt_of_lt_liminf (hb.trans_le (h v hlim))

/-- Global form of `TauCeti.SeqLowerSemicontinuousOn.le_liminf_toWeakSpace`. -/
theorem SeqLowerSemicontinuous.le_liminf_toWeakSpace
    {β : Type*} [CompleteLinearOrder β] {E : V → β}
    (hE : SeqLowerSemicontinuous (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)))
    {v : V} {u : ℕ → V}
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v))) :
    E v ≤ liminf (fun n ↦ E (u n)) atTop :=
  seqLowerSemicontinuous_toWeakSpace_iff_le_liminf.1 hE v huv

/-- A real-valued energy `E` is sequentially weakly lower semicontinuous on `S` if and only if
`(E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop` along sequences in `S` converging weakly
to `v ∈ S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_real_iff_le_liminf_ereal
    {E : V → ℝ} {S : Set V} :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' S) ↔
      ∀ v ∈ S, ∀ ⦃u : ℕ → V⦄, (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop :=
  seqLowerSemicontinuousOn_coe_ereal_iff.symm.trans
    (seqLowerSemicontinuousOn_toWeakSpace_iff_le_liminf (E := fun u ↦ (E u : EReal)))

/-- Along any sequence in `S` converging weakly to `v ∈ S`, a sequentially weakly lower
semicontinuous real-valued energy satisfies
`(E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop`. -/
theorem SeqLowerSemicontinuousOn.le_liminf_ereal_toWeakSpace
    {E : V → ℝ} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {v : V} (hv : v ∈ S) {u : ℕ → V} (hu : ∀ n, u n ∈ S)
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v))) :
    (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop :=
  seqLowerSemicontinuousOn_toWeakSpace_real_iff_le_liminf_ereal.1 hE v hv hu huv

/-- A real-valued energy `E` is globally sequentially weakly lower semicontinuous if and only if
`(E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop` along weakly convergent sequences in
`V`. -/
theorem seqLowerSemicontinuous_toWeakSpace_real_iff_le_liminf_ereal {E : V → ℝ} :
    SeqLowerSemicontinuous (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ↔
      ∀ v : V, ∀ ⦃u : ℕ → V⦄,
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop :=
  seqLowerSemicontinuous_coe_ereal_iff.symm.trans
    (seqLowerSemicontinuous_toWeakSpace_iff_le_liminf (E := fun u ↦ (E u : EReal)))

/-- Global form of `TauCeti.SeqLowerSemicontinuousOn.le_liminf_ereal_toWeakSpace`. -/
theorem SeqLowerSemicontinuous.le_liminf_ereal_toWeakSpace {E : V → ℝ}
    (hE : SeqLowerSemicontinuous (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)))
    {v : V} {u : ℕ → V}
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v))) :
    (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop :=
  seqLowerSemicontinuous_toWeakSpace_real_iff_le_liminf_ereal.1 hE v huv

/-- If `E` is sequentially weakly lower semicontinuous on `S`, `u n ∈ S` converges weakly to
`v ∈ S`, and `E (u n)` converges to `r` in a linear order with `ClosedIciTopology`, then
`E v ≤ r`. -/
theorem SeqLowerSemicontinuousOn.le_of_tendsto_toWeakSpace
    {β : Type*} [LinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {E : V → β} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {v : V} (hv : v ∈ S) {u : ℕ → V} (hu : ∀ n, u n ∈ S)
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)))
    {r : β} (hEu : Tendsto (fun n ↦ E (u n)) atTop (𝓝 r)) :
    E v ≤ r := by
  simpa only [LinearEquiv.symm_apply_apply] using
    hE.le_of_tendsto (mem_image_of_mem _ hv) (fun n ↦ mem_image_of_mem _ (hu n)) huv
      (by simpa only [LinearEquiv.symm_apply_apply] using hEu)

/-- Global form of `TauCeti.SeqLowerSemicontinuousOn.le_of_tendsto_toWeakSpace`. -/
theorem SeqLowerSemicontinuous.le_of_tendsto_toWeakSpace
    {β : Type*} [LinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {E : V → β}
    (hE : SeqLowerSemicontinuous (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)))
    {v : V} {u : ℕ → V}
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)))
    {r : β} (hEu : Tendsto (fun n ↦ E (u n)) atTop (𝓝 r)) :
    E v ≤ r :=
  (hE.seqLowerSemicontinuousOn _).le_of_tendsto_toWeakSpace (mem_univ v) (fun _ ↦ mem_univ _)
    huv hEu

/-- On a sequentially weakly closed set `S`, sequential weak lower semicontinuity into a linear
order is equivalent to sequential weak closedness of every relative sublevel
`{u ∈ S | E u ≤ b}`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel
    {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S)) :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' S) ↔
      ∀ b, IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  have heq (b : β) : toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} =
      {w ∈ toWeakSpace 𝕜 V '' S | E ((toWeakSpace 𝕜 V).symm w) ≤ b} := by
    ext w
    simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage, mem_ofPred_eq]
  simp_rw [seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel hS, heq]

/-- Relative sublevels `{u ∈ S | E u ≤ b}` of a sequentially weakly lower semicontinuous function
into a linear order on a sequentially weakly closed set `S` are sequentially weakly closed. -/
theorem isSeqClosed_toWeakSpace_sublevel
    {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) :
    IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
  (seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel hS).1 hE b

end WeakSemicontinuity

section SemicontinuityEquivalence

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  {β : Type*} [Preorder β] {E : V → β} {K : Set V}

/-- On a relatively weakly compact set in a real or complex seminormed space, sequential weak lower
semicontinuity and topological weak lower semicontinuity coincide. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact_closure
    (hK : IsCompact (closure (toWeakSpace 𝕜 V '' K))) :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' K) ↔
      LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' K) := by
  have := frechetUrysohnSpace_toWeakSpace_of_isCompact_closure hK
  exact seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn

/-- On a weakly compact set in a real or complex seminormed space, sequential weak lower
semicontinuity and topological weak lower semicontinuity coincide. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact
    (hK : IsCompact (toWeakSpace 𝕜 V '' K)) :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' K) ↔
      LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' K) :=
  seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact_closure hK.closure

/-- In a reflexive seminormed space over `ℝ` or `ℂ`, sequential weak lower semicontinuity and
topological weak lower semicontinuity coincide on every norm-bounded set. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isBounded
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V)) (hK : IsBounded K) :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' K) ↔
      LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' K) :=
  seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact_closure
    (isCompact_closure_toWeakSpace hV hK)

end SemicontinuityEquivalence

section LinearOrder

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}

/-- On a sequentially weakly closed set in a reflexive seminormed space over `ℝ` or `ℂ`, a
norm-bounded sublevel of a sequentially weakly lower semicontinuous energy is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  have hclosed : IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (isClosed_toWeakSpace_iff_isSeqClosed_of_isBounded hV hb).2
      (isSeqClosed_toWeakSpace_sublevel hS hE b)
  simpa only [hclosed.closure_eq] using isCompact_closure_toWeakSpace hV hb

/-- **Local sublevel sequential direct method.** In a reflexive seminormed space over `ℝ` or `ℂ`,
if a single nonempty norm-bounded sublevel `{u ∈ S | E u ≤ b}` is sequentially weakly closed and `E`
is sequentially weakly lower semicontinuous on that sublevel alone, then `E` attains its minimum on
all of `S`. -/
theorem exists_isMinOn_of_isSeqClosed_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    {b : β} (hsub : IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}))
    (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u := by
  have hclosed : IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (isClosed_toWeakSpace_iff_isSeqClosed_of_isBounded hV hb).2 hsub
  have hcompact : IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
    simpa only [hclosed.closure_eq] using isCompact_closure_toWeakSpace hV hb
  have hEL : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact hcompact).1 hE
  obtain ⟨_, ⟨u, hu, rfl⟩, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn (hne.image _) hcompact hEL
  refine ⟨u, hu.1, (isMinOn_sublevel_iff hu.2).1 fun x hx ↦ ?_⟩
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    hmin (mem_image_of_mem (toWeakSpace 𝕜 V) hx)

/-- In a reflexive seminormed space over `ℝ` or `ℂ`, a single nonempty norm-bounded sublevel
suffices for the sequential direct method on a sequentially weakly closed admissible set. -/
theorem exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u :=
  exists_isMinOn_of_isSeqClosed_sublevel hV
    (isSeqClosed_toWeakSpace_sublevel hS hE b)
    (hE.mono (image_mono fun _ hx ↦ hx.1)) hne hb

/-- **Sequential direct method (sublevel form).** A sequentially weakly lower semicontinuous energy
with bounded sublevels on a nonempty sequentially weakly closed set in a reflexive seminormed space
over `ℝ` or `ℂ` attains its minimum. Neither topological weak closedness of `S` nor boundedness
below of `E` is assumed. -/
theorem exists_isMinOn_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨v, hv⟩ := hne
  exact exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel hV hS hE
    ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v))

/-- If the set of minimizers of a sequentially weakly lower semicontinuous energy on a sequentially
weakly closed set in a reflexive seminormed space over `ℝ` or `ℂ` is norm-bounded, then that set of
minimizers is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : IsBounded {u ∈ S | IsMinOn E S u}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) := by
  obtain hempty | ⟨u, hu, hmin⟩ := {u ∈ S | IsMinOn E S u}.eq_empty_or_nonempty
  · simp [hempty]
  · rw [hmin.minimizers_eq_sublevel hu] at hb ⊢
    exact isCompact_toWeakSpace_sublevel_of_isSeqClosed hV hS hE (E u) hb

/-- For a sequentially weakly lower semicontinuous energy with bounded sublevels on a sequentially
weakly closed set in a reflexive seminormed space over `ℝ` or `ℂ`, the set of minimizers is weakly
compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded hV hS hE hb.isBounded_minimizers

end LinearOrder

section MinimizingSequence

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Subsequential convergence of bounded minimizing sequences.** In a reflexive seminormed space
over `ℝ` or `ℂ`, every norm-bounded minimizing sequence in a sequentially weakly closed set for a
sequentially weakly lower semicontinuous energy bounded below has a subsequence converging weakly to
an admissible minimizer. -/
theorem exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLattice β] [TopologicalSpace β]
    {E : V → β} {S : Set V}
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄, (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hseqlsc : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄ ⦃r : β⦄, v ∈ S → (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (w n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) ∧
      IsMinOn E S v := by
  obtain ⟨v, φ, hφ, hlim⟩ := tendsto_subseq_toWeakSpace_of_isCompact_closure
    (isCompact_closure_toWeakSpace hreflexive hb) mem_range_self
  have hvS : v ∈ S := hseqclosed (fun n ↦ hu (φ n)) hlim
  have hEv : E v ≤ sInf (E '' S) :=
    hseqlsc hvS (fun n ↦ hu (φ n)) hlim (hminseq.comp hφ.tendsto_atTop)
  exact ⟨v, hvS, φ, hφ, hlim, fun w hw ↦ hEv.trans (csInf_le hbelow (mem_image_of_mem E hw))⟩

/-- **The sequential direct method.** In a reflexive seminormed space over `ℝ` or `ℂ`, an energy
bounded below on a sequentially weakly closed set, sequentially weakly lower semicontinuous along
convergent energy sequences, attains its minimum on `S` as soon as one norm-bounded minimizing
sequence exists. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLattice β] [TopologicalSpace β]
    {E : V → β} {S : Set V}
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄, (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hseqlsc : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄ ⦃r : β⦄, v ∈ S → (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (w n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v := by
  obtain ⟨v, hvS, -, -, -, hmin⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
      hreflexive hbelow hseqclosed hseqlsc hu hb hminseq
  exact ⟨v, hvS, hmin⟩

/-- **Full-sequence weak convergence to a unique minimizer.** Under the hypotheses of the sequential
direct method, if at most one admissible point `v` can minimize `E` on `S` (`∀ w ∈ S, IsMinOn E S w
→ w = v`), then `v` is an admissible minimizer and the entire norm-bounded minimizing sequence
converges weakly to `v` without passing to a subsequence. -/
theorem tendsto_toWeakSpace_of_unique_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLattice β] [TopologicalSpace β]
    {E : V → β} {S : Set V}
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ ⦃w : ℕ → V⦄ ⦃z : V⦄, (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V z)) → z ∈ S)
    (hseqlsc : ∀ ⦃w : ℕ → V⦄ ⦃z : V⦄ ⦃r : β⦄, z ∈ S → (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V z)) →
      Tendsto (fun n ↦ E (w n)) atTop (𝓝 r) → E z ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S))))
    {v : V} (huniq : ∀ w ∈ S, IsMinOn E S w → w = v) :
    v ∈ S ∧ IsMinOn E S v ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
  obtain ⟨v₀, hv₀S, -, -, -, hv₀min⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
      hreflexive hbelow hseqclosed hseqlsc hu hb hminseq
  obtain rfl := huniq v₀ hv₀S hv₀min
  refine ⟨hv₀S, hv₀min, tendsto_of_subseq_tendsto fun ns hns ↦ ?_⟩
  obtain ⟨ψ, -, hnsψ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨w, hwS, σ, -, hlim, hwmin⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
      hreflexive hbelow hseqclosed hseqlsc (fun n ↦ hu (ns (ψ n)))
      (hb.subset (range_comp_subset_range _ _))
      (hminseq.comp hnsψ.tendsto_atTop)
  exact ⟨ψ ∘ σ, huniq w hwS hwmin ▸ hlim⟩

namespace SeqLowerSemicontinuousOn

/-- Bundled-predicate form of
`TauCeti.exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence` using
`IsSeqClosed` and `TauCeti.SeqLowerSemicontinuousOn`. -/
theorem exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {E : V → β} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) ∧
      IsMinOn E S v :=
  TauCeti.exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
    hreflexive hbelow (isSeqClosed_toWeakSpace_iff.1 hS)
    (fun _ _ _ hv hw hlim hEu ↦ hE.le_of_tendsto_toWeakSpace hv hw hlim hEu) hu hb hminseq

/-- Bundled-predicate form of `TauCeti.exists_isMinOn_of_bounded_minimizing_sequence` using
`IsSeqClosed` and `TauCeti.SeqLowerSemicontinuousOn`. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {E : V → β} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v :=
  TauCeti.exists_isMinOn_of_bounded_minimizing_sequence hreflexive hbelow
    (isSeqClosed_toWeakSpace_iff.1 hS)
    (fun _ _ _ hv hw hlim hEu ↦ hE.le_of_tendsto_toWeakSpace hv hw hlim hEu) hu hb hminseq

/-- Bundled-predicate form of
`TauCeti.tendsto_toWeakSpace_of_unique_isMinOn_of_bounded_minimizing_sequence` using `IsSeqClosed`
and `TauCeti.SeqLowerSemicontinuousOn`. -/
theorem tendsto_toWeakSpace_of_unique_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {E : V → β} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S))))
    {v : V} (huniq : ∀ w ∈ S, IsMinOn E S w → w = v) :
    v ∈ S ∧ IsMinOn E S v ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) :=
  TauCeti.tendsto_toWeakSpace_of_unique_isMinOn_of_bounded_minimizing_sequence
    hreflexive hbelow (isSeqClosed_toWeakSpace_iff.1 hS)
    (fun _ _ _ hv hw hlim hEu ↦ hE.le_of_tendsto_toWeakSpace hv hw hlim hEu) hu hb hminseq huniq

end SeqLowerSemicontinuousOn

end MinimizingSequence

end TauCeti
