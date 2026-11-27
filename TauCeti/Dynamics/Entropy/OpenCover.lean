/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
import Mathlib.Topology.UniformSpace.Compact

/-!
# The open-cover definition of topological entropy

For a self-map `T` of a topological space `X` and an open cover `𝒰` of `X`, the `n`-fold join
`𝒰 ∨ T⁻¹ 𝒰 ∨ ⋯ ∨ T^{-(n-1)} 𝒰` consists of the cylinders `⋂ k < n, T^[k] ⁻¹' w k` with every
`w k ∈ 𝒰`. `TauCeti.openCoverMincard T 𝒰 n` is the least number of such cylinders covering `X`,
counted by their words `w : Fin n → Set X`, and the Adler–Konheim–McAndrew entropy
`TauCeti.openCoverEntropy T` is the supremum over open covers of the exponential growth rate
(`limsup`) of these numbers.

On a compact uniform space this is Mathlib's `Dynamics.coverEntropy T univ`
(`TauCeti.openCoverEntropy_eq_coverEntropy`), for every map `T`:

* by the Lebesgue number lemma, an open cover `𝒰` has an entourage `V` whose balls each lie in a
  member of `𝒰`, and a `(V, n)`-dynamical cover then gives as many cylinders of the join covering
  `X`;
* conversely, for an entourage `U`, the balls of an open symmetric entourage `V` with
  `V ○ V ⊆ U` form an open cover any two points of whose members are `U`-close, and one point in
  each cylinder of a covering subfamily of the join is a `(U, n)`-dynamical cover.

On a compact Hausdorff space the compatible uniformity is unique, so this identifies the
open-cover entropy with the entropy of that uniformity.

## Main definitions

* `TauCeti.openCoverMincard T 𝒰 n`: the minimal number of cylinders of the `n`-fold join of `𝒰`
  covering `X`.
* `TauCeti.openCoverEntropy T`: the supremum over open covers `𝒰` of the growth rate of
  `openCoverMincard T 𝒰 n`.

## Main results

* `TauCeti.openCoverEntropy_le_coverEntropy`, `TauCeti.coverEntropy_le_openCoverEntropy`, and
  `TauCeti.openCoverEntropy_eq_coverEntropy`: on a compact uniform space the open-cover entropy
  is `coverEntropy T univ`.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, Definitions 4.5–4.7 and Theorem 4.8,
  pp. 119–121.
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth
open scoped ENNReal Uniformity SetRel

variable {X : Type*} {T : X → X} {𝒰 : Set (Set X)} {n : ℕ}

/-- The minimal number of cylinders `⋂ k < n, T^[k] ⁻¹' w k` with every `w k ∈ 𝒰` needed to
cover `X`, counted by their words `w`: the minimal cardinality of a subcover of the `n`-fold join
`𝒰 ∨ T⁻¹ 𝒰 ∨ ⋯ ∨ T^{-(n-1)} 𝒰`. -/
noncomputable def openCoverMincard (T : X → X) (𝒰 : Set (Set X)) (n : ℕ) : ℕ∞ :=
  ⨅ (s : Finset (Fin n → Set X)) (_ : ∀ w ∈ s, ∀ k, w k ∈ 𝒰)
    (_ : ∀ x, ∃ w ∈ s, ∀ k : Fin n, T^[k] x ∈ w k), (s.card : ℕ∞)

/-- The open-cover (Adler–Konheim–McAndrew) topological entropy of `T`: the supremum over open
covers `𝒰` of `X` of the exponential growth rate (`limsup`) of `openCoverMincard T 𝒰 n`. -/
noncomputable def openCoverEntropy [TopologicalSpace X] (T : X → X) : EReal :=
  ⨆ (𝒰 : Set (Set X)) (_ : ∀ U ∈ 𝒰, IsOpen U) (_ : ⋃₀ 𝒰 = univ),
    expGrowthSup fun n ↦ (openCoverMincard T 𝒰 n : ℝ≥0∞)

theorem openCoverMincard_def :
    openCoverMincard T 𝒰 n = ⨅ (s : Finset (Fin n → Set X)) (_ : ∀ w ∈ s, ∀ k, w k ∈ 𝒰)
      (_ : ∀ x, ∃ w ∈ s, ∀ k : Fin n, T^[k] x ∈ w k), (s.card : ℕ∞) :=
  (rfl)

theorem openCoverEntropy_def [TopologicalSpace X] :
    openCoverEntropy T = ⨆ (𝒰 : Set (Set X)) (_ : ∀ U ∈ 𝒰, IsOpen U) (_ : ⋃₀ 𝒰 = univ),
      expGrowthSup fun n ↦ (openCoverMincard T 𝒰 n : ℝ≥0∞) :=
  (rfl)

/-- A finite family of words of the join covering `X` bounds `openCoverMincard`. -/
theorem openCoverMincard_le_card {s : Finset (Fin n → Set X)} (hs : ∀ w ∈ s, ∀ k, w k ∈ 𝒰)
    (hcov : ∀ x, ∃ w ∈ s, ∀ k : Fin n, T^[k] x ∈ w k) : openCoverMincard T 𝒰 n ≤ s.card :=
  (iInf₂_le s hs).trans (iInf_le (fun _ ↦ (s.card : ℕ∞)) hcov)

/-- **Lebesgue numbers.** If the balls of `V` each lie in a member of `𝒰`, a `(V, n)`-dynamical
cover gives as many cylinders of the `n`-fold join of `𝒰` covering `X`. -/
theorem openCoverMincard_le_coverMincard {V : SetRel X X}
    (hV : ∀ x, ∃ U ∈ 𝒰, SetRel.ball V x ⊆ U) (n : ℕ) :
    openCoverMincard T 𝒰 n ≤ coverMincard T univ V n := by
  classical
  refine le_iInf₂ fun t ht ↦ ?_
  choose U hU hVU using hV
  let w : X → Fin n → Set X := fun y k ↦ U (T^[k] y)
  refine (openCoverMincard_le_card (s := t.image w) ?_ ?_).trans
    (by exact_mod_cast Finset.card_image_le)
  · simp only [Finset.mem_image]
    rintro _ ⟨y, -, rfl⟩ k
    exact hU _
  · intro x
    obtain ⟨y, hy, hxy⟩ := ht (mem_univ x)
    refine ⟨w y, Finset.mem_image_of_mem w hy, fun k ↦ hVU _ ?_⟩
    exact mem_dynEntourage.1 hxy k k.isLt

/-- **Small open covers.** If any two points of a member of `𝒰` are `U`-close, choosing one point
in each cylinder of a covering family of words gives a `(U, n)`-dynamical cover. -/
theorem coverMincard_le_openCoverMincard {U : SetRel X X}
    (hU : ∀ W ∈ 𝒰, ∀ a ∈ W, ∀ b ∈ W, (a, b) ∈ U) (n : ℕ) :
    coverMincard T univ U n ≤ openCoverMincard T 𝒰 n := by
  classical
  refine le_iInf₂ fun s hs ↦ le_iInf fun hcov ↦ ?_
  rcases isEmpty_or_nonempty X with hX | hX
  · refine (IsDynCoverOf.coverMincard_le_card (s := ∅) ?_).trans (by simp)
    rw [univ_eq_empty_iff.2 hX]
    exact isDynCoverOf_empty
  -- One point in each nonempty cylinder.
  have hpt : ∀ w ∈ s, ∃ z : X, (∃ x, ∀ k : Fin n, T^[k] x ∈ w k) →
      ∀ k : Fin n, T^[k] z ∈ w k := by
    intro w _
    by_cases h : ∃ x, ∀ k : Fin n, T^[k] x ∈ w k
    · obtain ⟨x, hx⟩ := h
      exact ⟨x, fun _ ↦ hx⟩
    · exact ⟨Classical.arbitrary X, fun h' ↦ (h h').elim⟩
  choose! z hz using hpt
  refine (IsDynCoverOf.coverMincard_le_card (s := s.image z) ?_).trans
    (by exact_mod_cast Finset.card_image_le)
  intro x _
  obtain ⟨w, hw, hxw⟩ := hcov x
  refine ⟨z w, Finset.mem_image_of_mem z hw, mem_dynEntourage.2 fun k hk ↦ ?_⟩
  have hzw := hz w hw ⟨x, hxw⟩ ⟨k, hk⟩
  exact hU (w ⟨k, hk⟩) (hs w hw ⟨k, hk⟩) _ (hxw ⟨k, hk⟩) _ hzw

variable [UniformSpace X]

/-- On a compact uniform space the open-cover entropy is at most `coverEntropy T univ`. -/
theorem openCoverEntropy_le_coverEntropy [CompactSpace X] (T : X → X) :
    openCoverEntropy T ≤ coverEntropy T univ := by
  refine iSup₂_le fun 𝒰 hopen ↦ iSup_le fun hcov ↦ ?_
  obtain ⟨V, hV, hball⟩ := lebesgue_number_lemma_sUnion isCompact_univ hopen hcov.symm.subset
  refine le_trans ?_ (coverEntropyEntourage_le_coverEntropy T univ hV)
  exact expGrowthSup_monotone fun n ↦ ENat.toENNReal_le.2
    (openCoverMincard_le_coverMincard (fun x ↦ hball x (mem_univ x)) n)

/-- `coverEntropy T univ` is at most the open-cover entropy, on any uniform space. -/
theorem coverEntropy_le_openCoverEntropy (T : X → X) :
    coverEntropy T univ ≤ openCoverEntropy T := by
  refine iSup₂_le fun U hU ↦ ?_
  obtain ⟨V, hV, hVo, hVs, hVU⟩ := comp_open_symm_mem_uniformity_sets hU
  have hopen : ∀ W ∈ range (SetRel.ball V), IsOpen W := by
    rintro _ ⟨x, rfl⟩
    exact hVo.preimage (continuous_id.prodMk continuous_const)
  have hcov : ⋃₀ range (SetRel.ball V) = univ :=
    eq_univ_of_forall fun x ↦ mem_sUnion.2 ⟨SetRel.ball V x, mem_range_self x,
      refl_mem_uniformity hV⟩
  have hsmall : ∀ W ∈ range (SetRel.ball V), ∀ a ∈ W, ∀ b ∈ W, (a, b) ∈ U := by
    rintro _ ⟨x, rfl⟩ a ha b hb
    exact hVU ⟨x, ha, SetRel.symm V hb⟩
  refine le_trans ?_ (le_iSup₂_of_le (range (SetRel.ball V)) hopen (le_iSup_of_le hcov le_rfl))
  exact expGrowthSup_monotone fun n ↦
    ENat.toENNReal_le.2 (coverMincard_le_openCoverMincard hsmall n)

/-- **Open-cover entropy.** On a compact uniform space the open-cover (Adler–Konheim–McAndrew)
entropy of any map `T` is Mathlib's `coverEntropy T univ`. -/
theorem openCoverEntropy_eq_coverEntropy [CompactSpace X] (T : X → X) :
    openCoverEntropy T = coverEntropy T univ :=
  (openCoverEntropy_le_coverEntropy T).antisymm (coverEntropy_le_openCoverEntropy T)

end TauCeti
