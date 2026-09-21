/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Extreme
public import TauCeti.Probability.Exchangeability.Arrays.Dissociated
public import TauCeti.Probability.Independence.DisjointBlocks
public import TauCeti.Probability.Independence.Map
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Sort

/-!
# Joint dissociation through finite square blocks

Joint dissociation of the coordinate array of a probability law on `ℕ × ℕ → α` is independence
of the restrictions of the array to every pair of disjoint finite square blocks. For a jointly
exchangeable law the blocks may be taken consecutive: independence of the windows `[0, k)²` and
`[k, k + l)²` for all `k, l` already gives independence of all disjoint blocks, since a finitely
supported permutation carries any two disjoint finite sets onto two consecutive windows and the
law is invariant under it. This is the form in which dissociation of a law on a different carrier,
read through a measurable encoding into arrays, is compared with joint dissociation.

## Main results

* `TauCeti.Probability.blockRestrict` — restriction of an array to a square block.
* `TauCeti.Probability.jointlyDissociated_coord_iff_indepFun_blockRestrict` — joint dissociation
  is independence of disjoint block restrictions.
* `TauCeti.Probability.indepFun_blockRestrict_of_forall_Ico` — for a jointly exchangeable law,
  consecutive windows suffice.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- The block σ-algebra of a family is the σ-algebra pulled back along the restriction of the
family to the block. -/
theorem blockSigma_eq_comap_restrict {ι Ω : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (Z : ∀ i, Ω → β i) (S : Set ι) :
    blockSigma Z S = MeasurableSpace.comap (fun ω => fun i : S => Z i ω) inferInstance := by
  rw [blockSigma_def, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp, iSup_subtype]
  rfl

/-- The restriction of an array to the square block `I ×ˢ I`. -/
def blockRestrict (I : Finset ℕ) (x : ℕ × ℕ → α) : (↑I ×ˢ ↑I : Set (ℕ × ℕ)) → α :=
  fun p => x p

omit [MeasurableSpace α] in
/-- The value of a block restriction. -/
@[simp]
theorem blockRestrict_apply (I : Finset ℕ) (x : ℕ × ℕ → α) (p : (↑I ×ˢ ↑I : Set (ℕ × ℕ))) :
    blockRestrict I x p = x p :=
  (rfl)

/-- Restriction to a block is measurable. -/
theorem measurable_blockRestrict (I : Finset ℕ) : Measurable (blockRestrict (α := α) I) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- Joint dissociation of the coordinate array of a probability law is independence of the
restrictions to every pair of disjoint square blocks. -/
theorem jointlyDissociated_coord_iff_indepFun_blockRestrict (ρ : Measure (ℕ × ℕ → α))
    [IsProbabilityMeasure ρ] :
    JointlyDissociated ρ (fun p x => x p) ↔
      ∀ I J : Finset ℕ, Disjoint I J → IndepFun (blockRestrict I) (blockRestrict J) ρ := by
  rw [jointlyDissociated_iff_indep_blockSigma_finset fun p => measurable_pi_apply p]
  simp only [IndepFun_iff_Indep, blockSigma_eq_comap_restrict]
  rfl

/-- Reindexing a block restriction along a permutation of the axis. -/
def blockReindex (σ : Equiv.Perm ℕ) (I : Finset ℕ)
    (y : (↑I ×ˢ ↑I : Set (ℕ × ℕ)) → α) :
    (↑(I.map σ.toEmbedding) ×ˢ ↑(I.map σ.toEmbedding) : Set (ℕ × ℕ)) → α :=
  fun p => y ⟨(σ.symm p.1.1, σ.symm p.1.2), by
    have hp := p.2
    simp only [Set.mem_prod, Finset.coe_map, Set.mem_image, Finset.mem_coe] at hp
    obtain ⟨⟨i, hi, hi'⟩, ⟨j, hj, hj'⟩⟩ := hp
    simp only [Set.mem_prod, Finset.mem_coe]
    refine ⟨?_, ?_⟩
    · rw [← hi']; simpa using hi
    · rw [← hj']; simpa using hj⟩

/-- Block reindexing is measurable. -/
theorem measurable_blockReindex (σ : Equiv.Perm ℕ) (I : Finset ℕ) :
    Measurable (blockReindex (α := α) σ I) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

omit [MeasurableSpace α] in
/-- The restriction to the image block of a permutation is the reindexed restriction to the
block of the relabelled array. -/
theorem blockRestrict_map_eq (σ : Equiv.Perm ℕ) (I : Finset ℕ) :
    blockRestrict (α := α) (I.map σ.toEmbedding)
      = blockReindex σ I ∘ blockRestrict I ∘ pairReindex σ σ := by
  funext x ⟨⟨a, b⟩, hab⟩
  simp [blockRestrict, blockReindex, pairReindex_apply]

/-- Block independence transports along a diagonal relabelling preserving the law. -/
theorem indepFun_blockRestrict_map {ρ : Measure (ℕ × ℕ → α)} [IsProbabilityMeasure ρ]
    (σ : Equiv.Perm ℕ) (hρ : ρ.map (pairReindex σ σ) = ρ) {I J : Finset ℕ}
    (h : IndepFun (blockRestrict I) (blockRestrict J) ρ) :
    IndepFun (blockRestrict (I.map σ.toEmbedding)) (blockRestrict (J.map σ.toEmbedding)) ρ := by
  rw [blockRestrict_map_eq, blockRestrict_map_eq]
  have hm : Measurable (pairReindex (α := α) σ σ) := by
    rw [pairReindex_def]; exact Measurable.of_eval fun p => measurable_pi_apply _
  have h' : IndepFun (blockRestrict I ∘ pairReindex σ σ) (blockRestrict J ∘ pairReindex σ σ) ρ := by
    rw [← indepFun_map_iff_comp hm (measurable_blockRestrict I) (measurable_blockRestrict J), hρ]
    exact h
  exact h'.comp (measurable_blockReindex σ I) (measurable_blockReindex σ J)

/-- Two disjoint finite sets of cardinalities `k` and `l` are the images of the two windows of
`Fin (k + l)` under a finitely supported permutation of `ℕ`. -/
theorem exists_finite_compl_fixedBy_castAdd_natAdd (I J : Finset ℕ) (hIJ : Disjoint I J)
    {k l : ℕ} (hI : I.card = k) (hJ : J.card = l) :
    ∃ σ : Equiv.Perm ℕ, (MulAction.fixedBy ℕ σ)ᶜ.Finite ∧
      (∀ i : Fin k, σ (Fin.castAdd l i) = I.orderEmbOfFin hI i) ∧
      ∀ j : Fin l, σ (Fin.natAdd k j) = J.orderEmbOfFin hJ j := by
  let f : Fin (k + l) → ℕ :=
    Fin.addCases (fun i => I.orderEmbOfFin hI i) (fun j => J.orderEmbOfFin hJ j)
  have hf : Function.Injective f := by
    intro a b hab
    induction a using Fin.addCases with
    | left a =>
      induction b using Fin.addCases with
      | left b =>
        simp only [f, Fin.addCases_left] at hab
        exact congrArg _ ((I.orderEmbOfFin hI).injective hab)
      | right b =>
        simp only [f, Fin.addCases_left, Fin.addCases_right] at hab
        exact absurd hab
          (hIJ.forall_ne_finset (I.orderEmbOfFin_mem hI a) (J.orderEmbOfFin_mem hJ b))
    | right a =>
      induction b using Fin.addCases with
      | left b =>
        simp only [f, Fin.addCases_left, Fin.addCases_right] at hab
        exact absurd hab.symm
          (hIJ.forall_ne_finset (I.orderEmbOfFin_mem hI b) (J.orderEmbOfFin_mem hJ a))
      | right b =>
        simp only [f, Fin.addCases_right] at hab
        exact congrArg _ ((J.orderEmbOfFin hJ).injective hab)
  obtain ⟨σ, hσfin, hσ⟩ :=
    Equiv.Perm.exists_finite_compl_fixedBy_apply_eq Fin.valEmbedding ⟨f, hf⟩
  refine ⟨σ, hσfin, fun i => ?_, fun j => ?_⟩
  · simpa [f] using hσ (Fin.castAdd l i)
  · simpa [f] using hσ (Fin.natAdd k j)


/-- A permutation carrying the window `[k, k + l)` onto the enumeration of `J` maps the window
onto `J`. -/
theorem map_Ico_eq_of_forall {σ : Equiv.Perm ℕ} {J : Finset ℕ} {k l : ℕ} (hJ : J.card = l)
    (h : ∀ j : Fin l, σ (k + j) = J.orderEmbOfFin hJ j) :
    (Finset.Ico k (k + l)).map σ.toEmbedding = J := by
  ext n; simp only [Finset.mem_map, Finset.mem_Ico, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨i, ⟨hki, hik⟩, rfl⟩
    have := h ⟨i - k, by omega⟩
    simp only [Nat.add_sub_cancel' hki] at this
    rw [this]; exact J.orderEmbOfFin_mem hJ _
  · intro hn
    obtain ⟨j, hj⟩ := Set.mem_range.mp ((J.range_orderEmbOfFin hJ) ▸ (Finset.mem_coe.mpr hn))
    exact ⟨k + j, ⟨by omega, by omega⟩, by rw [h j, hj]⟩

/-- **Consecutive windows suffice.** For a jointly exchangeable probability law, block
independence at every pair of consecutive windows `[0, k)`, `[k, k + l)` gives block independence
at every pair of disjoint finite sets. -/
theorem indepFun_blockRestrict_of_forall_Ico {ρ : Measure (ℕ × ℕ → α)} [IsProbabilityMeasure ρ]
    (hρ : JointlyExchangeable ρ fun p x => x p)
    (h : ∀ k l : ℕ, IndepFun (blockRestrict (Finset.Ico 0 (0 + k)))
      (blockRestrict (Finset.Ico k (k + l))) ρ)
    (I J : Finset ℕ) (hIJ : Disjoint I J) : IndepFun (blockRestrict I) (blockRestrict J) ρ := by
  obtain ⟨σ, -, hσI, hσJ⟩ := exists_finite_compl_fixedBy_castAdd_natAdd I J hIJ rfl rfl
  have hI : (Finset.Ico 0 (0 + I.card)).map σ.toEmbedding = I :=
    map_Ico_eq_of_forall rfl fun i => by simpa using hσI i
  have hJ : (Finset.Ico I.card (I.card + J.card)).map σ.toEmbedding = J :=
    map_Ico_eq_of_forall rfl fun j => by simpa using hσJ j
  rw [← hI, ← hJ]
  refine indepFun_blockRestrict_map σ ?_ (h _ _)
  have := (jointlyExchangeable_iff.mp hρ) σ
  simpa only [← pairReindex_def, Measure.map_id'] using this

end Probability

end TauCeti
