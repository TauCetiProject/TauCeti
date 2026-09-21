/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Dissociated
public import TauCeti.Probability.Independence.DisjointBlocks
public import TauCeti.Probability.Independence.Map
public import TauCeti.Algebra.GroupAction.FiniteSupportPerm
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Sort

/-!
# Joint dissociation through finite square blocks

Joint dissociation of the coordinate array of a law on `ℕ × ℕ → α` is independence of the
`Finset` restrictions of the array to every pair of disjoint finite square blocks `I ×ˢ I`,
`J ×ˢ J`. For a jointly exchangeable law the blocks may be taken consecutive: independence of the
windows `[0, k)²` and `[k, k + l)²` for all `k, l` already gives independence of all disjoint
blocks, since a finitely supported permutation carries any two disjoint finite sets onto two
consecutive windows and the law is invariant under it. This is the form in which dissociation of
a law on another carrier, read through a measurable encoding into arrays, is compared with joint
dissociation.

## Main results

* `TauCeti.Probability.jointlyDissociated_coord_iff_indepFun_restrict` — joint dissociation is
  independence of disjoint block restrictions.
* `TauCeti.Probability.indepFun_restrict_of_forall_Ico` — for a jointly exchangeable law,
  consecutive windows suffice.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- Joint dissociation of the coordinate array is independence of the restrictions to every
pair of disjoint square blocks. -/
theorem jointlyDissociated_coord_iff_indepFun_restrict (ρ : Measure (ℕ × ℕ → α))
    [IsZeroOrProbabilityMeasure ρ] :
    JointlyDissociated ρ (fun p x => x p) ↔
      ∀ I J : Finset ℕ, Disjoint I J →
        IndepFun (fun x : ℕ × ℕ → α => (I ×ˢ I).restrict x)
          (fun x : ℕ × ℕ → α => (J ×ˢ J).restrict x) ρ := by
  rw [jointlyDissociated_iff_indep_blockSigma_finset fun p => measurable_pi_apply p]
  refine forall₃_congr fun I J _ => ?_
  rw [IndepFun_iff_Indep, ← Finset.coe_product, ← Finset.coe_product,
    blockSigma_coe_eq_comap_finset_restrict, blockSigma_coe_eq_comap_finset_restrict]

/-- Reindexing a block restriction along a permutation of the axis. -/
private def blockReindex (σ : Equiv.Perm ℕ) (I : Finset ℕ)
    (y : (I ×ˢ I : Finset (ℕ × ℕ)) → α) :
    (I.map σ.toEmbedding ×ˢ I.map σ.toEmbedding : Finset (ℕ × ℕ)) → α :=
  fun p => y ⟨(σ.symm p.1.1, σ.symm p.1.2), by
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.1 p.2
    exact Finset.mem_product.2 ⟨Finset.mem_map_equiv.1 h₁, Finset.mem_map_equiv.1 h₂⟩⟩

private theorem measurable_blockReindex (σ : Equiv.Perm ℕ) (I : Finset ℕ) :
    Measurable (blockReindex (α := α) σ I) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

omit [MeasurableSpace α] in
private theorem restrict_map_product_eq (σ : Equiv.Perm ℕ) (I : Finset ℕ) :
    (fun x : ℕ × ℕ → α => (I.map σ.toEmbedding ×ˢ I.map σ.toEmbedding).restrict x)
      = blockReindex σ I ∘ (fun x : ℕ × ℕ → α => (I ×ˢ I).restrict x) ∘ pairReindex σ σ := by
  funext x ⟨⟨a, b⟩, hab⟩
  simp [Finset.restrict, blockReindex, pairReindex_apply]

/-- Block independence transports along a diagonal relabelling preserving the law: the blocks
`I ×ˢ I`, `J ×ˢ J` independent under `ρ` give the blocks over `σ '' I`, `σ '' J` independent. -/
theorem indepFun_restrict_map_of_map_pairReindex_eq {ρ : Measure (ℕ × ℕ → α)}
    (σ : Equiv.Perm ℕ) (hρ : ρ.map (pairReindex σ σ) = ρ) {I J : Finset ℕ}
    (h : IndepFun (fun x : ℕ × ℕ → α => (I ×ˢ I).restrict x)
      (fun x : ℕ × ℕ → α => (J ×ˢ J).restrict x) ρ) :
    IndepFun (fun x : ℕ × ℕ → α => (I.map σ.toEmbedding ×ˢ I.map σ.toEmbedding).restrict x)
      (fun x : ℕ × ℕ → α => (J.map σ.toEmbedding ×ˢ J.map σ.toEmbedding).restrict x) ρ := by
  rw [restrict_map_product_eq, restrict_map_product_eq]
  refine IndepFun.comp ?_ (measurable_blockReindex σ I) (measurable_blockReindex σ J)
  rw [← indepFun_map_iff_comp (measurable_pairReindex σ σ) (Finset.measurable_restrict _)
    (Finset.measurable_restrict _), hρ]
  exact h

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

/-- A permutation agreeing on the window `[k, k + l)` with the enumeration of `J` maps the window
onto `J`. -/
theorem map_Ico_eq_of_forall_apply_eq_orderEmbOfFin {σ : Equiv.Perm ℕ} {J : Finset ℕ} {k l : ℕ}
    (hJ : J.card = l) (h : ∀ j : Fin l, σ (k + j) = J.orderEmbOfFin hJ j) :
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

/-- **Consecutive windows suffice.** For a jointly exchangeable law, block independence at every
pair of consecutive windows `[0, k)²`, `[k, k + l)²` gives block independence at every pair of
disjoint finite sets. -/
theorem indepFun_restrict_of_forall_Ico {ρ : Measure (ℕ × ℕ → α)}
    (hρ : JointlyExchangeable ρ fun p x => x p)
    (h : ∀ k l : ℕ, IndepFun (fun x : ℕ × ℕ → α => (Finset.Ico 0 k ×ˢ Finset.Ico 0 k).restrict x)
      (fun x : ℕ × ℕ → α => (Finset.Ico k (k + l) ×ˢ Finset.Ico k (k + l)).restrict x) ρ)
    (I J : Finset ℕ) (hIJ : Disjoint I J) :
    IndepFun (fun x : ℕ × ℕ → α => (I ×ˢ I).restrict x)
      (fun x : ℕ × ℕ → α => (J ×ˢ J).restrict x) ρ := by
  obtain ⟨σ, -, hσI, hσJ⟩ := exists_finite_compl_fixedBy_castAdd_natAdd I J hIJ rfl rfl
  have hI : (Finset.Ico 0 I.card).map σ.toEmbedding = I := by
    have := map_Ico_eq_of_forall_apply_eq_orderEmbOfFin (k := 0) rfl fun i => by simpa using hσI i
    rwa [Nat.zero_add] at this
  have hJ : (Finset.Ico I.card (I.card + J.card)).map σ.toEmbedding = J :=
    map_Ico_eq_of_forall_apply_eq_orderEmbOfFin rfl fun j => by simpa using hσJ j
  rw [← hI, ← hJ]
  exact indepFun_restrict_map_of_map_pairReindex_eq σ (hρ.map_pairReindex σ) (h _ _)

end Probability

end TauCeti
