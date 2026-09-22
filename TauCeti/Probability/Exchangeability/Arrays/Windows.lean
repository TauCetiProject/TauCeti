/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Basic
public import TauCeti.Probability.Independence.Map
public import TauCeti.Algebra.GroupAction.FiniteSupportPerm

/-!
# Joint dissociation through finite square blocks

Joint dissociation of the coordinate array of a law on `ℕ × ℕ → α` is independence of the
`Finset` restrictions of the array to every pair of disjoint finite square blocks `I ×ˢ I`,
`J ×ˢ J` (`jointlyDissociated_iff_indepFun_restrict`). For a jointly exchangeable law the
blocks may be taken consecutive: independence of the
windows `[0, k)²` and `[k, k + l)²` for all `k, l` already gives independence of all disjoint
blocks, since a finitely supported permutation carries any two disjoint finite sets onto two
consecutive windows and the law is invariant under it. This is the form in which dissociation of
a law on another carrier, read through a measurable encoding into arrays, is compared with joint
dissociation.

## Main results

* `TauCeti.Probability.indepFun_restrict_of_forall_Ico` — for a jointly exchangeable law,
  consecutive windows suffice.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

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

/-- **Consecutive windows suffice.** For a jointly exchangeable law, block independence at the
consecutive windows `[0, |I|)²`, `[|I|, |I| + |J|)²` gives block independence at the disjoint
finite sets `I`, `J`. -/
theorem indepFun_restrict_of_forall_Ico {ρ : Measure (ℕ × ℕ → α)}
    (hρ : JointlyExchangeable ρ fun p x => x p)
    (I J : Finset ℕ) (hIJ : Disjoint I J)
    (h : IndepFun
      (fun x : ℕ × ℕ → α => (Finset.Ico 0 I.card ×ˢ Finset.Ico 0 I.card).restrict x)
      (fun x : ℕ × ℕ → α =>
        (Finset.Ico I.card (I.card + J.card) ×ˢ Finset.Ico I.card (I.card + J.card)).restrict x)
      ρ) :
    IndepFun (fun x : ℕ × ℕ → α => (I ×ˢ I).restrict x)
      (fun x : ℕ × ℕ → α => (J ×ˢ J).restrict x) ρ := by
  obtain ⟨σ, -, hσI, hσJ⟩ :=
    Equiv.Perm.exists_finite_compl_fixedBy_castAdd_natAdd I J hIJ rfl rfl
  have hI : (Finset.Ico 0 I.card).map σ.toEmbedding = I := by
    have := Equiv.Perm.map_Ico_eq_of_forall_apply_eq_orderEmbOfFin (k := 0) rfl fun i => by
      simpa using hσI i
    rwa [Nat.zero_add] at this
  have hJ : (Finset.Ico I.card (I.card + J.card)).map σ.toEmbedding = J :=
    Equiv.Perm.map_Ico_eq_of_forall_apply_eq_orderEmbOfFin rfl fun j => by simpa using hσJ j
  rw [← hI, ← hJ]
  exact indepFun_restrict_map_of_map_pairReindex_eq σ (hρ.map_pairReindex σ) h

end Probability

end TauCeti
