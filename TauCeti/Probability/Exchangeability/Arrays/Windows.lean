/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Basic
public import TauCeti.Probability.Process.Array.Block
public import TauCeti.Algebra.GroupAction.FiniteSupportPerm

/-!
# Block independence of a jointly exchangeable array law along consecutive windows

For a law on `ℕ × ℕ → α`, independence of the `Finset` restrictions of the array to two finite
blocks transports along any relabelling of the axes preserving the law
(`TauCeti.Probability.indepFun_restrict_map_of_map_pairReindex_eq`, in
`TauCeti.Probability.Process.Array.Block`). For a jointly exchangeable law the square blocks
`I ×ˢ I`, `J ×ˢ J` may therefore be taken consecutive: independence of the windows `[0, |I|)²` and
`[|I|, |I| + |J|)²` gives independence of the blocks over any two disjoint finite sets `I`, `J`,
since a finitely supported permutation carries the two sets onto the two windows. This is the form
in which independence of consecutive label windows, the shape of dissociation for a law on another
carrier read into arrays, is compared with independence of all disjoint blocks.

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
  exact indepFun_restrict_map_of_map_pairReindex_eq σ σ (hρ.map_pairReindex σ) h

end Probability

end TauCeti
