/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.FiniteSupportPerm
public import TauCeti.Probability.Process.Array
public import TauCeti.Probability.Process.Array.Tail
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# The finitary symmetric group acting on array space

The finitely supported permutations of `ℕ`, packaged as `TauCeti.FinitaryPerm`, act on array space
`ℕ × ℕ → α` in two ways, both by reindexing along inverse permutations so that reindexing is a
*left* action:

* **diagonally**, one permutation relabelling both axes at once,
  `(g • x) (i, j) = x (g⁻¹ i, g⁻¹ j)`;
* **separately**, a pair of permutations relabelling rows and columns independently,
  `(g • x) (i, j) = x (g.1⁻¹ i, g.2⁻¹ j)`.

Each element acts by the measurable map `pairReindex`, so both actions are `MeasurableConstSMul`.

A finitely supported permutation fixes every index beyond some cutoff, so it changes no entry with
both indices that large. Hence every event of the corner tail `arrayTail` of the coordinate array
is **exactly** fixed by both actions, not only almost surely. This is the input that relates
corner-tail triviality to ergodicity of the actions.

These are the actions under which jointly and separately exchangeable array laws are invariant,
but nothing here assumes a symmetry of a law.

## Main declarations

* `TauCeti.Probability.instMulActionFinitaryPermArray` — the diagonal action;
* `TauCeti.Probability.instMulActionFinitaryPermPairArray` — the separate row-and-column action;
* `TauCeti.Probability.preimage_pairReindex_eq_self_of_measurableSet_arrayTail` — a corner-tail
  event is fixed by every pair of finitely supported axis permutations;
* `TauCeti.Probability.preimage_finitaryPerm_smul_array_eq_self_of_measurableSet_arrayTail` and
  `TauCeti.Probability.preimage_finitaryPermPair_smul_array_eq_self_of_measurableSet_arrayTail` —
  the same statement read through the diagonal and the separate action.
-/

public section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α : Type*}

/-! ## The diagonal and separate actions -/

/-- Finitely supported vertex permutations act diagonally on array path space, by the inverse
permutation so that reindexing is a left action. -/
instance instSMulFinitaryPermArray : SMul FinitaryPerm (ℕ × ℕ → α) :=
  ⟨fun g x => pairReindex (FinitaryPerm.toPerm g)⁻¹ (FinitaryPerm.toPerm g)⁻¹ x⟩

/-- The diagonal array action written as an explicit pair reindexing. -/
theorem finitaryPerm_smul_array_def (g : FinitaryPerm) (x : ℕ × ℕ → α) :
    g • x = pairReindex (FinitaryPerm.toPerm g)⁻¹ (FinitaryPerm.toPerm g)⁻¹ x :=
  rfl

/-- The diagonal array action relabels both coordinates by the inverse permutation. -/
@[simp]
theorem finitaryPerm_smul_array_apply (g : FinitaryPerm) (x : ℕ × ℕ → α) (p : ℕ × ℕ) :
    (g • x) p = x ((FinitaryPerm.toPerm g)⁻¹ p.1, (FinitaryPerm.toPerm g)⁻¹ p.2) :=
  by rw [finitaryPerm_smul_array_def, pairReindex_apply]

/-- Diagonal finitary relabelling is a left action of `FinitaryPerm` on array space. -/
instance instMulActionFinitaryPermArray : MulAction FinitaryPerm (ℕ × ℕ → α) where
  one_smul x := by ext p; simp
  mul_smul g h x := by ext p; simp [mul_inv_rev]

/-- Independent finitely supported permutations act on the two axes of an array. The inverse
permutations make reindexing a left action. -/
instance instSMulFinitaryPermPairArray :
    SMul (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) :=
  ⟨fun g x => pairReindex (FinitaryPerm.toPerm g.1)⁻¹
    (FinitaryPerm.toPerm g.2)⁻¹ x⟩

/-- The separate array action written as an explicit pair reindexing. -/
theorem finitaryPermPair_smul_array_def (g : FinitaryPerm × FinitaryPerm) (x : ℕ × ℕ → α) :
    g • x = pairReindex (FinitaryPerm.toPerm g.1)⁻¹ (FinitaryPerm.toPerm g.2)⁻¹ x :=
  rfl

/-- The separate action is coordinate reindexing on each axis. -/
@[simp]
theorem finitaryPermPair_smul_array_apply (g : FinitaryPerm × FinitaryPerm)
    (x : ℕ × ℕ → α) (p : ℕ × ℕ) :
    (g • x) p = x ((FinitaryPerm.toPerm g.1)⁻¹ p.1,
      (FinitaryPerm.toPerm g.2)⁻¹ p.2) := by
  rw [finitaryPermPair_smul_array_def, pairReindex_apply]

/-- Independent row and column permutations compose as a left action on arrays. -/
instance instMulActionFinitaryPermPairArray :
    MulAction (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) where
  one_smul x := by ext p; simp
  mul_smul g h x := by ext p; simp [mul_inv_rev]

variable [MeasurableSpace α]

/-- Each diagonal finitary relabeling is measurable. -/
instance instMeasurableConstSMulFinitaryPermArray :
    MeasurableConstSMul FinitaryPerm (ℕ × ℕ → α) :=
  ⟨fun _ => measurable_pairReindex (α := α) _ _⟩

/-- Each independent finitary relabeling is measurable. -/
instance instMeasurableConstSMulFinitaryPermPairArray :
    MeasurableConstSMul (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) :=
  ⟨fun _ => measurable_pairReindex _ _⟩

/-! ## Corner-tail events are invariant -/

private theorem preimage_pairReindex_eq_of_measurable_arrayTailFamily
    {s : Set (ℕ × ℕ → α)} {σ τ : Equiv.Perm ℕ} {N : ℕ}
    (hs : MeasurableSet[arrayTailFamily (fun p (x : ℕ × ℕ → α) => x p) N] s)
    (hσ : ∀ k, N ≤ k → σ k = k) (hτ : ∀ k, N ≤ k → τ k = k) :
    pairReindex (α := α) σ τ ⁻¹' s = s := by
  rw [arrayTailFamily_eq_blockSigma, blockSigma_def] at hs
  rw [MeasurableSpace.measurableSet_iSup] at hs
  induction hs with
  | basic u hu =>
      rcases hu with ⟨p, hu⟩
      rw [MeasurableSpace.measurableSet_iSup] at hu
      induction hu with
      | basic u hu =>
          rcases hu with ⟨hp, v, _, rfl⟩
          ext x
          simp only [Set.mem_preimage, pairReindex_apply]
          rw [hσ p.1 hp.1, hτ p.2 hp.2]
      | empty => simp
      | compl t _ hpre => rw [Set.preimage_compl, hpre]
      | iUnion f _ hf =>
          rw [Set.preimage_iUnion]
          simp [hf]
  | empty => simp
  | compl t _ hpre => rw [Set.preimage_compl, hpre]
  | iUnion f _ hf =>
      rw [Set.preimage_iUnion]
      simp [hf]

/-- **Every corner-tail event is fixed by a finitely supported separate relabelling**: permuting
the two axes independently by finitely supported permutations fixes every sufficiently far corner,
which is all that a corner-tail event reads. -/
theorem preimage_pairReindex_eq_self_of_measurableSet_arrayTail
    {s : Set (ℕ × ℕ → α)}
    (hs : MeasurableSet[arrayTail (fun p (x : ℕ × ℕ → α) => x p)] s)
    {σ τ : Equiv.Perm ℕ} (hσ : (MulAction.fixedBy ℕ σ)ᶜ.Finite)
    (hτ : (MulAction.fixedBy ℕ τ)ᶜ.Finite) : pairReindex (α := α) σ τ ⁻¹' s = s := by
  obtain ⟨M, hM⟩ := finite_compl_fixedBy_eventually_eq_self hσ
  obtain ⟨N, hN⟩ := finite_compl_fixedBy_eventually_eq_self hτ
  exact preimage_pairReindex_eq_of_measurable_arrayTailFamily
    ((measurableSet_arrayTail_iff.mp hs) (max M N))
    (fun k hk => hM k ((le_max_left M N).trans hk)) fun k hk => hN k ((le_max_right M N).trans hk)

/-- **Every corner-tail event is fixed by the diagonal action**: a finitely supported relabelling
of both coordinates leaves every entry in a sufficiently far corner unchanged, which is all that a
corner-tail event reads. -/
theorem preimage_finitaryPerm_smul_array_eq_self_of_measurableSet_arrayTail
    {s : Set (ℕ × ℕ → α)}
    (hs : MeasurableSet[arrayTail (fun p (x : ℕ × ℕ → α) => x p)] s)
    (g : FinitaryPerm) : (fun x : ℕ × ℕ → α => g • x) ⁻¹' s = s := by
  have hfin : (MulAction.fixedBy ℕ (FinitaryPerm.toPerm g)⁻¹)ᶜ.Finite := by
    simpa only [FinitaryPerm.toPerm_inv] using FinitaryPerm.finite_compl_fixedBy_toPerm g⁻¹
  simp only [finitaryPerm_smul_array_def]
  exact preimage_pairReindex_eq_self_of_measurableSet_arrayTail hs hfin hfin

/-- A corner-tail event is fixed by every separate finitary relabeling. -/
theorem preimage_finitaryPermPair_smul_array_eq_self_of_measurableSet_arrayTail
    {s : Set (ℕ × ℕ → α)}
    (hs : MeasurableSet[arrayTail (fun p (x : ℕ × ℕ → α) => x p)] s)
    (g : FinitaryPerm × FinitaryPerm) :
    (fun x : ℕ × ℕ → α => g • x) ⁻¹' s = s := by
  have h₁ : (MulAction.fixedBy ℕ (FinitaryPerm.toPerm g.1)⁻¹)ᶜ.Finite := by
    simpa only [FinitaryPerm.toPerm_inv] using FinitaryPerm.finite_compl_fixedBy_toPerm g.1⁻¹
  have h₂ : (MulAction.fixedBy ℕ (FinitaryPerm.toPerm g.2)⁻¹)ᶜ.Finite := by
    simpa only [FinitaryPerm.toPerm_inv] using FinitaryPerm.finite_compl_fixedBy_toPerm g.2⁻¹
  simp only [finitaryPermPair_smul_array_def]
  exact preimage_pairReindex_eq_self_of_measurableSet_arrayTail hs h₁ h₂

end Probability

end TauCeti
