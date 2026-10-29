/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.FiniteSupportPerm
public import TauCeti.Probability.Process.PathLaw.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# The finitary symmetric group acting on path space

The finitely supported permutations of the time index, packaged as `TauCeti.FinitaryPerm`, act on
path space `ℕ → α` by reindexing along the inverse permutation, `(g • x) n = x (g⁻¹ n)`. The inverse
is what makes reindexing a *left* action. Each element acts by the measurable map `permReindex`, so
the action is a `MeasurableConstSMul`.

This is the action whose invariant laws and ergodic laws are studied for exchangeable sequences; it
needs no symmetry hypothesis on a law to be stated, and `FinitaryPerm` being countable is what lets
a.e.-invariance under it be handled one element at a time.

## Main declarations

* `TauCeti.Probability.instMulActionFinitaryPermPath` — the left action of `FinitaryPerm` on
  `ℕ → α` by finitary reindexing of the time index;
* `TauCeti.Probability.preimage_finitaryPerm_smul_path` — preimages under the action are preimages
  under the corresponding `permReindex`;
* `TauCeti.Probability.instMeasurableConstSMulFinitaryPermPath` — each element acts measurably.
-/

public section

namespace TauCeti

namespace Probability

variable {α : Type*}

/-- The finitely supported time permutations act on path space by reindexing along the inverse,
`(g • x) n = x (g⁻¹ n)`.  The inverse is what makes reindexing a *left* action. -/
instance instSMulFinitaryPermPath : SMul FinitaryPerm (ℕ → α) :=
  ⟨fun g x => permReindex (FinitaryPerm.toPerm g)⁻¹ x⟩

/-- The path action written as an explicit `permReindex`. -/
theorem finitaryPerm_smul_path_def (g : FinitaryPerm) (x : ℕ → α) :
    g • x = permReindex (FinitaryPerm.toPerm g)⁻¹ x :=
  rfl

/-- The path action reads the coordinate at the inverse-permuted time. -/
@[simp]
theorem finitaryPerm_smul_path_apply (g : FinitaryPerm) (x : ℕ → α) (n : ℕ) :
    (g • x) n = x ((FinitaryPerm.toPerm g)⁻¹ n) :=
  rfl

/-- Finitary reindexing of the time index is a left action of `FinitaryPerm` on path space. -/
instance instMulActionFinitaryPermPath : MulAction FinitaryPerm (ℕ → α) where
  one_smul x := by ext n; simp
  mul_smul g h x := by ext n; simp [mul_inv_rev]

/-- Reindexing along a permutation is the same map whether it is read as an action of `FinitaryPerm`
or written out with `permReindex`.  This is the form in which events stated with `permReindex`, such
as those of the exchangeable σ-algebra, meet the action. -/
theorem preimage_finitaryPerm_smul_path (g : FinitaryPerm) (s : Set (ℕ → α)) :
    (fun x : ℕ → α => g • x) ⁻¹' s = permReindex (FinitaryPerm.toPerm g)⁻¹ ⁻¹' s :=
  rfl

variable [MeasurableSpace α]

/-- Each finitary reindexing of the time index is measurable. -/
instance instMeasurableConstSMulFinitaryPermPath : MeasurableConstSMul FinitaryPerm (ℕ → α) :=
  ⟨fun g => measurable_reindex (α := α) ⇑(FinitaryPerm.toPerm g)⁻¹⟩

end Probability

end TauCeti
