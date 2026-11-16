/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Splitting off the initial coordinate of a `Fin`-indexed product

For a family of topological spaces `Y : Fin (n + 1) → Type*`, separating coordinate `0` from the
remaining coordinates via `Fin.consEquiv` is a homeomorphism for the product topologies.

## Main declarations

* `TauCeti.finConsHomeomorph`: `Fin.consEquiv` as a homeomorphism
  `Y 0 × (∀ i, Y (Fin.succ i)) ≃ₜ ∀ i, Y i`, with `TauCeti.finConsHomeomorph_apply`,
  `TauCeti.finConsHomeomorph_symm_apply`, and `TauCeti.finConsHomeomorph_toEquiv`.
-/

public section

namespace TauCeti

/-- **Splitting off coordinate `0` of a `Fin (n + 1)`-indexed family.** `Fin.consEquiv` as a
homeomorphism between `Y 0 × ∀ i, Y (Fin.succ i)` and `∀ i, Y i`. -/
def finConsHomeomorph {n : ℕ} (Y : Fin (n + 1) → Type*) [∀ i, TopologicalSpace (Y i)] :
    Y 0 × (∀ i, Y (Fin.succ i)) ≃ₜ ∀ i, Y i where
  toEquiv := Fin.consEquiv Y
  continuous_toFun := continuous_fst.finCons continuous_snd
  continuous_invFun := (continuous_apply 0).prodMk (continuous_pi fun i ↦ continuous_apply i.succ)

/-- `TauCeti.finConsHomeomorph` prepends the first component to the second via `Fin.cons`. -/
@[simp]
theorem finConsHomeomorph_apply {n : ℕ} (Y : Fin (n + 1) → Type*) [∀ i, TopologicalSpace (Y i)]
    (p : Y 0 × ∀ i, Y (Fin.succ i)) :
    finConsHomeomorph Y p = Fin.cons p.1 p.2 :=
  (rfl)

/-- The inverse of `TauCeti.finConsHomeomorph` splits a tuple into its `0` coordinate and its
`Fin.tail`. -/
@[simp]
theorem finConsHomeomorph_symm_apply {n : ℕ} (Y : Fin (n + 1) → Type*)
    [∀ i, TopologicalSpace (Y i)] (v : ∀ i, Y i) :
    (finConsHomeomorph Y).symm v = (v 0, Fin.tail v) :=
  (rfl)

/-- The underlying equivalence of `TauCeti.finConsHomeomorph` is `Fin.consEquiv`. -/
@[simp]
theorem finConsHomeomorph_toEquiv {n : ℕ} (Y : Fin (n + 1) → Type*)
    [∀ i, TopologicalSpace (Y i)] :
    (finConsHomeomorph Y).toEquiv = Fin.consEquiv Y :=
  (rfl)

end TauCeti

end
