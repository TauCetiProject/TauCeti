/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Basic facts about root systems

Elementary consequences of the definition of a root system that need no further theory.

## Main results

* `RootPairing.ext_of_coroot`: two root pairings with the same pairing map, root embedding, and
  coroot embedding are equal.
* `RootPairing.nonempty_of_isRootSystem`: a root system on a nontrivial module has a root.
* `RootPairing.finite_weight_of_isRootSystem`: the weight module of a finite root system is finitely
  generated.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- Two root pairings with the same pairing map, root embedding, and coroot embedding are equal.
Unlike `RootPairing.ext`, no characteristic-zero, domain, or finiteness hypotheses are needed, as
equality of the coroot embeddings directly fixes `reflectionPerm`. -/
theorem ext_of_coroot {P₁ P₂ : RootPairing ι R M N}
    (he : P₁.toLinearMap = P₂.toLinearMap) (hr : P₁.root = P₂.root)
    (hc : P₁.coroot = P₂.coroot) : P₁ = P₂ := by
  have hperm : P₁.reflectionPerm = P₂.reflectionPerm := by
    ext i j
    refine P₂.root.injective ?_
    rw [← hr, ← P₁.reflectionPerm_root, he, hr, hc, P₂.reflectionPerm_root]
  cases P₁
  cases P₂
  simp only at he hr hc hperm
  subst he hr hc hperm
  rfl

/-- A root system on a nontrivial module has a root. -/
lemma nonempty_of_isRootSystem [Nontrivial M] (P : RootPairing ι R M N) [P.IsRootSystem] :
    Nonempty ι := by
  by_contra! h
  have hspan := IsRootSystem.span_root_eq_top (P := P)
  rw [Set.range_eq_empty, Submodule.span_empty] at hspan
  exact bot_ne_top hspan

/-- On a finite root system, the weight module is finitely generated because it is spanned by the
finite set of roots. -/
theorem finite_weight_of_isRootSystem (P : RootPairing ι R M N) [Finite ι] [P.IsRootSystem] :
    Module.Finite R M :=
  Module.finite_def.mpr
    (IsRootSystem.span_root_eq_top (P := P) ▸ Submodule.fg_span (Set.finite_range P.root))

end RootPairing
