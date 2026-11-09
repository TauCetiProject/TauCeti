/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compact operators with finite product targets

A map into a finite product is compact when each component is compact. No linearity is needed:
the finitely many neighbourhoods witnessing compactness have a common intersection.
-/

public section

open Filter Set Topology

/-- A finite family of compact operators with a common source defines a compact operator into
the product of their targets. -/
theorem IsCompactOperator.pi {E : Type*} [Zero E] [TopologicalSpace E]
    {ι : Type*} [Finite ι] {F : ι → Type*} [∀ i, TopologicalSpace (F i)]
    {f : (i : ι) → E → F i} (hf : ∀ i, IsCompactOperator (f i)) :
    IsCompactOperator (fun x i ↦ f i x) := by
  choose K hK hfK using hf
  exact ⟨Set.pi Set.univ K, isCompact_univ_pi hK,
    (Filter.eventually_all.2 hfK).mono fun _ hx ↦ fun i _ ↦ hx i⟩
