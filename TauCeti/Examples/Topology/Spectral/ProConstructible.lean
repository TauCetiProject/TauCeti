/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Spectral.ProConstructible
import Mathlib.Topology.Order.UpperLowerSetTopology
import Mathlib.Topology.WithTopology

/-!
# Worked examples: the constructible topology of the Sierpiński space

The Sierpiński space `Prop` (with `{True}` its only nontrivial open subset) is the smallest space
on which the constructible topology differs from the given one.

* Its constructible topology is discrete, as `WithConstructibleTopology.instTotallySeparatedSpace`
  predicts for a finite T₀ prespectral space.
* The identity from the constructible topology to `Prop` is a spectral bijection that is neither
  generalizing nor a quotient map. So the generalizing hypothesis of
  `IsSpectralMap.isQuotientMap_of_generalizingMap` cannot be dropped.
-/

open Topology

namespace TauCeti

/-- The constructible topology of the Sierpiński space is discrete. -/
example : DiscreteTopology (WithConstructibleTopology Prop) := inferInstance

/-- The identity from the constructible topology of the Sierpiński space to the Sierpiński space
is a spectral bijection, but it is not generalizing and not a quotient map. -/
example : IsSpectralMap (WithTopology.ofTopology : WithConstructibleTopology Prop → Prop) ∧
    Function.Bijective (WithTopology.ofTopology : WithConstructibleTopology Prop → Prop) ∧
    ¬ GeneralizingMap (WithTopology.ofTopology : WithConstructibleTopology Prop → Prop) ∧
    ¬ IsQuotientMap (WithTopology.ofTopology : WithConstructibleTopology Prop → Prop) := by
  -- In `Prop` an open set is an upper set, and `False ≤ True`.
  have hup {s : Set Prop} (hs : IsOpen s) (hFs : False ∈ s) : True ∈ s :=
    Topology.IsUpperSet.isOpen_iff_isUpperSet.1 hs (fun h ↦ h.elim : False ≤ True) hFs
  -- So `{False}` is not open, while `True ⤳ False`.
  have hF : ¬ IsOpen ({False} : Set Prop) := fun h ↦ by simpa using hup h rfl
  refine ⟨⟨continuous_ofTopology_withConstructibleTopology Prop,
    fun _ _ _ ↦ (Set.toFinite _).isCompact⟩, WithTopology.ofTopology_bijective _, fun hg ↦ ?_,
    fun hq ↦ hF (hq.isOpen_preimage.1 (isOpen_discrete _))⟩
  -- The specialization `True ⤳ False` does not lift to the discrete constructible topology.
  obtain ⟨y, hy, hyT⟩ := hg (a := WithTopology.toTopology _ False)
    (specializes_iff_forall_open.2 fun _ ↦ hup)
  simp [hy.eq] at hyT

end TauCeti
