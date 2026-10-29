/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.AdicHom.Basic
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Basic

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

/-!
# Topologically finite type homomorphisms are adic

A topologically finite type homomorphism of Huber rings is continuous and preserves open ideals,
so it is adic. This allows finite type presentations to supply adic homomorphisms without
choosing compatible rings of definition again.
-/

public section

namespace TauCeti.Huber

/-- A topologically finite type homomorphism of Huber rings is adic. -/
theorem IsTopologicallyFiniteType.isAdicHom {A B : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] {f : A →+* B} (hf : IsTopologicallyFiniteType f) :
    IsAdicHom f := by
  obtain ⟨k, T, hfinite, hT, π, hπ, _⟩ := isTopologicallyFiniteType_iff.mp hf
  have : IsHuberRing B := IsHuberRing.of_isOpenQuotientMap hπ
  exact IsAdicHom.of_continuous_isOpen_map hf.continuous fun _ hI ↦ hf.isOpen_map hI

end TauCeti.Huber
