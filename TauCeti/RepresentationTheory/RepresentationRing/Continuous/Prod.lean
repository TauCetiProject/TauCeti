/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.RepresentationRing.Continuous
public import TauCeti.RepresentationTheory.FDRep.Continuous.Prod

/-!
# Product classes in the continuous representation ring

The class of a componentwise product of continuous finite-dimensional representations is the
sum of their classes in `contRepRing`. The comparison uses the actual representation isomorphism
to a categorical biproduct, followed by the defining `SplitK0` relation.
-/

public section

open TauCeti

namespace ContRepresentation

/-- A product of continuous finite-dimensional representations represents the sum of its factors
in the continuous representation ring. -/
theorem contRepRing_of_prod {𝕜 G V W : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [Monoid G] [TopologicalSpace G] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [FiniteDimensional 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)
    (hπ : Continuous π) (hρ : Continuous ρ) :
    (SplitK0.of (ContFDRep.ofContRepresentation (π.prod ρ) (π.continuous_prod ρ hπ hρ)) :
      contRepRing 𝕜 G) =
      SplitK0.of (ContFDRep.ofContRepresentation π hπ) +
        SplitK0.of (ContFDRep.ofContRepresentation ρ hρ) := by
  obtain ⟨e⟩ := π.nonempty_contFDRepIso_prod ρ hπ hρ
  rw [SplitK0.of_congr e, SplitK0.of_biprod]

end ContRepresentation
