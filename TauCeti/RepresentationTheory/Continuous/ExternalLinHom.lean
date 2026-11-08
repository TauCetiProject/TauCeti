/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LinHom.External
public import TauCeti.RepresentationTheory.Continuous.LinHom

/-!
# Comparing algebraic and continuous external Hom

For a finite-dimensional normed domain, every linear map is continuous.
`ContRepresentation.externalLinHomEquiv` makes this identification equivariant for the
two-sided Hom action. The algebraic convention puts the domain group first, whereas
`ContRepresentation.biLinHom` puts the codomain group first, so the comparison explicitly
pulls back along the factor swap. No finiteness or topology on the groups is required;
in particular the comparison applies to finite discrete groups.

This uses the existing `ContRepresentation.biLinHom` action and Mathlib's
`LinearMap.toContinuousLinearMap` equivalence.
-/

public section

namespace ContRepresentation

variable {𝕜 G H V W : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [Group G] [Group H] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [FiniteDimensional 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  (ρ : ContRepresentation 𝕜 G V) (σ : ContRepresentation 𝕜 H W)

/-- Every linear map from a finite-dimensional normed space is continuous, equivariantly
for external Hom. The swap reconciles domain-first and codomain-first group conventions. -/
noncomputable def externalLinHomEquiv :
    Representation.Equiv (Representation.externalLinHom ρ.toRepresentation σ.toRepresentation)
      ((biLinHom ρ σ).toRepresentation.comp
        (MulEquiv.prodComm (M := G) (N := H))) :=
  .mk LinearMap.toContinuousLinearMap fun p ↦ by
    ext f v
    simp [Representation.externalLinHom_apply, ContRepresentation.toMonoidHom_apply]

/-- The forward comparison is the continuous linear map with the same values. -/
@[simp]
theorem externalLinHomEquiv_apply (f : V →ₗ[𝕜] W) :
    externalLinHomEquiv ρ σ f = LinearMap.toContinuousLinearMap f :=
  (rfl)

/-- The inverse comparison forgets continuity and preserves every value. -/
@[simp]
theorem externalLinHomEquiv_symm_apply (f : V →L[𝕜] W) :
    (externalLinHomEquiv ρ σ).symm f = f.toLinearMap :=
  (rfl)

end ContRepresentation
