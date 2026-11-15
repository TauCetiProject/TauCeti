/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.MinimalProjectivePresentation.Existence
public import TauCeti.Algebra.Module.Projective.FinitePresentation

/-!
# Finite minimal projective presentations

Over a semiprimary Noetherian ring, a finitely generated module has a minimal presentation
by finitely generated projectives. This file packages that presentation using
`FiniteProjectivePresentation`, retaining the minimality proof needed to form an
Auslander–Reiten translate independent of choices up to actual isomorphism.

The ring need only be small in the universe of the module. The construction cuts projective
covers out of finite projective surjections, so both covering modules stay in that universe.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Sections I.2 and IV.1.
-/

public section

namespace TauCeti.FiniteProjectivePresentation

universe u v

variable {A : Type u} [Ring A] [IsSemiprimaryRing A] [IsNoetherianRing A]
  {M : ModuleCat.{v} A} [Module.Finite A M] [Small.{v} A]

/-- A finitely generated module over a semiprimary Noetherian ring has a finite minimal
projective presentation in its own universe. -/
theorem exists_isMinimal :
    ∃ P : FiniteProjectivePresentation M, IsMinimalProjectivePresentation P.p P.π := by
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  let F := ofFinitePresentation (M := M)
  obtain ⟨P₀, h₀⟩ := exists_isProjectiveCover_comp_subtype F.π F.surjective
  let π := F.π ∘ₗ P₀.subtype
  have : Module.Finite A ↥P₀ := h₀.finite
  have : Module.FinitePresentation A ↥(LinearMap.ker π) :=
    Module.finitePresentation_of_finite A _
  let K := ofFinitePresentation (M := ModuleCat.of A ↥(LinearMap.ker π))
  obtain ⟨P₁, h₁⟩ := exists_isProjectiveCover_comp_subtype K.π K.surjective
  let c := K.π ∘ₗ P₁.subtype
  have : Module.Finite A ↥P₁ := h₁.finite
  have : Module.Projective A ↥P₀ := h₀.projective
  have : Module.Projective A ↥P₁ := h₁.projective
  have h := h₀.isMinimalProjectivePresentation h₁
  exact ⟨⟨ModuleCat.of A ↥P₀, ModuleCat.of A ↥P₁,
    (LinearMap.ker π).subtype ∘ₗ c, π, h.exact, h.surjective⟩, h⟩

/-- A chosen finite minimal projective presentation. Its minimality is recorded by
`isMinimal_minimal`; constructions using it should provide independence of this choice. -/
noncomputable def minimal : FiniteProjectivePresentation M :=
  exists_isMinimal.choose

/-- The chosen finite projective presentation is minimal. -/
theorem isMinimal_minimal :
    IsMinimalProjectivePresentation (minimal (M := M)).p (minimal (M := M)).π :=
  exists_isMinimal.choose_spec

end TauCeti.FiniteProjectivePresentation
