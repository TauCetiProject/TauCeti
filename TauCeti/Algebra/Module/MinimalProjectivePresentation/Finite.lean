/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.MinimalProjectivePresentation.Existence
public import TauCeti.Algebra.Module.Projective.FinitePresentation
public import TauCeti.Algebra.Module.ProjectiveCover.Semiperfect

/-!
# Finite minimal projective presentations

Over a semiperfect ring, a finitely presented module has a minimal presentation by finitely
generated projectives. This covers finitely generated modules over a semiprimary Noetherian ring,
such as an Artin algebra. This file packages that presentation using
`FiniteProjectivePresentation`, retaining the minimality proof needed to form an
Auslander–Reiten translate independent of choices up to actual isomorphism.

The covers come from `TauCeti.exists_isProjectiveCover_of_isSemiperfectRing`. The ring need only be
small in the universe of the module: each cover is cut out of a finite free surjection in that
universe (`TauCeti.IsProjectiveCover.exists_isProjectiveCover_comp_subtype`), so both covering
modules stay in it. Finite presentation makes the kernel of the first cover finitely generated.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Sections I.2 and IV.1.
-/

public section

namespace TauCeti.FiniteProjectivePresentation

universe u v

variable {A : Type u} [Ring A] [IsSemiperfectRing A]
  {M : ModuleCat.{v} A} [Module.FinitePresentation A M] [Small.{v} A]

/-- A finitely presented module over a semiperfect ring has a finite minimal projective
presentation in its own universe. -/
theorem exists_isMinimal :
    ∃ P : FiniteProjectivePresentation M, IsMinimalProjectivePresentation P.p P.π := by
  let F := ofFinitePresentation (M := M)
  obtain ⟨Q, _, _, q, hq⟩ := exists_isProjectiveCover_of_isSemiperfectRing (R := A) M
  obtain ⟨P₀, h₀⟩ := hq.exists_isProjectiveCover_comp_subtype F.surjective
  let π := F.π ∘ₗ P₀.subtype
  have : Module.Finite A ↥P₀ := h₀.finite
  have : Module.Projective A ↥P₀ := h₀.projective
  -- The kernel is finitely generated, as `M` is finitely presented.
  have : Module.Finite A ↥(LinearMap.ker π) :=
    Module.Finite.iff_fg.mpr (Module.FinitePresentation.fg_ker π h₀.surjective)
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin' A ↥(LinearMap.ker π)
  let e : Shrink.{v} (Fin m → A) ≃ₗ[A] (Fin m → A) := Shrink.linearEquiv A (Fin m → A)
  obtain ⟨Q', _, _, q', hq'⟩ :=
    exists_isProjectiveCover_of_isSemiperfectRing (R := A) ↥(LinearMap.ker π)
  have hge : Function.Surjective (g ∘ₗ e.toLinearMap) := hg.comp e.surjective
  obtain ⟨P₁, h₁⟩ := hq'.exists_isProjectiveCover_comp_subtype hge
  have : Module.Finite A ↥P₁ := h₁.finite
  have : Module.Projective A ↥P₁ := h₁.projective
  have h := h₀.isMinimalProjectivePresentation h₁
  exact ⟨⟨ModuleCat.of A ↥P₀, ModuleCat.of A ↥P₁,
    (LinearMap.ker π).subtype ∘ₗ (g ∘ₗ e.toLinearMap) ∘ₗ P₁.subtype, π, h.exact, h.surjective⟩, h⟩

/-- A chosen finite minimal projective presentation. Its minimality is recorded by
`isMinimal_minimal`; constructions using it should provide independence of this choice. -/
noncomputable def minimal : FiniteProjectivePresentation M :=
  exists_isMinimal.choose

/-- The chosen finite projective presentation is minimal. -/
theorem isMinimal_minimal :
    IsMinimalProjectivePresentation (minimal (M := M)).p (minimal (M := M)).π :=
  exists_isMinimal.choose_spec

end TauCeti.FiniteProjectivePresentation
