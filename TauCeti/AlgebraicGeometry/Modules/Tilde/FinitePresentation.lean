/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic

/-!
# Finite presentation of the sheaf associated with a module

A finite presentation of an `R`-module gives a finite presentation of its associated sheaf on
`Spec R`. This transfers algebraic finiteness results, such as finite presentation of Kähler
differentials, to sheaves of modules without a Noetherian hypothesis. Use Mathlib's
`presentationTilde`: its generating and relation families are precisely those of the given
module presentation.

## References

* The Stacks Project, *Properties of Schemes*, Section 28.16 (Tag 01PA).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- Finite generating and relation sets give a finite presentation of the associated sheaf. -/
instance isFinite_presentationTilde (s : Set M) (hs : Submodule.span R s = ⊤)
    (t : Set (s →₀ R))
    (ht : Submodule.span R t = LinearMap.ker (Finsupp.linearCombination R ((↑) : s → M)))
    [Finite s] [Finite t] : (presentationTilde M s hs t ht).IsFinite where
  isFiniteType_generators := ⟨by simpa [presentationTilde] using inferInstanceAs (Finite s)⟩
  isFiniteType_relations := ⟨by simpa [presentationTilde] using inferInstanceAs (Finite t)⟩

/-- The sheaf associated with a finitely presented module is finitely presented. -/
instance isFinitePresentation_tilde [Module.FinitePresentation R M] :
    (tilde M).IsFinitePresentation := by
  obtain ⟨s, hs, t, ht⟩ := Module.FinitePresentation.out (R := R) (M := M)
  let P := presentationTilde M (s : Set M) hs (t : Set (s →₀ R)) ht
  have : P.IsFinite := isFinite_presentationTilde M _ hs _ ht
  let q := P.quasicoherentData
  have : q.IsFinitePresentation := by
    refine { isFinite_presentation := ?_ }
    intro U
    dsimp [q, SheafOfModules.Presentation.quasicoherentData]
    apply +allowSynthFailures SheafOfModules.Presentation.isFinite_map
  exact SheafOfModules.IsFinitePresentation.mk (M := tilde M) ⟨q, inferInstance⟩

end

end TauCeti.AlgebraicGeometry
