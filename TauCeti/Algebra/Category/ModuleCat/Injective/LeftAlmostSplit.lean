/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.Defs
public import TauCeti.CategoryTheory.AlmostSplit.Basic
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Injective
import TauCeti.Algebra.Module.Injective.Envelope.Indecomposable

/-!
# The left almost split map out of an indecomposable injective module

An injective module `N` with a local endomorphism ring is uniform: any two nonzero submodules meet
nontrivially (`TauCeti.IsIndecomposableModule.isEssential_of_ne_bot`). If `N` is Artinian, it
therefore has a smallest nonzero submodule `S`, which is simple, and the quotient map `N ⟶ N ⧸ S`
is left almost split (`TauCeti.exists_isAtom_isLeftAlmostSplit_ofHom_mkQ`). A morphism out of `N`
that is not a split monomorphism is not injective, so its kernel contains `S`.

Indecomposable injective modules start no almost-split sequence, and this is the left almost split
map that takes the place of such a sequence at them. It is the dual of the inclusion of the radical
of an indecomposable projective module.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section V.1.
-/

public section

namespace TauCeti

open CategoryTheory

universe v w

variable {A : Type v} [Ring A] {N : ModuleCat.{w} A} [Injective N]

/-- If `S` is a nonzero submodule of an injective module `N` contained in every nonzero submodule,
the quotient map `N ⟶ N ⧸ S` is left almost split. -/
theorem isLeftAlmostSplit_ofHom_mkQ {S : Submodule A N} (hS : S ≠ ⊥)
    (hmin : ∀ U : Submodule A N, U ≠ ⊥ → S ≤ U) :
    IsLeftAlmostSplit (ModuleCat.ofHom S.mkQ) := by
  refine isLeftAlmostSplit_iff.mpr ⟨fun _ ↦ ?_, fun Z g hg ↦ ?_⟩
  · have hmono : Function.Injective S.mkQ :=
      (ModuleCat.mono_iff_injective (ModuleCat.ofHom S.mkQ)).mp inferInstance
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ] at hmono
    exact hS hmono
  · have hker : LinearMap.ker g.hom ≠ ⊥ := fun h ↦ by
      have : Mono g := (ModuleCat.mono_iff_injective g).mpr (LinearMap.ker_eq_bot.mp h)
      exact hg (IsSplitMono.mk' ⟨Injective.factorThru (𝟙 N) g, by simp⟩)
    exact ⟨ModuleCat.ofHom (S.liftQ g.hom (hmin _ hker)), ModuleCat.hom_ext (by ext; simp)⟩

/-- **The left almost split map out of an indecomposable injective module.** An Artinian injective
module `N` with a local endomorphism ring has a simple submodule `S` such that `N ⟶ N ⧸ S` is left
almost split. -/
theorem exists_isAtom_isLeftAlmostSplit_ofHom_mkQ [IsArtinian A N] [IsLocalRing (End N)] :
    ∃ S : Submodule A N, IsAtom S ∧ IsLeftAlmostSplit (ModuleCat.ofHom S.mkQ) := by
  have : Module.Injective A N := Module.injective_module_of_injective_object A N
  have := N.endRingEquiv.isLocalRing
  have hN : IsIndecomposableModule A N := isIndecomposableModule_of_isLocalRing_end
  have := hN.nontrivial
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule A N)
  exact ⟨S, hS, isLeftAlmostSplit_ofHom_mkQ hS.1 fun U hU ↦
    (hN.isEssential_of_ne_bot hU).atom_le hS⟩

end TauCeti
