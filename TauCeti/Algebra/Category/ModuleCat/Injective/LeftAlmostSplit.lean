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

/-!
# The left almost split map out of an indecomposable injective module

An injective module `N` with a local endomorphism ring is uniform: any two nonzero submodules meet
nontrivially (`TauCeti.inf_ne_bot_of_isLocalRing_end`). If `N` is moreover Artinian, it therefore
has a smallest nonzero submodule `S`, which is simple, and the quotient map `N ⟶ N ⧸ S` is left
almost split (`TauCeti.exists_isAtom_isLeftAlmostSplit_ofHom_mkQ`). A morphism out of `N` that is
not a split monomorphism is not injective, so its kernel contains `S`.

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

/-- An injective module with a local endomorphism ring is uniform: two nonzero submodules meet
nontrivially. -/
theorem inf_ne_bot_of_isLocalRing_end [IsLocalRing (End N)] {S U : Submodule A N} (hS : S ≠ ⊥)
    (hU : U ≠ ⊥) : S ⊓ U ≠ ⊥ := by
  -- If `S` and `U` were disjoint, injectivity would extend the projection of `S ⊕ U` onto `S` to an
  -- endomorphism `φ` of `N`. Then `φ` vanishes on `U` and `1 - φ` vanishes on `S`, so neither is
  -- invertible.
  intro hSU
  have hdisj : Disjoint S U := disjoint_iff.mpr hSU
  -- The inclusion of `S × U` into `N`, and the projection of `S × U` to `S ⊆ N`.
  let j : ModuleCat.of A (S × U) ⟶ N := ModuleCat.ofHom (LinearMap.coprod S.subtype U.subtype)
  have hj : Function.Injective j := by
    rw [← LinearMap.ker_eq_bot]
    exact LinearMap.ker_coprod_of_disjoint_range _ _ (by simpa using hdisj) |>.trans (by simp)
  have : Mono j := (ModuleCat.mono_iff_injective j).mpr hj
  let φ : N ⟶ N := Injective.factorThru (ModuleCat.ofHom (S.subtype ∘ₗ LinearMap.fst A S U)) j
  have hφ (x : S × U) : φ (x.1 + x.2 : N) = x.1 := by
    have hcomp : j ≫ φ = ModuleCat.ofHom (S.subtype ∘ₗ LinearMap.fst A S U) :=
      Injective.comp_factorThru _ _
    simpa [j] using ConcreteCategory.congr_hom hcomp x
  have hnotIso {f : N ⟶ N} {T : Submodule A N} (hT : T ≠ ⊥) (hf : ∀ x ∈ T, f x = 0) :
      ¬ IsIso f := by
    intro _
    obtain ⟨x, hx, hx0⟩ := T.exists_mem_ne_zero_of_ne_bot hT
    exact hx0 ((ModuleCat.mono_iff_injective f).mp inferInstance (by simp [hf x hx]))
  have hφU : ¬ IsIso φ := hnotIso hU fun x hx ↦ by simpa using hφ (0, ⟨x, hx⟩)
  have hφS : ¬ IsIso (𝟙 N - φ) := hnotIso hS fun x hx ↦ by
    simpa [sub_eq_zero] using (hφ (⟨x, hx⟩, 0)).symm
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (End.of φ) with h | h
  · exact hφU ((isUnit_iff_isIso _).mp h)
  · exact hφS ((isUnit_iff_isIso _).mp h)

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
  have : Nontrivial N := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact one_ne_zero (α := End N)
      (End.ext (ModuleCat.hom_ext (LinearMap.ext fun _ ↦ Subsingleton.elim _ _)))
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule A N)
  refine ⟨S, hS, isLeftAlmostSplit_ofHom_mkQ hS.1 fun U hU ↦ ?_⟩
  exact inf_eq_left.mp ((hS.le_iff.mp inf_le_left).resolve_left
    (inf_ne_bot_of_isLocalRing_end hS.1 hU))

end TauCeti
