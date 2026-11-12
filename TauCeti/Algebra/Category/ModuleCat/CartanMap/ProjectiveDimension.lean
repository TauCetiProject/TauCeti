/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic

/-!
# Finite projective dimension and the Cartan map

Over a left Noetherian ring, a finitely generated module of projective dimension at most `n`
admits a resolution of length at most `n` by finitely generated projectives. Successive finite
free surjections have finitely generated kernels, and dimension shifting makes the last kernel
projective.

Consequently, if every finitely generated module has finite projective dimension, the Cartan map
is bijective. No uniform bound is required. In particular this applies when the projective
dimensions of all modules have a common finite bound.

## References

* Charles A. Weibel, *The K-book*, Chapter II, Section 7, for the resolution theorem.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.2 and 4.1, for finite
  projective resolutions and dimension shifting.

The induction refines Mathlib's
`CategoryTheory.ObjectProperty.hasFiniteResolutionOfLength.iff_hasProjectiveDimensionLE`
by choosing finite free covers, retaining finite generation, and constructing explicit
`TauCeti.ExactStructure.FiniteResolution` data. The dimension-shifting step uses
`CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- A finite projective-dimension bound on a finitely generated module over a left Noetherian
ring is realized by a finite resolution of the same length bound, with finitely generated
projective terms. -/
theorem exists_finiteProjectiveResolution_of_hasProjectiveDimensionLE
    {M : ModuleCat.{u} R} [Module.Finite R M] {n : ℕ} (hM : HasProjectiveDimensionLE M n) :
    ∃ r : (ExactStructure.abelian (ModuleCat.{u} R)).FiniteResolution
      (finiteProjectiveModules R) M, r.length ≤ n := by
  induction n generalizing M with
  | zero =>
    have : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).2 hM
    have : Module.Projective R M := ModuleCat.projective_of_module_projective M
    exact ⟨.base (finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩), by simp⟩
  | succ n ih =>
    obtain ⟨d, f, hf⟩ := Module.Finite.exists_fin' R M
    let S := f.shortComplexKer
    have hS : S.ShortExact := f.shortExact_shortComplexKer hf
    have : Module.Finite R S.X₁ := inferInstanceAs (Module.Finite R f.ker)
    have : Projective S.X₂ := ModuleCat.projective_of_categoryTheory_projective _
    obtain ⟨r, hr⟩ := ih ((hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).1 hM)
    exact ⟨.step (finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩)
      S.f S.g S.zero ((ExactStructure.abelian_conflation S).2 hS) r, by simpa using hr⟩

/-- Finite projective dimension of every finitely generated module supplies the finite-resolution
hypothesis of the Cartan comparison theorem. The bound may depend on the module. -/
theorem finiteModules_le_admitsFiniteResolution_of_finite_projectiveDimension
    (h : ∀ M : ModuleCat.{u} R, Module.Finite R M → ∃ n, HasProjectiveDimensionLE M n) :
    ModuleCat.isFG R ≤ (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
      (finiteProjectiveModules R) := by
  intro M hM
  have : Module.Finite R M := (ModuleCat.isFG_iff M).1 hM
  obtain ⟨n, hn⟩ := h M inferInstance
  obtain ⟨r, _⟩ := exists_finiteProjectiveResolution_of_hasProjectiveDimensionLE hn
  exact (ExactStructure.admitsFiniteResolution_iff _ _).2 ⟨r⟩

/-- The Cartan map is bijective over a left Noetherian ring when every finitely generated module
has finite projective dimension. In particular, finite global dimension suffices. -/
theorem cartanMap_bijective_of_finite_projectiveDimension
    (h : ∀ M : ModuleCat.{u} R, Module.Finite R M → ∃ n, HasProjectiveDimensionLE M n) :
    Function.Bijective (cartanMap R) :=
  cartanMap_bijective R
    (finiteModules_le_admitsFiniteResolution_of_finite_projectiveDimension h)

end TauCeti
