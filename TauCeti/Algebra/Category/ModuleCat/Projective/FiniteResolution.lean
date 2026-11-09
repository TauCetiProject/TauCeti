/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.ProjectiveDimension
public import TauCeti.CategoryTheory.Exact.Resolution.ProjectiveResolution

/-!
# Finite projective resolutions of modules of finite projective dimension

Over a left Noetherian ring, a finitely generated module `M` of projective dimension at most `n`
has a projective resolution `F → M`, in the sense of Mathlib's
`CategoryTheory.ProjectiveResolution`, whose terms are finitely generated projective modules and
vanish above degree `n`. The minimal finite free refinement over a Noetherian local ring is
provided in `TauCeti.Algebra.Category.ModuleCat.Projective.MinimalResolution.ChainComplex`.

This is the form in which a bound on the projective dimension of a module, such as the residue
field of a local ring, enters arguments with explicit resolutions: comparison maps into the
resolution are chain maps of projective resolutions, and over a local ring the ranks of its terms
are defined.

The resolution is the chain complex of the finite resolution of
`TauCeti.exists_finiteProjectiveResolution_of_hasProjectiveDimensionLE`, obtained by iterating
finite free surjections and dimension shifting, made into a projective resolution by
`TauCeti.ExactStructure.FiniteResolution.toProjectiveResolution`.

## Main results

* `ModuleCat.exists_projectiveResolution_finite`: over a left Noetherian ring, a finite module of
  projective dimension at most `n` has a projective resolution by finite projective modules
  vanishing above degree `n`.

## References

* [Stacks Project, Tag 0CXF](https://stacks.math.columbia.edu/tag/0CXF).
* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 4.1, for projective
  dimension and dimension shifting.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TauCeti.ExactStructure.FiniteResolution

/-- Converting a finite resolution by finite projective modules to a projective resolution
preserves finiteness of every term, including the zero terms above its length. -/
theorem finite_toProjectiveResolution_X {R : Type u} [Ring R] {M : ModuleCat.{u} R}
    (r : (ExactStructure.abelian (ModuleCat.{u} R)).FiniteResolution
      (finiteProjectiveModules R) M)
    (hP : finiteProjectiveModules R ≤ CategoryTheory.isProjective (ModuleCat.{u} R)) (i : ℕ) :
    Module.Finite R ((r.toProjectiveResolution hP).complex.X i) := by
  have : Module.Finite R (r.term i) := by
    by_cases hi : i ≤ r.length
    · exact (finiteProjectiveModules_iff.mp (r.prop_term_of_le_length hi)).1
    · have : Subsingleton (r.term i) :=
        ModuleCat.isZero_iff_subsingleton.mp (r.isZero_term_of_length_lt (by omega))
      infer_instance
  exact Module.Finite.equiv (r.toProjectiveResolutionXIso hP i).toLinearEquiv.symm

end TauCeti.ExactStructure.FiniteResolution

namespace ModuleCat

/-- **Finite projective resolutions.** Over a left Noetherian ring, a finitely generated module
of projective dimension at most `n` has a projective resolution whose terms are finitely
generated and vanish above degree `n`. -/
theorem exists_projectiveResolution_finite {R : Type u} [Ring R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] {n : ℕ} (hM : HasProjectiveDimensionLE M n) :
    ∃ F : ProjectiveResolution M,
      (∀ i, Module.Finite R (F.complex.X i)) ∧ ∀ i, n < i → IsZero (F.complex.X i) := by
  obtain ⟨r, hr⟩ := TauCeti.exists_finiteProjectiveResolution_of_hasProjectiveDimensionLE hM
  have hP := TauCeti.finiteProjectiveModules_le_categoryTheory_isProjective R
  exact ⟨r.toProjectiveResolution hP, r.finite_toProjectiveResolution_X hP, fun i hi ↦
    r.isZero_toProjectiveResolution_X_of_length_lt hP (by omega)⟩

end ModuleCat
