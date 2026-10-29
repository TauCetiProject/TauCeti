/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.ProjectiveDimension
public import TauCeti.CategoryTheory.Exact.Resolution.ProjectiveResolution
import Mathlib.RingTheory.LocalRing.Module

/-!
# Finite free resolutions of modules of finite projective dimension

Over a left Noetherian ring, a finitely generated module `M` of projective dimension at most `n`
has a projective resolution `F → M`, in the sense of Mathlib's
`CategoryTheory.ProjectiveResolution`, whose terms are finitely generated projective modules and
vanish above degree `n`. Over a Noetherian local ring these terms are free, so `M` has a finite
free resolution of length at most `n`.

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
* `ModuleCat.exists_projectiveResolution_finite_free`: over a Noetherian local ring, the terms
  of such a resolution can be taken finite free.

## References

* [Stacks Project, Tag 0CXF](https://stacks.math.columbia.edu/tag/0CXF).
* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 4.1, for projective
  dimension and dimension shifting.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleCat

/-- **Finite projective resolutions.** Over a left Noetherian ring, a finitely generated module
of projective dimension at most `n` has a projective resolution whose terms are finitely
generated and vanish above degree `n`. -/
theorem exists_projectiveResolution_finite {R : Type u} [Ring R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] {n : ℕ} (hM : HasProjectiveDimensionLE M n) :
    ∃ F : ProjectiveResolution M,
      (∀ i, Module.Finite R (F.complex.X i)) ∧ ∀ i, n < i → IsZero (F.complex.X i) := by
  obtain ⟨r, hr⟩ := TauCeti.exists_finiteProjectiveResolution_of_hasProjectiveDimensionLE hM
  have hP : TauCeti.finiteProjectiveModules R ≤ isProjective (ModuleCat.{u} R) := fun Q hQ ↦
    have := (TauCeti.finiteProjectiveModules_iff.mp hQ).2
    inferInstanceAs (Projective Q)
  refine ⟨r.toProjectiveResolution hP, fun i ↦ ?_, fun i hi ↦
    (r.isZero_term_of_length_lt (by omega)).of_iso (r.toProjectiveResolutionXIso hP i)⟩
  -- The terms up to the length are finite projective; the terms beyond it are zero.
  have : Module.Finite R (r.term i) := by
    by_cases hi : i ≤ r.length
    · exact (TauCeti.finiteProjectiveModules_iff.mp (r.prop_term_of_le_length hi)).1
    · have : Subsingleton (r.term i) :=
        isZero_iff_subsingleton.mp (r.isZero_term_of_length_lt (by omega))
      infer_instance
  exact Module.Finite.equiv (r.toProjectiveResolutionXIso hP i).toLinearEquiv.symm

/-- **Finite free resolutions.** Over a Noetherian local ring, a finitely generated module of
projective dimension at most `n` has a projective resolution whose terms are finite free modules
and vanish above degree `n`. -/
theorem exists_projectiveResolution_finite_free {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M] {n : ℕ}
    (hM : HasProjectiveDimensionLE M n) :
    ∃ F : ProjectiveResolution M,
      (∀ i, Module.Finite R (F.complex.X i) ∧ Module.Free R (F.complex.X i)) ∧
        ∀ i, n < i → IsZero (F.complex.X i) := by
  obtain ⟨F, hF, hzero⟩ := M.exists_projectiveResolution_finite hM
  refine ⟨F, fun i ↦ ?_, hzero⟩
  have := hF i
  exact ⟨inferInstance, Module.free_of_flat_of_isLocalRing⟩

end ModuleCat
