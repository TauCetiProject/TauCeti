/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import TauCeti.Algebra.Category.GradedModuleCat.Projective
public import TauCeti.Algebra.Module.GradedModule.Resolution

/-!
# Concrete graded resolutions as categorical projective resolutions

A `TauCeti.GradedProjectiveResolution` records projective modules, homogeneous differentials,
and an exact augmentation as linear maps. This file turns that data into a
`CategoryTheory.ProjectiveResolution` in `TauCeti.GradedModuleCat`. Its terms retain their
internal gradings, and its differentials and augmentation are the original maps.

The resulting resolution can be used directly with Mathlib's comparison maps, uniqueness up to
chain homotopy, and computation of Ext from projective resolutions. No enough-projectives
hypothesis is needed to bundle a given resolution. The construction imposes neither linearity,
minimality, finite generation, nor boundedness.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.2 and 2.4.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}
  {M : GradedModuleCat.{v} 𝒜}

namespace GradedProjectiveResolution

variable (r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading)

/-- A term of a concrete graded resolution, with its specified internal grading. -/
abbrev termObj (n : ℕ) : GradedModuleCat.{v} 𝒜 where
  carrier := r.X n
  grading := r.grading n

/-- The differential of a concrete graded resolution as a morphism of graded modules. -/
abbrev differential (n : ℕ) : r.termObj (n + 1) ⟶ r.termObj n :=
  GradedModuleCat.ofHom (r.d n) (r.isHomogeneous_d n)

/-- The augmentation of a concrete graded resolution as a morphism of graded modules. -/
abbrev augmentation : r.termObj 0 ⟶ M :=
  GradedModuleCat.ofHom r.π r.isHomogeneous_π

@[reassoc (attr := simp)]
theorem differential_comp_differential (n : ℕ) :
    r.differential (n + 1) ≫ r.differential n = 0 :=
  GradedModuleCat.hom_ext (r.exact_d_d n).linearMap_comp_eq_zero

@[reassoc (attr := simp)]
theorem differential_zero_comp_augmentation : r.differential 0 ≫ r.augmentation = 0 :=
  GradedModuleCat.hom_ext r.exact_d_π.linearMap_comp_eq_zero

private noncomputable def complex : ChainComplex (GradedModuleCat.{v} 𝒜) ℕ :=
  ChainComplex.of r.termObj r.differential r.differential_comp_differential

private theorem complex_d (n : ℕ) :
    r.complex.d (n + 1) n = r.differential n := by
  simp [complex]

private noncomputable def complexπ :
    r.complex ⟶ (ChainComplex.single₀ (GradedModuleCat.{v} 𝒜)).obj M :=
  (r.complex.toSingle₀Equiv M).symm
    ⟨r.augmentation, by rw [complex_d]; exact r.differential_zero_comp_augmentation⟩

private theorem complexπ_f_zero : r.complexπ.f 0 = r.augmentation :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

variable [DirectSum.Decomposition 𝒜]

/-- A concrete graded projective resolution is a categorical projective resolution in the
category of graded modules. The quasi-isomorphism is its original augmentation. -/
noncomputable def toProjectiveResolution : ProjectiveResolution M where
  complex := r.complex
  projective n := by
    let := r.projective n
    exact inferInstanceAs (Projective (r.termObj n))
  π := r.complexπ
  quasiIso := by
    constructor
    intro n
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      constructor
      · rw [GradedModuleCat.exact_iff]
        -- Reduce the short-complex projections before rewriting the concrete maps.
        change Function.Exact (r.complex.d 1 0).hom (r.complexπ.f 0).hom
        rw [complex_d, complexπ_f_zero]
        exact r.exact_d_π
      · exact (GradedModuleCat.epi_iff_surjective r.augmentation).mpr r.surjective_π
    | succ n =>
      rw [quasiIsoAt_iff_exactAt'
        (hL := ChainComplex.exactAt_succ_single_obj ..),
        HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
        GradedModuleCat.exact_iff]
      -- `exactAt_iff'` uses short-complex projections; expose just its two maps.
      change Function.Exact (r.complex.d (n + 2) (n + 1)).hom
        (r.complex.d (n + 1) n).hom
      rw [complex_d, complex_d]
      exact r.exact_d_d n

/-- The terms of the categorical resolution are the original graded modules. -/
noncomputable def toProjectiveResolutionXIso (n : ℕ) :
    r.toProjectiveResolution.complex.X n ≅ r.termObj n :=
  Iso.refl _

/-- The categorical differential is the original differential, through the term identifications. -/
@[simp]
theorem toProjectiveResolution_complex_d (n : ℕ) :
    r.toProjectiveResolution.complex.d (n + 1) n =
      (r.toProjectiveResolutionXIso (n + 1)).hom ≫ r.differential n ≫
        (r.toProjectiveResolutionXIso n).inv := by
  -- Expose the identity identifications and their endpoints to the category identity laws.
  change r.complex.d (n + 1) n =
    𝟙 (r.termObj (n + 1)) ≫ r.differential n ≫ 𝟙 (r.termObj n)
  rw [Category.id_comp, Category.comp_id]
  exact r.complex_d n

/-- The categorical augmentation is the original augmentation, through the term identification. -/
@[simp]
theorem toProjectiveResolution_π_f_zero :
    r.toProjectiveResolution.π.f 0 =
      (r.toProjectiveResolutionXIso 0).hom ≫ r.augmentation := by
  -- Expose the identity identification so the category identity law can rewrite it.
  change r.complexπ.f 0 = 𝟙 (r.termObj 0) ≫ r.augmentation
  rw [Category.id_comp]
  exact r.complexπ_f_zero

end GradedProjectiveResolution

end TauCeti
