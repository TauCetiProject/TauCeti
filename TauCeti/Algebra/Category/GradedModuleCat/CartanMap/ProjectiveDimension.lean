/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Resolution
public import TauCeti.Algebra.Category.GradedModuleCat.Free

/-!
# Finite projective dimension and the graded Cartan map

A finitely generated graded module over a left Noetherian graded algebra has a finite resolution
by finitely generated graded projectives whenever its underlying module has finite projective
dimension. The resolution has length at most the underlying projective-dimension bound. Finite
graded free surjections retain the internal grading at every step; Noetherianity keeps the
syzygies finitely generated, and ungraded dimension shifting makes the last syzygy projective.

Thus a pointwise finite projective-dimension hypothesis on the underlying modules suffices for
the graded Cartan isomorphism over `ℤ[q,q⁻¹]`. No uniform bound, nonnegative grading, or
semisimplicity of the degree-zero algebra is required.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded free
  presentations and graded projectives.
* Charles A. Weibel, *The K-book*, Chapter II, Section 7, for the resolution theorem.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 4.1, for dimension shifting.

The induction refines Mathlib's
`CategoryTheory.ObjectProperty.hasFiniteResolutionOfLength.iff_hasProjectiveDimensionLE`
by using `TauCeti.GradedModuleCat.exists_finite_free_surjection` and retaining finite generation
and internal degrees. Dimension shifting uses
`CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff` on the underlying
short exact sequence.
-/

public section

open scoped DirectSum

namespace TauCeti

open CategoryTheory

universe uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [IsNoetherianRing A]

/-- A projective-dimension bound on the underlying module is realized by a finite resolution
with finitely generated graded-projective terms and the same length bound. -/
theorem exists_gradedFiniteProjectiveResolution_of_hasProjectiveDimensionLE
    {M : GradedModuleCat.{uA} 𝒜} [Module.Finite A M] {n : ℕ}
    (hM : HasProjectiveDimensionLE (GradedModuleCat.toModuleCat.obj M) n) :
    ∃ r : (gradedModuleCanonicalExactStructure 𝒜).toExactStructure.FiniteResolution
      (gradedFiniteProjectiveModules 𝒜) M, r.length ≤ n := by
  induction n generalizing M with
  | zero =>
    have : Projective (GradedModuleCat.toModuleCat.obj M) :=
      (projective_iff_hasProjectiveDimensionLE_zero _).2 hM
    have : Module.Projective A M :=
      ModuleCat.projective_of_module_projective (GradedModuleCat.toModuleCat.obj M)
    exact ⟨.base (gradedFiniteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩), by simp⟩
  | succ n ih =>
    obtain ⟨I, _, d, π, hπ⟩ := GradedModuleCat.exists_finite_free_surjection M
    have : Module.Finite A (GradedModuleCat.kernelObj π) :=
      inferInstanceAs (Module.Finite A (LinearMap.ker π.hom))
    let S := ShortComplex.mk (GradedModuleCat.kernelι π) π
      (GradedModuleCat.kernelι_comp π)
    have hS : S.ShortExact :=
      { exact := GradedModuleCat.exact_iff.2 (by
          simpa [S, GradedModuleCat.hom_kernelι] using LinearMap.exact_subtype_ker_map π.hom)
        mono_f := (GradedModuleCat.mono_iff_injective _).2 (by
          simp [S, GradedModuleCat.hom_kernelι])
        epi_g := (GradedModuleCat.epi_iff_surjective _).2 hπ }
    have : Module.Projective A (GradedModuleCat.free 𝒜 d) :=
      inferInstanceAs (Module.Projective A (⨁ _ : I, A))
    -- Retype the underlying free module at the mapped short-complex term for instance search.
    have : Projective (S.map GradedModuleCat.toModuleCat).X₂ := by
      have : Module.Projective A (S.map GradedModuleCat.toModuleCat).X₂ :=
        ‹Module.Projective A (GradedModuleCat.free 𝒜 d)›
      exact ModuleCat.projective_of_categoryTheory_projective _
    have hK := ((hS.map_of_exact GradedModuleCat.toModuleCat).hasProjectiveDimensionLT_X₃_iff
      n inferInstance).1 hM
    obtain ⟨r, hr⟩ := ih hK
    have hconf : (gradedModuleCanonicalExactStructure 𝒜).Conflation S := by
      rw [gradedModuleCanonicalExactStructure, GradedExactStructure.abelian_toExactStructure,
        ExactStructure.abelian_conflation]
      exact hS
    exact ⟨.step (gradedFiniteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩)
      S.f S.g S.zero hconf r, by simpa using hr⟩

/-- Pointwise finite projective dimension of the underlying finite graded modules supplies the
finite graded-resolution hypothesis of the graded Cartan comparison theorem. -/
theorem gradedFiniteModules_le_admitsFiniteResolution_of_finite_projectiveDimension
    (h : ∀ M : GradedModuleCat.{uA} 𝒜, Module.Finite A M →
      ∃ n, HasProjectiveDimensionLE (GradedModuleCat.toModuleCat.obj M) n) :
    gradedFiniteModules 𝒜 ≤ (gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution
      (gradedFiniteProjectiveModules 𝒜) := by
  intro M hM
  have : Module.Finite A M := gradedFiniteModules_iff.1 hM
  obtain ⟨n, hn⟩ := h M inferInstance
  obtain ⟨r, _⟩ := exists_gradedFiniteProjectiveResolution_of_hasProjectiveDimensionLE hn
  exact (ExactStructure.admitsFiniteResolution_iff _ _).2 ⟨r⟩

/-- The graded Cartan map is bijective when the underlying finite graded modules have finite
projective dimension over the left Noetherian algebra. Finite ungraded global dimension suffices;
no separate bound on graded projective dimension is assumed. -/
theorem gradedCartanMap_bijective_of_finite_projectiveDimension
    (h : ∀ M : GradedModuleCat.{uA} 𝒜, Module.Finite A M →
      ∃ n, HasProjectiveDimensionLE (GradedModuleCat.toModuleCat.obj M) n) :
    Function.Bijective (gradedCartanMap 𝒜) :=
  gradedCartanMap_bijective 𝒜
    (gradedFiniteModules_le_admitsFiniteResolution_of_finite_projectiveDimension h)

end TauCeti
