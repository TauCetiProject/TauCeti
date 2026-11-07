/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Resolution.Unbounded.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Relative projective resolutions in an abelian category

For the canonical exact structure of an abelian category, splicing a relative projective
resolution gives a projective resolution in Mathlib's sense. Thus constructions made from
conflations can use Mathlib's comparison and Ext APIs, without an enough-projectives assumption
on the entire category.

The exactness argument is the unbounded counterpart of
`TauCeti.ExactStructure.FiniteResolution.toProjectiveResolution`. The quasi-isomorphism
argument follows Mathlib's `CategoryTheory.ProjectiveResolution.of`, by Markus Himmel,
Kim Morrison, Jakob von Raumer and Joël Riou.

## References

* Theo Bühler, *Exact categories*, Section 12.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 2.2.
-/

public section

namespace TauCeti.ExactStructure.ProjectiveResolution

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  (r : (ExactStructure.abelian C).ProjectiveResolution)

/-- The syzygy deflations of a relative resolution are epimorphisms. -/
instance epi_π (n : ℕ) : Epi (r.π n) :=
  ((ExactStructure.abelian_conflation _).mp (r.conflation n)).epi_g

/-- The admissible kernel maps of a relative resolution are monomorphisms. -/
instance mono_ι (n : ℕ) : Mono (r.ι n) :=
  ((ExactStructure.abelian_conflation _).mp (r.conflation n)).mono_f

/-- The terms are projective in the ordinary abelian-category sense. -/
instance projective_X (n : ℕ) : Projective (r.X n) :=
  (ExactStructure.abelian_isProjective_iff _).mp (r.projective n)

/-- Splicing preserves exactness at each resolving term before its syzygy deflation. -/
theorem exact_d_π (n : ℕ) :
    (ShortComplex.mk (r.d n) (r.π n) (r.d_comp_π n)).Exact := by
  refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk (r.d n) (r.π n) (r.d_comp_π n))
    (S₂ := ShortComplex.mk (r.ι n) (r.π n) (r.ι_π n))
    { τ₁ := r.π (n + 1), τ₂ := 𝟙 _, τ₃ := 𝟙 _, comm₁₂ := by simp [d_def] }).2 ?_
  exact ((ExactStructure.abelian_conflation _).mp (r.conflation n)).exact

/-- The spliced complex is exact in every positive degree. -/
theorem exact_d_succ_d (n : ℕ) :
    (ShortComplex.mk (r.d (n + 1)) (r.d n) (r.d_comp_d n)).Exact := by
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk (r.d (n + 1)) (r.π (n + 1)) (r.d_comp_π (n + 1)))
    (S₂ := ShortComplex.mk (r.d (n + 1)) (r.d n) (r.d_comp_d n))
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := r.ι n, comm₂₃ := by simp [d_def] }).1
      (r.exact_d_π (n + 1))

/-- Exactness of the spliced complex, in the vocabulary of homological complexes. -/
theorem exactAt_complex_succ (n : ℕ) : r.complex.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  exact (ShortComplex.exact_iff_of_iso
    (S₁ := r.complex.sc' (n + 2) (n + 1) n)
    (S₂ := ShortComplex.mk (r.d (n + 1)) (r.d n) (r.d_comp_d n))
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa only [HomologicalComplex.shortComplexFunctor'_obj_f, Iso.refl_hom,
        Category.id_comp, Category.comp_id] using (r.complex_d (n + 1)).symm)
      (by simp))).2 (r.exact_d_succ_d n)

/-- A relative projective resolution for the canonical abelian exact structure is a projective
resolution in Mathlib's sense, with the same spliced complex and augmentation. -/
noncomputable def toProjectiveResolution : CategoryTheory.ProjectiveResolution (r.Z 0) where
  complex := r.complex
  projective n := r.projective_X n
  π := r.augmentation
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      refine (ShortComplex.exact_and_epi_g_iff_of_iso
        (S₂ := ShortComplex.mk (r.d 0) (r.π 0) (r.d_comp_π 0)) ?_).2
          ⟨r.exact_d_π 0, r.epi_π 0⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simpa using (r.complex_d 0).symm) (by simp)
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
      exact r.exactAt_complex_succ n⟩

/-- The abelian realization retains the original spliced complex. -/
noncomputable def toProjectiveResolutionComplexIso : r.toProjectiveResolution.complex ≅
    r.complex := Iso.refl _

/-- The comparison of complexes identifies the abelian augmentation with the original one. -/
@[reassoc (attr := simp)]
theorem toProjectiveResolutionComplexIso_hom_comp_augmentation :
    r.toProjectiveResolutionComplexIso.hom ≫ r.augmentation = r.toProjectiveResolution.π := by
  simp [toProjectiveResolutionComplexIso, toProjectiveResolution]

end TauCeti.ExactStructure.ProjectiveResolution
