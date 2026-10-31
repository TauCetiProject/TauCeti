/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.Resolution.ChainComplex

/-!
# Finite resolutions in abelian categories are projective resolutions

For the canonical exact structure of an abelian category, the conflations of a finite resolution

```text
K₁ ↪ Q₀ ↠ X,   K₂ ↪ Q₁ ↠ K₁,   …,   Kₙ ↪ Qₙ₋₁ ↠ Kₙ₋₁
```

are short exact sequences, so the spliced complex `0 ⟶ Kₙ ⟶ Qₙ₋₁ ⟶ ⋯ ⟶ Q₀` is exact in positive
degrees and its augmentation `Q₀ ⟶ X` is an epimorphism with kernel the image of `Q₁ ⟶ Q₀`.
When the resolving terms are projective, this is a projective resolution of `X` in Mathlib's
sense, bounded by the length of the resolution. This makes the recursive data produced by
dimension shifting usable with Mathlib's comparison theory of projective resolutions, which only
sees chain complexes.

## Main definitions

* `TauCeti.ExactStructure.FiniteResolution.toProjectiveResolution`: a finite resolution by
  projective objects in an abelian category, as a `CategoryTheory.ProjectiveResolution`.

## Main results

* `TauCeti.ExactStructure.FiniteResolution.exact_d_zero_aug` and
  `TauCeti.ExactStructure.FiniteResolution.exact_d_succ_d`: the augmented complex of a finite
  resolution in an abelian category is exact.
* `TauCeti.ExactStructure.FiniteResolution.toProjectiveResolution_complex_d` and
  `TauCeti.ExactStructure.FiniteResolution.toProjectiveResolution_π_f_zero`: the projective
  resolution has the differentials and augmentation of the finite resolution, through the
  identifications `TauCeti.ExactStructure.FiniteResolution.toProjectiveResolutionXIso` of its
  terms with those of the finite resolution.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace TauCeti.ExactStructure.FiniteResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {P : ObjectProperty C}

/-- The augmentation of a finite resolution in an abelian category is an epimorphism. -/
instance epi_aug {X : C} (r : (ExactStructure.abelian C).FiniteResolution P X) : Epi r.aug := by
  cases r with
  | base hX => simpa using (inferInstance : Epi (𝟙 X))
  | step hQ i p zero hp r => simpa using ((abelian_conflation _).mp hp).epi_g

/-- The augmented complex of a finite resolution in an abelian category is exact at its
degree-zero term: the kernel of the augmentation is the image of the first differential. -/
theorem exact_d_zero_aug {X : C} (r : (ExactStructure.abelian C).FiniteResolution P X) :
    (ShortComplex.mk (r.d 0) r.aug r.d_comp_aug).Exact := by
  cases r with
  | base hX =>
    exact (ShortComplex.exact_iff_mono _ (d_base hX 0)).2
      (by simpa using (inferInstance : Mono (𝟙 X)))
  | step hQ i p zero hp r =>
    -- Precomposing the inflation `i` with the epimorphism `r.aug` does not change its image.
    have h := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk (r.aug ≫ i) p (by simp [zero]))
      (S₂ := ShortComplex.mk i p zero)
      { τ₁ := r.aug, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }).2 ((abelian_conflation _).mp hp).exact
    simpa using h

/-- The complex of a finite resolution in an abelian category is exact in every positive
degree. -/
theorem exact_d_succ_d {X : C} (r : (ExactStructure.abelian C).FiniteResolution P X) (n : ℕ) :
    (ShortComplex.mk (r.d (n + 1)) (r.d n) (r.d_comp_d n)).Exact := by
  induction r generalizing n with
  | base hX => exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)
  | step hQ i p zero hp r ih =>
    cases n with
    | zero =>
      -- Postcomposing `r.aug` with the monomorphism `i` does not change its kernel.
      have : Mono i := ((abelian_conflation _).mp hp).mono_f
      have h := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
        (S₁ := ShortComplex.mk (r.d 0) r.aug r.d_comp_aug)
        (S₂ := ShortComplex.mk (r.d 0) (r.aug ≫ i) (by simp))
        { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := i }).1 r.exact_d_zero_aug
      simpa using h
    | succ n => simpa using ih n

/-- The complex of a finite resolution in an abelian category is exact in every positive
degree, in the vocabulary of homological complexes. -/
theorem exactAt_toChainComplex_succ {X : C} (r : (ExactStructure.abelian C).FiniteResolution P X)
    (n : ℕ) : r.toChainComplex.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  exact (ShortComplex.exact_iff_of_iso (S₁ := r.toChainComplex.sc' (n + 2) (n + 1) n)
    (S₂ := ShortComplex.mk _ _ (r.d_comp_d n))
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa only [HomologicalComplex.shortComplexFunctor'_obj_f, Iso.refl_hom,
        Category.id_comp, Category.comp_id] using (r.toChainComplex_d (n + 1)).symm)
      (by simp))).2 (r.exact_d_succ_d n)

/-- The augmentation kills the first differential of the complex of a finite resolution. -/
private theorem toChainComplex_d_one_zero_comp_aug {X : C}
    (r : (ExactStructure.abelian C).FiniteResolution P X) : r.toChainComplex.d 1 0 ≫ r.aug = 0 := by
  rw [toChainComplex_d, d_comp_aug]

variable (hP : P ≤ isProjective C)

/-- A finite resolution by projective objects in an abelian category is a projective resolution
in Mathlib's sense: its complex is the spliced complex of the resolution, which vanishes beyond
the length, and the quasi-isomorphism to `X` is the augmentation.

The proof that the augmentation is a quasi-isomorphism follows that of Mathlib's
`CategoryTheory.ProjectiveResolution.of` in `Mathlib/CategoryTheory/Abelian/Projective/Resolution`
(by Markus Himmel, Kim Morrison, Jakob von Raumer and Joël Riou). -/
noncomputable def toProjectiveResolution {X : C}
    (r : (ExactStructure.abelian C).FiniteResolution P X) : ProjectiveResolution X where
  complex := r.toChainComplex
  projective n := by
    by_cases hn : n ≤ r.length
    · exact hP _ (r.prop_term_of_le_length hn)
    · exact (r.isZero_term_of_length_lt (not_le.mp hn)).projective
  π := (ChainComplex.toSingle₀Equiv _ X).symm ⟨r.aug, r.toChainComplex_d_one_zero_comp_aug⟩
  quasiIso := ⟨fun n ↦ by
    cases n with
    | zero =>
      have hπ := ChainComplex.toSingle₀Equiv_symm_apply_f_zero (C := r.toChainComplex) r.aug
        r.toChainComplex_d_one_zero_comp_aug
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      refine (ShortComplex.exact_and_epi_g_iff_of_iso
        (S₂ := ShortComplex.mk _ _ r.d_comp_aug) ?_).2 ⟨r.exact_d_zero_aug, r.epi_aug⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simpa using (r.toChainComplex_d 0).symm) (by simp [hπ])
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
      exact r.exactAt_toChainComplex_succ n⟩

/-- The terms of the projective resolution are the terms of the finite resolution. -/
noncomputable def toProjectiveResolutionXIso {X : C}
    (r : (ExactStructure.abelian C).FiniteResolution P X) (n : ℕ) :
    (r.toProjectiveResolution hP).complex.X n ≅ r.term n :=
  Iso.refl _

/-- The differentials of the projective resolution are those of the finite resolution, through
the identifications of the terms. -/
@[simp]
theorem toProjectiveResolution_complex_d {X : C}
    (r : (ExactStructure.abelian C).FiniteResolution P X) (n : ℕ) :
    (r.toProjectiveResolution hP).complex.d (n + 1) n =
      (r.toProjectiveResolutionXIso hP (n + 1)).hom ≫ r.d n ≫
        (r.toProjectiveResolutionXIso hP n).inv := by
  simp [toProjectiveResolutionXIso, toProjectiveResolution]

/-- The augmentation of the projective resolution is that of the finite resolution, through the
identification of the degree-zero terms. -/
@[simp]
theorem toProjectiveResolution_π_f_zero {X : C}
    (r : (ExactStructure.abelian C).FiniteResolution P X) :
    (r.toProjectiveResolution hP).π.f 0 = (r.toProjectiveResolutionXIso hP 0).hom ≫ r.aug := by
  simpa [toProjectiveResolutionXIso, toProjectiveResolution] using
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero (C := r.toChainComplex) r.aug
      r.toChainComplex_d_one_zero_comp_aug

end TauCeti.ExactStructure.FiniteResolution
