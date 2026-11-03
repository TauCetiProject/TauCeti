/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Projective.MinimalResolution.Basic
public import TauCeti.Algebra.Category.ModuleCat.Projective.FiniteResolution

/-!
# Bounded minimal free chain resolutions

Over a Noetherian local ring `(R, 𝔪)`, a finite module of projective dimension at most `n`
has a projective resolution by finite free modules, zero above degree `n`, with every
unaugmented differential landing in `𝔪` times its target. Such resolutions are used to compare
Koszul complexes with resolutions of the residue field: reduction modulo `𝔪` kills all the
resolution differentials.

This file identifies the recursive minimality condition on a finite resolution with the
condition on the differentials of its spliced chain complex. It then converts the minimal
finite projective resolution into Mathlib's `CategoryTheory.ProjectiveResolution`, retaining
both minimality and the length bound.

## References

* The Stacks Project, Lemma 10.102.2 (00MT), minimal finite free resolutions.
* Winfried Bruns and Jürgen Herzog, *Cohen–Macaulay Rings*, Section 1.3.
-/

public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v

namespace TauCeti.ExactStructure.FiniteResolution

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {E : ExactStructure (ModuleCat.{v} R)} {P : ObjectProperty (ModuleCat.{v} R)}

/-- Every differential of a minimal finite resolution lands in the maximal ideal times its
target. The augmentation is not included. -/
theorem IsMinimal.range_d_le {M : ModuleCat.{v} R} {r : FiniteResolution E P M}
    (hr : r.IsMinimal) (n : ℕ) :
    LinearMap.range (r.d n).hom ≤ maximalIdeal R • ⊤ := by
  induction hr generalizing n with
  | base hM => simp
  | step hQ i p zero hp hi hr ih =>
    cases n with
    | zero =>
      simpa only [d_step_zero, ModuleCat.hom_comp] using
        (LinearMap.range_comp_le_range _ i.hom).trans hi
    | succ n => simpa only [d_step_succ] using ih n

/-- Recursive minimality is equivalent to the differential condition on the associated chain
complex, for any exact structure on modules. -/
theorem isMinimal_iff_forall_range_d_le {M : ModuleCat.{v} R}
    (r : FiniteResolution E P M) :
    r.IsMinimal ↔ ∀ n, LinearMap.range (r.d n).hom ≤ maximalIdeal R • ⊤ := by
  refine ⟨fun hr ↦ hr.range_d_le, ?_⟩
  induction r with
  | base hM => exact fun _ ↦ .base hM
  | step hQ i p zero hp r ih =>
    intro h
    have hi := h 0
    have : Epi r.aug := r.isDeflation_aug.epi
    have haug : LinearMap.range r.aug.hom = ⊤ :=
      LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective r.aug).mp inferInstance)
    simp only [d_step_zero, ModuleCat.hom_comp,
      LinearMap.range_comp_of_range_eq_top i.hom haug] at hi
    exact .step hQ i p zero hp hi (ih fun n ↦ by simpa only [d_step_succ] using h (n + 1))

end TauCeti.ExactStructure.FiniteResolution

namespace ModuleCat

/-- A finite module over a Noetherian local ring with projective dimension at most `n` has a
minimal finite free projective resolution of length at most `n`: all terms are finite free,
all terms above degree `n` vanish, and every differential lands in the maximal ideal times
its target. -/
theorem exists_projectiveResolution_finite_free_minimal {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M] {n : ℕ}
    (hM : HasProjectiveDimensionLE M n) :
    ∃ F : ProjectiveResolution M,
      (∀ i, Module.Finite R (F.complex.X i) ∧ Module.Free R (F.complex.X i)) ∧
      (∀ i, n < i → IsZero (F.complex.X i)) ∧
      ∀ i, LinearMap.range (F.complex.d (i + 1) i).hom ≤ maximalIdeal R • ⊤ := by
  obtain ⟨r, hr, hmin⟩ :=
    TauCeti.exists_minimal_finiteProjectiveResolution_of_hasProjectiveDimensionLE hM
  have hP := TauCeti.finiteProjectiveModules_le_categoryTheory_isProjective R
  refine ⟨r.toProjectiveResolution hP, fun i ↦ ?_, fun i hi ↦
    r.isZero_toProjectiveResolution_X_of_length_lt hP (by omega),
    fun i ↦ ?_⟩
  · have := r.finite_toProjectiveResolution_X hP i
    exact ⟨inferInstance, Module.free_of_flat_of_isLocalRing⟩
  · simp only [TauCeti.ExactStructure.FiniteResolution.toProjectiveResolution_complex_d,
      ModuleCat.hom_comp]
    rw [LinearMap.comp_assoc, LinearMap.range_comp]
    exact Submodule.map_le_iff_le_comap.mpr <|
      ((LinearMap.range_comp_le_range _ _).trans (hmin.range_d_le i)).trans <|
        Submodule.smul_top_le_comap_smul_top _ _

end ModuleCat
