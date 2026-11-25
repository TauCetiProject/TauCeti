/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Projective.MinimalResolution.Basic
public import TauCeti.Algebra.Category.ModuleCat.Projective.FiniteResolution
public import TauCeti.Algebra.Homology.ModuleCat.Minimal.Basic
import TauCeti.CategoryTheory.Abelian.Projective.Resolution

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
both minimality and the length bound, and provides the inductive step constructor
`CategoryTheory.ProjectiveResolution.exists_minimal_cons` over any commutative ring.

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
  | step hQ i p zero hp hi _ ih =>
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

/-- Converting a minimal finite resolution by projective modules to a projective resolution
preserves minimality of its complex. -/
theorem IsMinimal.isMinimal_toProjectiveResolution_complex {M : ModuleCat.{v} R}
    {r : (ExactStructure.abelian (ModuleCat.{v} R)).FiniteResolution P M}
    (hr : r.IsMinimal) (hP : P ≤ CategoryTheory.isProjective (ModuleCat.{v} R)) :
    (r.toProjectiveResolution hP).complex.IsMinimal := by
  rw [ChainComplex.isMinimal_iff_range_d_succ_le_maximalIdeal_smul]
  intro i
  simp only [toProjectiveResolution_complex_d, ModuleCat.hom_comp]
  rw [LinearMap.comp_assoc, LinearMap.range_comp]
  exact Submodule.map_le_iff_le_comap.mpr <|
    ((LinearMap.range_comp_le_range _ _).trans (hr.range_d_le i)).trans <|
      Submodule.smul_top_le_comap_smul_top _ _

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
      F.complex.IsMinimal := by
  obtain ⟨r, hr, hmin⟩ :=
    TauCeti.exists_minimal_finiteProjectiveResolution_of_hasProjectiveDimensionLE hM
  have hP := TauCeti.finiteProjectiveModules_le_categoryTheory_isProjective R
  refine ⟨r.toProjectiveResolution hP, fun i ↦ ?_, fun i hi ↦
    r.isZero_toProjectiveResolution_X_of_length_lt hP (by omega), ?_⟩
  · have := r.finite_toProjectiveResolution_X hP i
    exact ⟨inferInstance, Module.free_of_flat_of_isLocalRing⟩
  · exact hmin.isMinimal_toProjectiveResolution_complex hP

end ModuleCat

namespace CategoryTheory.ProjectiveResolution

private theorem range_eqToHom_comp_le {R : Type u} [CommRing R] {I : Ideal R}
    {X Y Z W : ModuleCat.{v} R} (hX : X = Y) (hW : Z = W) (f : Y ⟶ Z)
    (hf : LinearMap.range f.hom ≤ I • ⊤) :
    LinearMap.range (eqToHom hX ≫ f ≫ eqToHom hW).hom ≤ I • ⊤ := by
  subst hX hW
  simp [hf]

/-- Prepending a minimal finite-free presentation `0 → K --i--> F --p--> M → 0` to a minimal
finite-free projective resolution `Q` of `K` yields a minimal finite-free projective resolution `P`
of `M` whose truncation is isomorphic to `Q`. -/
theorem exists_minimal_cons {R : Type u} [CommRing R]
    {K F M : ModuleCat.{v} R} [Module.Finite R F] [Module.Free R F]
    (Q : ProjectiveResolution K) {i : K ⟶ F} {p : F ⟶ M}
    (hi : Function.Injective i.hom) (hip : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) (hi_min : LinearMap.range i.hom ≤ Ring.jacobson R • ⊤)
    (hQ_ff : ∀ k, Module.Finite R (Q.complex.X k) ∧ Module.Free R (Q.complex.X k))
    (hQ_min : Q.complex.IsMinimal) :
    ∃ P : ProjectiveResolution M,
      (∀ k, Module.Finite R (P.complex.X k) ∧ Module.Free R (P.complex.X k)) ∧
      P.complex.IsMinimal ∧ Nonempty (ChainComplex.truncate.obj P.complex ≅ Q.complex) := by
  have : Module.Projective R F := Module.Projective.of_free
  have : Projective F := ModuleCat.projective_of_categoryTheory_projective F
  have hip' : i ≫ p = 0 := ModuleCat.hom_ext (LinearMap.ext hip.apply_apply_eq_zero)
  have hS : (ShortComplex.mk i p hip').ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hip
      mono_f := (ModuleCat.mono_iff_injective i).2 hi
      epi_g := (ModuleCat.epi_iff_surjective p).2 hp }
  let P := Q.cons hS
  refine ⟨P, fun k ↦ ?_, ?_, ⟨Q.consTruncateIso hS⟩⟩
  · rcases k with _ | k
    · have e := (eqToIso (Q.cons_complex_X_zero hS)).symm.toLinearEquiv
      exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩
    · have := (hQ_ff k).1
      have := (hQ_ff k).2
      have e := (eqToIso (Q.cons_complex_X_succ hS k)).symm.toLinearEquiv
      exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩
  · rw [ChainComplex.isMinimal_iff_range_d_succ_le]
    rw [ChainComplex.isMinimal_iff_range_d_succ_le] at hQ_min
    rintro (_ | k)
    · rw [show (Q.cons hS).complex.d 1 0 =
          eqToHom (Q.cons_complex_X_succ hS 0) ≫ (Q.augZero ≫ i) ≫
            eqToHom (Q.cons_complex_X_zero hS).symm by simp]
      exact range_eqToHom_comp_le _ _ _ (by
        rw [ModuleCat.hom_comp]
        exact (LinearMap.range_comp_le_range _ i.hom).trans hi_min)
    · rw [show (Q.cons hS).complex.d (k + 2) (k + 1) =
          eqToHom (Q.cons_complex_X_succ hS (k + 1)) ≫ Q.complex.d (k + 1) k ≫
            eqToHom (Q.cons_complex_X_succ hS k).symm by simp]
      exact range_eqToHom_comp_le _ _ _ (hQ_min k)

end CategoryTheory.ProjectiveResolution
