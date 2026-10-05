/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Resolution

/-!
# Ext computed from minimal graded resolutions

Write `A₊` for the sum of the strictly positive pieces of a graded algebra. If a graded
projective resolution is minimal and `A₊ N = 0`, applying graded `Hom(-, N)` kills every
differential. Thus `Extⁿ(M, N)` is the graded Hom module from the `n`th resolution term, in
every degree including zero. The augmentation supplies the degree-zero identification.

Unlike the computation from a linear resolution, this result does not assume that the terms
are generated in their homological degrees. It therefore allows Ext vanishing to detect the
maps out of the terms of a minimal resolution, the first step in recovering linearity from
diagonal Ext vanishing. No nonnegative grading, semisimplicity, finite generation, or
boundedness assumption is needed for this computation: minimality and `A₊ N = 0` suffice.

## Main definitions

* `TauCeti.GradedProjectiveResolution.IsMinimal.extLinearEquiv`: identify the graded Hom module
  from a resolution term with Ext against a target annihilated by `A₊`.

## Main results

* `TauCeti.GradedProjectiveResolution.IsMinimal.differential_comp_eq_zero`: the differentials
  vanish after applying graded Hom into a target annihilated by `A₊`.
* `TauCeti.GradedProjectiveResolution.IsMinimal.extLinearEquiv_comp_mk₀`: the identification
  is natural in targets annihilated by `A₊`, with postcomposition giving the covariant Ext map.
* `TauCeti.GradedProjectiveResolution.IsMinimal.subsingleton_ext_iff`: Ext vanishes exactly
  when the corresponding graded Hom module vanishes.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  Section 1.2, for minimal resolutions and the diagonal Ext criterion.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 2.4, for computation
  of Ext by projective resolutions.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {M N : GradedModuleCat.{v} 𝒜}

namespace GradedProjectiveResolution

variable {r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
  (hr : r.IsMinimal)
  (hN : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) = ⊥)

include hr hN

/-- Every differential of a minimal graded resolution vanishes after composition with a
map to a module annihilated by the strictly positive part of the algebra. -/
@[reassoc (attr := simp)]
theorem IsMinimal.differential_comp_eq_zero (n : ℕ) (f : r.termObj n ⟶ N) :
    r.differential n ≫ f = 0 := by
  apply GradedModuleCat.hom_ext
  have hker : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (r.X n)) ≤
      (f.hom.restrictScalars k).ker := by
    refine Submodule.smul_le.mpr fun a ha x _ ↦ ?_
    rw [LinearMap.mem_ker, LinearMap.restrictScalars_apply, map_smul]
    exact (Submodule.eq_bot_iff _).mp hN _ (Submodule.smul_mem_smul ha Submodule.mem_top)
  ext x
  exact hker ((isMinimal_iff.mp hr) n x)

variable [DirectSum.Decomposition 𝒜]

variable [HasExt.{w} (GradedModuleCat.{v} 𝒜)]

/-- A minimal graded resolution computes Ext into a module annihilated by `A₊` as graded
Hom from each resolution term. In degree zero the inverse of precomposition with the
augmentation identifies these maps with `Hom(M, N)`. -/
noncomputable def IsMinimal.extLinearEquiv (hr : r.IsMinimal)
    (hN : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) = ⊥) (n : ℕ) :
    (r.termObj n ⟶ N) ≃ₗ[k] Ext.{w} M N n :=
  match n with
  | 0 => (r.augmentationHomLinearEquiv (hr.differential_comp_eq_zero hN 0)).symm.trans
      (Ext.linearEquiv₀ (R := k)).symm
  | n + 1 => r.extLinearEquivOfCompEqZero n
      (hr.differential_comp_eq_zero hN (n + 1)) (hr.differential_comp_eq_zero hN n)

/-- In degree zero, the class of a map precomposed with the augmentation is its ordinary
Hom class in Ext. -/
@[simp]
theorem IsMinimal.extLinearEquiv_zero_augmentation_comp (f : M ⟶ N) :
    hr.extLinearEquiv hN 0 (r.augmentation ≫ f) = Ext.mk₀ f := by
  rw [IsMinimal.extLinearEquiv, LinearEquiv.trans_apply,
    ← r.augmentationHomLinearEquiv_apply (hr.differential_comp_eq_zero hN 0),
    LinearEquiv.symm_apply_apply]
  exact Ext.linearEquiv₀_symm_apply f

/-- In positive degree, the minimal-resolution identification sends a graded map to its
projective-resolution class. -/
@[simp]
theorem IsMinimal.extLinearEquiv_succ_apply (n : ℕ) (f : r.termObj (n + 1) ⟶ N) :
    hr.extLinearEquiv hN (n + 1) f =
      r.toProjectiveResolution.extMk ((r.toProjectiveResolutionXIso (n + 1)).hom ≫ f)
        (n + 2) rfl (r.toProjectiveResolution_d_comp_eq_zero (n + 1)
          (hr.differential_comp_eq_zero hN (n + 1)) _) :=
  r.extLinearEquivOfCompEqZero_apply n _ _ f

/-- The degree-zero identification recovers a map by precomposing its ordinary Hom
representative with the augmentation. -/
@[simp]
theorem IsMinimal.augmentation_comp_linearEquiv₀_extLinearEquiv (f : r.termObj 0 ⟶ N) :
    r.augmentation ≫ Ext.linearEquiv₀ (R := k) (hr.extLinearEquiv hN 0 f) = f := by
  rw [IsMinimal.extLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  simpa only [augmentationHomLinearEquiv_apply] using
    (r.augmentationHomLinearEquiv (hr.differential_comp_eq_zero hN 0)).apply_symm_apply f

/-- The minimal-resolution Hom computation is natural in targets annihilated by `A₊`:
postcomposition of graded maps computes the covariant map on Ext. -/
@[simp]
theorem IsMinimal.extLinearEquiv_comp_mk₀ {N' : GradedModuleCat.{v} 𝒜}
    (hN' : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N') = ⊥)
    (n : ℕ) (f : r.termObj n ⟶ N) (g : N ⟶ N') :
    (hr.extLinearEquiv hN n f).comp (Ext.mk₀ g) (add_zero _) =
      hr.extLinearEquiv hN' n (f ≫ g) := by
  cases n with
  | zero =>
      obtain ⟨f, rfl⟩ :=
        (r.augmentationHomLinearEquiv (hr.differential_comp_eq_zero hN 0)).surjective f
      simp only [augmentationHomLinearEquiv_apply, Category.assoc,
        hr.extLinearEquiv_zero_augmentation_comp, Ext.mk₀_comp_mk₀]
  | succ n =>
      simp only [hr.extLinearEquiv_succ_apply, ProjectiveResolution.extMk_comp_mk₀,
        Category.assoc]

/-- For a minimal resolution and a target annihilated by `A₊`, Ext vanishes in a degree
exactly when all graded maps from the corresponding resolution term vanish. -/
theorem IsMinimal.subsingleton_ext_iff (n : ℕ) :
    Subsingleton (Ext.{w} M N n) ↔ Subsingleton (r.termObj n ⟶ N) :=
  (hr.extLinearEquiv hN n).toEquiv.subsingleton_congr.symm

omit hN in
/-- For a target concentrated in one internal degree, Ext vanishes exactly when graded
maps from the corresponding term of a minimal resolution vanish. -/
theorem IsMinimal.subsingleton_ext_iff_of_piece_eq_bot (j : ℤ)
    (hN₀ : ∀ p, p ≠ j → N.grading.piece p = ⊥) (n : ℕ) :
    Subsingleton (Ext.{w} M N n) ↔ Subsingleton (r.termObj n ⟶ N) := by
  apply hr.subsingleton_ext_iff
  let := N.gradedSMul
  exact InternalGrading.smul_top_eq_bot_of_piece_eq_bot 𝒜 N.grading j hN₀

omit hN in
/-- For a degree-zero target, Ext into any internal shift vanishes exactly when graded
maps from the corresponding term of a minimal resolution vanish. -/
theorem IsMinimal.subsingleton_ext_shiftObj_iff
    (hN₀ : ∀ p, p ≠ 0 → N.grading.piece p = ⊥) (n : ℕ) (j : ℤ) :
    Subsingleton (Ext.{w} M (N.shiftObj j) n) ↔
      Subsingleton (r.termObj n ⟶ N.shiftObj j) := by
  apply hr.subsingleton_ext_iff_of_piece_eq_bot j _ n
  intro p hp
  rw [GradedModuleCat.shiftObj_piece]
  exact hN₀ (p - j) (sub_ne_zero.mpr hp)

end GradedProjectiveResolution

end TauCeti
