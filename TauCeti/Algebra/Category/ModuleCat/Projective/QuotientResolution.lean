/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Projective resolutions of ideal quotients

`Ideal.quotientProjectiveResolution I` resolves `A ⧸ I` by prepending the regular module
`A` to the chosen projective resolution of `I`. Its complex and augmentation are described by
`Ideal.quotientProjectiveResolution_complex` and
`Ideal.quotientProjectiveResolution_π_f_zero`.
-/

public section

namespace Ideal

open CategoryTheory Limits

universe u

variable {A : Type u} [Ring A]

/-- The projective resolution of `A ⧸ I` obtained by prepending `A` to the chosen projective
resolution of `I`. The final differential is the resolution map followed by the ideal inclusion,
and the augmentation is the quotient map. -/
noncomputable def quotientProjectiveResolution (I : Ideal A) :
    ProjectiveResolution (ModuleCat.of A (A ⧸ I)) := by
  -- Resolve the ideal first, then prepend the ambient ring.
  let P := projectiveResolution (ModuleCat.of A I : ModuleCat.{u} A)
  let p : P.complex.X 0 ⟶ ModuleCat.of A I :=
    P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 _).hom
  have hp : P.complex.d 1 0 ≫ p = 0 := by
    simp only [p, ← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]
  let f := p ≫ ModuleCat.ofHom I.subtype
  have hf : P.complex.d 1 0 ≫ f = 0 := by
    dsimp only [f]
    rw [← Category.assoc, hp, zero_comp]
  let K := P.complex.augment f hf
  let q : K.X 0 ⟶ ModuleCat.of A (A ⧸ I) := ModuleCat.ofHom I.mkQ
  have hq : K.d 1 0 ≫ q = 0 := by
    apply ModuleCat.hom_ext
    ext x
    exact (Submodule.Quotient.mk_eq_zero I).2 (p x).property
  refine { complex := K
           projective := ?_
           π := (ChainComplex.toSingle₀Equiv K _).symm ⟨q, hq⟩
           quasiIso := ?_ }
  · intro n
    cases n with
    | zero => exact inferInstanceAs (Projective (ModuleCat.of A A))
    | succ n => exact P.projective n
  · constructor
    intro n
    cases n with
    | zero =>
      -- The cokernel of the ideal inclusion is the required quotient.
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        simp only [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
        refine ⟨?_, (ModuleCat.epi_iff_surjective _).2 I.mkQ_surjective⟩
        rw [ShortComplex.moduleCat_exact_iff]
        intro x hx
        obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective p).1 inferInstance
          ⟨x, (Submodule.Quotient.mk_eq_zero I).1 hx⟩
        exact ⟨y, congrArg Subtype.val hy⟩
      all_goals rfl
    | succ n =>
      -- Exactness above degree one is inherited from the resolution of the ideal.
      rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
      rw [HomologicalComplex.exactAt_iff' K (n + 2) (n + 1) n (by simp) (by simp)]
      cases n with
      | zero =>
        rw [ShortComplex.moduleCat_exact_iff]
        intro x hx
        have hx' : P.π.f 0 x = 0 := by
          apply (ModuleCat.mono_iff_injective
            (HomologicalComplex.singleObjXSelf _ 0 _).hom).1 inferInstance
          exact Subtype.val_injective hx
        exact (ShortComplex.moduleCat_exact_iff _).1 P.exact₀ x hx'
      | succ n => exact P.exact_succ n

/-- The ideal-quotient resolution is the resolution of `I` augmented by its inclusion into `A`.
-/
theorem quotientProjectiveResolution_complex (I : Ideal A) :
    (quotientProjectiveResolution I).complex =
      (projectiveResolution (ModuleCat.of A I : ModuleCat.{u} A)).complex.augment
        (((projectiveResolution (ModuleCat.of A I : ModuleCat.{u} A)).π.f 0 ≫
          (HomologicalComplex.singleObjXSelf _ 0 _).hom) ≫ ModuleCat.ofHom I.subtype)
        (by simp only [← Category.assoc, ProjectiveResolution.complex_d_comp_π_f_zero,
          zero_comp]) := by
  rfl

/-- The augmentation in degree zero is the quotient map, after identifying the degree-zero
object with the regular module through `quotientProjectiveResolution_complex`. -/
theorem quotientProjectiveResolution_π_f_zero (I : Ideal A) :
    eqToHom (show ModuleCat.of A A = (quotientProjectiveResolution I).complex.X 0 by
      rw [quotientProjectiveResolution_complex]; rfl) ≫
        (quotientProjectiveResolution I).π.f 0 = ModuleCat.ofHom I.mkQ := by
  rfl

end Ideal
