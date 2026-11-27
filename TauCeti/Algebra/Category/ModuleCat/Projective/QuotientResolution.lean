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
import TauCeti.CategoryTheory.Abelian.Projective.Resolution

/-!
# Projective resolutions of ideal quotients

`Ideal.quotientProjectiveResolution I` resolves `A ⧸ I` by prepending the regular module
`A` to the chosen projective resolution of `I` via `CategoryTheory.ProjectiveResolution.cons`.
Its complex and augmentation are described by `Ideal.quotientProjectiveResolution_complex` and
`Ideal.quotientProjectiveResolution_π_f_zero`.
-/

public section

namespace Ideal

open CategoryTheory Limits

universe u

variable {A : Type u} [Ring A]

private theorem quotientShortExact (I : Ideal A) :
    (ShortComplex.mk (ModuleCat.ofHom I.subtype) (ModuleCat.ofHom I.mkQ)
      (ModuleCat.hom_ext (LinearMap.ext fun x ↦
        (Submodule.Quotient.mk_eq_zero I).2 x.property))).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    -- `ModuleCat.ofHom I.subtype ⟨x, _⟩` is definitionally `x`.
    exact fun x hx ↦ ⟨⟨x, (Submodule.Quotient.mk_eq_zero I).1 hx⟩, rfl⟩
  mono_f := (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  epi_g := (ModuleCat.epi_iff_surjective _).2 I.mkQ_surjective

/-- The projective resolution of `A ⧸ I` obtained by prepending `A` to the chosen projective
resolution of `I`. The final differential is the resolution map followed by the ideal inclusion,
and the augmentation is the quotient map. -/
noncomputable def quotientProjectiveResolution (I : Ideal A) :
    ProjectiveResolution (ModuleCat.of A (A ⧸ I)) :=
  (projectiveResolution (ModuleCat.of A I : ModuleCat.{u} A)).cons (quotientShortExact I)

/-- The ideal-quotient resolution is the resolution of `I` augmented by its inclusion into `A`.
-/
theorem quotientProjectiveResolution_complex (I : Ideal A) :
    (quotientProjectiveResolution I).complex =
      (projectiveResolution (ModuleCat.of A I : ModuleCat.{u} A)).complex.augment
        ((projectiveResolution (ModuleCat.of A I : ModuleCat.{u} A)).π.f 0 ≫
          ModuleCat.ofHom I.subtype)
        (by simp only [← Category.assoc, ProjectiveResolution.complex_d_comp_π_f_zero,
          zero_comp]) :=
  (projectiveResolution (ModuleCat.of A I : ModuleCat.{u} A)).cons_complex (quotientShortExact I)

/-- The augmentation in degree zero is the quotient map, after identifying the degree-zero
object with the regular module through `quotientProjectiveResolution_complex`. -/
theorem quotientProjectiveResolution_π_f_zero (I : Ideal A) :
    eqToHom (show ModuleCat.of A A = (quotientProjectiveResolution I).complex.X 0 by
      rw [quotientProjectiveResolution_complex, ChainComplex.augment_X_zero]) ≫
        (quotientProjectiveResolution I).π.f 0 = ModuleCat.ofHom I.mkQ := by
  let Q := projectiveResolution (ModuleCat.of A I : ModuleCat.{u} A)
  -- `quotientProjectiveResolution I` is definitionally `Q.cons (quotientShortExact I)`.
  change eqToHom (Q.cons_complex_X_zero (quotientShortExact I)).symm ≫
      (Q.cons (quotientShortExact I)).π.f 0 = ModuleCat.ofHom I.mkQ
  rw [Q.cons_π_f_zero (quotientShortExact I), eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end Ideal
