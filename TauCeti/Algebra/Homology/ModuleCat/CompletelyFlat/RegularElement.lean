/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import TauCeti.Algebra.Category.ModuleCat.Projective.RegularElementResolution
public import TauCeti.Algebra.Homology.ModuleCat.CompletelyFlat
import TauCeti.Algebra.Category.ModuleCat.ExtendScalarsQuotient
import TauCeti.Algebra.Homology.ModuleCat.KFlat.Basic

/-!
# The quotient by a nonzerodivisor is not completely flat

Let `f` be a nonzerodivisor of a commutative ring `A` with `(f) ≠ A`. The quotient `A ⧸ (f)`,
placed in degree zero of `D(A)`, is not `(f)`-completely flat: its derived reduction
`A ⧸ (f) ⊗^L_A A ⧸ (f)` has nonzero cohomology `A ⧸ (f)` in degree `-1`, whereas a module placed
in degree zero has none.

The derived reduction is computed on the two-term resolution `A --f--> A` of `A ⧸ (f)`
(`TauCeti.regularElementProjectiveResolution`): it is K-flat, so the derived reduction is its
degreewise reduction `A ⧸ (f) --0--> A ⧸ (f)`, whose differential vanishes because `f` maps to
zero in `A ⧸ (f)`. This is the obstruction in the `F_p` Check of `TauCetiRoadmap`'s
`DerivedModuleAlgebra` §1.7, for `A = ℤ` and `f = p`.

## Main results

* `TauCeti.DerivedDeRham.extendScalars_map_regularElementMul`: the reduction modulo `(f)` of
  multiplication by `f` is zero.
* `TauCeti.DerivedDeRham.not_isZero_homology_derivedReduction_quotient`: the derived reduction of
  `A ⧸ (f)` has nonzero cohomology in degree `-1`.
* `TauCeti.DerivedDeRham.not_isCompletelyFlat_quotient`: `A ⧸ (f)` in degree zero is not
  `(f)`-completely flat.
-/

public section

noncomputable section

open CategoryTheory Limits DerivedCategory

universe w w' u

namespace TauCeti.DerivedDeRham

variable {A : Type u} [CommRing A] {f : A}

/-- Reducing multiplication by `f` modulo `(f)` gives the zero map. -/
theorem extendScalars_map_regularElementMul :
    (ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {f}))).map (regularElementMul f) =
      0 := by
  ext m
  apply (Ideal.extendScalarsMkEquivQuotSMul (Ideal.span {f}) A).injective
  erw [ModuleCat.ExtendScalars.map_tmul]
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {f}))]
  erw [Ideal.extendScalarsMkEquivQuotSMul_mk_tmul]
  have h0 : (Submodule.Quotient.mk ((1 : A) • (regularElementMul f).hom m) :
      A ⧸ (Ideal.span {f} • ⊤ : Submodule A A)) = 0 := by
    rw [ModuleCat.hom_ofHom, LinearMap.mulLeft_apply, one_smul, Submodule.Quotient.mk_eq_zero,
      Ideal.smul_top_eq_map]
    simpa using Ideal.mul_mem_right m _ (Ideal.mem_span_singleton_self f)
  exact h0.trans ((Ideal.extendScalarsMkEquivQuotSMul (Ideal.span {f}) A).map_zero).symm

/-- The extension of scalars of the regular module along `A → A ⧸ (f)` is nonzero when
`(f) ≠ A`. -/
theorem not_isZero_extendScalars_quotient (hI : Ideal.span {f} ≠ ⊤) :
    ¬ IsZero ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj
      (ModuleCat.of A A)) := by
  intro h
  have := ModuleCat.subsingleton_of_isZero h
  have hs : Subsingleton (A ⧸ (Ideal.span {f} • ⊤ : Submodule A A)) :=
    (Ideal.extendScalarsMkEquivQuotSMul (Ideal.span {f}) A).symm.injective.subsingleton
  apply hI
  rw [Ideal.eq_top_iff_one]
  have h1 := (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim
    (Submodule.Quotient.mk (1 : A) : A ⧸ (Ideal.span {f} • ⊤ : Submodule A A)) 0)
  simpa [Ideal.smul_eq_mul] using h1

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w'} (ModuleCat.{u} (A ⧸ Ideal.span {f}))]

/-- **The degree `-1` cohomology of the derived reduction of `A ⧸ (f)`.** For a nonzerodivisor
`f` with `(f) ≠ A`, the derived reduction `A ⧸ (f) ⊗^L_A A ⧸ (f)` has nonzero cohomology in
degree `-1`. -/
theorem not_isZero_homology_derivedReduction_quotient (hf : f ∈ nonZeroDivisors A)
    (hI : Ideal.span {f} ≠ ⊤) :
    ¬ IsZero ((homologyFunctor (ModuleCat.{u} (A ⧸ Ideal.span {f})) (-1)).obj
      ((derivedReduction (Ideal.span {f})).obj
        ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ Ideal.span {f}))))) := by
  intro hz
  set R := regularElementProjectiveResolution f hf
  let P := R.cochainComplex
  have : P.IsKFlat :=
    CochainComplex.isKFlat_of_boundedAbove_flat_moduleCat P 0 fun _ ↦ inferInstance
  let F := ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk (Ideal.span {f}))
  let B := (complexBaseChange (Ideal.Quotient.mk (Ideal.span {f}))).obj P
  let e₁ : (singleFunctor _ 0).obj (ModuleCat.of A (A ⧸ Ideal.span {f})) ≅ Q.obj P :=
    (singleFunctorIsoCompQ _ 0).app _ ≪≫ (asIso (Q.map R.π')).symm
  let e₂ : B.homology (-1) ≅ (homologyFunctor _ (-1)).obj ((derivedReduction (Ideal.span {f})).obj
      ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ Ideal.span {f})))) :=
    ((homologyFunctorFactors _ (-1)).app B).symm ≪≫
      (homologyFunctor _ (-1)).mapIso
        ((derivedExtendScalarsKFlatIso _ P).symm ≪≫ (derivedReduction _).mapIso e₁.symm)
  -- the differentials into and out of degree `-1` vanish
  have hX₁ : P.X (-1) ≅ ModuleCat.of A A :=
    R.cochainComplexXIso (-1) 1 ≪≫ regularElementProjectiveResolutionXIso₁ f hf
  have hin : B.d (-2) (-1) = 0 :=
    IsZero.eq_of_src (F.map_isZero ((isZero_regularElementProjectiveResolution_complex_X f hf 2
      le_rfl).of_iso (R.cochainComplexXIso (-2) 2))) _ _
  have hout : B.d (-1) 0 = 0 := by
    change F.map (P.d (-1) 0) = 0
    rw [R.cochainComplex_d (-1) 0 1 0, regularElementProjectiveResolution_complex_d f hf]
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp,
      show F.map (regularElementMul f) = 0 from extendScalars_map_regularElementMul]
    simp only [zero_comp, comp_zero]
  have hB : IsZero (B.X (-1)) := hz.of_iso
    ((B.iCyclesIso (-1) 0 (by simp) hout).symm ≪≫ B.isoHomologyπ (-2) (-1) (by simp) hin ≪≫ e₂)
  exact not_isZero_extendScalars_quotient hI (hB.of_iso (F.mapIso hX₁).symm)

/-- **`A ⧸ (f)` is not `(f)`-completely flat.** For a nonzerodivisor `f` with `(f) ≠ A`, the
quotient `A ⧸ (f)` placed in degree zero of `D(A)` is not `(f)`-completely flat: its derived
reduction has nonzero cohomology in degree `-1`, which a module placed in degree zero has not. -/
theorem not_isCompletelyFlat_quotient (hf : f ∈ nonZeroDivisors A) (hI : Ideal.span {f} ≠ ⊤) :
    ¬ IsCompletelyFlat (Ideal.span {f})
      ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ Ideal.span {f}))) := by
  intro h
  obtain ⟨F, -, ⟨e⟩⟩ := isCompletelyFlat_iff.1 h
  refine not_isZero_homology_derivedReduction_quotient hf hI
    (IsZero.of_iso ?_ ((homologyFunctor _ (-1)).mapIso e))
  exact (IsZero.of_iso (ShortComplex.isZero_homology_of_isZero_X₂ _
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F (-1) (by omega)))
      ((homologyFunctor _ (-1)).mapIso ((singleFunctorIsoCompQ _ 0).app F) ≪≫
        (homologyFunctorFactors _ (-1)).app _))

end TauCeti.DerivedDeRham
