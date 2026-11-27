/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.CompletelyFlat.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import TauCeti.Algebra.Category.ModuleCat.ExtendScalars.Quotient
import TauCeti.Algebra.Category.ModuleCat.Quotient
import TauCeti.Algebra.Homology.ModuleCat.KFlat.Basic
import TauCeti.CategoryTheory.Abelian.LeftDerived

/-!
# The quotient by a nonzerodivisor is not completely flat

Let `f` be a nonzerodivisor of a commutative ring `A` with `(f) ≠ A`. The quotient `A ⧸ (f)`,
placed in degree zero of `D(A)`, is not `(f)`-completely flat: its derived reduction
`A ⧸ (f) ⊗^L_A A ⧸ (f)` has nonzero cohomology `A ⧸ (f)` in degree `-1`, whereas a module placed
in degree zero has none.

The derived reduction is computed on the two-term resolution `A --f--> A` of `A ⧸ (f)`, the
projective resolution given by the short exact sequence
`TauCeti.mulQuotientSpanSingletonShortComplex`
(`CategoryTheory.ShortComplex.ShortExact.projectiveResolution`): it is K-flat, so the derived
reduction is its degreewise reduction `A ⧸ (f) --0--> A ⧸ (f)`, whose differential vanishes
because `f` maps to zero in `A ⧸ (f)`. For `A = ℤ` and `f = p` this shows that `F_p` is not
`p`-completely flat over `ℤ`.

## Main results

* `TauCeti.DerivedDeRham.not_isZero_homology_derivedReduction_quotient`: the derived reduction of
  `A ⧸ (f)` has nonzero cohomology in degree `-1`.
* `TauCeti.DerivedDeRham.not_isCompletelyFlat_quotient_self`: `A ⧸ (f)` in degree zero is not
  `(f)`-completely flat.
-/

public section

noncomputable section

open CategoryTheory Limits DerivedCategory

universe w w' u

namespace TauCeti.DerivedDeRham

variable {A : Type u} [CommRing A] {f : A}

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
  set R := (isRegular_iff_mem_nonZeroDivisors.2 hf).left
    |>.mulQuotientSpanSingletonShortComplex_shortExact.projectiveResolution
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
  have hin : B.d (-2) (-1) = 0 :=
    IsZero.eq_of_src (F.map_isZero
      (((mulQuotientSpanSingletonShortComplex f).isZero_resolutionComplex_X_add_two 0).of_iso
        (R.cochainComplexXIso (-2) 2))) _ _
  -- `R.complex` is `resolutionComplex` by definition (`projectiveResolution_complex`), whose
  -- differential `R.complex.d 1 0` is multiplication by `f` (`resolutionComplex_d_one_zero`);
  -- rewriting along these equations would break the types of the degree identifications of
  -- `R.cochainComplex`, so the vanishing of the reduced differential is restated instead
  have hd : F.map (R.complex.d 1 0) = 0 :=
    Ideal.extendScalars_mk_map_ofHom_mulLeft_eq_zero (Ideal.mem_span_singleton_self f)
  have hout : B.d (-1) 0 = 0 := by
    simp only [B, Functor.mapHomologicalComplex_obj_d]
    rw [R.cochainComplex_d (-1) 0 1 0, Functor.map_comp, Functor.map_comp, hd, zero_comp,
      comp_zero]
  have hB : IsZero (B.X (-1)) := hz.of_iso
    ((B.iCyclesIso (-1) 0 (by simp) hout).symm ≪≫ B.isoHomologyπ (-2) (-1) (by simp) hin ≪≫ e₂)
  -- `R.complex.X 1` is the regular module `A` by definition (`resolutionComplex_X_one`)
  exact Ideal.not_isZero_extendScalars_mk_of_ne_top hI
    (hB.of_iso (F.mapIso (R.cochainComplexXIso (-1) 1)).symm)

/-- **`A ⧸ (f)` is not `(f)`-completely flat.** For a nonzerodivisor `f` with `(f) ≠ A`, the
quotient `A ⧸ (f)` placed in degree zero of `D(A)` is not `(f)`-completely flat: its derived
reduction has nonzero cohomology in degree `-1`, which a module placed in degree zero has not. -/
theorem not_isCompletelyFlat_quotient_self (hf : f ∈ nonZeroDivisors A) (hI : Ideal.span {f} ≠ ⊤) :
    ¬ IsCompletelyFlat (Ideal.span {f})
      ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ Ideal.span {f}))) := by
  intro h
  obtain ⟨F, -, ⟨e⟩⟩ := isCompletelyFlat_iff.1 h
  refine not_isZero_homology_derivedReduction_quotient hf hI
    (IsZero.of_iso ?_ ((homologyFunctor _ (-1)).mapIso e))
  exact (HomologicalComplex.isZero_single_obj_homology _ _ F (-1) (by omega)).of_iso
    ((homologyFunctor _ (-1)).mapIso ((singleFunctorIsoCompQ _ 0).app F) ≪≫
      (homologyFunctorFactors _ (-1)).app _)

end TauCeti.DerivedDeRham
