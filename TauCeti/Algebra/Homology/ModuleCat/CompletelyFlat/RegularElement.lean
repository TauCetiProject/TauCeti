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
zero in `A ⧸ (f)`. For `A = ℤ` and `f = p` this shows that `F_p` is not `p`-completely flat over
`ℤ`.

## Main results

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
    simp only [B, Functor.mapHomologicalComplex_obj_d]
    rw [R.cochainComplex_d (-1) 0 1 0, regularElementProjectiveResolution_complex_d f hf]
    simp
  have hB : IsZero (B.X (-1)) := hz.of_iso
    ((B.iCyclesIso (-1) 0 (by simp) hout).symm ≪≫ B.isoHomologyπ (-2) (-1) (by simp) hin ≪≫ e₂)
  exact Ideal.not_isZero_extendScalars_mk_of_ne_top hI (hB.of_iso (F.mapIso hX₁).symm)

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
  exact (HomologicalComplex.isZero_single_obj_homology _ _ F (-1) (by omega)).of_iso
    ((homologyFunctor _ (-1)).mapIso ((singleFunctorIsoCompQ _ 0).app F) ≪≫
      (homologyFunctorFactors _ (-1)).app _)

end TauCeti.DerivedDeRham
