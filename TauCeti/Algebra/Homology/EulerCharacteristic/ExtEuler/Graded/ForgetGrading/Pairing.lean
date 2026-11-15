/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ForgetGrading
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.ForgetGrading.Comparison

/-!
# The q-Euler form at `q = 1` on Grothendieck groups

Let `C` be a `k`-linear abelian category with a grading-shift autoequivalence `e`, and let `D` be
an ungraded `k`-linear abelian category.  Suppose conflation-exact functors forget the grading of
two shift-stable extension-closed subcategories `P` and `Q` of `C`, landing in extension-closed
subcategories `P'` and `Q'` of `D`, and identify the shift with the identity.  By
`TauCeti.LaurentK0.forgetGrading` they induce maps from graded `K₀`, specialized at `q = 1`, to
ungraded `K₀`.

If, for every pair of objects, the bigraded `Ext` groups assemble into the ungraded `Ext` groups of
the forgotten pair (`TauCeti.IsGradedExtComparison`), then the q-Euler form specialized at `q = 1`
is the ordinary Ext-Euler pairing pulled back along these maps.  The object-level identity is
`TauCeti.IsGradedExtComparison.gradedExtEulerSpecialized_one_mk_of_mk_of`; this file extends it to
all classes.  Shift compatibility alone does not give the identity: the comparison isomorphisms
are a genuine hypothesis.

Over a left Noetherian graded algebra, `TauCeti.GradedModuleCat.isGradedExtComparison_toModuleCat`
supplies the comparison isomorphisms for finitely generated graded modules, so the identity holds
on `G₀^gr(mod A)` whenever both forms are defined.  Euler-admissibility of all pairs of finitely
generated ungraded modules is assumed separately: an ungraded module need not admit a grading, so
it does not follow from the graded hypothesis.

## Main results

* `TauCeti.gradedExtEulerSpecialized_one_eq_extEulerPairing`: under the `Ext` comparison
  hypothesis, the q-Euler form at `q = 1` is the Ext-Euler pairing of the forgotten classes.
* `TauCeti.gradedExtEulerSpecialized_one_eq_extEulerPairing_gradedFiniteModules`: the same identity
  on the Grothendieck groups of finitely generated graded modules over a left Noetherian graded
  algebra.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Section 2.2, for graded Grothendieck groups, the
  q-Euler form and its specialization at `q = 1`.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Lecture Notes in Mathematics
  1836, Springer (2004), Section 2.4, for the agreement of graded and ungraded `Ext` of a finitely
  generated module over a Noetherian graded ring.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial

universe w w' v v' u u' t uk uA

section General

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  {k : Type t} [Field k] [Linear k C] [Linear k D] [HasExt.{w} C] [HasExt.{w'} D] {e : C ≌ C}
  [e.functor.Additive] [e.functor.Linear k]

variable {P Q : ObjectProperty C} [LocallySmall.{w} C]
  [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]

variable {P' Q' : ObjectProperty D} [LocallySmall.{w'} D]
  [ObjectProperty.EssentiallySmall.{w'} P'] [ObjectProperty.EssentiallySmall.{w'} Q']
  [P'.ContainsZero] [P'.IsClosedUnderBinaryProducts]
  [Q'.ContainsZero] [Q'.IsClosedUnderBinaryProducts]

/-- **The q-Euler form at `q = 1` is the ordinary Ext-Euler pairing on Grothendieck groups.**
Let `FP` and `FQ` forget the grading of `P` and `Q`, conflation-exactly and compatibly with the
grading shift.  If for all objects `X` of `P` and `Y` of `Q` the bigraded `Ext` groups of `(X, Y)`
assemble into the ungraded `Ext` groups of `(FP X, FQ Y)`, then the q-Euler form specialized at
`q = 1` is the Ext-Euler pairing of the classes with their grading forgotten. -/
theorem gradedExtEulerSpecialized_one_eq_extEulerPairing
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)
    (hP' : (ExactStructure.abelian D).IsExtensionClosed P')
    (hQ' : (ExactStructure.abelian D).IsExtensionClosed Q')
    (h' : IsEulerAdmissibleOn.{w'} k P' Q')
    {FP : P.FullSubcategory ⥤ P'.FullSubcategory} [FP.Additive]
    {FQ : Q.FullSubcategory ⥤ Q'.FullSubcategory} [FQ.Additive]
    (hFP : ((GradedExactStructure.abelian C e).fullSubcategory P hP
      hPshift).toExactStructure.IsConflationExact
        ((ExactStructure.abelian D).fullSubcategory P' hP') FP)
    (hFQ : ((GradedExactStructure.abelian C e).fullSubcategory Q hQ
      hQshift).toExactStructure.IsConflationExact
        ((ExactStructure.abelian D).fullSubcategory Q' hQ') FQ)
    (commP : ((GradedExactStructure.abelian C e).fullSubcategory P hP hPshift).shift.functor ⋙
      FP ≅ FP)
    (commQ : ((GradedExactStructure.abelian C e).fullSubcategory Q hQ hQshift).shift.functor ⋙
      FQ ≅ FQ)
    (hc : ∀ (X : P.FullSubcategory) (Y : Q.FullSubcategory),
      IsGradedExtComparison.{w, w'} k e X.obj Y.obj (FP.obj X).obj (FQ.obj Y).obj)
    (x : LaurentSpecialization (1 : ℤˣ)
      (LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P hP hPshift)))
    (y : LaurentSpecialization (1 : ℤˣ)
      (LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q hQ hQshift))) :
    gradedExtEulerSpecialized hP hQ hPshift hQshift h 1 x y =
      extEulerPairing hP' hQ' h' (LaurentK0.forgetGrading hFP commP x)
        (LaurentK0.forgetGrading hFQ commQ y) := by
  -- First fix a specialized object class in the first argument and compare in the second.
  have hX (X : P.FullSubcategory) :
      gradedExtEulerSpecialized hP hQ hPshift hQshift h 1
          (LaurentSpecialization.mk 1 (LaurentK0.of _ X)) =
        (extEulerPairing hP' hQ' h' (ExactK0.of (FP.obj X))).toIntLinearMap.comp
          (LaurentK0.forgetGrading hFQ commQ) := by
    ext Y
    simp [(hc X Y).gradedExtEulerSpecialized_one_mk_of_mk_of, LaurentK0.forgetGrading_mk_of]
  -- Then compare the two sides as linear maps in the first argument.
  have key : (gradedExtEulerSpecialized hP hQ hPshift hQshift h 1).flip y =
      ((extEulerPairing hP' hQ' h').flip
        (LaurentK0.forgetGrading hFQ commQ y)).toIntLinearMap.comp
          (LaurentK0.forgetGrading hFP commP) :=
    LaurentK0.hom_ext_laurentSpecialization 1 fun X => by
      simp [hX, LaurentK0.forgetGrading_mk_of]
  simpa using LinearMap.congr_fun key x

end General

section GradedModule

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜] [IsNoetherianRing A]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)] [HasExt.{uA} (ModuleCat.{uA} A)]

/-- **The q-Euler form of finitely generated graded modules at `q = 1` is the ordinary Ext-Euler
pairing.**  Over a left Noetherian graded algebra, if every pair of finitely generated graded
modules is graded Euler-admissible and every pair of finitely generated modules is
Euler-admissible, then the q-Euler form on `G₀^gr(mod A)` specialized at `q = 1` is the Ext-Euler
pairing on `G₀(mod A)` of the classes with their grading forgotten. -/
theorem gradedExtEulerSpecialized_one_eq_extEulerPairing_gradedFiniteModules
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (h' : IsEulerAdmissibleOn.{uA} k (ModuleCat.isFG.{uA} A) (ModuleCat.isFG.{uA} A))
    (x y : LaurentSpecialization (1 : ℤˣ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜))) :
    gradedExtEulerSpecialized.{uA} isExtensionClosed_gradedFiniteModules_gradedAbelian
        isExtensionClosed_gradedFiniteModules_gradedAbelian
        gradedFiniteModules_gradedAbelian_shift gradedFiniteModules_gradedAbelian_shift h 1 x y =
      extEulerPairing (isExtensionClosed_finiteModules A) (isExtensionClosed_finiteModules A) h'
        (finiteModulesExactK0Equiv A (gradedFiniteModulesForgetK0 𝒜 x))
        (finiteModulesExactK0Equiv A (gradedFiniteModulesForgetK0 𝒜 y)) := by
  simp only [finiteModulesExactK0Equiv_gradedFiniteModulesForgetK0]
  refine gradedExtEulerSpecialized_one_eq_extEulerPairing _ _ _ _ h _ _ h' _ _ _ _
    (fun X Y => ?_) x y
  have : Module.Finite A X.obj := gradedFiniteModules_iff.mp X.property
  exact GradedModuleCat.isGradedExtComparison_toModuleCat X.obj Y.obj

end GradedModule

end TauCeti
