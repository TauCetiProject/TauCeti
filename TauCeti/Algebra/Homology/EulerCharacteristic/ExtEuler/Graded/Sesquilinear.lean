/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Descent
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Shift
public import TauCeti.CategoryTheory.Exact.Graded.FullSubcategory
public import TauCeti.CategoryTheory.GrothendieckGroup.Laurent
public import TauCeti.LinearAlgebra.SesquilinearForm.LaurentSpecialization
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# The q-Euler form on graded Grothendieck groups

Let `P` and `Q` be extension-closed, shift-stable full subcategories of a graded abelian category.
The preliminary exact-`K₀` descent `TauCeti.gradedExtEulerPairing` makes the graded Ext-Euler
characteristic biadditive on their induced exact Grothendieck groups.  The shift identities say
that the shift acts on this pairing by `q⁻¹` in the first variable and by `q` in the second.
Consequently the pairing upgrades to a map on Laurent-module Grothendieck groups which is
semilinear for the involution `q ↦ q⁻¹` in the first variable and linear in the second.

The two subcategories are allowed to differ: neither symmetry nor Hermitian symmetry is assumed.
The coefficient involution is Mathlib's `LaurentPolynomial.invert`, and the handedness is fixed by
the convention `[M{1}] = q[M]` on `TauCeti.LaurentK0`.

## Main definitions

* `TauCeti.gradedExtEulerSesquilinear`: the q-Euler form on the Laurent-module Grothendieck
  groups of `P` and `Q`.
* `TauCeti.gradedExtEulerSpecialized`: its specialization at `q = ε` for a unit `ε : ℤˣ`, that is
  at `q = 1` or `q = -1`, a `ℤ`-bilinear form on specialized graded Grothendieck groups.

## Main results

* `TauCeti.gradedExtEulerSesquilinear_of_of`: evaluation on two object classes.
* `TauCeti.gradedExtEulerSesquilinear_T_smul_left` and
  `TauCeti.gradedExtEulerSesquilinear_T_smul_right`: the shift normalizations in both variables.
* `TauCeti.gradedExtEulerSesquilinear_unique`: the form is determined by its values on object
  classes.
* `TauCeti.gradedExtEulerSpecialized_mk_of_mk_of`: the specialized form on two object classes is
  the graded Ext-Euler characteristic evaluated at `q = ε`.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Sections 1.2, 2.2 and 3.1.
-/

public section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe w v u t

private def InvertedLaurentPolynomial := LaurentPolynomial ℤ

private noncomputable instance : AddCommGroup InvertedLaurentPolynomial :=
  inferInstanceAs (AddCommGroup (LaurentPolynomial ℤ))

private noncomputable instance : Module (LaurentPolynomial ℤ) InvertedLaurentPolynomial := by
  letI : Module (LaurentPolynomial ℤ) InvertedLaurentPolynomial :=
    inferInstanceAs (Module (LaurentPolynomial ℤ) (LaurentPolynomial ℤ))
  exact Module.compHom _ (LaurentPolynomial.invert (R := ℤ)).toRingEquiv.toRingHom

private def toInvertedLaurentPolynomial (x : LaurentPolynomial ℤ) :
    InvertedLaurentPolynomial :=
  x

private def ofInvertedLaurentPolynomial (x : InvertedLaurentPolynomial) :
    LaurentPolynomial ℤ :=
  x

private lemma ofInvertedLaurentPolynomial_injective :
    Function.Injective ofInvertedLaurentPolynomial := fun _ _ h ↦ h

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Field k] [Linear k C]
  [HasExt.{w} C] {e : C ≌ C} [e.functor.Additive] [e.functor.Linear k]

variable {P Q : ObjectProperty C} [LocallySmall.{w} C]
  [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]

local instance : P.IsClosedUnderIsomorphisms :=
  ObjectProperty.isClosedUnderIsomorphisms_of_containsZero P

local instance : Q.IsClosedUnderIsomorphisms :=
  ObjectProperty.isClosedUnderIsomorphisms_of_containsZero Q

omit [HasExt.{w} C] [LocallySmall.{w} C] in
/-- The identity functor compares the exact structure induced from the graded abelian structure
with the one induced from the underlying abelian structure. -/
private theorem isConflationExact_id_fullSubcategory {R : ObjectProperty C} [R.ContainsZero]
    [R.IsClosedUnderBinaryProducts]
    (hR : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed R)
    (hR' : (ExactStructure.abelian C).IsExtensionClosed R)
    (hRshift : R.inverseImage (GradedExactStructure.abelian C e).shift.functor = R) :
    ((GradedExactStructure.abelian C e).fullSubcategory R hR
      hRshift).toExactStructure.IsConflationExact
        ((ExactStructure.abelian C).fullSubcategory R hR') (𝟭 _) where
  map_conflation {S} hS := by
    rw [GradedExactStructure.fullSubcategory_toExactStructure,
      ExactStructure.fullSubcategory_conflation_iff] at hS
    rw [ExactStructure.fullSubcategory_conflation_iff, S.map_id]
    simpa only [GradedExactStructure.abelian_toExactStructure] using hS

/-- The preliminary exact-`K₀` pairing `gradedExtEulerPairing`, read on the Grothendieck groups of
the graded full-subcategory exact structures. -/
private noncomputable def gradedExtEulerPairingOnGradedSubcategories
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) :
    ExactK0 (((GradedExactStructure.abelian C e).fullSubcategory P hP hPshift).toExactStructure) →+
      ExactK0
          (((GradedExactStructure.abelian C e).fullSubcategory Q hQ hQshift).toExactStructure) →+
      LaurentPolynomial ℤ :=
  have hP' : (ExactStructure.abelian C).IsExtensionClosed P := by
    simpa only [GradedExactStructure.abelian_toExactStructure] using hP
  have hQ' : (ExactStructure.abelian C).IsExtensionClosed Q := by
    simpa only [GradedExactStructure.abelian_toExactStructure] using hQ
  (((gradedExtEulerPairing hP' hQ' h).comp
    (ExactK0.map (𝟭 _) (isConflationExact_id_fullSubcategory hP hP' hPshift))).flip.comp
      (ExactK0.map (𝟭 _) (isConflationExact_id_fullSubcategory hQ hQ' hQshift))).flip

omit [Functor.Linear k e.functor] in
private theorem gradedExtEulerPairingOnGradedSubcategories_of_of
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)
    (X : P.FullSubcategory) (Y : Q.FullSubcategory) :
    gradedExtEulerPairingOnGradedSubcategories hP hQ hPshift hQshift h
        (ExactK0.of X) (ExactK0.of Y) =
      gradedExtEuler k e (h.isGradedEulerAdmissible X.property Y.property) := by
  simp [gradedExtEulerPairingOnGradedSubcategories]

omit [Functor.Linear k e.functor] in
private theorem gradedExtEulerPairing_shiftTarget
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)
    (x : ExactK0 (((GradedExactStructure.abelian C e).fullSubcategory P
      hP hPshift).toExactStructure))
    (y : ExactK0 (((GradedExactStructure.abelian C e).fullSubcategory Q
      hQ hQshift).toExactStructure)) :
    gradedExtEulerPairingOnGradedSubcategories hP hQ hPshift hQshift h x
        (((GradedExactStructure.abelian C e).fullSubcategory Q
          hQ hQshift).shiftEquiv y) =
      T 1 * gradedExtEulerPairingOnGradedSubcategories hP hQ hPshift hQshift h x y := by
  let EP := (GradedExactStructure.abelian C e).fullSubcategory P
    hP hPshift
  let EQ := (GradedExactStructure.abelian C e).fullSubcategory Q
    hQ hQshift
  let b := gradedExtEulerPairingOnGradedSubcategories hP hQ hPshift hQshift h
  let lhs : ExactK0 EP.toExactStructure →+ ExactK0 EQ.toExactStructure →+ LaurentPolynomial ℤ :=
    { toFun := fun x => (b x).comp EQ.shiftEquiv.toAddMonoidHom
      map_zero' := by ext y; simp
      map_add' := by intro x₁ x₂; ext y; simp }
  let rhs : ExactK0 EP.toExactStructure →+ ExactK0 EQ.toExactStructure →+ LaurentPolynomial ℤ :=
    { toFun := fun x =>
        { toFun := fun y => T 1 * b x y
          map_zero' := by simp
          map_add' := by intro y₁ y₂; simp [mul_add] }
      map_zero' := by ext y; simp
      map_add' := by intro x₁ x₂; ext y; simp [mul_add] }
  have hmaps : lhs = rhs := ExactK0.hom_ext fun X => by
    apply ExactK0.hom_ext
    intro Y
    -- `ExactK0.hom_ext` exposes applications of the two local additive-map wrappers.
    change b (ExactK0.of X) (EQ.shiftEquiv (ExactK0.of Y)) =
      T 1 * b (ExactK0.of X) (ExactK0.of Y)
    rw [GradedExactStructure.shiftEquiv_of,
      GradedExactStructure.fullSubcategory_shift]
    simp only [b, gradedExtEulerPairingOnGradedSubcategories_of_of]
    let j : (GradedExactStructure.abelian C e).shift.functor.obj Y.obj ≅ e.functor.obj Y.obj :=
      eqToIso (congrArg (fun f : C ≌ C => f.functor.obj Y.obj)
        (GradedExactStructure.abelian_shift e))
    let i :=
      ((GradedExactStructure.abelian C e).fullSubcategoryShiftFunctorCompιIso Q hQshift).app Y ≪≫ j
    exact (gradedExtEuler_of_iso k
      (h.isGradedEulerAdmissible X.property
        (((GradedExactStructure.abelian C e).fullSubcategoryShift Q hQshift).functor.obj
          Y).property)
      (h.isGradedEulerAdmissible X.property Y.property).shiftTarget
      (Iso.refl X.obj) i).trans
        (gradedExtEuler_shiftTarget (h.isGradedEulerAdmissible X.property Y.property))
  exact DFunLike.congr_fun (DFunLike.congr_fun hmaps x) y

private theorem gradedExtEulerPairing_shiftSource
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)
    (x : ExactK0 (((GradedExactStructure.abelian C e).fullSubcategory P
      hP hPshift).toExactStructure))
    (y : ExactK0 (((GradedExactStructure.abelian C e).fullSubcategory Q
      hQ hQshift).toExactStructure)) :
    gradedExtEulerPairingOnGradedSubcategories hP hQ hPshift hQshift h
        (((GradedExactStructure.abelian C e).fullSubcategory P
          hP hPshift).shiftEquiv x) y =
      T (-1) * gradedExtEulerPairingOnGradedSubcategories hP hQ hPshift hQshift h x y := by
  let EP := (GradedExactStructure.abelian C e).fullSubcategory P
    hP hPshift
  let EQ := (GradedExactStructure.abelian C e).fullSubcategory Q
    hQ hQshift
  let b := gradedExtEulerPairingOnGradedSubcategories hP hQ hPshift hQshift h
  let lhs : ExactK0 EP.toExactStructure →+ ExactK0 EQ.toExactStructure →+ LaurentPolynomial ℤ :=
    b.comp EP.shiftEquiv.toAddMonoidHom
  let rhs : ExactK0 EP.toExactStructure →+ ExactK0 EQ.toExactStructure →+ LaurentPolynomial ℤ :=
    { toFun := fun x =>
        { toFun := fun y => T (-1) * b x y
          map_zero' := by simp
          map_add' := by intro y₁ y₂; simp [mul_add] }
      map_zero' := by ext y; simp
      map_add' := by intro x₁ x₂; ext y; simp [mul_add] }
  have hmaps : lhs = rhs := ExactK0.hom_ext fun X => by
    apply ExactK0.hom_ext
    intro Y
    -- `ExactK0.hom_ext` exposes applications of the two local additive-map wrappers.
    change b (EP.shiftEquiv (ExactK0.of X)) (ExactK0.of Y) =
      T (-1) * b (ExactK0.of X) (ExactK0.of Y)
    rw [GradedExactStructure.shiftEquiv_of,
      GradedExactStructure.fullSubcategory_shift]
    simp only [b, gradedExtEulerPairingOnGradedSubcategories_of_of]
    let j : (GradedExactStructure.abelian C e).shift.functor.obj X.obj ≅ e.functor.obj X.obj :=
      eqToIso (congrArg (fun f : C ≌ C => f.functor.obj X.obj)
        (GradedExactStructure.abelian_shift e))
    let i :=
      ((GradedExactStructure.abelian C e).fullSubcategoryShiftFunctorCompιIso P hPshift).app X ≪≫ j
    exact (gradedExtEuler_of_iso k
      (h.isGradedEulerAdmissible
        (((GradedExactStructure.abelian C e).fullSubcategoryShift P hPshift).functor.obj X).property
        Y.property)
      (h.isGradedEulerAdmissible X.property Y.property).shiftSource i (Iso.refl Y.obj)).trans
        (gradedExtEuler_shiftSource (h.isGradedEulerAdmissible X.property Y.property))
  exact DFunLike.congr_fun (DFunLike.congr_fun hmaps x) y

private theorem gradedExtEulerPairing_shiftSourceZPow
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) (n : ℤ)
    (x : ExactK0 (((GradedExactStructure.abelian C e).fullSubcategory P
      hP hPshift).toExactStructure))
    (y : ExactK0 (((GradedExactStructure.abelian C e).fullSubcategory Q
      hQ hQshift).toExactStructure)) :
    gradedExtEulerPairingOnGradedSubcategories hP hQ hPshift hQshift h
        (((GradedExactStructure.abelian C e).fullSubcategory P
          hP hPshift).shiftZPow n x) y =
      T (-n) * gradedExtEulerPairingOnGradedSubcategories hP hQ hPshift hQshift h x y := by
  let EP := (GradedExactStructure.abelian C e).fullSubcategory P
    hP hPshift
  let b := gradedExtEulerPairingOnGradedSubcategories hP hQ hPshift hQshift h
  let f : ExactK0 EP.toExactStructure →+ InvertedLaurentPolynomial :=
    { toFun := fun x ↦ toInvertedLaurentPolynomial (b x y)
      map_zero' := by
        exact DFunLike.congr_fun (map_zero b) y
      map_add' := by
        intro x₁ x₂
        exact DFunLike.congr_fun (map_add b x₁ x₂) y }
  have hf : ∀ x, f (EP.shiftEquiv x) = (T 1 : LaurentPolynomial ℤ) • f x := fun x => by
    apply ofInvertedLaurentPolynomial_injective
    calc
      ofInvertedLaurentPolynomial (f (EP.shiftEquiv x)) = b (EP.shiftEquiv x) y := rfl
      _ = T (-1) * b x y := by
        simpa only [b, EP] using
          gradedExtEulerPairing_shiftSource hP hQ hPshift hQshift h x y
      _ = LaurentPolynomial.invert (T 1) * b x y := by
        rw [LaurentPolynomial.invert_T]
      _ = ofInvertedLaurentPolynomial ((T 1 : LaurentPolynomial ℤ) • f x) := rfl
  calc
    b (EP.shiftZPow n x) y = ofInvertedLaurentPolynomial (f (EP.shiftZPow n x)) := rfl
    _ = ofInvertedLaurentPolynomial ((T n : LaurentPolynomial ℤ) • f x) :=
      congrArg ofInvertedLaurentPolynomial (LaurentK0.map_shiftZPow f hf n x)
    _ = LaurentPolynomial.invert (T n) * b x y := rfl
    _ = T (-n) * b x y := by rw [LaurentPolynomial.invert_T]

/-- **The q-Euler form on graded Grothendieck groups.**  It is semilinear in the first variable
for the Laurent involution `q ↦ q⁻¹` and linear in the second variable.  Its value on object
classes is the graded Ext-Euler characteristic.

The source and target properties may differ; no symmetry hypothesis is imposed. -/
noncomputable def gradedExtEulerSesquilinear
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) :
    LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P
        hP hPshift) →ₛₗ[(LaurentPolynomial.invert (R := ℤ)).toRingEquiv.toRingHom]
      LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q
        hQ hQshift) →ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ := by
  let EP := (GradedExactStructure.abelian C e).fullSubcategory P
    hP hPshift
  let EQ := (GradedExactStructure.abelian C e).fullSubcategory Q
    hQ hQshift
  let b := gradedExtEulerPairingOnGradedSubcategories hP hQ hPshift hQshift h
  refine LinearMap.mk₂'ₛₗ (LaurentPolynomial.invert (R := ℤ)).toRingEquiv.toRingHom
    (RingHom.id _) (fun x y =>
    b ((LaurentK0.ofExactK0 EP).symm x) ((LaurentK0.ofExactK0 EQ).symm y)) ?_ ?_ ?_ ?_
  · intro x₁ x₂ y
    simp
  · intro p x y
    obtain ⟨z, rfl⟩ : ∃ z, LaurentK0.ofExactK0 EP z = x :=
      ⟨(LaurentK0.ofExactK0 EP).symm x, by simp⟩
    simp only [AddEquiv.symm_apply_apply]
    induction p using LaurentPolynomial.induction_on' with
    | add p q hp hq =>
        rw [add_smul, map_add, map_add, AddMonoidHom.add_apply, hp, hq, map_add, add_smul]
    | C_mul_T n a =>
        rw [mul_smul, LaurentK0.T_smul, laurentPolynomialC_smul,
          ← map_zsmul (LaurentK0.ofExactK0 EP), AddEquiv.symm_apply_apply, map_zsmul b,
          AddMonoidHom.zsmul_apply]
        have hshift : b (EP.shiftZPow n z) ((LaurentK0.ofExactK0 EQ).symm y) =
            T (-n) * b z ((LaurentK0.ofExactK0 EQ).symm y) := by
          simpa only [b, EP, EQ] using gradedExtEulerPairing_shiftSourceZPow
            hP hQ hPshift hQshift h n z ((LaurentK0.ofExactK0 EQ).symm y)
        rw [hshift]
        simp [map_mul, smul_eq_mul, mul_assoc]
  · intro x y₁ y₂
    simp
  · intro p x y
    obtain ⟨z, rfl⟩ : ∃ z, LaurentK0.ofExactK0 EQ z = y :=
      ⟨(LaurentK0.ofExactK0 EQ).symm y, by simp⟩
    simp only [AddEquiv.symm_apply_apply, RingHom.id_apply]
    induction p using LaurentPolynomial.induction_on' with
    | add p q hp hq =>
        rw [add_smul, map_add, map_add, hp, hq, ← add_smul]
    | C_mul_T n a =>
        rw [mul_smul, LaurentK0.T_smul, laurentPolynomialC_smul,
          ← map_zsmul (LaurentK0.ofExactK0 EQ), AddEquiv.symm_apply_apply, map_zsmul (b _),
          LaurentK0.map_shiftZPow (b _) (gradedExtEulerPairing_shiftTarget
            hP hQ hPshift hQshift h _)]
        simp [smul_eq_mul, mul_assoc]

/-- The q-Euler form evaluates on two object classes as the object-level graded Ext-Euler
characteristic. -/
@[simp]
theorem gradedExtEulerSesquilinear_of_of
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)
    (X : P.FullSubcategory) (Y : Q.FullSubcategory) :
    gradedExtEulerSesquilinear hP hQ hPshift hQshift h
        (LaurentK0.of _ X) (LaurentK0.of _ Y) =
      gradedExtEuler k e (h.isGradedEulerAdmissible X.property Y.property) := by
  rw [gradedExtEulerSesquilinear]
  simp only [LinearMap.mk₂'ₛₗ_apply]
  rw [← LaurentK0.ofExactK0_exactK0_of, ← LaurentK0.ofExactK0_exactK0_of,
    AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  exact gradedExtEulerPairingOnGradedSubcategories_of_of hP hQ hPshift hQshift h X Y

/-- Shifting the first graded Grothendieck class by `n` multiplies the q-Euler form by `q⁻ⁿ`. -/
@[simp]
theorem gradedExtEulerSesquilinear_T_smul_left
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) (n : ℤ)
    (x : LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P
      hP hPshift))
    (y : LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q
      hQ hQshift)) :
    gradedExtEulerSesquilinear hP hQ hPshift hQshift h
        ((T n : LaurentPolynomial ℤ) • x) y =
      (T (-n) : LaurentPolynomial ℤ) *
        gradedExtEulerSesquilinear hP hQ hPshift hQshift h x y := by
  rw [map_smulₛₗ]
  -- Expose the ring-hom coercion used by semilinear scalar multiplication.
  change ((LaurentPolynomial.invert (R := ℤ)) (T n) •
      gradedExtEulerSesquilinear hP hQ hPshift hQshift h x) y = _
  rw [LaurentPolynomial.invert_T, LinearMap.smul_apply, smul_eq_mul]

/-- Shifting the second graded Grothendieck class by `n` multiplies the q-Euler form by `qⁿ`. -/
theorem gradedExtEulerSesquilinear_T_smul_right
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) (n : ℤ)
    (x : LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P
      hP hPshift))
    (y : LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q
      hQ hQshift)) :
    gradedExtEulerSesquilinear hP hQ hPshift hQshift h x
        ((T n : LaurentPolynomial ℤ) • y) =
      (T n : LaurentPolynomial ℤ) *
        gradedExtEulerSesquilinear hP hQ hPshift hQshift h x y := by
  simp

/-- The q-Euler form is the unique Laurent-sesquilinear map with the prescribed values on pairs
of object classes. -/
theorem gradedExtEulerSesquilinear_unique
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)
    (B : LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P
        hP hPshift) →ₛₗ[(LaurentPolynomial.invert (R := ℤ)).toRingEquiv.toRingHom]
      LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q
        hQ hQshift) →ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ)
    (hB : ∀ (X : P.FullSubcategory) (Y : Q.FullSubcategory),
      B (LaurentK0.of _ X) (LaurentK0.of _ Y) =
        gradedExtEuler k e (h.isGradedEulerAdmissible X.property Y.property)) :
    B = gradedExtEulerSesquilinear hP hQ hPshift hQshift h := by
  let EP := (GradedExactStructure.abelian C e).fullSubcategory P hP hPshift
  have houter : B.toAddMonoidHom.comp (LaurentK0.ofExactK0 EP).toAddMonoidHom =
      (gradedExtEulerSesquilinear hP hQ hPshift hQshift h).toAddMonoidHom.comp
        (LaurentK0.ofExactK0 EP).toAddMonoidHom := ExactK0.hom_ext fun X => by
    apply LaurentK0.hom_ext
    intro Y
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    rw [LaurentK0.ofExactK0_exactK0_of]
    exact (hB X Y).trans
      (gradedExtEulerSesquilinear_of_of hP hQ hPshift hQshift h X Y).symm
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ : ∃ z, LaurentK0.ofExactK0 EP z = x :=
    ⟨(LaurentK0.ofExactK0 EP).symm x, by simp⟩
  exact DFunLike.congr_fun houter z

/-- **The q-Euler form specialized at `q = ε`**, for a unit `ε : ℤˣ`, that is at `q = 1` or
`q = -1`.  It is the `ℤ`-bilinear form on the specializations of the Laurent-module Grothendieck
groups of `P` and `Q` obtained from `TauCeti.gradedExtEulerSesquilinear` by evaluating at `ε`;
since `ε⁻¹ = ε` over `ℤ`, both arguments are specialized at the same unit. -/
noncomputable def gradedExtEulerSpecialized
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) (ε : ℤˣ) :
    LaurentSpecialization ε
        (LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P hP hPshift)) →ₗ[ℤ]
      LaurentSpecialization ε
        (LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q hQ hQshift)) →ₗ[ℤ] ℤ :=
  (gradedExtEulerSesquilinear hP hQ hPshift hQshift h).laurentSpecialize (Int.units_inv_eq_self ε)

/-- The specialized q-Euler form on two specialized object classes is the graded Ext-Euler
characteristic evaluated at `q = ε`. -/
@[simp]
theorem gradedExtEulerSpecialized_mk_of_mk_of
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) (ε : ℤˣ)
    (X : P.FullSubcategory) (Y : Q.FullSubcategory) :
    gradedExtEulerSpecialized hP hQ hPshift hQshift h ε
        (LaurentSpecialization.mk ε (LaurentK0.of _ X))
        (LaurentSpecialization.mk ε (LaurentK0.of _ Y)) =
      laurentEval ε (gradedExtEuler k e (h.isGradedEulerAdmissible X.property Y.property)) := by
  rw [gradedExtEulerSpecialized, LinearMap.laurentSpecialize_mk_mk,
    gradedExtEulerSesquilinear_of_of]

end TauCeti
