/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.BaseChange.Homotopy
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Triangulated
public import TauCeti.Algebra.Homology.Curved.Triangulated

/-!
# Base change of matrix factorizations is a triangle functor

Let `f : S →+* T` be a ring map with `f w = 0`. Extension of scalars sends a finite-projective
matrix factorization of `w` to a square-zero curved duplex over `T`, and this descends to a
functor `HMF(S,w) ⥤ K(T-duplexes, 0)` between homotopy categories. Both homotopy categories are
triangulated through their componentwise split Frobenius structures, with the shift by `1` given
by the parity shift. This file shows that the descended functor is a triangle functor.

Extension of scalars commutes with the parity shift on the nose: both sides have the same
components, and the negated differentials agree because extension of scalars is additive. This
gives the compatibility with the shifts by `ℤ`. Extension of scalars is additive, so it preserves
componentwise split short complexes, and it carries the disk-sum presentation
`X ⟶ diskSum X ⟶ X[1]` to the disk-sum presentation of the image up to the canonical comparison
of scalar extension with biproducts. Hence the image of the distinguished triangle of a
componentwise split short complex is the distinguished triangle of its image. The hypersurface
reduction modulo `w` is the case `f = Ideal.Quotient.mk (Ideal.span {w})`.

## Main results

* `TauCeti.MatrixFactorization.parityShiftCompBaseChangeToCurvedDuplexIso`: base change commutes
  with the parity shifts.
* `TauCeti.MatrixFactorization.isConflationExact_baseChangeToCurvedDuplex`: base change preserves
  componentwise split conflations.
* `TauCeti.MatrixFactorization.HomotopyCategory.baseChangeToCurvedDuplex_commShiftIso_one`: the
  compatibility of homotopy-level base change with the shifts by `ℤ` is, in degree one, the
  commutation with the parity shifts.
* The `Functor.IsTriangulated` instance for
  `TauCeti.MatrixFactorization.HomotopyCategory.baseChangeToCurvedDuplex`: homotopy-level base
  change is a triangle functor.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5, for the reduction of a
  matrix factorization modulo its potential.
* D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg models*,
  Proc. Steklov Inst. Math. **246** (2004), Section 3, for the triangulated category of
  matrix factorizations.

The argument follows the triangle-functor proof for the inclusion of matrix factorizations among
curved duplexes in `TauCeti.CommutativeAlgebra.MatrixFactorization.HomotopyInclusion`.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory CategoryTheory.Limits

variable {S T : Type u} [CommRing S] [CommRing T] {w : S}

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

/-! ### Compatibilities of base change before passing to homotopy categories -/

/-- Extension of scalars of finitely generated modules, the functor applied componentwise by
`baseChangeToCurvedDuplex`. -/
private noncomputable abbrev scalarExtension (f : S →+* T) :
    FGModuleCat.{u} S ⥤ ModuleCat.{u} T :=
  forget₂ (FGModuleCat.{u} S) (ModuleCat.{u} S) ⋙ ModuleCat.extendScalars f

/-- Extension of scalars along a map killing `w` kills multiplication by `w`. -/
private theorem scalarExtension_map_smul_id (f : S →+* T) (hw : f w = 0)
    (A : FGModuleCat.{u} S) : (scalarExtension f).map (w • 𝟙 A) = (0 : T) • 𝟙 _ := by
  rw [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.map_smul,
    CategoryTheory.Functor.map_id, ModuleCat.extendScalars_map_smul_id, hw, zero_smul, zero_smul]

/-- Base change commutes with the parity shifts: both sides have the same components, and the
negated differentials agree because extension of scalars is additive. -/
noncomputable def parityShiftCompBaseChangeToCurvedDuplexIso (f : S →+* T) (hw : f w = 0) :
    parityShift ⋙ baseChangeToCurvedDuplex f hw ≅
      baseChangeToCurvedDuplex f hw ⋙ CurvedDuplex.parityShift (ModuleCat.{u} T) (0 : T) :=
  NatIso.ofComponents
    (fun X ↦ (CurvedDuplex.isoMk (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans
        ((scalarExtension f).map_neg.symm.trans (Category.comp_id _).symm))
      ((Category.id_comp _).trans
        ((scalarExtension f).map_neg.symm.trans (Category.comp_id _).symm)) :
      (baseChangeToCurvedDuplex f hw).obj (parityShift.obj X) ≅
        (CurvedDuplex.parityShift (ModuleCat.{u} T) (0 : T)).obj
          ((baseChangeToCurvedDuplex f hw).obj X)))
    (fun g ↦ by
      apply CurvedDuplex.hom_ext <;> exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The even component of `parityShiftCompBaseChangeToCurvedDuplexIso` is an identity. -/
@[simp]
theorem parityShiftCompBaseChangeToCurvedDuplexIso_hom_app_f₀ (f : S →+* T) (hw : f w = 0)
    (X : MatrixFactorization S w) :
    ((parityShiftCompBaseChangeToCurvedDuplexIso f hw).hom.app X).f₀ = 𝟙 _ := (rfl)

/-- The odd component of `parityShiftCompBaseChangeToCurvedDuplexIso` is an identity. -/
@[simp]
theorem parityShiftCompBaseChangeToCurvedDuplexIso_hom_app_f₁ (f : S →+* T) (hw : f w = 0)
    (X : MatrixFactorization S w) :
    ((parityShiftCompBaseChangeToCurvedDuplexIso f hw).hom.app X).f₁ = 𝟙 _ := (rfl)

/-- The even component of the inverse of `parityShiftCompBaseChangeToCurvedDuplexIso` is an
identity. -/
@[simp]
theorem parityShiftCompBaseChangeToCurvedDuplexIso_inv_app_f₀ (f : S →+* T) (hw : f w = 0)
    (X : MatrixFactorization S w) :
    ((parityShiftCompBaseChangeToCurvedDuplexIso f hw).inv.app X).f₀ = 𝟙 _ := (rfl)

/-- The odd component of the inverse of `parityShiftCompBaseChangeToCurvedDuplexIso` is an
identity. -/
@[simp]
theorem parityShiftCompBaseChangeToCurvedDuplexIso_inv_app_f₁ (f : S →+* T) (hw : f w = 0)
    (X : MatrixFactorization S w) :
    ((parityShiftCompBaseChangeToCurvedDuplexIso f hw).inv.app X).f₁ = 𝟙 _ := (rfl)

/-- Base change carries componentwise split conflations of matrix factorizations to
componentwise split conflations of square-zero curved duplexes: an additive functor carries a
splitting in each parity to a splitting. -/
theorem isConflationExact_baseChangeToCurvedDuplex (f : S →+* T) (hw : f w = 0) :
    (splitExact S w).IsConflationExact
      ((ExactStructure.split (ModuleCat.{u} T)).curvedDuplex (0 : T))
      (baseChangeToCurvedDuplex f hw) where
  map_conflation {X} hX := by
    obtain ⟨⟨s₀⟩, ⟨s₁⟩⟩ := (splitExact_conflation_iff X).1 hX
    rw [ExactStructure.curvedDuplex_conflation_iff, ExactStructure.split_conflation,
      ExactStructure.split_conflation]
    exact ⟨⟨s₀.map (scalarExtension f)⟩, ⟨s₁.map (scalarExtension f)⟩⟩

/-- The comparison from the base change of the disk sum of `X` to the disk sum of the base change
of `X`: in each parity it is the biproduct comparison of extension of scalars. -/
private noncomputable def diskSumComparison (f : S →+* T) (hw : f w = 0)
    (X : MatrixFactorization S w) :
    (baseChangeToCurvedDuplex f hw).obj (diskSum X) ⟶
      CurvedDuplex.diskSum ((baseChangeToCurvedDuplex f hw).obj X) :=
  CurvedDuplex.homMk ((scalarExtension f).biprodComparison X.obj.X₁ X.obj.X₀)
    ((scalarExtension f).biprodComparison X.obj.X₁ X.obj.X₀)
    (by
      have h := (Functor.biprodComparison_natural (scalarExtension f) (𝟙 X.obj.X₁)
        (-(w • 𝟙 X.obj.X₀))).symm
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_neg,
        scalarExtension_map_smul_id f hw] at h
      exact h)
    (by
      have h := (Functor.biprodComparison_natural (scalarExtension f) (w • 𝟙 X.obj.X₁)
        (-𝟙 X.obj.X₀)).symm
      rw [CategoryTheory.Functor.map_neg, CategoryTheory.Functor.map_id,
        scalarExtension_map_smul_id f hw] at h
      exact h)

/-- The disk-sum comparison carries the base change of the inclusion of `X` into its disk sum to
the inclusion of the base change of `X` into its disk sum. -/
private theorem map_toDiskSum_comp_diskSumComparison (f : S →+* T) (hw : f w = 0)
    (X : MatrixFactorization S w) :
    (baseChangeToCurvedDuplex f hw).map (toDiskSum X) ≫ diskSumComparison f hw X =
      CurvedDuplex.toDiskSum ((baseChangeToCurvedDuplex f hw).obj X) := by
  apply CurvedDuplex.hom_ext
  · have h := Functor.map_biprod_lift_comp_biprodComparison (scalarExtension f) X.obj.d₀
      (𝟙 X.obj.X₀)
    rw [CategoryTheory.Functor.map_id] at h
    simp only [CurvedDuplex.comp_f₀, baseChangeToCurvedDuplex_map_f₀, toDiskSum_hom,
      CurvedDuplex.toDiskSum_f₀]
    exact h
  · have h := Functor.map_biprod_lift_comp_biprodComparison (scalarExtension f) (𝟙 X.obj.X₁)
      (-X.obj.d₁)
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_neg] at h
    simp only [CurvedDuplex.comp_f₁, baseChangeToCurvedDuplex_map_f₁, toDiskSum_hom,
      CurvedDuplex.toDiskSum_f₁]
    exact h

/-- The disk-sum comparison carries the base change of the projection from the disk sum of `X`
onto its parity shift to the projection from the disk sum of the base change of `X` onto its
parity shift. -/
private theorem diskSumComparison_comp_diskSumToParityShift (f : S →+* T) (hw : f w = 0)
    (X : MatrixFactorization S w) :
    diskSumComparison f hw X ≫
        CurvedDuplex.diskSumToParityShift ((baseChangeToCurvedDuplex f hw).obj X) =
      (baseChangeToCurvedDuplex f hw).map (diskSumToParityShift X) ≫
        (parityShiftCompBaseChangeToCurvedDuplexIso f hw).hom.app X := by
  have := preservesBinaryBiproducts_of_preservesBiproducts (scalarExtension f)
  apply CurvedDuplex.hom_ext
  · have h := Functor.biprodComparison_comp_biprod_desc (scalarExtension f) (𝟙 X.obj.X₁)
      (-X.obj.d₀)
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_neg] at h
    simp only [CurvedDuplex.comp_f₀, baseChangeToCurvedDuplex_map_f₀, diskSumToParityShift_hom,
      CurvedDuplex.diskSumToParityShift_f₀, parityShiftCompBaseChangeToCurvedDuplexIso_hom_app_f₀]
    exact h.trans (Category.comp_id _).symm
  · have h := Functor.biprodComparison_comp_biprod_desc (scalarExtension f) (-X.obj.d₁)
      (-𝟙 X.obj.X₀)
    rw [CategoryTheory.Functor.map_neg, CategoryTheory.Functor.map_neg,
      CategoryTheory.Functor.map_id] at h
    simp only [CurvedDuplex.comp_f₁, baseChangeToCurvedDuplex_map_f₁, diskSumToParityShift_hom,
      CurvedDuplex.diskSumToParityShift_f₁, parityShiftCompBaseChangeToCurvedDuplexIso_hom_app_f₁]
    exact h.trans (Category.comp_id _).symm

/-! ### Base change on homotopy categories -/

namespace HomotopyCategory

open CategoryTheory.Pretriangulated

/-- Base change on homotopy categories commutes with the parity shifts. On the image of a
factorization `X` it is induced by `parityShiftCompBaseChangeToCurvedDuplexIso`. -/
noncomputable def parityShiftCompBaseChangeToCurvedDuplexIso (f : S →+* T) (hw : f w = 0) :
    (parityShiftEquivalence (S := S) (w := w)).functor ⋙ baseChangeToCurvedDuplex f hw ≅
      baseChangeToCurvedDuplex f hw ⋙
        (CurvedDuplex.HomotopyCategory.parityShiftEquivalence (ModuleCat.{u} T) (0 : T)).functor :=
  Quotient.natIsoLift _
    (eqToIso (by
        rw [← Functor.assoc, quotientFunctor_comp_parityShiftEquivalence_functor, Functor.assoc,
          quotientFunctor_comp_baseChangeToCurvedDuplex]
        rfl) ≪≫
      Functor.isoWhiskerRight (MatrixFactorization.parityShiftCompBaseChangeToCurvedDuplexIso f hw)
        (CurvedDuplex.nullHomotopic (ModuleCat.{u} T) (0 : T)).quotientFunctor ≪≫
      eqToIso (by
        rw [← Functor.assoc, quotientFunctor_comp_baseChangeToCurvedDuplex, Functor.assoc,
          Functor.assoc,
          CurvedDuplex.HomotopyCategory.quotientFunctor_comp_parityShiftEquivalence_functor]))

/-- On the image of a factorization `X`, the commutation of homotopy-level base change with the
parity shifts is the homotopy class of `parityShiftCompBaseChangeToCurvedDuplexIso` at `X`. -/
theorem parityShiftCompBaseChangeToCurvedDuplexIso_hom_app_quotientFunctor_obj (f : S →+* T)
    (hw : f w = 0) (X : MatrixFactorization S w) :
    (parityShiftCompBaseChangeToCurvedDuplexIso f hw).hom.app
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj X) =
      eqToHom (by simp) ≫
        (CurvedDuplex.nullHomotopic (ModuleCat.{u} T) (0 : T)).quotientFunctor.map
          ((MatrixFactorization.parityShiftCompBaseChangeToCurvedDuplexIso f hw).hom.app X) ≫
        eqToHom (by simp) := by
  simp [parityShiftCompBaseChangeToCurvedDuplexIso, eqToHom_app]

/-- Base change on homotopy categories commutes with the shifts by `ℤ` generated by the parity
shifts. -/
noncomputable instance (f : S →+* T) (hw : f w = 0) :
    (baseChangeToCurvedDuplex f hw).CommShift ℤ :=
  Functor.commShiftOfIntertwining _ _ _ (parityShiftCompBaseChangeToCurvedDuplexIso f hw)

/-- In degree one, the shift compatibility of base change on homotopy categories is its
commutation with the parity shifts. -/
theorem baseChangeToCurvedDuplex_commShiftIso_one (f : S →+* T) (hw : f w = 0) :
    (baseChangeToCurvedDuplex f hw).commShiftIso (1 : ℤ) =
      Functor.isoWhiskerRight (shiftFunctorOneIso S w) _ ≪≫
        parityShiftCompBaseChangeToCurvedDuplexIso f hw ≪≫
          Functor.isoWhiskerLeft _
            (CurvedDuplex.HomotopyCategory.shiftFunctorOneIso (ModuleCat.{u} T) (0 : T)).symm := by
  rw [shiftFunctorOneIso_def, CurvedDuplex.HomotopyCategory.shiftFunctorOneIso_def]
  exact Functor.commShiftOfIntertwining_iso_one _ _ _ _

/-- On the image of a factorization `X`, the degree-one shift compatibility of base change is
induced by `parityShiftCompBaseChangeToCurvedDuplexIso` at `X`. -/
@[reassoc]
private theorem map_parityShiftCompQuotientFunctorIso_hom_app_comp_commShiftIso_hom_app
    (f : S →+* T) (hw : f w = 0) (X : MatrixFactorization S w) :
    (baseChangeToCurvedDuplex f hw).map ((parityShiftCompQuotientFunctorIso S w).hom.app X) ≫
        ((baseChangeToCurvedDuplex f hw).commShiftIso (1 : ℤ)).hom.app
          ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj X) =
      eqToHom (by simp) ≫
        (CurvedDuplex.nullHomotopic (ModuleCat.{u} T) (0 : T)).quotientFunctor.map
          ((MatrixFactorization.parityShiftCompBaseChangeToCurvedDuplexIso f hw).hom.app X) ≫
        (CurvedDuplex.HomotopyCategory.parityShiftCompQuotientFunctorIso (ModuleCat.{u} T)
          (0 : T)).hom.app ((MatrixFactorization.baseChangeToCurvedDuplex f hw).obj X) ≫
        eqToHom (by simp) := by
  rw [baseChangeToCurvedDuplex_commShiftIso_one]
  simp [eqToHom_map, parityShiftCompBaseChangeToCurvedDuplexIso_hom_app_quotientFunctor_obj]

/-- **Base change of matrix factorizations is a triangle functor.** If `f : S →+* T` kills `w`,
the image of the distinguished triangle of a componentwise split short complex of
finite-projective factorizations of `w` is the distinguished triangle of its scalar extension,
a componentwise split short complex of square-zero curved duplexes over `T`. -/
instance (f : S →+* T) (hw : f w = 0) : (baseChangeToCurvedDuplex f hw).IsTriangulated where
  map_distinguished D hD := by
    obtain ⟨X, hX, a, δ, ha, hδ, ⟨e⟩⟩ := (mem_distTriang_iff S w D).1 hD
    let B := MatrixFactorization.baseChangeToCurvedDuplex f hw
    -- The extension of the inclusion into the disk sum, and the induced map on cokernels, are
    -- the scalar extensions of `a` and `δ`, read through the disk-sum and parity comparisons.
    refine isomorphic_distinguished _
      (CurvedDuplex.HomotopyCategory.mk_distinguished_of_conflation
        ((isConflationExact_baseChangeToCurvedDuplex f hw).map_conflation hX)
        (B.map a ≫ diskSumComparison f hw X.X₁)
        (B.map δ ≫
          (MatrixFactorization.parityShiftCompBaseChangeToCurvedDuplexIso f hw).hom.app X.X₁)
        ?_ ?_) _ ((baseChangeToCurvedDuplex f hw).mapTriangle.mapIso e ≪≫ ?_)
    · rw [ShortComplex.map_f, ← B.map_comp_assoc, ha]
      exact map_toDiskSum_comp_diskSumComparison f hw X.X₁
    · rw [ShortComplex.map_g, ← B.map_comp_assoc, hδ, B.map_comp_assoc, Category.assoc]
      exact congrArg (B.map a ≫ ·) (diskSumComparison_comp_diskSumToParityShift f hw X.X₁).symm
    · refine Triangle.isoMk _ _ (eqToIso (baseChangeToCurvedDuplex_obj_quotientFunctor_obj f hw _))
        (eqToIso (baseChangeToCurvedDuplex_obj_quotientFunctor_obj f hw _))
        (eqToIso (baseChangeToCurvedDuplex_obj_quotientFunctor_obj f hw _)) ?_ ?_ ?_
      · exact baseChangeToCurvedDuplex_map_quotientFunctor_map f hw X.f
      · exact baseChangeToCurvedDuplex_map_quotientFunctor_map f hw X.g
      · simp only [Functor.mapTriangle_obj, Triangle.mk_obj₁, Triangle.mk_mor₃,
          ShortComplex.map_X₁, eqToIso.hom, Functor.map_comp, Category.assoc,
          map_parityShiftCompQuotientFunctorIso_hom_app_comp_commShiftIso_hom_app_assoc,
          eqToHom_map, eqToHom_trans, eqToHom_refl, Category.comp_id]
        rw [← Category.assoc, baseChangeToCurvedDuplex_map_quotientFunctor_map, Category.assoc]

end HomotopyCategory

end TauCeti.MatrixFactorization
