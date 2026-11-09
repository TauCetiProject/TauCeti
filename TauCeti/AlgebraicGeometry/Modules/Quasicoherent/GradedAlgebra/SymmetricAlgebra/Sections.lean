/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Sections
public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Sections
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Sections
-- Identify the homogeneous components and their multiplication in the comparison proofs.
import all TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.Basic
import all TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Sections
import all TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Sections
import all TauCeti.AlgebraicGeometry.Modules.TensorProduct
import all TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Basic
import all TauCeti.Algebra.Category.ModuleCat.Presheaf.SymmetricPower.Basic
import all TauCeti.Algebra.Category.ModuleCat.SymmetricPower.Mul

/-!
# Affine sections of graded symmetric algebras

For a quasicoherent sheaf `F` and an affine open `U`, the native graded ring
`⨁ n, Γ(Symⁿ F, U)` is canonically the symmetric algebra of the module `Γ(F, U)`.
The comparison is the sheafification map in each degree, so it retains the homogeneous
multiplication, not just the underlying module. It is natural in `F` and compatible with
restriction between affine opens. No finiteness, freeness or flatness is required.

The construction combines `Scheme.Modules.symmetricPowerSectionsIso` with the internal
grading of `TauCeti.SymmetricAlgebra.gradedAlgebra`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2 and Exercise II.5.16.
-/

public section

open CategoryTheory MonoidalCategory Opposite DirectSum

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}} (F : QuasicoherentSheaf X) {U : X.Opens}

/-- The affine symmetric-power comparison, with codomain the actual graded component. -/
private def sectionsDegreeIso (hU : IsAffineOpen U) (n : ℕ) :
    ((Scheme.Modules.sectionsFunctor U).obj F.obj).symmetricPower n ≅
      (Scheme.Modules.sectionsFunctor U).obj (((gradedSymmetricAlgebra X).obj F).obj.X n) :=
  Scheme.Modules.symmetricPowerSectionsIso (F.obj : X.Modules) hU n ≪≫
    (Scheme.Modules.sectionsFunctor U).mapIso
      (eqToIso (gradedSymmetricAlgebra_obj_obj_X F n).symm)

/-- Homogeneous multiplication is preserved by the affine symmetric-power comparisons. -/
private lemma sectionsDegreeIso_mul (hU : IsAffineOpen U) (i j : ℕ)
    (x : ((Scheme.Modules.sectionsFunctor U).obj F.obj).symmetricPower i)
    (y : ((Scheme.Modules.sectionsFunctor U).obj F.obj).symmetricPower j) :
    (sectionsDegreeIso F hU (i + j)).hom
      (GradedMonoid.GMul.mul
        (A := fun n ↦ ↥(TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(X, U)
          ((Scheme.Modules.sectionsFunctor U).obj F.obj) n)) x y) =
      GradedMonoid.GMul.mul (A := fun n ↦ Γ(((gradedSymmetricAlgebra X).obj F).obj.X n, U))
        ((sectionsDegreeIso F hU i).hom x) ((sectionsDegreeIso F hU j).hom y) := by
  have h := congrArg (fun α ↦ PresheafOfModules.Hom.app' (R := X.presheaf) α (op U))
    (SheafOfModules.symmetricPowerUnit_mul F.obj i j)
  have hv := ConcreteCategory.congr_hom h (TensorProduct.tmul Γ(X, U) x y)
  -- The graded components are the symmetric powers. Their defining transports are identities;
  -- the tensor comparison of sections is the sectionwise tensor comparison of `forget`.
  erw [CommMon.sections_gMul_def, mul_gradedSymmetricAlgebra]
  exact hv.symm

/-- The direct sum of the affine symmetric-power comparisons. -/
private def sectionsLinearEquiv (hU : IsAffineOpen U) :
    (⨁ n, TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(X, U)
      ((Scheme.Modules.sectionsFunctor U).obj F.obj) n) ≃ₗ[Γ(X, U)]
      (⨁ n, Γ(((gradedSymmetricAlgebra X).obj F).obj.X n, U)) :=
  DirectSum.congrLinearEquiv fun n ↦ (sectionsDegreeIso F hU n).toLinearEquiv

private lemma sectionsLinearEquiv_of (hU : IsAffineOpen U) (n : ℕ)
    (x : TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(X, U)
      ((Scheme.Modules.sectionsFunctor U).obj F.obj) n) :
    sectionsLinearEquiv F hU (DirectSum.of _ n x) =
      DirectSum.of _ n ((sectionsDegreeIso F hU n).hom x) := by
  exact (congrFun (DirectSum.coe_congrLinearEquiv
    (fun n ↦ (sectionsDegreeIso F hU n).toLinearEquiv)) _).trans
      (DirectSum.lmap_lof (fun n ↦ (sectionsDegreeIso F hU n).toLinearEquiv.toLinearMap) n x)

private lemma sectionsLinearEquiv_of_mul_of (hU : IsAffineOpen U) (i j : ℕ)
    (x : TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(X, U)
      ((Scheme.Modules.sectionsFunctor U).obj F.obj) i)
    (y : TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(X, U)
      ((Scheme.Modules.sectionsFunctor U).obj F.obj) j) :
    sectionsLinearEquiv F hU (DirectSum.of _ i x * DirectSum.of _ j y) =
      sectionsLinearEquiv F hU (DirectSum.of _ i x) *
        sectionsLinearEquiv F hU (DirectSum.of _ j y) := by
  -- Fix the grading index explicitly: inferring it from `x` and `y` instead chooses submodules
  -- as indices. Composing the homogeneous equations as terms also avoids expensive rewrites
  -- through the bundled section modules.
  exact (congrArg (sectionsLinearEquiv F hU)
    (DirectSum.of_mul_of
      (A := fun n ↦ ↥(TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(X, U)
        ((Scheme.Modules.sectionsFunctor U).obj F.obj) n)) x y)).trans
    ((sectionsLinearEquiv_of F hU (i + j) _).trans
      ((congrArg (DirectSum.of _ (i + j)) (sectionsDegreeIso_mul F hU i j x y)).trans
        ((DirectSum.of_mul_of _ _).symm.trans
          (congrArg₂ (· * ·) (sectionsLinearEquiv_of F hU i x).symm
            (sectionsLinearEquiv_of F hU j y).symm))))

private lemma sectionsLinearEquiv_mul (hU : IsAffineOpen U)
    (x y : ⨁ n, TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(X, U)
      ((Scheme.Modules.sectionsFunctor U).obj F.obj) n) :
    sectionsLinearEquiv F hU (x * y) = sectionsLinearEquiv F hU x * sectionsLinearEquiv F hU y := by
  induction x using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i x =>
    induction y using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j y => exact sectionsLinearEquiv_of_mul_of F hU i j x y
    | add y z hy hz => simp only [mul_add, map_add, hy, hz]
  | add x z hx hz => simp only [add_mul, map_add, hx, hz]

/-- The native graded ring of sections of the graded symmetric algebra on an affine open `U`
is the symmetric algebra of the module of sections on `U`. It sends each homogeneous tensor
to its image under the sheafification unit in the same degree. -/
def gradedSymmetricAlgebraSectionsEquiv (hU : IsAffineOpen U) :
    SymmetricAlgebra Γ(X, U) ((Scheme.Modules.sectionsFunctor U).obj F.obj) ≃ₐ[Γ(X, U)]
      (⨁ n, Γ(((gradedSymmetricAlgebra X).obj F).obj.X n, U)) :=
  (DirectSum.decomposeAlgEquiv
    (TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(X, U)
      ((Scheme.Modules.sectionsFunctor U).obj F.obj))).trans <|
    AlgEquiv.ofLinearEquiv (sectionsLinearEquiv F hU)
      (MulEquiv.map_one
        { (sectionsLinearEquiv F hU).toEquiv with map_mul' := sectionsLinearEquiv_mul F hU })
      (sectionsLinearEquiv_mul F hU)

/-- The affine comparison sends a homogeneous tensor of degree `n` to the corresponding section
of the degree-`n` summand, via the canonical symmetric-power comparison. -/
@[simp]
lemma gradedSymmetricAlgebraSectionsEquiv_homogeneous (hU : IsAffineOpen U) (n : ℕ)
    (x : TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(X, U)
      ((Scheme.Modules.sectionsFunctor U).obj F.obj) n) :
    gradedSymmetricAlgebraSectionsEquiv F hU x.1 = DirectSum.of _ n
      (((Scheme.Modules.sectionsFunctor U).map
          (eqToHom (gradedSymmetricAlgebra_obj_obj_X F n).symm))
        ((Scheme.Modules.symmetricPowerSectionsIso (F.obj : X.Modules) hU n).hom x)) := by
  dsimp only [gradedSymmetricAlgebraSectionsEquiv, AlgEquiv.trans_apply,
    DirectSum.decomposeAlgEquiv_apply, AlgEquiv.ofLinearEquiv_apply]
  rw [DirectSum.decompose_of_mem _ x.2]
  exact sectionsLinearEquiv_of F hU n x

/-- The inverse comparison takes a section of degree `n` to the corresponding homogeneous
tensor, using the inverse affine symmetric-power comparison. -/
@[simp]
lemma gradedSymmetricAlgebraSectionsEquiv_symm_of (hU : IsAffineOpen U) (n : ℕ)
    (x : Γ(((gradedSymmetricAlgebra X).obj F).obj.X n, U)) :
    (gradedSymmetricAlgebraSectionsEquiv F hU).symm (DirectSum.of _ n x) =
      ((Scheme.Modules.symmetricPowerSectionsIso (F.obj : X.Modules) hU n).inv
        (((Scheme.Modules.sectionsFunctor U).map
          (eqToHom (gradedSymmetricAlgebra_obj_obj_X F n))) x)).1 := by
  apply (AlgEquiv.symm_apply_eq _).mpr
  have h := gradedSymmetricAlgebraSectionsEquiv_homogeneous F hU n
    ((sectionsDegreeIso F hU n).inv x)
  exact (congrArg (DirectSum.of _ n)
    ((sectionsDegreeIso F hU n).inv_hom_id_apply x)).symm.trans h.symm

/-- The affine comparison identifies exactly the degree-`n` homogeneous pieces. -/
@[simp]
lemma gradedSymmetricAlgebraSectionsEquiv_mem_grade_iff (hU : IsAffineOpen U) (n : ℕ)
    (a : SymmetricAlgebra Γ(X, U) ((Scheme.Modules.sectionsFunctor U).obj F.obj)) :
    gradedSymmetricAlgebraSectionsEquiv F hU a ∈
        (((gradedSymmetricAlgebra X).obj F).obj.gradedSectionsGrading U n) ↔
      a ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(X, U)
        ((Scheme.Modules.sectionsFunctor U).obj F.obj) n := by
  constructor
  · intro ha
    obtain ⟨x, hx⟩ := DirectSum.mem_summand.mp ha
    have h := congrArg (gradedSymmetricAlgebraSectionsEquiv F hU).symm hx
    rw [gradedSymmetricAlgebraSectionsEquiv_symm_of, AlgEquiv.symm_apply_apply] at h
    exact h ▸ ((Scheme.Modules.symmetricPowerSectionsIso (F.obj : X.Modules) hU n).inv
      (((Scheme.Modules.sectionsFunctor U).map
        (eqToHom (gradedSymmetricAlgebra_obj_obj_X F n))) x)).2
  · intro ha
    rw [gradedSymmetricAlgebraSectionsEquiv_homogeneous F hU n ⟨a, ha⟩]
    exact CommMon.of_mem_gradedSectionsGrading _ n _

/-- Naturality of the degreewise affine comparisons. -/
private lemma sectionsDegreeIso_naturality {G : QuasicoherentSheaf X} (φ : F ⟶ G)
    (hU : IsAffineOpen U) (n : ℕ)
    (x : ((Scheme.Modules.sectionsFunctor U).obj F.obj).symmetricPower n) :
    (sectionsDegreeIso G hU n).hom
        (ModuleCat.symmetricPower.map ((Scheme.Modules.sectionsFunctor U).map φ.hom) n x) =
      (((gradedSymmetricAlgebra X).map φ).hom.hom.hom n).app U
        ((sectionsDegreeIso F hU n).hom x) := by
  erw [gradedSymmetricAlgebra_map_hom_hom_hom]
  exact ConcreteCategory.congr_hom
    (Scheme.Modules.symmetricPowerSectionsIso_hom_naturality
      (F.obj : X.Modules) φ.hom hU n) x

/-- The affine graded symmetric-algebra comparison is natural in the quasicoherent sheaf. -/
lemma gradedSymmetricAlgebraSectionsEquiv_naturality {G : QuasicoherentSheaf X} (φ : F ⟶ G)
    (hU : IsAffineOpen U)
    (a : SymmetricAlgebra Γ(X, U) ((Scheme.Modules.sectionsFunctor U).obj F.obj)) :
    CommMon.gradedSectionsMap ((gradedSymmetricAlgebra X).map φ).hom U
        (gradedSymmetricAlgebraSectionsEquiv F hU a) =
      gradedSymmetricAlgebraSectionsEquiv G hU
        (SymmetricAlgebra.map Γ(X, U) ((Scheme.Modules.sectionsFunctor U).map φ.hom).hom a) := by
  refine DirectSum.Decomposition.inductionOn
    (TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(X, U)
      ((Scheme.Modules.sectionsFunctor U).obj F.obj)) ?_ (fun {n} x ↦ ?_)
      (fun a b ha hb ↦ ?_) a
  · simp only [map_zero]
  · have hmap := ModuleCat.symmetricPower.coe_map_apply
      ((Scheme.Modules.sectionsFunctor U).map φ.hom) n x
    rw [← hmap, gradedSymmetricAlgebraSectionsEquiv_homogeneous,
      gradedSymmetricAlgebraSectionsEquiv_homogeneous]
    erw [CommMon.gradedSectionsMap_of]
    exact congrArg (DirectSum.of _ n) (sectionsDegreeIso_naturality F φ hU n x).symm
  · simp only [map_add, ha, hb]

/-- Compatibility of the degreewise affine comparison with restriction. -/
private lemma sectionsDegreeIso_restrict (hU : IsAffineOpen U) {V : X.Opens}
    (hV : IsAffineOpen V) (i : V ⟶ U) (n : ℕ)
    (x : ((Scheme.Modules.sectionsFunctor U).obj F.obj).symmetricPower n) :
    (((gradedSymmetricAlgebra X).obj F).obj.X n).val.map i.op
        ((sectionsDegreeIso F hU n).hom x) =
      (sectionsDegreeIso F hV n).hom
        (((PresheafOfModulesOfCommRing.symmetricPower n).obj F.obj.val).map i.op x) :=
  Scheme.Modules.symmetricPowerSectionsIso_hom_restrict (F.obj : X.Modules) hU hV i n x

/-- Restriction between affine opens corresponds to the symmetric algebra of the semilinear
restriction map of sections. In particular the comparison retains the affine localization maps. -/
lemma gradedSymmetricAlgebraSectionsEquiv_restrict (hU : IsAffineOpen U) {V : X.Opens}
    (hV : IsAffineOpen V) (i : V ⟶ U)
    (a : SymmetricAlgebra Γ(X, U) ((Scheme.Modules.sectionsFunctor U).obj F.obj)) :
    ((gradedSymmetricAlgebra X).obj F).obj.restrictGradedSections i
        (gradedSymmetricAlgebraSectionsEquiv F hU a) =
      gradedSymmetricAlgebraSectionsEquiv F hV
        (SymmetricAlgebra.mapₛₗ
          ((ModuleCat.semilinearMapAddEquiv (X.presheaf.map i.op).hom _ _).symm
            (PresheafOfModulesOfCommRing.map (R := X.presheaf) F.obj.val i.op)) a) := by
  let ρ : SymmetricAlgebra Γ(X, U) ((Scheme.Modules.sectionsFunctor U).obj F.obj) →+*
      SymmetricAlgebra Γ(X, V) ((Scheme.Modules.sectionsFunctor V).obj F.obj) :=
    SymmetricAlgebra.mapₛₗ
      ((ModuleCat.semilinearMapAddEquiv (X.presheaf.map i.op).hom _ _).symm
        (PresheafOfModulesOfCommRing.map (R := X.presheaf) F.obj.val i.op))
  -- The named ring map fixes the section-module presentations before rewriting its laws.
  change _ = gradedSymmetricAlgebraSectionsEquiv F hV (ρ a)
  refine DirectSum.Decomposition.inductionOn
    (TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(X, U)
      ((Scheme.Modules.sectionsFunctor U).obj F.obj)) ?_ (fun {n} x ↦ ?_)
      (fun a b ha hb ↦ ?_) a
  · simp only [map_zero]
  · have hmap :
        (((PresheafOfModulesOfCommRing.symmetricPower n).obj F.obj.val).map i.op x).1 = ρ x.1 :=
      PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply n F.obj.val i.op x
    erw [← hmap, gradedSymmetricAlgebraSectionsEquiv_homogeneous,
      gradedSymmetricAlgebraSectionsEquiv_homogeneous]
    erw [CommMon.restrictGradedSections_of]
    exact congrArg (DirectSum.of _ n) (sectionsDegreeIso_restrict F hU hV i n x)
  · simp only [map_add, ha, hb]

end

end TauCeti.AlgebraicGeometry
