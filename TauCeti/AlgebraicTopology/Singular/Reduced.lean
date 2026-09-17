/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Zero
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Reduced singular homology

Reduced singular homology is the kernel of the augmentation in degree zero and ordinary singular
homology in positive degrees. The inclusion into ordinary homology is natural and reduced homology
is homotopy invariant. A chosen point splits zeroth homology as reduced homology plus the
coefficient object; the splitting commutes with maps preserving that point.

Coefficients lie in a preadditive category with coproducts, homology and kernels. The splitting
isomorphism additionally uses binary biproducts. No connectedness assumption is needed for the
splitting; for a path-connected space the reduced group in degree zero vanishes.

This follows Hatcher, *Algebraic Topology*, Section 2.1, using Mathlib's singular homology and
augmentation and `ShortComplex.Splitting.isoBinaryBiproduct`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C] (R : C)

/-- The augmentation of zeroth singular homology is natural in the space. -/
@[reassoc (attr := simp)]
lemma singularHomologyMap_comp_ε {X Y : TopCat.{w}} (f : X ⟶ Y) :
    ((singularHomologyFunctor C 0).obj R).map f ≫ Y.singularHomology₀ε R =
      X.singularHomology₀ε R :=
  SSet.homologyMap_homology₀ε R (TopCat.toSSet.map f)

/-- The class of a chosen point gives a section of the singular augmentation. -/
def singularHomology₀Section {X : TopCat.{w}} (x : X) :
    R ⟶ ((singularHomologyFunctor C 0).obj R).obj X :=
  SSet.ιHomology₀ R (TopCat.toSSetObj₀Equiv.symm x)

lemma singularHomology₀Section_def {X : TopCat.{w}} (x : X) :
    singularHomology₀Section R x = SSet.ιHomology₀ R (TopCat.toSSetObj₀Equiv.symm x) := (rfl)

@[reassoc (attr := simp)]
lemma singularHomology₀Section_comp_ε {X : TopCat.{w}} (x : X) :
    singularHomology₀Section R x ≫ X.singularHomology₀ε R = 𝟙 R :=
  SSet.ιHomology₀_homology₀ε R _

@[reassoc (attr := simp)]
lemma singularHomology₀Section_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    singularHomology₀Section R x ≫ ((singularHomologyFunctor C 0).obj R).map f =
      singularHomology₀Section R (f x) := by
  exact (SSet.ιHomology₀_homologyMap R (TopCat.toSSet.map f)
    (TopCat.toSSetObj₀Equiv.symm x)).trans (by rfl)

variable [HasKernels C]

/-- Reduced singular homology: the augmentation kernel in degree zero and ordinary singular
homology in positive degrees. -/
def reducedSingularHomologyFunctor : ℕ → TopCat.{w} ⥤ C
  | 0 =>
    { obj X := kernel (X.singularHomology₀ε R)
      map {X Y} f := kernel.map _ _ (((singularHomologyFunctor C 0).obj R).map f)
        (𝟙 R) (by simp)
      map_id X := by simp
      map_comp f g := by ext; simp }
  | n + 1 => (singularHomologyFunctor C (n + 1)).obj R

@[simp]
lemma reducedSingularHomologyFunctor_zero_obj (X : TopCat.{w}) :
    (reducedSingularHomologyFunctor R 0).obj X = kernel (X.singularHomology₀ε R) := (rfl)

@[simp]
lemma reducedSingularHomologyFunctor_succ (n : ℕ) :
    reducedSingularHomologyFunctor R (n + 1) =
      (singularHomologyFunctor C (n + 1)).obj R := (rfl)

/-- The canonical inclusion from reduced to ordinary singular homology. -/
def reducedSingularHomologyι : (n : ℕ) →
    reducedSingularHomologyFunctor R n ⟶ (singularHomologyFunctor C n).obj R
  | 0 =>
    { app X := kernel.ι (X.singularHomology₀ε R)
      naturality f := by simp [reducedSingularHomologyFunctor] }
  | _ + 1 => 𝟙 _

@[simp]
lemma reducedSingularHomologyι_zero_app (X : TopCat.{w}) :
    (reducedSingularHomologyι R 0).app X =
      eqToHom (reducedSingularHomologyFunctor_zero_obj R X) ≫
        kernel.ι (X.singularHomology₀ε R) := by
  exact (Category.id_comp (kernel.ι (X.singularHomology₀ε R))).symm

@[simp]
lemma reducedSingularHomologyι_succ_app (n : ℕ) (X : TopCat.{w}) :
    (reducedSingularHomologyι R (n + 1)).app X =
      eqToHom (Functor.congr_obj (reducedSingularHomologyFunctor_succ R n) X) := (rfl)

instance (n : ℕ) (X : TopCat.{w}) : Mono ((reducedSingularHomologyι R n).app X) := by
  cases n <;> simp only [reducedSingularHomologyι_zero_app,
    reducedSingularHomologyι_succ_app] <;> infer_instance

/-- Reduced and ordinary singular homology agree naturally in positive degrees. -/
def reducedSingularHomologySuccIso (n : ℕ) :
    reducedSingularHomologyFunctor R (n + 1) ≅
      (singularHomologyFunctor C (n + 1)).obj R :=
  eqToIso (reducedSingularHomologyFunctor_succ R n)

@[simp]
lemma reducedSingularHomologySuccIso_hom (n : ℕ) :
    (reducedSingularHomologySuccIso R n).hom = reducedSingularHomologyι R (n + 1) := (rfl)

/-- Homotopic continuous maps induce the same map on reduced singular homology. -/
lemma reducedSingularHomologyFunctor_map_eq_of_homotopy {X Y : TopCat.{w}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (n : ℕ) :
    (reducedSingularHomologyFunctor R n).map f =
      (reducedSingularHomologyFunctor R n).map g := by
  apply (cancel_mono ((reducedSingularHomologyι R n).app Y)).1
  rw [(reducedSingularHomologyι R n).naturality,
    (reducedSingularHomologyι R n).naturality]
  exact congrArg (((reducedSingularHomologyι R n).app X) ≫ ·)
    (H.congr_homologyMap_singularChainComplexFunctor R n)

/-- The reduced zeroth homology of a path-connected space is zero. -/
lemma isZero_reducedSingularHomologyFunctor_zero (X : TopCat.{w}) [PathConnectedSpace X] :
    IsZero ((reducedSingularHomologyFunctor R 0).obj X) :=
  isZero_kernel_of_mono (X.singularHomology₀ε R)

/-- The augmentation sequence split by the class of a chosen point. -/
private def singularHomology₀Splitting {X : TopCat.{w}} (x : X) :
    (ShortComplex.mk (kernel.ι (X.singularHomology₀ε R)) (X.singularHomology₀ε R)
      (kernel.condition _)).Splitting where
  r := kernel.lift _ (𝟙 _ - X.singularHomology₀ε R ≫ singularHomology₀Section R x)
    (by simp [Preadditive.sub_comp])
  s := singularHomology₀Section R x
  f_r := by
    apply (cancel_mono (kernel.ι (X.singularHomology₀ε R))).1
    simp [Preadditive.comp_sub]
  s_g := singularHomology₀Section_comp_ε R x
  id := by simp

variable [HasBinaryBiproducts C]

/-- A basepoint splits ordinary zeroth singular homology into its reduced part and one copy of
the coefficient object. -/
def singularHomology₀SplitIso {X : TopCat.{w}} (x : X) :
    ((singularHomologyFunctor C 0).obj R).obj X ≅
      (reducedSingularHomologyFunctor R 0).obj X ⊞ R :=
  (singularHomology₀Splitting R x).isoBinaryBiproduct

@[reassoc (attr := simp)]
lemma singularHomology₀SplitIso_hom_snd {X : TopCat.{w}} (x : X) :
    (singularHomology₀SplitIso R x).hom ≫ biprod.snd = X.singularHomology₀ε R := by
  exact biprod.lift_snd _ _

@[reassoc (attr := simp)]
lemma inl_singularHomology₀SplitIso_inv {X : TopCat.{w}} (x : X) :
    biprod.inl ≫ (singularHomology₀SplitIso R x).inv =
      (reducedSingularHomologyι R 0).app X := by
  exact biprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma inr_singularHomology₀SplitIso_inv {X : TopCat.{w}} (x : X) :
    biprod.inr ≫ (singularHomology₀SplitIso R x).inv = singularHomology₀Section R x := by
  exact biprod.inr_desc _ _

/-- The splitting of zeroth homology is natural in pointed maps. -/
@[reassoc]
lemma singularHomology₀SplitIso_inv_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    biprod.map ((reducedSingularHomologyFunctor R 0).map f) (𝟙 R) ≫
        (singularHomology₀SplitIso R (f x)).inv =
      (singularHomology₀SplitIso R x).inv ≫ ((singularHomologyFunctor C 0).obj R).map f := by
  apply biprod.hom_ext'
  · simp only [biprod.inl_map_assoc, inl_singularHomology₀SplitIso_inv,
      inl_singularHomology₀SplitIso_inv_assoc, (reducedSingularHomologyι R 0).naturality]
  · simp

end TauCeti
