/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Zero
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.CategoryTheory.Limits.Shapes.Products
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Reduced singular homology

Reduced singular homology is the kernel of the augmentation in degree zero and ordinary singular
homology in positive degrees. The inclusion into ordinary homology is natural and reduced homology
is homotopy invariant. A chosen point splits zeroth homology as reduced homology plus the
coefficient object; the splitting commutes with maps preserving that point.

Coefficients lie in a preadditive category with coproducts, homology and kernels. The splitting
isomorphism additionally uses binary biproducts. No connectedness assumption is needed for the
splitting; for a path-connected space the reduced homology object in degree zero vanishes, and for
the empty space reduced homology vanishes in every degree.

In degree zero, a chosen point identifies reduced homology with the coproduct of copies of the
coefficient object indexed by the path components other than that of the point
(`TauCeti.reducedSingularHomology₀Iso`); the generator at the component of `y` is the class
`[y] - [x]`. This is the kernel of the codiagonal of Mathlib's `TopCat.singularHomology₀Iso`.

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
lemma singularHomologyMap_singularHomology₀ε {X Y : TopCat.{w}} (f : X ⟶ Y) :
    ((singularHomologyFunctor C 0).obj R).map f ≫ Y.singularHomology₀ε R =
      X.singularHomology₀ε R :=
  SSet.homologyMap_homology₀ε R (TopCat.toSSet.map f)

/-- The class of a chosen point gives a section of the singular augmentation. -/
def singularHomology₀Section {X : TopCat.{w}} (x : X) :
    R ⟶ ((singularHomologyFunctor C 0).obj R).obj X :=
  SSet.ιHomology₀ R (TopCat.toSSetObj₀Equiv.symm x)

lemma singularHomology₀Section_def {X : TopCat.{w}} (x : X) :
    singularHomology₀Section R x = SSet.ιHomology₀ R (TopCat.toSSetObj₀Equiv.symm x) := (rfl)

/-- The class of a chosen point is a right inverse to the augmentation. -/
@[reassoc (attr := simp)]
lemma singularHomology₀Section_singularHomology₀ε {X : TopCat.{w}} (x : X) :
    singularHomology₀Section R x ≫ X.singularHomology₀ε R = 𝟙 R :=
  SSet.ιHomology₀_homology₀ε R _

/-- The section is natural in the chosen point under continuous maps. -/
@[reassoc (attr := simp)]
lemma singularHomology₀Section_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    singularHomology₀Section R x ≫ ((singularHomologyFunctor C 0).obj R).map f =
      singularHomology₀Section R (f x) := by
  exact (SSet.ιHomology₀_homologyMap R (TopCat.toSSet.map f)
    (TopCat.toSSetObj₀Equiv.symm x)).trans
      (congrArg (SSet.ιHomology₀ R) (TopCat.toSSet_map_app_toSSetObj₀Equiv_symm f x))

/-- Mathlib's identification of zeroth homology with the coproduct over path components sends the
class of a point to the coproduct inclusion indexed by its path component. -/
@[reassoc (attr := simp)]
lemma singularHomology₀Section_singularHomology₀Iso_hom {X : TopCat.{w}} (x : X) :
    singularHomology₀Section R x ≫ (X.singularHomology₀Iso R).hom =
      Sigma.ι (fun _ : ZerothHomotopy X ↦ R) (ZerothHomotopy.mk x) := by
  -- `TopCat.singularHomology₀Iso` is stated on `singularHomologyFunctor`, which is by definition
  -- the homology of `TopCat.toSSet`; the statement is restated at that definitional unfolding so
  -- that the simplicial lemma `TauCeti.SSet.ιHomology₀_homology₀Iso_hom` applies.
  change SSet.ιHomology₀ R (TopCat.toSSetObj₀Equiv.symm x) ≫
    ((TopCat.toSSet.obj X).homology₀Iso R ≪≫
      (sigmaConst.obj R).mapIso TopCat.zerothHomotopyEquiv.toIso.symm).hom = _
  simp [sigmaConst]

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

/-- A homotopy equivalence induces an isomorphism on reduced singular homology in every degree,
with inverse induced by the homotopy inverse. -/
def _root_.ContinuousMap.HomotopyEquiv.reducedSingularHomologyIso {X Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (reducedSingularHomologyFunctor R n).obj (TopCat.of X) ≅
      (reducedSingularHomologyFunctor R n).obj (TopCat.of Y) where
  hom := (reducedSingularHomologyFunctor R n).map (TopCat.ofHom e.toFun)
  inv := (reducedSingularHomologyFunctor R n).map (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← Functor.map_comp, ← CategoryTheory.Functor.map_id]
    exact reducedSingularHomologyFunctor_map_eq_of_homotopy R e.left_inv.some n
  inv_hom_id := by
    rw [← Functor.map_comp, ← CategoryTheory.Functor.map_id]
    exact reducedSingularHomologyFunctor_map_eq_of_homotopy R e.right_inv.some n

@[simp]
lemma _root_.ContinuousMap.HomotopyEquiv.reducedSingularHomologyIso_hom {X Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (e.reducedSingularHomologyIso R n).hom =
      (reducedSingularHomologyFunctor R n).map (TopCat.ofHom e.toFun) := (rfl)

@[simp]
lemma _root_.ContinuousMap.HomotopyEquiv.reducedSingularHomologyIso_inv {X Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (e.reducedSingularHomologyIso R n).inv =
      (reducedSingularHomologyFunctor R n).map (TopCat.ofHom e.invFun) := (rfl)

/-- The reduced zeroth homology of a path-connected space is zero. -/
lemma isZero_reducedSingularHomologyFunctor_zero (X : TopCat.{w}) [PathConnectedSpace X] :
    IsZero ((reducedSingularHomologyFunctor R 0).obj X) :=
  isZero_kernel_of_mono (X.singularHomology₀ε R)

/-- The reduced singular homology of the empty space vanishes in every degree. -/
lemma isZero_reducedSingularHomologyFunctor_of_isEmpty (X : TopCat.{w}) [IsEmpty X] (n : ℕ) :
    IsZero ((reducedSingularHomologyFunctor R n).obj X) := by
  cases n with
  | zero =>
    have hπ : IsEmpty (ZerothHomotopy X) :=
      ⟨fun c ↦ ZerothHomotopy.rec (motive := fun _ ↦ False) (fun x ↦ isEmptyElim x) c⟩
    have h₀ : IsZero (((singularHomologyFunctor C 0).obj R).obj X) :=
      ((IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun c ↦ isEmptyElim c)).of_iso
        (X.singularHomology₀Iso R)
    rw [reducedSingularHomologyFunctor_zero_obj, IsZero.iff_id_eq_zero,
      ← cancel_mono (kernel.ι (X.singularHomology₀ε R))]
    exact h₀.eq_of_tgt _ _
  | succ n =>
    exact (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C (n + 1) R X
      n.succ_ne_zero).of_iso ((reducedSingularHomologySuccIso R n).app X)

/-- **Reduced homology in degree zero is free on the path components other than that of a
basepoint.**  A point `x` identifies the reduced zeroth singular homology of `X` with the
coproduct of copies of `R` indexed by the path components of `X` different from that of `x`.  The
generator at the component of `y` corresponds to the class `[y] - [x]`
(`TauCeti.ι_reducedSingularHomology₀Iso_inv_ι`). -/
def reducedSingularHomology₀Iso {X : TopCat.{w}} (x : X) :
    (reducedSingularHomologyFunctor R 0).obj X ≅
      ∐ fun _ : {c : ZerothHomotopy X // c ≠ ZerothHomotopy.mk x} ↦ R :=
  haveI := hasCoproducts_shrink.{0, w} (C := C)
  haveI : HasZeroObject C := ⟨_, initialIsInitial.isZero⟩
  eqToIso (reducedSingularHomologyFunctor_zero_obj R X) ≪≫
    kernelIsoOfEq (X.singularHomology₀Iso_sigma_desc_id R).symm ≪≫
    kernelIsIsoComp (X.singularHomology₀Iso R).hom (Sigma.desc fun _ ↦ 𝟙 R) ≪≫
    kernelSigmaDescIdIso R (ZerothHomotopy.mk x)

/-- The generator of `TauCeti.reducedSingularHomology₀Iso` at the path component of `y` is the
class `[y] - [x]` in ordinary zeroth homology. -/
-- Not a simp lemma: `reducedSingularHomologyι_zero_app` rewrites the degree-zero inclusion
-- inside the left-hand side first, so this would fail the `simpNF` linter.
@[reassoc]
lemma ι_reducedSingularHomology₀Iso_inv_ι {X : TopCat.{w}} (x y : X)
    (h : ZerothHomotopy.mk y ≠ ZerothHomotopy.mk x) :
    Sigma.ι (fun _ : {c : ZerothHomotopy X // c ≠ ZerothHomotopy.mk x} ↦ R) ⟨.mk y, h⟩ ≫
        (reducedSingularHomology₀Iso R x).inv ≫ (reducedSingularHomologyι R 0).app X =
      singularHomology₀Section R y - singularHomology₀Section R x := by
  simp [reducedSingularHomology₀Iso, ← singularHomology₀Section_singularHomology₀Iso_hom]

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
  s_g := singularHomology₀Section_singularHomology₀ε R x
  id := by simp

variable [HasBinaryBiproducts C]

/-- A basepoint splits ordinary zeroth singular homology into its reduced part and one copy of
the coefficient object. -/
def singularHomology₀SplitIso {X : TopCat.{w}} (x : X) :
    ((singularHomologyFunctor C 0).obj R).obj X ≅
      (reducedSingularHomologyFunctor R 0).obj X ⊞ R :=
  (singularHomology₀Splitting R x).isoBinaryBiproduct

/-- The reduced projection subtracts the chosen point class weighted by the augmentation. -/
@[reassoc (attr := simp)]
lemma singularHomology₀SplitIso_hom_fst {X : TopCat.{w}} (x : X) :
    (singularHomology₀SplitIso R x).hom ≫ biprod.fst =
      kernel.lift (X.singularHomology₀ε R)
        (𝟙 _ - X.singularHomology₀ε R ≫ singularHomology₀Section R x)
        (by simp [Preadditive.sub_comp]) ≫
        eqToHom (reducedSingularHomologyFunctor_zero_obj R X).symm := by
  exact (biprod.lift_fst _ _).trans (Category.comp_id _).symm

/-- The coefficient projection of the splitting is the augmentation. -/
@[reassoc (attr := simp)]
lemma singularHomology₀SplitIso_hom_snd {X : TopCat.{w}} (x : X) :
    (singularHomology₀SplitIso R x).hom ≫ biprod.snd = X.singularHomology₀ε R := by
  exact biprod.lift_snd _ _

/-- The reduced summand of the inverse splitting is the canonical reduced inclusion. -/
@[reassoc (attr := simp)]
lemma inl_singularHomology₀SplitIso_inv {X : TopCat.{w}} (x : X) :
    biprod.inl ≫ (singularHomology₀SplitIso R x).inv =
      (reducedSingularHomologyι R 0).app X := by
  exact biprod.inl_desc _ _

/-- The coefficient summand of the inverse splitting is the section at the chosen point. -/
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
