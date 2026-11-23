/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Triangulation.Geometry
public import TauCeti.AlgebraicTopology.Singular.Cubical.ChainComplex
public import TauCeti.AlgebraicTopology.Singular.Cubical.Augment
public import Mathlib.Algebra.BigOperators.Fin
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Chains
public import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Tactic

/-!
# Literal triangulation on native singular chains

The positive staircase sum reverses the native cubical boundary sign. Multiplication by
`(-1)^n` in degree `n` gives a chain map on the original raw cubical chains. Coefficient
naturality uses the native coproduct inclusions and applies to arbitrary modules over a ring.
The ring universe is independent of the space and coefficient-module universe.

## Main definitions and results

* `TauCeti.SingularCube.orderedChain`: the signed permutation sum with arbitrary categorical
  coefficients; it has the positive interval orientation `[1] - [0]`.
* `TauCeti.SingularCube.orderedChain_boundary`: the all-degree face-cancellation identity.
* `TauCeti.CubicalChain.orderedTriangulation`: the R-linear map on the original raw cubes.
* `TauCeti.CubicalChain.nativeOrderedTriangulation`: the correction by `(-1)^n` for the
  native cubical convention `[0] - [1]`.
* `TauCeti.CubicalChain.orderedTriangulationChainMap`: the actual bundled native chain map.
* `TauCeti.singularAugment_orderedTriangulation`: the native augmentation square.

These maps are raw, absolute chain constructions. No normalized descent or relative homology
comparison is asserted.
-/

public section
noncomputable section
open CategoryTheory Limits Simplicial Convexity Equiv Equiv.Perm Finsupp
universe r w v u
namespace TauCeti


/-- Adjacent orderings have the identical internal simplex face. -/
private lemma simplexFace_mul_swap {n : ℕ} (π : Perm (Fin (n + 1))) (k : Fin n) :
    ContinuousMap.simplexFace (staircaseSimplex (π * swap k.castSucc k.succ)) k.succ.castSucc =
      ContinuousMap.simplexFace (staircaseSimplex π) k.succ.castSucc := by
  apply ContinuousMap.ext
  intro w
  simpa only [ContinuousMap.simplexFace_apply] using staircaseSimplex_mul_swap_face π k w

/-- The first simplex face is the ordered simplex in the upper cubical face. -/
private lemma simplexFace_decompose_upper {n : ℕ} (j : Fin (n + 1)) (π : Perm (Fin n)) :
    ContinuousMap.simplexFace (staircaseSimplex (consFin j π)) 0 =
      ((SingularCube.face j 1 (ContinuousMap.id _))).comp (staircaseSimplex π) := by
  apply ContinuousMap.ext
  intro w
  simpa only [ContinuousMap.simplexFace_apply, SingularCube.face_apply, ContinuousMap.comp_apply,
    ContinuousMap.id_apply, ContinuousMap.coe_mk, Fin.succAbove_zero] using
    staircaseSimplex_decompose_upper j π w

/-- The last simplex face is the ordered simplex in the lower cubical face. -/
private lemma simplexFace_snocFin_lower {n : ℕ} (j : Fin (n + 1))
    (π : Perm (Fin n)) :
    ContinuousMap.simplexFace (staircaseSimplex (snocFin j π)) (Fin.last (n + 1)) =
      ((SingularCube.face j 0 (ContinuousMap.id _))).comp (staircaseSimplex π) := by
  apply ContinuousMap.ext
  intro w
  simpa only [ContinuousMap.simplexFace_apply, SingularCube.face_apply, ContinuousMap.comp_apply,
    ContinuousMap.id_apply, ContinuousMap.coe_mk, Fin.succAbove_last] using
    staircaseSimplex_snocFin_lower j π w

variable {A : Type*} [AddCommGroup A]

/-- The internal faces cancel in the sum over all coordinate orderings. -/
private lemma sum_sign_internal_face {n : ℕ}
    (F : C(StdSimplex ℝ (Fin (n + 1)), Fin (n + 1) → unitInterval) → A)
    (k : Fin n) :
    ∑ π : Perm (Fin (n + 1)), π.sign •
      F (ContinuousMap.simplexFace (staircaseSimplex π) k.succ.castSucc) = 0 := by
  exact TauCeti.sum_sign_smul_eq_zero_of_mul_swap _ k.castSucc k.succ
    k.castSucc_lt_succ.ne (fun π ↦ congrArg F (simplexFace_mul_swap π k))

/-- The upper exterior faces have the alternating cubical upper-face signs. -/
private lemma sum_sign_upper_face {n : ℕ}
    (F : C(StdSimplex ℝ (Fin (n + 1)), Fin (n + 1) → unitInterval) → A) :
    ∑ π : Perm (Fin (n + 1)), π.sign • F (ContinuousMap.simplexFace (staircaseSimplex π) 0) =
      ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j : ℕ)) •
        ∑ π : Perm (Fin n), π.sign • F (((SingularCube.face j 1 (ContinuousMap.id _))).comp
          (staircaseSimplex π)) := by
  rw [TauCeti.sum_sign_smul_eq_sum_consFin n]
  simp only [simplexFace_decompose_upper]

/-- The sign on a last simplex face becomes the negative lower cubical face sign. -/
private lemma last_face_sign {n : ℕ} (j : Fin (n + 1)) (π : Perm (Fin n)) (a : A) :
    ((-1 : ℤ) ^ (n + 1)) • ((snocFin j π).sign • a) =
      -(((-1 : ℤ) ^ (j : ℕ)) • (π.sign • a)) := by
  have h : (-1 : ℤ) ^ (n + 1) * (-1) ^ ((j : ℕ) + n) = -((-1) ^ (j : ℕ)) := by
    rw [← pow_add]
    have he : n + 1 + ((j : ℕ) + n) = (j : ℕ) + 2 * (n) + 1 := by omega
    rw [he]
    simp [pow_add, pow_mul]
  rw [sign_snocFin]
  simp only [Units.smul_def, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one, smul_smul]
  rw [← mul_assoc, h]
  simp

/-- The lower exterior faces have the negative alternating cubical lower-face signs. -/
private lemma sum_sign_lower_face {n : ℕ}
    (F : C(StdSimplex ℝ (Fin (n + 1)), Fin (n + 1) → unitInterval) → A) :
    ((-1 : ℤ) ^ (n + 1)) •
        ∑ π : Perm (Fin (n + 1)), π.sign •
          F (ContinuousMap.simplexFace (staircaseSimplex π) (Fin.last (n + 1))) =
      -(∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j : ℕ)) •
        ∑ π : Perm (Fin n), π.sign • F (((SingularCube.face j 0 (ContinuousMap.id _))).comp
          (staircaseSimplex π))) := by
  calc
    _ = ∑ j : Fin (n + 1), ∑ π : Perm (Fin n),
        ((-1 : ℤ) ^ (n + 1)) • ((snocFin j π).sign •
          F (ContinuousMap.simplexFace (staircaseSimplex (snocFin j π)) (Fin.last (n + 1)))) := by
      rw [← (snocFinEquiv n).sum_comp, Fintype.sum_prod_type]
      simp only [Finset.smul_sum, snocFinEquiv_apply]
    _ = _ := by
      simp_rw [simplexFace_snocFin_lower, last_face_sign]
      simp only [Finset.smul_sum, Finset.sum_neg_distrib]

/-- The signed boundary of the literal ordered triangulation, in every positive dimension. -/
private lemma sum_sign_boundary {n : ℕ}
    (F : C(StdSimplex ℝ (Fin (n + 1)), Fin (n + 1) → unitInterval) → A) :
    ∑ π : Perm (Fin (n + 1)), π.sign •
        ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
          F (ContinuousMap.simplexFace (staircaseSimplex π) k) =
      ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j : ℕ)) •
        (∑ π : Perm (Fin n), π.sign • F (((SingularCube.face j 1 (ContinuousMap.id _))).comp
          (staircaseSimplex π)) -
         ∑ π : Perm (Fin n), π.sign • F (((SingularCube.face j 0 (ContinuousMap.id _))).comp
           (staircaseSimplex π))) := by
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hi (k : Fin n) :
      ∑ π : Perm (Fin (n + 1)), π.sign •
        ((-1 : ℤ) ^ (k.castSucc.succ : ℕ)) •
          F (ContinuousMap.simplexFace (staircaseSimplex π) k.castSucc.succ) = 0 := by
    simp_rw [smul_comm (Perm.sign _)]
    rw [← Finset.smul_sum]
    have h := sum_sign_internal_face F k
    simp only [Fin.succ_castSucc, h, smul_zero]
  simp only [hi, Finset.sum_const_zero, zero_add, Fin.val_zero, pow_zero, one_smul]
  simp_rw [smul_comm (Perm.sign _) ((-1 : ℤ) ^ (Fin.last (n)).succ.val)]
  simp only [Fin.succ_last, Fin.val_last]
  rw [← Finset.smul_sum, sum_sign_upper_face, sum_sign_lower_face]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib]
  rw [sub_eq_add_neg]


namespace SingularCube

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : TopCat.{w}}

/-- The literal positive permutation sum, as a morphism out of the original coefficient object. -/
def orderedChain {n : ℕ} (c : SingularCube X n) (M : C) :
    M ⟶ ((TopCat.toSSet.obj X).chainComplex M).X n :=
  ∑ π : Perm (Fin n), π.sign • (TopCat.toSSet.obj X).ιChainComplex
    ((X.toSSetObjEquiv _).symm (c.comp (staircaseSimplex π)))

/-- The actual permutation sum defining the cube morphism. -/
lemma orderedChain_eq_sum {n : ℕ} (c : SingularCube X n) (M : C) :
    orderedChain c M = ∑ π : Perm (Fin n), π.sign • (TopCat.toSSet.obj X).ιChainComplex
      ((X.toSSetObjEquiv _).symm (c.comp (staircaseSimplex π))) := by
  unfold orderedChain
  rfl

/-- The literal positive sum has the positive cubical boundary, opposite to the native one. -/
lemma orderedChain_boundary {n : ℕ} (c : SingularCube X (n + 1)) (M : C) :
    orderedChain c M ≫ ((TopCat.toSSet.obj X).chainComplex M).d (n + 1) n =
      ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j : ℕ)) •
        (orderedChain (SingularCube.face j 1 c) M - orderedChain (SingularCube.face j 0 c) M) := by
  simp only [orderedChain, Preadditive.sum_comp, Units.smul_def, Preadditive.zsmul_comp,
    SSet.ιChainComplex_d, TopCat.toSSetObjEquiv_symm_δ, ContinuousMap.simplexFace_comp]
  simp only [← Units.smul_def]
  have h := sum_sign_boundary (fun s ↦ (TopCat.toSSet.obj X).ιChainComplex
    (R := M) ((X.toSSetObjEquiv _).symm (c.comp s)))
  simpa only [← ContinuousMap.comp_assoc, SingularCube.comp_face_id,
    Finset.sum_sub_distrib] using h

/-- Triangulation commutes with an actual continuous map of spaces. -/
lemma orderedChain_naturality {n : ℕ} (c : SingularCube X n) (M : C) (f : X ⟶ Y) :
    orderedChain c M ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) M).f n =
      orderedChain (f.hom.comp c) M := by
  simp only [orderedChain, Preadditive.sum_comp, Units.smul_def, Preadditive.zsmul_comp,
    SSet.ι_chainComplexMap_f, TopCat.toSSet_map_app_toSSetObjEquiv_symm,
    ContinuousMap.comp_assoc]

/-- Triangulation commutes with arbitrary morphisms of coefficient objects. -/
lemma orderedChain_coefficient_naturality {M N : C} {n : ℕ}
    (c : SingularCube X n) (f : M ⟶ N) :
    orderedChain c M ≫ (((SSet.chainComplexFunctor C).map f).app (TopCat.toSSet.obj X)).f n =
      f ≫ orderedChain c N := by
  simp only [orderedChain, Preadditive.sum_comp, Units.smul_def, Preadditive.zsmul_comp,
    SSet.ιChainComplex_chainComplexFunctor_map_app_f, Preadditive.comp_sum,
    Preadditive.comp_zsmul]

/-- The literal triangulation has the raw coordinate-permutation sign in every degree. -/
lemma orderedChain_coordinatePermutation {n : ℕ}
    (c : SingularCube X n) (M : C) (τ : Perm (Fin n)) :
    orderedChain (c.comp ((ContinuousMap.precomp (X := fun _ ↦ unitInterval) ⇑τ))) M = τ.sign •
      orderedChain c M := by
  have hτ : τ.symm * τ = 1 := by
    apply Equiv.ext
    intro i
    simp [Perm.mul_apply]
  simp only [orderedChain, ContinuousMap.comp_assoc, precomp_comp_staircaseSimplex]
  rw [← Equiv.sum_comp (Equiv.mulLeft τ)]
  simp only [Equiv.coe_mulLeft, ← mul_assoc, hτ, one_mul,
    Perm.sign_mul, mul_smul, Finset.smul_sum]

/-- In degree zero the literal sum is the original point simplex. -/
lemma orderedChain_zero (c : SingularCube X 0) (M : C) :
    orderedChain c M = (TopCat.toSSet.obj X).ιChainComplex
      (TopCat.toSSetObj₀Equiv.symm (c (fun i ↦ i.elim0))) := by
  rw [orderedChain_eq_sum, Fintype.sum_subsingleton _ 1, Perm.sign_one, one_smul]
  congr 1
  apply TopCat.toSSetObj₀Equiv.injective
  simp only [TopCat.toSSetObj₀Equiv_apply, Equiv.apply_symm_apply, ContinuousMap.comp_apply]
  congr 1
  funext i
  exact i.elim0

/-- The degree-one positive sum is the actual positive native interval simplex. -/
lemma orderedChain_one (c : SingularCube X 1) (M : C) :
    orderedChain c M = (TopCat.toSSet.obj X).ιChainComplex
      (TauCeti.TopCat.simplex₁ ⟨fun t ↦ c (fun _ ↦ t), by fun_prop⟩) := by
  rw [orderedChain_eq_sum, Fintype.sum_subsingleton _ 1, Perm.sign_one, one_smul]
  congr 1
  apply (X.toSSetObjEquiv _).injective
  rw [Equiv.apply_symm_apply, TauCeti.TopCat.toSSetObjEquiv_simplex₁]
  apply ContinuousMap.ext
  intro w
  simp only [ContinuousMap.comp_apply, staircaseSimplex_one]
  rfl


end SingularCube

open SingularCube
namespace CubicalChain
variable {R : Type r} [Ring R] {X Y : TopCat.{w}}

/-- The positive ordered triangulation on finitely supported cubes with module
  coefficients. -/
def orderedTriangulation (X : TopCat.{w}) (M : ModuleCat.{max u w} R) (n : ℕ) :
    (SingularCube X n →₀ M) →ₗ[R] ((TopCat.toSSet.obj X).chainComplex M).X n :=
  Finsupp.lsum ℕ fun c ↦ (orderedChain (X := X) c M).hom

/-- Evaluation on a cube with its original module coefficient. -/
@[simp]
lemma orderedTriangulation_single (M : ModuleCat.{max u w} R) {n : ℕ} (c : SingularCube X n) (a :
  M) :
    orderedTriangulation X M n (Finsupp.single c a) = (orderedChain (X := X) c M).hom a := by
  simp [orderedTriangulation]

/-- Coefficient naturality on the actual raw cubical modules. -/
lemma orderedTriangulation_coefficient_naturality {M N : ModuleCat.{max u w} R} (f : M ⟶ N) (n :
  ℕ) :
    ((((SSet.chainComplexFunctor.{w} (ModuleCat.{max u w} R)).map f).app
        (TopCat.toSSet.obj X)).f n).hom ∘ₗ orderedTriangulation X M n =
      orderedTriangulation X N n ∘ₗ Finsupp.mapRange.linearMap f.hom := by
  apply Finsupp.lhom_ext
  intro c a
  have h := congrArg (fun g ↦ g.hom a) (orderedChain_coefficient_naturality c f)
  simpa using h

/-- Space naturality on the actual raw cubical modules. -/
lemma orderedTriangulation_naturality (M : ModuleCat.{max u w} R) (f : X ⟶ Y) (n : ℕ) :
    ((SSet.chainComplexMap (TopCat.toSSet.map f) M).f n).hom ∘ₗ orderedTriangulation X M n =
      orderedTriangulation Y M n ∘ₗ Finsupp.lmapDomain M R f.hom.comp := by
  apply Finsupp.lhom_ext
  intro c a
  have h := congrArg (fun g ↦ g.hom a) (orderedChain_naturality c M f)
  simpa using h

/-- The positive boundary formula with arbitrary native module coefficients. -/
lemma orderedTriangulation_boundary_single (M : ModuleCat.{max u w} R) {n : ℕ}
    (c : SingularCube X (n + 1)) (a : M) :
    (((TopCat.toSSet.obj X).chainComplex M).d (n + 1) n).hom
        (orderedTriangulation X M (n + 1) (Finsupp.single c a)) =
      ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j : ℕ)) •
        (orderedTriangulation X M n (Finsupp.single (SingularCube.face j 1 c) a) -
         orderedTriangulation X M n (Finsupp.single (SingularCube.face j 0 c) a)) := by
  simp only [orderedTriangulation_single]
  have h := congrArg (fun g ↦ g.hom a) (orderedChain_boundary (X := X) c M)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum,
    LinearMap.sum_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_sub,
    LinearMap.sub_apply] using h

/-- The degree-corrected map on the original raw cubes with arbitrary module coefficients. -/
def nativeOrderedTriangulation (X : TopCat.{w}) (M : ModuleCat.{max u w} R) (n : ℕ) :
    (SingularCube X n →₀ M) →ₗ[R] ((TopCat.toSSet.obj X).chainComplex M).X n :=
  ((-1 : ℤ) ^ n) • orderedTriangulation X M n

/-- Evaluation of the native sign correction. -/
@[simp]
lemma nativeOrderedTriangulation_apply (M : ModuleCat.{max u w} R) (n : ℕ) (c : SingularCube X n
  →₀ M) :
    nativeOrderedTriangulation X M n c = ((-1 : ℤ) ^ n) • orderedTriangulation X M n c := by
  unfold nativeOrderedTriangulation
  rfl

/-- The sign-corrected maps retain coefficient naturality over arbitrary rings. -/
lemma nativeOrderedTriangulation_coefficient_naturality {M N : ModuleCat.{max u w} R}
    (f : M ⟶ N) (n : ℕ) :
    ((((SSet.chainComplexFunctor.{w} (ModuleCat.{max u w} R)).map f).app
        (TopCat.toSSet.obj X)).f n).hom ∘ₗ nativeOrderedTriangulation X M n =
      nativeOrderedTriangulation X N n ∘ₗ Finsupp.mapRange.linearMap f.hom := by
  simp only [nativeOrderedTriangulation, LinearMap.comp_smul, LinearMap.smul_comp,
    orderedTriangulation_coefficient_naturality]

/-- The sign-corrected maps retain naturality in spaces. -/
lemma nativeOrderedTriangulation_naturality (M : ModuleCat.{max u w} R) (f : X ⟶ Y) (n : ℕ) :
    ((SSet.chainComplexMap (TopCat.toSSet.map f) M).f n).hom ∘ₗ nativeOrderedTriangulation X M n =
      nativeOrderedTriangulation Y M n ∘ₗ Finsupp.lmapDomain M R f.hom.comp := by
  simp only [nativeOrderedTriangulation, LinearMap.comp_smul, LinearMap.smul_comp,
    orderedTriangulation_naturality]

/-- The positive degree-zero map sends each raw point coefficient to that same singular point. -/
lemma orderedTriangulation_single_zero (M : ModuleCat.{max u w} R) (c : SingularCube X 0) (a : M) :
    orderedTriangulation X M 0 (Finsupp.single c a) =
      ((TopCat.toSSet.obj X).ιChainComplex (R := M)
        (TopCat.toSSetObj₀Equiv.symm (c (fun i ↦ i.elim0)))).hom a := by
  rw [orderedTriangulation_single, orderedChain_zero]

/-- The native degree-zero sign is one, so the original point coefficient is preserved. -/
lemma nativeOrderedTriangulation_single_zero (M : ModuleCat.{max u w} R) (c : SingularCube X 0) (a
  : M) :
    nativeOrderedTriangulation X M 0 (Finsupp.single c a) =
      ((TopCat.toSSet.obj X).ιChainComplex (R := M)
        (TopCat.toSSetObj₀Equiv.symm (c (fun i ↦ i.elim0)))).hom a := by
  simp only [nativeOrderedTriangulation_apply, pow_zero, one_smul, orderedTriangulation_single_zero]

/-- The positive permutation sum reverses the raw module boundary. -/
lemma orderedTriangulation_boundary (M : ModuleCat.{max u w} R) (n : ℕ) :
    (((TopCat.toSSet.obj X).chainComplex M).d (n + 1) n).hom ∘ₗ orderedTriangulation X M (n + 1) =
      -(orderedTriangulation X M n ∘ₗ CubicalChain.boundary X R M n) := by
  apply Finsupp.lhom_ext
  intro c a
  simp only [LinearMap.comp_apply, LinearMap.neg_apply]
  rw [orderedTriangulation_boundary_single, CubicalChain.boundary_single]
  simp only [map_sum, map_zsmul, map_sub]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← smul_neg, neg_sub]

/-- The degree sign gives the native chain-map law for arbitrary module coefficients. -/
lemma nativeOrderedTriangulation_boundary (M : ModuleCat.{max u w} R) (n : ℕ) :
    (((TopCat.toSSet.obj X).chainComplex M).d (n + 1) n).hom ∘ₗ
        nativeOrderedTriangulation X M (n + 1) = nativeOrderedTriangulation X M n ∘ₗ
          CubicalChain.boundary X R M n := by
  apply LinearMap.ext
  intro c
  have h := LinearMap.congr_fun (orderedTriangulation_boundary (X := X) M n) c
  simp only [LinearMap.comp_apply, LinearMap.neg_apply] at h
  simp only [LinearMap.comp_apply]
  rw [nativeOrderedTriangulation_apply, map_zsmul, h, nativeOrderedTriangulation_apply]
  simp [pow_succ]

/-- The actual bundled all-degree chain map from raw cubes to native simplicial singular chains. -/
def orderedTriangulationChainMap (X : TopCat.{w}) (M : ModuleCat.{max u w} R) :
    rawCubicalChainComplexObj X M ⟶ (TopCat.toSSet.obj X).chainComplex M where
  f n := ModuleCat.ofHom (nativeOrderedTriangulation X M n)
  comm' := by
    rintro _ n rfl
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    -- The raw term is definitionally the original Finsupp module; naming that carrier
    -- keeps ModuleCat composition rewrites from selecting an opaque source object.
    change SingularCube X (n + 1) →₀ M at c
    change ((TopCat.toSSet.obj X).chainComplex M).d (n + 1) n
      (nativeOrderedTriangulation X M (n + 1) c) =
      nativeOrderedTriangulation X M n (((rawCubicalChainComplexObj X M).d (n + 1) n).hom c)
    rw [rawCubicalChainComplexObj_d_apply]
    exact LinearMap.congr_fun (nativeOrderedTriangulation_boundary (X := X) M n) c


/-- The component of the native chain map is the literal degree-corrected permutation sum. -/
@[simp]
lemma orderedTriangulationChainMap_f (X : TopCat.{w}) (M : ModuleCat.{max u w} R) (n : ℕ) :
    (orderedTriangulationChainMap X M).f n =
      ModuleCat.ofHom (nativeOrderedTriangulation X M n) := by
  rfl


end CubicalChain

section ScalarAugmentation
variable {R : Type u} [Ring R] {X : TopCat.{u}}
open CubicalChain
/-- The degree-zero positive cube map preserves the native singular augmentation. -/
lemma singularAugment_orderedTriangulation_single (c : SingularCube X 0) (a : R) :
    TauCeti.singularAugment R X
      (orderedTriangulation X (ModuleCat.of R R) 0 (Finsupp.single c a)) = a := by
  rw [orderedTriangulation_single, orderedChain_zero]
  exact TauCeti.singularAugment_simplexChain X _ a

/-- The whole native augmentation square is coefficient summation on the original raw cubes. -/
lemma singularAugment_orderedTriangulation :
    TauCeti.singularAugment R X ∘ₗ orderedTriangulation X (ModuleCat.of R R) 0 =
      CubicalChain.augment X R := by
  apply Finsupp.lhom_ext
  intro c a
  rw [CubicalChain.augment_single]
  exact singularAugment_orderedTriangulation_single c a

/-- The native sign-corrected chain map also preserves the original augmentation. -/
lemma singularAugment_nativeOrderedTriangulation :
    TauCeti.singularAugment R X ∘ₗ nativeOrderedTriangulation X (ModuleCat.of R R) 0 =
      CubicalChain.augment X R := by
  simpa only [nativeOrderedTriangulation, pow_zero, one_smul] using
    (singularAugment_orderedTriangulation (R := R) (X := X))

end ScalarAugmentation

end TauCeti
