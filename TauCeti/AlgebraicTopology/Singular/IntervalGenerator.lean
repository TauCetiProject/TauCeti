/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.DiskSphere
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Class

/-!
# The generator of the relative homology of the interval modulo its endpoints

The identification `TauCeti.singularHomologyCubeBoundaryPairIso R 1 : H₁(I¹, ∂I¹; R) ≅ R` is
transported from the disk pair `(D¹, S⁰)`, whose generator is sent by the connecting morphism to
the standard generator `[-e₀] - [e₀]` of reduced `H₀(S⁰)`
(`TauCeti.reducedSingularHomologyTopCatSphereIso`).
This file computes the generator explicitly: it is the **negative** of the relative class of the
standard singular simplex `t ↦ t` of the interval, that is, the class of the simplex running from
`1` to `0` (`TauCeti.singularHomologyCubeBoundaryPairIso_one_inv`).

The sign is checked through the connecting morphism, which is injective because `I¹` is
contractible. Under the homeomorphism `TauCeti.diskHomeomorphCube 1`, the point `e₀` of `S⁰` goes
to `1` and `-e₀` to `0` (the radial rescaling onto the sup-norm ball keeps the sign of the
coordinate and the affine map `x ↦ (x + 1) / 2` follows), so the generator is sent to `[0] - [1]`.
The standard simplex is sent to `[1] - [0]` (`TauCeti.cubeRelClass_singularHomologyδ`).

## Main definitions and results

* `TauCeti.cubeSimplex`, `TauCeti.cubeRelClass`: the standard `1`-simplex of `I¹` and its class in
  `H₁(I¹, ∂I¹; R)`; `TauCeti.cubeRelClass_singularHomologyMap`: its image under a map of pairs.
* `TauCeti.reducedSingularHomologyTopCatSphereIso_zero_inv_ι`: the generator of reduced `H₀(S⁰)` is
  `[-e₀] - [e₀]` on `TopCat.sphere 0`.
* `TauCeti.eq_sphereMinus_or_eq_spherePlus`, `TauCeti.sphereMinus_ne_spherePlus`: `S⁰` consists
  of the two distinct points `-e₀` and `e₀`.
* `TauCeti.singularHomologyCubeBoundaryPairIso_one_inv`: the generator of `H₁(I¹, ∂I¹; R)` is
  `-cubeRelClass R`.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial unitInterval

universe w v u

namespace TauCeti

section Cube

/-- The point of the cube `I¹` with coordinate `t`. -/
def cubePoint (t : I) : (cubeBoundaryPair.{w} 1).fst := ULift.up fun _ ↦ t

@[simp]
lemma cubePoint_down (t : I) : (cubePoint.{w} t).down = fun _ ↦ t := by
  rw [cubePoint]

/-- An endpoint of the cube `I¹`, as a point of its boundary. -/
def cubeEnd (t : I) (ht : t = 0 ∨ t = 1) : (cubeBoundaryPair.{w} 1).snd :=
  ⟨cubePoint t, ⟨0, ht⟩⟩

/-- The standard singular `1`-simplex of the cube `I¹`, from `0` to `1`. -/
def cubeSimplex : (TopCat.toSSet.obj (cubeBoundaryPair.{w} 1).fst) _⦋1⦌ :=
  ((cubeBoundaryPair.{w} 1).fst.toSSetObjEquiv _).symm
    ⟨fun a ↦ cubePoint ⟨a.weights 1, a.weights_nonneg 1, a.weights_apply_le_one 1⟩,
      continuous_uliftUp.comp (continuous_pi fun _ ↦
        (Convexity.StdSimplex.continuous_weights_apply ℝ 1).subtype_mk _)⟩

/-- An endpoint of the cube `I¹`, as a singular `0`-simplex of its boundary. -/
def cubeEndVertex (t : I) (ht : t = 0 ∨ t = 1) :
    (TopCat.toSSet.obj (cubeBoundaryPair.{w} 1).snd) _⦋0⦌ :=
  TopCat.toSSetObj₀Equiv.symm (cubeEnd t ht)

/-- The standard simplex of `I¹` is the parametrization of the standard `1`-simplex by its last
weight. -/
lemma toSSetObjEquiv_cubeSimplex_apply (a : Convexity.StdSimplex ℝ (Fin 2)) :
    (cubeBoundaryPair.{w} 1).fst.toSSetObjEquiv _ cubeSimplex a =
      cubePoint (Convexity.StdSimplex.homeomorphI a) := by
  rw [cubeSimplex, Equiv.apply_symm_apply]
  exact congrArg cubePoint (Subtype.ext (Convexity.StdSimplex.homeomorphI_apply_coe a).symm)

lemma δ_one_cubeSimplex :
    (TopCat.toSSet.obj (cubeBoundaryPair.{w} 1).fst).δ 1 cubeSimplex =
      (TopCat.toSSet.map (cubeBoundaryPair.{w} 1).map).app _ (cubeEndVertex 0 (Or.inl rfl)) := by
  apply ((cubeBoundaryPair.{w} 1).fst.toSSetObjEquiv _).injective
  ext a : 1
  -- Both sides evaluate a singular simplex of the cube: the face of `cubeSimplex` is
  -- `cubePoint` of the last weight of the face inclusion, and the vertex is `cubePoint` of the
  -- endpoint, by `toSSetObjEquiv_δ_apply` and the definitions of `cubeSimplex`/`cubeEndVertex`.
  change cubePoint _ = cubePoint 0
  congr 1
  ext
  exact Finsupp.mapDomain_of_notMem_range _ _ (by
    simp only [Quiver.Hom.unop_op, Set.mem_range]
    decide)

lemma δ_zero_cubeSimplex :
    (TopCat.toSSet.obj (cubeBoundaryPair.{w} 1).fst).δ 0 cubeSimplex =
      (TopCat.toSSet.map (cubeBoundaryPair.{w} 1).map).app _ (cubeEndVertex 1 (Or.inr rfl)) := by
  apply ((cubeBoundaryPair.{w} 1).fst.toSSetObjEquiv _).injective
  ext a : 1
  -- Both sides evaluate a singular simplex of the cube: the face of `cubeSimplex` is
  -- `cubePoint` of the last weight of the face inclusion, and the vertex is `cubePoint` of the
  -- endpoint, by `toSSetObjEquiv_δ_apply` and the definitions of `cubeSimplex`/`cubeEndVertex`.
  change cubePoint _ = cubePoint 1
  congr 1
  ext
  -- The coordinate is the weight at `1 = (0 : Fin 2).succAbove 0` of the face inclusion.
  change (Convexity.StdSimplex.map (Fin.succAbove 0) a).weights ((0 : Fin 2).succAbove 0) = 1
  rw [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_apply_of_injective
    Fin.succAbove_right_injective]
  simp

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- The relative class in `H₁(I¹, ∂I¹; R)` of the standard singular `1`-simplex of the cube. -/
def cubeRelClass : R ⟶ (cubeBoundaryPair.{w} 1).singularHomology R 1 :=
  SSetPair.relClass₁ R (TopPair.toSSetPair.obj (cubeBoundaryPair.{w} 1)) cubeSimplex
    (cubeEndVertex 0 (Or.inl rfl)) (cubeEndVertex 1 (Or.inr rfl)) δ_one_cubeSimplex
    δ_zero_cubeSimplex

/-- The connecting morphism sends the relative class of the standard simplex of `I¹` to the
difference of the classes of its endpoints, `[1] - [0]`. -/
lemma cubeRelClass_singularHomologyδ :
    cubeRelClass R ≫ (cubeBoundaryPair.{w} 1).singularHomologyδ R 1 0 =
      singularHomology₀Section R (cubeEnd.{w} 1 (Or.inr rfl)) -
        singularHomology₀Section R (cubeEnd.{w} 0 (Or.inl rfl)) := by
  rw [cubeRelClass, singularHomology₀Section_def, singularHomology₀Section_def]
  exact SSetPair.relClass₁_homologyδ R _ _ _ _ _ _

/-- A map of pairs `f : (I¹, ∂I¹) ⟶ P` sends the relative class of the standard simplex of `I¹`
to the relative class of the image simplex. -/
lemma cubeRelClass_singularHomologyMap {P : TopPair.{w}} (f : cubeBoundaryPair.{w} 1 ⟶ P) :
    cubeRelClass R ≫ TopPair.singularHomologyMap f R 1 =
      SSetPair.relClass₁ R (TopPair.toSSetPair.obj P)
        ((TopPair.toSSetPair.map f).right.app _ cubeSimplex)
        ((TopPair.toSSetPair.map f).left.app _ (cubeEndVertex 0 (Or.inl rfl)))
        ((TopPair.toSSetPair.map f).left.app _ (cubeEndVertex 1 (Or.inr rfl)))
        (SSetPair.δ_map_eq _ _ 1 _ δ_one_cubeSimplex)
        (SSetPair.δ_map_eq _ _ 0 _ δ_zero_cubeSimplex) := by
  rw [cubeRelClass]
  exact SSetPair.relClass₁_homologyMap R _ _ _ _ _ _

end Cube

section Sphere

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- The standard orthonormal basis of `EuclideanSpace ℝ (ULift (Fin 1))`, which determines the
generator of reduced `H₀(S⁰)`. -/
abbrev sphereZeroBasis : OrthonormalBasis (Fin 1) ℝ (EuclideanSpace ℝ (ULift.{w} (Fin 1))) :=
  (EuclideanSpace.basisFun (ULift.{w} (Fin 1)) ℝ).reindex Equiv.ulift

/-- The point `e₀` of `TopCat.sphere 0`. -/
def spherePlus : TopCat.diskBoundary.{w} 1 :=
  (diskBoundaryHomeomorph 1).symm ⟨sphereZeroBasis 0, by simp⟩

/-- The point `-e₀` of `TopCat.sphere 0`. -/
def sphereMinus : TopCat.diskBoundary.{w} 1 :=
  (diskBoundaryHomeomorph 1).symm (-⟨sphereZeroBasis 0, by simp⟩)

/-- **The standard generator of reduced `H₀(S⁰)`** is the class `[-e₀] - [e₀]`. -/
lemma reducedSingularHomologyTopCatSphereIso_zero_inv_ι :
    (reducedSingularHomologyTopCatSphereIso R 0).inv ≫
        (reducedSingularHomologyι R 0).app (TopCat.sphere.{w} 0) =
      singularHomology₀Section R sphereMinus - singularHomology₀Section R spherePlus := by
  have hid : TopCat.ofHom (diskBoundaryHomeomorph.{w} 1).toHomotopyEquiv.toFun ≫
      TopCat.ofHom (diskBoundaryHomeomorph.{w} 1).toHomotopyEquiv.invFun = 𝟙 _ := by
    ext x
    exact (diskBoundaryHomeomorph 1).symm_apply_apply x
  have hinv : (reducedSingularHomologyTopCatSphereIso R 0).inv =
      (reducedSingularHomologySphereIso R sphereZeroBasis).inv ≫
        (reducedSingularHomologyFunctor R 0).map
          (TopCat.ofHom (diskBoundaryHomeomorph.{w} 1).toHomotopyEquiv.invFun) := by
    apply Iso.inv_ext
    rw [reducedSingularHomologyTopCatSphereIso_hom]
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc _ _)).trans
      ((Functor.map_comp _ _ _).symm.trans
        ((congrArg _ hid).trans (CategoryTheory.Functor.map_id _ _))))
  have key : (reducedSingularHomologySphereIso R sphereZeroBasis).inv ≫
      (reducedSingularHomologyFunctor R 0).map
        (TopCat.ofHom (diskBoundaryHomeomorph.{w} 1).toHomotopyEquiv.invFun) ≫
      (reducedSingularHomologyι R 0).app (TopCat.of (TopCat.diskBoundary.{w} 1)) =
        singularHomology₀Section R sphereMinus - singularHomology₀Section R spherePlus := by
    rw [(reducedSingularHomologyι R 0).naturality, ← Category.assoc,
      reducedSingularHomologySphereIso_inv_ι, Preadditive.sub_comp,
      singularHomology₀Section_naturality, singularHomology₀Section_naturality]
    rfl
  rw [hinv]
  exact (Category.assoc _ _ _).trans key

lemma spherePlus_coord :
    (((TopCat.diskBoundaryInclusion.{w} 1 spherePlus) :
      ULift.{w} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
        EuclideanSpace ℝ (Fin 1)) 0 = 1 := by
  -- `spherePlus`/`sphereMinus` are defined through `(diskBoundaryHomeomorph 1).symm`, and the
  -- inclusion of the boundary sphere into the disk keeps the underlying vector.
  change ((((diskBoundaryHomeomorph 1).symm _ : TopCat.diskBoundary.{w} 1) :
    ULift.{w} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
      EuclideanSpace ℝ (Fin 1)) 0 = 1
  rw [diskBoundaryHomeomorph_symm_apply_down_apply]
  simp

lemma sphereMinus_coord :
    (((TopCat.diskBoundaryInclusion.{w} 1 sphereMinus) :
      ULift.{w} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
        EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
  -- `spherePlus`/`sphereMinus` are defined through `(diskBoundaryHomeomorph 1).symm`, and the
  -- inclusion of the boundary sphere into the disk keeps the underlying vector.
  change ((((diskBoundaryHomeomorph 1).symm _ : TopCat.diskBoundary.{w} 1) :
    ULift.{w} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
      EuclideanSpace ℝ (Fin 1)) 0 = -1
  rw [diskBoundaryHomeomorph_symm_apply_down_apply]
  simp

/-- **`S⁰` consists of the two points `-e₀` and `e₀`.** -/
lemma eq_sphereMinus_or_eq_spherePlus (p : TopCat.diskBoundary.{w} 1) :
    p = sphereMinus ∨ p = spherePlus := by
  have hnorm : ‖((p : ULift.{w} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
      EuclideanSpace ℝ (Fin 1))‖ = 1 := by
    simp
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs,
    Real.sqrt_sq_eq_abs, abs_eq zero_le_one] at hnorm
  rcases hnorm with h | h
  · exact Or.inr (diskBoundary_one_ext (h.trans spherePlus_coord.{w}.symm))
  · exact Or.inl (diskBoundary_one_ext (h.trans sphereMinus_coord.{w}.symm))

/-- The two points `-e₀` and `e₀` of `S⁰` are distinct. -/
lemma sphereMinus_ne_spherePlus : (sphereMinus : TopCat.diskBoundary.{w} 1) ≠ spherePlus := by
  intro h
  have h' := sphereMinus_coord.{w}
  rw [h, spherePlus_coord] at h'
  norm_num at h'

lemma diskBoundaryPairToCube_snd_spherePlus :
    TopPair.Hom.snd (diskBoundaryPairToCube.{w} 1) spherePlus = cubeEnd 1 (Or.inr rfl) := by
  refine Subtype.ext (ULift.ext
    ((diskBoundaryPairToCube_snd_apply_down (n := 1) spherePlus).trans ?_))
  rw [diskHomeomorphCube_one_of_pos _ ⟨_, rfl⟩ (by rw [spherePlus_coord]; norm_num)]
  rfl

lemma diskBoundaryPairToCube_snd_sphereMinus :
    TopPair.Hom.snd (diskBoundaryPairToCube.{w} 1) sphereMinus = cubeEnd 0 (Or.inl rfl) := by
  refine Subtype.ext (ULift.ext
    ((diskBoundaryPairToCube_snd_apply_down (n := 1) sphereMinus).trans ?_))
  rw [diskHomeomorphCube_one_of_neg _ ⟨_, rfl⟩ (by rw [sphereMinus_coord]; norm_num)]
  rfl

end Sphere

section Generator

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- The connecting morphism of the cube pair `(I¹, ∂I¹)` is a monomorphism, since `I¹` is
contractible. -/
instance mono_cubeBoundaryPair_singularHomologyδ :
    Mono ((cubeBoundaryPair.{w} 1).singularHomologyδ R 1 0) :=
  ((cubeBoundaryPair.{w} 1).singularHomology_exact_relative R 1 0).mono_g
    ((isZero_singularHomologyFunctor_of_contractibleSpace R (cubeBoundaryPair.{w} 1).fst
      one_ne_zero).eq_of_src _ _)

/-- The connecting morphism sends the generator of `H₁(I¹, ∂I¹; R)` to `[0] - [1]`. -/
lemma singularHomologyCubeBoundaryPairIso_one_inv_singularHomologyδ :
    (singularHomologyCubeBoundaryPairIso R 1).inv ≫
        (cubeBoundaryPair.{w} 1).singularHomologyδ R 1 0 =
      singularHomology₀Section R (cubeEnd.{w} 0 (Or.inl rfl)) -
        singularHomology₀Section R (cubeEnd.{w} 1 (Or.inr rfl)) := by
  have hm : singularHomology₀Section R sphereMinus ≫
      ((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map
        (TopPair.Hom.snd (diskBoundaryPairToCube.{w} 1)) =
      singularHomology₀Section R (cubeEnd.{w} 0 (Or.inl rfl)) :=
    (singularHomology₀Section_naturality R (TopPair.Hom.snd (diskBoundaryPairToCube.{w} 1))
      sphereMinus).trans (congrArg _ diskBoundaryPairToCube_snd_sphereMinus)
  have hp : singularHomology₀Section R spherePlus ≫
      ((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map
        (TopPair.Hom.snd (diskBoundaryPairToCube.{w} 1)) =
      singularHomology₀Section R (cubeEnd.{w} 1 (Or.inr rfl)) :=
    (singularHomology₀Section_naturality R (TopPair.Hom.snd (diskBoundaryPairToCube.{w} 1))
      spherePlus).trans (congrArg _ diskBoundaryPairToCube_snd_spherePlus)
  have hδ := (singularHomologyDiskBoundaryPairIso_inv_comp_singularHomologyδ.{w} R 0).trans
    (reducedSingularHomologyTopCatSphereIso_zero_inv_ι R)
  have hn := TopPair.singularHomologyδ_naturality R (diskBoundaryPairToCube.{w} 1) 1 0
  rw [singularHomologyCubeBoundaryPairIso_inv, Category.assoc]
  refine (congrArg (_ ≫ ·) hn.symm).trans ((Category.assoc _ _ _).symm.trans ?_)
  refine (congrArg (· ≫ _) hδ).trans ?_
  exact (Preadditive.sub_comp _ _ _).trans (congrArg₂ (· - ·) hm hp)

/-- **The generator of `H₁(I¹, ∂I¹; R)`** is the negative of the relative class of the standard
singular simplex `t ↦ t` of the interval: it is the class of the simplex running from `1` to `0`.
Indeed the connecting morphism sends the generator to `[0] - [1]`, the transport of the standard
generator `[-e₀] - [e₀]` of reduced `H₀(S⁰)`, and the standard simplex to `[1] - [0]`. -/
theorem singularHomologyCubeBoundaryPairIso_one_inv :
    (singularHomologyCubeBoundaryPairIso R 1).inv = -cubeRelClass.{w} R := by
  rw [← cancel_mono ((cubeBoundaryPair.{w} 1).singularHomologyδ R 1 0 rfl)]
  exact (singularHomologyCubeBoundaryPairIso_one_inv_singularHomologyδ R).trans
    ((neg_sub _ _).symm.trans ((congrArg Neg.neg (cubeRelClass_singularHomologyδ R)).symm.trans
      (Preadditive.neg_comp _ _).symm))

end Generator

end TauCeti
