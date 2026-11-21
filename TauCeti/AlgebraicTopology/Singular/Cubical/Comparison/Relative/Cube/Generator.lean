/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Cube.Pair
public import TauCeti.AlgebraicTopology.Disk.CubeBoundary
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.MayerVietoris
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Calibrating the identity cube against the selected relative generator

The normalized cubical identity class of the `(n + 1)`-cube, read in singular homology,
has coordinate `(-1)^(n(n+1)/2)` under `singularHomologyCubeBoundaryPairIso`. This determines
the sign left undetermined by the integral unit-generator theorem. Coefficients may be any
ring, including a noncommutative or trivial ring, and the cube and coefficients lie in any
common universe.

The boundary is split into faces in the ordered antipodal cover. The native Mayer–Vietoris
map takes its class to `(-1)^(n+1)` times the lower cube boundary class, transported by the
positive equator comparison. Naturality for the ordered coordinate bases gives the same
scalar recurrence. The native dimension-one result supplies the initial value.

## Main declarations

* `TauCeti.singularHomologyCubeBoundaryPairIso_hom_cubeBoundaryPairCycle`: the literal coefficient.
* `TauCeti.singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle`: the equivalent class
  formula, with the native selected generator.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Mayer–Vietoris and sphere generators.
-/

public section

noncomputable section
open CategoryTheory Limits HomologicalComplex Metric Set
universe u
namespace TauCeti
namespace CubeBoundary

private abbrev E (n : ℕ) := EuclideanSpace ℝ (ULift.{u} (Fin n))
private abbrev S (n : ℕ) := sphere (0 : E.{u} n) 1
private abbrev B (n : ℕ) := (cubeBoundaryPair.{u} n).snd
private abbrev stdBasis (n : ℕ) :=
  (EuclideanSpace.basisFun (ULift.{u} (Fin n)) ℝ).reindex Equiv.ulift
private abbrev pole (n : ℕ) := lastPole.{u} n
private abbrev PE (n : ℕ) := (ℝ ∙ (pole.{u} n : E.{u} (n + 1)))ᗮ
private abbrev Coeff (k : Type u) [Ring k] : ModuleCat.{u} k := ModuleCat.of k k
-- The same derived divisibility instance is used by the native sphere suspension module.
private instance instHasUniqueDiv (m : ℕ) : HasUniqueDiv (E.{u} m) :=
  .of_isTorsionFree ℝ (E m)

private theorem upperFace_coefficient (k : Type*) [Ring k] (n : ℕ) :
    (-1 : k) ^ (n + 2) = -((-1 : k) ^ (n + 1)) := by
  simpa only [mul_neg, mul_one] using pow_succ (-1 : k) (n + 1)

section CoordinateValue

private def cubeCoordinateValue (k : Type u) [Ring k] (n : ℕ) : k :=
  (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (n + 1)).hom
    ((TopPair.singularCubicalHomologyIso k (cubeBoundaryPair.{u} (n + 1)) (n + 1)).inv
      (((cubeBoundaryPair.{u} (n + 1)).cubicalChainComplex k).homologyπ (n + 1)
        (cubeBoundaryPairCycle k n)))

private theorem cubeCoordinateValue_zero (k : Type u) [Ring k] : cubeCoordinateValue k 0 = 1 := by
  rw [cubeCoordinateValue, singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_zero]
  exact ModuleCat.hom_inv_apply _ _

end CoordinateValue

section FaceFactors

private abbrev U (n : ℕ) : Set (S.{u} (n + 1)) := {pole n}ᶜ
private abbrev V (n : ℕ) : Set (S.{u} (n + 1)) := {-pole n}ᶜ

private def boundaryFace (n : ℕ) (i : Fin (n + 2)) (t : unitInterval) (ht : t = 0 ∨ t = 1) :
    SingularCube (B.{u} (n + 2)) (n + 1) where
  toFun z := ⟨ULift.up (Fin.insertNth i t z), ⟨i, by
    simpa only [Fin.insertNth_apply_same] using ht⟩⟩
  continuous_toFun := by fun_prop

@[simp] private lemma boundaryFace_coordinate (n : ℕ) (i : Fin (n + 2)) (t : unitInterval)
    (ht : t = 0 ∨ t = 1) (z : Fin (n + 1) → unitInterval) :
    (boundaryFace n i t ht z).val.down i = t :=
  Fin.insertNth_apply_same (α := fun _ : Fin (n + 2) ↦ unitInterval) i t z

private lemma boundaryFace_map (n : ℕ) (i : Fin (n + 2)) (t : unitInterval) (ht : t = 0 ∨ t = 1) :
    (cubeBoundaryPair.{u} (n + 2)).map.hom.comp (boundaryFace n i t ht) =
      SingularCube.face i t (upCube (n + 2)) := by
  apply ContinuousMap.ext
  intro z
  -- The pair ambient space is `cubeModel`; `face_apply` uses that same presentation.
  erw [SingularCube.face_apply]
  rfl

private def sideOverlap (n : ℕ) (i : Fin (n + 1)) (t : unitInterval) (ht : t = 0 ∨ t = 1) :
    SingularCube (U.{u} (n + 1) ∩ V (n + 1) : Set (S (n + 2))) (n + 1) where
  toFun z := ⟨(ContinuousMap.ofClass (radialHomeomorph (n + 2))) (boundaryFace n i.castSucc t
    ht z), by
    apply radialHomeomorph_mem_overlap_of_apply_castSucc_ne_half (n + 1) _ i
    rw [boundaryFace_coordinate]
    rcases ht with rfl | rfl <;> norm_num⟩
  continuous_toFun := ((ContinuousMap.ofClass (radialHomeomorph (n + 2))).continuous.comp
    (boundaryFace n i.castSucc t ht).continuous).subtype_mk _

private def bottomU (n : ℕ) : SingularCube (U.{u} (n + 1)) (n + 1) where
  toFun z := ⟨(ContinuousMap.ofClass (radialHomeomorph (n + 2)))
      (boundaryFace n (Fin.last (n + 1)) 0 (Or.inl rfl) z),
    radialHomeomorph_mem_compl_lastPole_of_last_eq_zero (n + 1) _ (congrArg (fun t :
      unitInterval ↦ (t :
      ℝ))
      (boundaryFace_coordinate.{u} n (Fin.last (n + 1)) 0 (Or.inl rfl) z))⟩
  continuous_toFun := ((ContinuousMap.ofClass (radialHomeomorph (n + 2))).continuous.comp
    (boundaryFace n (Fin.last (n + 1)) 0 (Or.inl rfl)).continuous).subtype_mk _

private def topV (n : ℕ) : SingularCube (V.{u} (n + 1)) (n + 1) where
  toFun z := ⟨(ContinuousMap.ofClass (radialHomeomorph (n + 2)))
      (boundaryFace n (Fin.last (n + 1)) 1 (Or.inr rfl) z),
    radialHomeomorph_mem_compl_neg_lastPole_of_last_eq_one (n + 1) _ (congrArg (fun t :
      unitInterval ↦ (t :
      ℝ))
      (boundaryFace_coordinate.{u} n (Fin.last (n + 1)) 1 (Or.inr rfl) z))⟩
  continuous_toFun := ((ContinuousMap.ofClass (radialHomeomorph (n + 2))).continuous.comp
    (boundaryFace n (Fin.last (n + 1)) 1 (Or.inr rfl)).continuous).subtype_mk _

private lemma boundaryFace_apply (n : ℕ) (i : Fin (n + 2)) (t : unitInterval)
    (ht : t = 0 ∨ t = 1) (z : Fin (n + 1) → unitInterval) :
    (boundaryFace.{u} n i t ht z).val.down = Fin.insertNth i t z := by
  rw [boundaryFace]
  rfl

private lemma liftSnd_eq_boundaryFace (n : ℕ) (i : Fin (n + 2)) (t : unitInterval)
    (ht : t = 0 ∨ t = 1)
    (h : ∀ z, SingularCube.face i t (upCube.{u} (n + 2)) z ∈
      Set.range (cubeBoundaryPair.{u} (n + 2)).map) :
    (cubeBoundaryPair.{u} (n + 2)).liftSnd (SingularCube.face i t (upCube (n + 2))) h =
      boundaryFace n i t ht := by
  apply ContinuousMap.ext
  intro z
  apply (cubeBoundaryPair.{u} (n + 2)).isEmbedding_map.injective
  exact (TopPair.map_liftSnd _ _ z).trans
    (ContinuousMap.congr_fun (boundaryFace_map n i t ht) z).symm

private lemma sideOverlap_coe (n : ℕ) (i : Fin (n + 1)) (t : unitInterval)
    (ht : t = 0 ∨ t = 1) (z : Fin (n + 1) → unitInterval) :
    (sideOverlap.{u} n i t ht z : S (n + 2)) =
      (ContinuousMap.ofClass (radialHomeomorph (n + 2))) (boundaryFace n i.castSucc t ht z) := by
  rw [sideOverlap]
  rfl
private lemma bottomU_coe (n : ℕ) (z : Fin (n + 1) → unitInterval) :
    (bottomU.{u} n z : S (n + 2)) =
      (ContinuousMap.ofClass (radialHomeomorph (n + 2))) (boundaryFace n (Fin.last (n + 1)) 0
        (Or.inl
        rfl) z) := by
  rw [bottomU]
  rfl
private lemma topV_coe (n : ℕ) (z : Fin (n + 1) → unitInterval) :
    (topV.{u} n z : S (n + 2)) =
      (ContinuousMap.ofClass (radialHomeomorph (n + 2))) (boundaryFace n (Fin.last (n + 1)) 1
        (Or.inr
        rfl) z) := by
  rw [topV]
  rfl

end FaceFactors

section NormalizedBoundarySplit

private abbrev overlapToU (n : ℕ) : C((U.{u} n ∩ V n : Set (S (n + 1))), U n) :=
  ContinuousMap.inclusion Set.inter_subset_left
private abbrev overlapToV (n : ℕ) : C((U.{u} n ∩ V n : Set (S (n + 1))), V n) :=
  ContinuousMap.inclusion Set.inter_subset_right

private def sideU (n : ℕ) (i : Fin (n + 1)) (t : unitInterval) (ht : t = 0 ∨ t = 1) :
    SingularCube (U.{u} (n + 1)) (n + 1) :=
  (overlapToU (n + 1)).comp (sideOverlap n i t ht)

private lemma sideU_ambient (n : ℕ) (i : Fin (n + 1)) (t : unitInterval) (ht : t = 0 ∨ t = 1) :
    (ContinuousMap.subtypeVal (U.{u} (n + 1))).comp (sideU n i t ht) =
      (ContinuousMap.ofClass (radialHomeomorph (n + 2))).comp (boundaryFace n i.castSucc t ht) := by
  apply ContinuousMap.ext
  intro z
  rw [sideU]
  exact sideOverlap_coe n i t ht z

private lemma bottomU_ambient (n : ℕ) :
    (ContinuousMap.subtypeVal (U.{u} (n + 1))).comp (bottomU n) =
      (ContinuousMap.ofClass (radialHomeomorph (n + 2))).comp
        (boundaryFace n (Fin.last (n + 1)) 0 (Or.inl rfl)) := by
  apply ContinuousMap.ext
  exact bottomU_coe n

private lemma topV_ambient (n : ℕ) :
    (ContinuousMap.subtypeVal (V.{u} (n + 1))).comp (topV n) =
      (ContinuousMap.ofClass (radialHomeomorph (n + 2))).comp
        (boundaryFace n (Fin.last (n + 1)) 1 (Or.inr rfl)) := by
  apply ContinuousMap.ext
  exact topV_coe n

variable (k : Type u) [Ring k]
private def uNorm (n : ℕ) : NormalizedCubicalChain (U.{u} (n + 1)) k (n + 1) :=
  (∑ i : Fin (n + 1), (-1 : k) ^ (i : ℕ) •
    (NormalizedCubicalChain.ofCube (U (n + 1)) k (sideU n i 0 (Or.inl rfl)) -
      NormalizedCubicalChain.ofCube (U (n + 1)) k (sideU n i 1 (Or.inr rfl)))) +
    (-1 : k) ^ (n + 1) • NormalizedCubicalChain.ofCube (U (n + 1)) k (bottomU n)

private def vNorm (n : ℕ) : NormalizedCubicalChain (V.{u} (n + 1)) k (n + 1) :=
  (-1 : k) ^ (n + 2) • NormalizedCubicalChain.ofCube (V (n + 1)) k (topV n)

private def fullBoundary (n : ℕ) : NormalizedCubicalChain (B.{u} (n + 2)) k (n + 1) :=
  TopPair.cubicalBoundaryChainOfCube k (upCube (n + 2)) (mapsTo_upCube_boundary (n + 2))

private lemma fullBoundary_i (n : ℕ) :
    ((normalizedCubicalChainComplex k).obj (TopCat.of (B.{u} (n + 2)))).iCycles (n + 1)
      (cubeBoundaryCycle k (n + 1)) = fullBoundary k n :=
  iCycles_cubeBoundaryCycle k (n + 1)

private lemma fullBoundary_faces (n : ℕ) : fullBoundary k n =
    ∑ i : Fin (n + 2), (-1 : k) ^ (i : ℕ) •
      (NormalizedCubicalChain.ofCube (B (n + 2)) k (boundaryFace n i 0 (Or.inl rfl)) -
        NormalizedCubicalChain.ofCube (B (n + 2)) k (boundaryFace n i 1 (Or.inr rfl))) := by
  rw [fullBoundary]
  -- Normalize the pair ambient space and the native boundary index `n + 1 + 1`.
  erw [TopPair.cubicalBoundaryChainOfCube_def]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun z : NormalizedCubicalChain (B.{u} (n + 2)) k (n + 1) ↦ (-1 : k) ^ (i : ℕ) • z)
  exact congrArg₂ (fun a b : NormalizedCubicalChain (B.{u} (n + 2)) k (n + 1) ↦ a - b)
    (congrArg (fun c : SingularCube (B.{u} (n + 2)) (n + 1) ↦ NormalizedCubicalChain.ofCube _ k c)
      (liftSnd_eq_boundaryFace n i 0 (Or.inl rfl) _))
    (congrArg (fun c : SingularCube (B.{u} (n + 2)) (n + 1) ↦ NormalizedCubicalChain.ofCube _ k c)
      (liftSnd_eq_boundaryFace n i 1 (Or.inr rfl) _))

private lemma fullBoundary_cycle (n : ℕ) :
    NormalizedCubicalChain.boundary (B (n + 2)) k n (fullBoundary k n) = 0 := by
  rw [fullBoundary]
  exact TopPair.boundary_cubicalBoundaryChainOfCube k _ _

private lemma cover_sum (n : ℕ) :
    NormalizedCubicalChain.map k (ContinuousMap.subtypeVal (U (n + 1))) (n + 1) (uNorm k n) +
      NormalizedCubicalChain.map k (ContinuousMap.subtypeVal (V (n + 1))) (n + 1) (vNorm k n) =
    NormalizedCubicalChain.map k (ContinuousMap.ofClass (radialHomeomorph (n + 2))) (n + 1)
      (fullBoundary k n) := by
  rw [fullBoundary_faces]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  rw [uNorm, vNorm]
  simp only [map_sum, map_add, map_sub, map_smul, NormalizedCubicalChain.map_ofCube,
    sideU_ambient, bottomU_ambient, topV_ambient, Fin.val_castSucc, Fin.val_last]
  rw [upperFace_coefficient k n]
  simp only [neg_smul, sub_eq_add_neg, add_assoc, smul_add, smul_neg]

end NormalizedBoundarySplit

section UpperFaceBoundary

private lemma lastFace_eq_upperInclusion (n : ℕ) (x : B.{u} (n + 1)) :
    boundaryFace n (Fin.last (n + 1)) 1 (Or.inr rfl) x.val.down = upperInclusion (n + 1) x := by
  apply Subtype.ext
  apply ULift.ext
  rw [boundaryFace_apply, upperInclusion_apply_down]
  exact Fin.insertNth_last' 1 x.val.down

private def upperCubeMap (n : ℕ) : C((cubeBoundaryPair.{u} (n + 1)).fst, V.{u} (n + 1)) :=
  (topV n).comp ⟨ULift.down, continuous_uliftDown⟩

private lemma upperCubeMap_comp_upCube (n : ℕ) :
    (upperCubeMap.{u} n).comp (upCube (n + 1)) = topV n := by
  apply ContinuousMap.ext
  intro z
  rw [upperCubeMap]
  rfl

private lemma upperCubeMap_on_boundary (n : ℕ) :
    (upperCubeMap.{u} n).comp (cubeBoundaryPair.{u} (n + 1)).map.hom =
      (overlapToV (n + 1)).comp (upperOverlap (n + 1)) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact (topV_coe n x.val.down).trans
    ((congrArg (ContinuousMap.ofClass (radialHomeomorph (n + 2))) (lastFace_eq_upperInclusion n
      x)).trans
      (coe_upperOverlap_apply (n + 1) x).symm)

variable (k : Type u) [Ring k]

private def lowerBoundary (n : ℕ) : NormalizedCubicalChain (B.{u} (n + 1)) k n :=
  TopPair.cubicalBoundaryChainOfCube k (upCube (n + 1)) (mapsTo_upCube_boundary (n + 1))

private lemma topV_boundary (n : ℕ) :
    NormalizedCubicalChain.boundary (V.{u} (n + 1)) k n
      (NormalizedCubicalChain.ofCube (V (n + 1)) k (topV n)) =
      NormalizedCubicalChain.map k (overlapToV (n + 1)) n
        (NormalizedCubicalChain.map k (upperOverlap (n + 1)) n (lowerBoundary k n)) := by
  have h := TopPair.boundary_ofCube_comp k (cubeBoundaryPair.{u} (n + 1)) (upCube (n + 1))
    (mapsTo_upCube_boundary (n + 1)) (upperCubeMap n)
  rw [upperCubeMap_on_boundary, upperCubeMap_comp_upCube,
    NormalizedCubicalChain.map_comp] at h
  exact h

private lemma lowerBoundary_i (n : ℕ) :
    ((normalizedCubicalChainComplex k).obj (TopCat.of (B.{u} (n + 1)))).iCycles n
      (cubeBoundaryCycle k n) = lowerBoundary k n :=
  iCycles_cubeBoundaryCycle k n

private def wNorm (n : ℕ) : NormalizedCubicalChain (U.{u} (n + 1) ∩ V (n + 1) : Set (S (n + 2))) k n
  :=
  (-1 : k) ^ (n + 1) • NormalizedCubicalChain.map k (upperOverlap (n + 1)) n (lowerBoundary k n)

private lemma vNorm_boundary (n : ℕ) : NormalizedCubicalChain.boundary (V.{u} (n + 1)) k n (vNorm k
  n) =
    -(NormalizedCubicalChain.map k (overlapToV (n + 1)) n (wNorm k n)) := by
  rw [vNorm, map_smul, topV_boundary, wNorm, upperFace_coefficient k n]
  simp only [map_smul, neg_smul]

end UpperFaceBoundary



section SmallSingularCycles

private abbrev XI (n : ℕ) := TopCat.toSSet.obj (TopCat.of (U.{u} (n + 1) ∩ V (n + 1) : Set (S (n +
  2))))
private abbrev XU (n : ℕ) := TopCat.toSSet.obj (TopCat.of (U.{u} (n + 1)))
private abbrev XV (n : ℕ) := TopCat.toSSet.obj (TopCat.of (V.{u} (n + 1)))
private abbrev XS (n : ℕ) := ((TopCat.of (S.{u} (n + 2))).smallSingularSubcomplex
  ![U (n + 1), V (n + 1)] : SSet)
private abbrev KI (k : Type u) [Ring k] (n : ℕ) := (XI.{u} n).chainComplex (Coeff k)
private abbrev KU (k : Type u) [Ring k] (n : ℕ) := (XU.{u} n).chainComplex (Coeff k)
private abbrev KV (k : Type u) [Ring k] (n : ℕ) := (XV.{u} n).chainComplex (Coeff k)
private abbrev KS (k : Type u) [Ring k] (n : ℕ) := (XS.{u} n).chainComplex (Coeff k)
private abbrev KSphere (k : Type u) [Ring k] (n : ℕ) := (singularChains k).obj (TopCat.of (S.{u} (n
  + 2)))
private abbrev tU (n : ℕ) : XI.{u} n ⟶ XU n := TopCat.toSSet.map (TopCat.ofHom (overlapToU (n + 1)))
private abbrev tV (n : ℕ) : XI.{u} n ⟶ XV n := TopCat.toSSet.map (TopCat.ofHom (overlapToV (n + 1)))
private abbrev jU (n : ℕ) : XU.{u} n ⟶ XS n :=
  TopCat.toSmallSingularSubcomplex (X := TopCat.of (S.{u} (n + 2))) (S := U (n + 1))
    (i := (0 : Fin 2)) ![U (n + 1), V (n + 1)] (Set.Subset.refl _)
private abbrev jV (n : ℕ) : XV.{u} n ⟶ XS n :=
  TopCat.toSmallSingularSubcomplex (X := TopCat.of (S.{u} (n + 2))) (S := V (n + 1))
    (i := (1 : Fin 2)) ![U (n + 1), V (n + 1)] (Set.Subset.refl _)
private abbrev incS (n : ℕ) : XS.{u} n ⟶ TopCat.toSSet.obj (TopCat.of (S.{u} (n + 2))) :=
  ((TopCat.of (S.{u} (n + 2))).smallSingularSubcomplex ![U (n + 1), V (n + 1)]).ι

private instance instMonoOverlapToU (n : ℕ) : Mono (tU.{u} n) := by
  dsimp only [tU, overlapToU]
  infer_instance
private instance instMonoToSmallU (n : ℕ) : Mono (jU.{u} n) := by
  have h : jU.{u} n ≫ incS n = TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.subtypeVal (U.{u} (n + 1)))) :=
    TopCat.toSmallSingularSubcomplex_ι (X := TopCat.of (S.{u} (n + 2)))
      (S := U (n + 1)) (i := (0 : Fin 2)) ![U (n + 1), V (n + 1)]
      (Set.Subset.refl (U (n + 1)))
  exact mono_of_mono_fac h

private lemma cover_square (n : ℕ) : IsPushout (tU.{u} n) (tV n) (jU n) (jV n) :=
  TopCat.isPushout_toSSet_inter_smallSingularSubcomplex (X := TopCat.of (S.{u} (n + 2)))
    (U (n + 1)) (V (n + 1))

variable (k : Type u) [Ring k] (n : ℕ)
private def uSing : (KU k n).X (n + 1) :=
  ((cubicalToSingular k).app (TopCat.of (U (n + 1)))).f (n + 1) (uNorm k n)
private def vSing : (KV k n).X (n + 1) :=
  ((cubicalToSingular k).app (TopCat.of (V (n + 1)))).f (n + 1) (vNorm k n)
private def zSmall : (KS k n).X (n + 1) :=
  (SSet.chainComplexMap (jU n) (Coeff k)).f (n + 1) (uSing k n) +
    (SSet.chainComplexMap (jV n) (Coeff k)).f (n + 1) (vSing k n)

private def wNCycle : ((normalizedCubicalChainComplex k).obj
    (TopCat.of (U.{u} (n + 1) ∩ V (n + 1) : Set (S (n + 2))))).cycles n :=
  (-1 : k) ^ (n + 1) • HomologicalComplex.cyclesMap
    ((normalizedCubicalChainComplex k).map (TopCat.ofHom (upperOverlap (n + 1)))) n
      (cubeBoundaryCycle k n)

private def wCycle : (KI k n).cycles n := HomologicalComplex.cyclesMap
  ((cubicalToSingular k).app (TopCat.of (U.{u} (n + 1) ∩ V (n + 1) : Set (S (n + 2))))) n (wNCycle k
    n)

private lemma wCycle_i : (KI k n).iCycles n (wCycle k n) =
    ((cubicalToSingular k).app (TopCat.of (U.{u} (n + 1) ∩ V (n + 1) : Set (S (n + 2))))).f n
      (wNorm k n) := by
  rw [wCycle]
  -- Identify KI as the singular-chain codomain of the chosen comparison.
  erw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply]
  rw [wNCycle]
  rw [map_smul, HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, lowerBoundary_i,
    normalizedCubicalChainComplex_map_f_apply]
  rw [wNorm]
  rfl

private def sphereCycle : (KSphere k n).cycles (n + 1) := HomologicalComplex.cyclesMap
  ((cubicalToSingular k).app (TopCat.of (B.{u} (n + 2))) ≫
    (singularChains k).map (TopCat.ofHom (ContinuousMap.ofClass (radialHomeomorph (n + 2)))))
      (n + 1)
      (cubeBoundaryCycle k (n + 1))

private lemma sphereCycle_i : (KSphere k n).iCycles (n + 1) (sphereCycle k n) =
    ((cubicalToSingular k).app (TopCat.of (S.{u} (n + 2)))).f (n + 1)
      (NormalizedCubicalChain.map k (ContinuousMap.ofClass (radialHomeomorph (n + 2))) (n + 1)
        (fullBoundary k n)) := by
  rw [sphereCycle, HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, fullBoundary_i]
  exact (cubicalToSingular_app_f_map (TopCat.ofHom (ContinuousMap.ofClass (radialHomeomorph (n
    + 2))))
    (n + 1) (fullBoundary k n)).symm

private lemma zSmall_inclusion : (SSet.chainComplexMap (incS n) (Coeff k)).f (n + 1) (zSmall k n) =
    (KSphere k n).iCycles (n + 1) (sphereCycle k n) := by
  rw [zSmall]
  rw [map_add]
  rw [uSing, vSing, sphereCycle_i]
  have hu := chainComplexMap_ι_toSmallSingularSubcomplex_cubicalToSingular (k := k) (X :=
    TopCat.of (S.{u} (n + 2)))
    ![U (n + 1), V (n + 1)] (S := U (n + 1)) (i := (0 : Fin 2))
    (Set.Subset.refl _) (n + 1) (uNorm k n)
  have hv := chainComplexMap_ι_toSmallSingularSubcomplex_cubicalToSingular (k := k) (X :=
    TopCat.of (S.{u} (n + 2)))
    ![U (n + 1), V (n + 1)] (S := V (n + 1)) (i := (1 : Fin 2))
    (Set.Subset.refl _) (n + 1) (vNorm k n)
  exact (congrArg₂ (· + ·) hu hv).trans
    (((((cubicalToSingular k).app (TopCat.of (S.{u} (n + 2)))).f (n + 1)).hom.map_add _
      _).symm.trans
      (congrArg (((cubicalToSingular k).app (TopCat.of (S.{u} (n + 2)))).f (n + 1)) (cover_sum k
        n)))

private lemma zSmall_cycle : (KS k n).d (n + 1) n (zSmall k n) = 0 := by
  apply (ModuleCat.mono_iff_injective ((SSet.chainComplexMap (incS n) (Coeff k)).f n)).1
    inferInstance
  calc
    _ = (KSphere k n).d (n + 1) n
        ((SSet.chainComplexMap (incS n) (Coeff k)).f (n + 1) (zSmall k n)) :=
      (HomologicalComplex.Hom.comm_apply _ (n + 1) n _).symm
    _ = (KSphere k n).d (n + 1) n ((KSphere k n).iCycles (n + 1) (sphereCycle k n)) :=
      congrArg _ (zSmall_inclusion k n)
    _ = 0 := (KSphere k n).moduleCat_d_iCycles_apply (n + 1) n (sphereCycle k n)
    _ = _ := (map_zero _).symm

private def zCycle : (KS k n).cycles (n + 1) :=
  (KS k n).moduleCatCyclesMk (zSmall k n) n (by simp) (zSmall_cycle k n)
private lemma zCycle_i : (KS k n).iCycles (n + 1) (zCycle k n) = zSmall k n :=
  HomologicalComplex.iCycles_moduleCatCyclesMk ..

private lemma vSing_boundary : (KV k n).d (n + 1) n (vSing k n) =
    -((SSet.chainComplexMap (tV n) (Coeff k)).f n ((KI k n).iCycles n (wCycle k n))) := by
  rw [vSing]
  -- KV uses simplicial chains; the comparison uses singular and normalized cubical chains.
  erw [singularChains_d_cubicalToSingular, vNorm_boundary, wCycle_i, map_neg]
  exact congrArg Neg.neg (cubicalToSingular_app_f_map (TopCat.ofHom (overlapToV (n + 1))) n
    (wNorm k n))

private lemma uSing_boundary : (KU k n).d (n + 1) n (uSing k n) =
    (SSet.chainComplexMap (tU n) (Coeff k)).f n ((KI k n).iCycles n (wCycle k n)) := by
  apply (ModuleCat.mono_iff_injective ((SSet.chainComplexMap (jU n) (Coeff k)).f n)).1 inferInstance
  let a := (SSet.chainComplexMap (jU n) (Coeff k)).f n
  let b := (SSet.chainComplexMap (jV n) (Coeff k)).f n
  let du := (KU k n).d (n + 1) n (uSing k n)
  let wi := (KI k n).iCycles n (wCycle k n)
  have he : (KS k n).d (n + 1) n (zSmall k n) =
      a du + b ((KV k n).d (n + 1) n (vSing k n)) :=
    (((KS k n).d (n + 1) n).hom.map_add _ _).trans
      (congrArg₂ (· + ·)
        (HomologicalComplex.Hom.comm_apply (SSet.chainComplexMap (jU n) (Coeff k)) (n + 1) n (uSing
          k n))
        (HomologicalComplex.Hom.comm_apply (SSet.chainComplexMap (jV n) (Coeff k)) (n + 1) n (vSing
          k n)))
  have hv : b ((KV k n).d (n + 1) n (vSing k n)) =
      -(b ((SSet.chainComplexMap (tV n) (Coeff k)).f n wi)) :=
    (congrArg b (vSing_boundary k n)).trans (b.hom.map_neg _)
  have hz : a du = b ((SSet.chainComplexMap (tV n) (Coeff k)).f n wi) :=
    add_neg_eq_zero.mp ((he.trans (congrArg (a du + ·) hv)).symm.trans (zSmall_cycle k n))
  have h : SSet.chainComplexMap (tU n) (Coeff k) ≫ SSet.chainComplexMap (jU n) (Coeff k) =
      SSet.chainComplexMap (tV n) (Coeff k) ≫ SSet.chainComplexMap (jV n) (Coeff k) := by
    rw [← Functor.map_comp, ← Functor.map_comp, (cover_square n).w]
  exact hz.trans (congrArg (fun f ↦ f.f n ((KI k n).iCycles n (wCycle k n))) h).symm

private lemma actual_small_mv :
    SSet.mayerVietorisδ (Coeff k) (cover_square n) (n + 1) n rfl
      ((KS k n).homologyπ (n + 1) (zCycle k n)) = (KI k n).homologyπ n (wCycle k n) := by
  apply SSet.mayerVietorisδ_homologyπ (Coeff k) n (cover_square n) (zCycle k n) (uSing k n) (vSing k
    n) (wCycle k n)
  · rw [zCycle_i, zSmall]
  · exact (uSing_boundary k n).symm
  · exact (vSing_boundary k n).symm

private lemma included_zCycle : HomologicalComplex.cyclesMap
    (SSet.chainComplexMap (incS n) (Coeff k)) (n + 1) (zCycle k n) = sphereCycle k n := by
  apply (KSphere k n).moduleCat_iCycles_injective (n + 1)
  -- The inclusion is expressed using SSet chains, and KSphere using singular chains.
  erw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, zCycle_i, zSmall_inclusion]

private lemma included_zClass : SSet.homologyMap (incS n) (Coeff k) (n + 1)
    ((KS k n).homologyπ (n + 1) (zCycle k n)) = (KSphere k n).homologyπ (n + 1) (sphereCycle k n) :=
      by
  rw [← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply,
    included_zCycle]
  rfl

end SmallSingularCycles

section RelativeSphereClass

private abbrev P (n : ℕ) := cubeBoundaryPair.{u} (n + 1)
private abbrev KBoundary (k : Type u) [Ring k] (n : ℕ) :=
  (normalizedCubicalChainComplex k).obj (TopCat.of (B.{u} (n + 1)))
private abbrev KUnitSphere (k : Type u) [Ring k] (n : ℕ) :=
  (singularChains k).obj (TopCat.of (S.{u} (n + 1)))
variable (k : Type u) [Ring k] (n : ℕ)

private def relativeCubeClass : (P.{u} n).singularHomology (C := ModuleCat.{u} k) (Coeff k) (n + 1)
  :=
  (TopPair.singularCubicalHomologyIso k (P n) (n + 1)).inv
    (((P n).cubicalChainComplex k).homologyπ (n + 1) (cubeBoundaryPairCycle k n))

private def cubeToSphereBoundary :
    (P.{u} n).singularHomology (Coeff k) (n + 1) ⟶
      (reducedSingularHomologyFunctor (Coeff k) n).obj (TopCat.of (S.{u} (n + 1))) :=
  TopPair.singularHomologyMap (diskBoundaryPairIsoCube.{u} (n + 1)).inv (Coeff k) (n + 1) ≫
    (diskBoundaryPair.{u} (n + 1)).reducedSingularHomologyδ (Coeff k) n ≫
      (reducedSingularHomologyFunctor (Coeff k) n).map
        (TopCat.ofHom (diskBoundaryHomeomorph.{u} (n + 1)).toHomotopyEquiv.toFun)

private def sphereBoundaryCycle : (KUnitSphere k n).cycles n :=
  HomologicalComplex.cyclesMap ((cubicalToSingular k).app (TopCat.of (B.{u} (n + 1))) ≫
    (singularChains k).map (TopCat.ofHom (ContinuousMap.ofClass (radialHomeomorph (n + 1))))) n
      (cubeBoundaryCycle k n)

private lemma sphereBoundaryCycle_i : (KUnitSphere k n).iCycles n (sphereBoundaryCycle k n) =
    ((singularChains k).map (TopCat.ofHom (ContinuousMap.ofClass (radialHomeomorph (n + 1))))).f n
      (((cubicalToSingular k).app (TopCat.of (B.{u} (n + 1)))).f n
        ((KBoundary k n).iCycles n (cubeBoundaryCycle k n))) := by
  rw [sphereBoundaryCycle, HomologicalComplex.moduleCat_iCycles_cyclesMap_apply]
  rfl


private lemma relativeCubeClass_boundary :
    (P n).singularHomologyδ (Coeff k) (n + 1) n rfl (relativeCubeClass k n) =
      (singularCubicalHomologyIso k (P n).snd n).inv
        ((KBoundary k n).homologyπ n (cubeBoundaryCycle k n)) := by
  rw [relativeCubeClass]
  have h := ConcreteCategory.congr_hom
    (TopPair.singularCubicalHomologyIso_inv_singularHomologyδ k (P n) (n + 1) n rfl)
    (((P n).cubicalChainComplex k).homologyπ (n + 1) (cubeBoundaryPairCycle k n))
  exact (ModuleCat.comp_apply _ _ _).symm.trans
    (h.trans ((ModuleCat.comp_apply _ _ _).trans
      (congrArg _ (cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle k n))))

private lemma sphereBoundaryCycle_class : (KUnitSphere k n).homologyπ n (sphereBoundaryCycle k n) =
    HomologicalComplex.homologyMap ((singularChains k).map
      (TopCat.ofHom (ContinuousMap.ofClass (radialHomeomorph (n + 1))))) n
        ((singularCubicalHomologyIso k (P n).snd n).inv
          ((KBoundary k n).homologyπ n (cubeBoundaryCycle k n))) := by
  rw [singularCubicalHomologyIso_inv, ← ModuleCat.comp_apply,
    ← HomologicalComplex.homologyMap_comp, ← ModuleCat.comp_apply,
    HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply, sphereBoundaryCycle]

private lemma cubeToSphereBoundary_eq_redδ : cubeToSphereBoundary k n =
    (P n).reducedSingularHomologyδ (Coeff k) n ≫
      (reducedSingularHomologyFunctor (Coeff k) n).map (TopCat.ofHom (ContinuousMap.ofClass
        (radialHomeomorph (n + 1)))) := by
  rw [cubeToSphereBoundary]
  -- Normalize the pair boundary object before composing its TopCat boundary maps.
  erw [← Category.assoc,
    ← TopPair.reducedSingularHomologyδ_naturality (Coeff k) (diskBoundaryPairIsoCube.{u} (n +
      1)).inv n,
    Category.assoc, ← Functor.map_comp]
  congr 1
  congr 1
  apply ConcreteCategory.hom_ext
  intro x
  exact (radialHomeomorph_apply (n + 1) x).symm

private lemma cubeToSphereBoundary_comp_ι :
    cubeToSphereBoundary k n ≫ (reducedSingularHomologyι (Coeff k) n).app (TopCat.of (S.{u} (n +
      1))) =
      (P n).singularHomologyδ (Coeff k) (n + 1) n ≫
        SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.ofClass
          (radialHomeomorph (n + 1))))) (Coeff k) n := by
  rw [cubeToSphereBoundary_eq_redδ]
  -- The inclusion uses the ordinary homology functor, and the pair boundary uses SSet maps.
  erw [Category.assoc, (reducedSingularHomologyι (Coeff k) n).naturality,
    ← Category.assoc, TopPair.reducedSingularHomologyδ_comp_ι]
  rfl

private lemma relativeCubeClass_reduced_boundary :
    (reducedSingularHomologyι (Coeff k) n).app (TopCat.of (S.{u} (n + 1)))
      (cubeToSphereBoundary k n (relativeCubeClass k n)) =
        (KUnitSphere k n).homologyπ n (sphereBoundaryCycle k n) := by
  have h := ConcreteCategory.congr_hom (cubeToSphereBoundary_comp_ι k n) (relativeCubeClass k n)
  exact (ModuleCat.comp_apply _ _ _).symm.trans
    (h.trans ((ModuleCat.comp_apply _ _ _).trans
      ((congrArg _ (relativeCubeClass_boundary k n)).trans (sphereBoundaryCycle_class k n).symm)))

private lemma disk_cube_inverse :
    TopPair.singularHomologyMap (diskBoundaryPairToCube.{u} (n + 1)) (Coeff k) (n + 1) ≫
      TopPair.singularHomologyMap (diskBoundaryPairIsoCube.{u} (n + 1)).inv (Coeff k) (n + 1) =
        𝟙 ((diskBoundaryPair.{u} (n + 1)).singularHomology (Coeff k) (n + 1)) := by
  rw [← diskBoundaryPairIsoCube_hom, ← TopPair.singularHomologyMap_comp,
    Iso.hom_inv_id, TopPair.singularHomologyMap_id]

private lemma disk_boundary_coordinate : (diskBoundaryPair.{u} (n + 1)).reducedSingularHomologyδ
  (Coeff k) n ≫
    (reducedSingularHomologyFunctor (Coeff k) n).map
      (TopCat.ofHom (diskBoundaryHomeomorph.{u} (n + 1)).toHomotopyEquiv.toFun) ≫
    (reducedSingularHomologySphereIso (Coeff k) (stdBasis (n + 1))).hom =
      (singularHomologyDiskBoundaryPairIso (Coeff k) (n + 1)).hom := by
  rw [stdBasis]
  exact ((singularHomologyDiskBoundaryPairIso_succ_hom (Coeff k) n).trans
    (congrArg ((diskBoundaryPair.{u} (n + 1)).reducedSingularHomologyδ (Coeff k) n ≫ ·)
      (reducedSingularHomologyTopCatSphereIso_hom (Coeff k) n))).symm

private lemma cube_coordinate : cubeToSphereBoundary k n ≫
    (reducedSingularHomologySphereIso (Coeff k) (stdBasis (n + 1))).hom =
      (singularHomologyCubeBoundaryPairIso (Coeff k) (n + 1)).hom := by
  have hc : TopPair.singularHomologyMap (diskBoundaryPairToCube.{u} (n + 1)) (Coeff k) (n + 1) ≫
      TopPair.singularHomologyMap (diskBoundaryPairIsoCube.{u} (n + 1)).inv (Coeff k) (n + 1) ≫
        ((diskBoundaryPair.{u} (n + 1)).reducedSingularHomologyδ (Coeff k) n ≫
          (reducedSingularHomologyFunctor (Coeff k) n).map
            (TopCat.ofHom (diskBoundaryHomeomorph.{u} (n + 1)).toHomotopyEquiv.toFun) ≫
          (reducedSingularHomologySphereIso (Coeff k) (stdBasis (n + 1))).hom) =
      (diskBoundaryPair.{u} (n + 1)).reducedSingularHomologyδ (Coeff k) n ≫
        (reducedSingularHomologyFunctor (Coeff k) n).map
          (TopCat.ofHom (diskBoundaryHomeomorph.{u} (n + 1)).toHomotopyEquiv.toFun) ≫
        (reducedSingularHomologySphereIso (Coeff k) (stdBasis (n + 1))).hom := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (disk_cube_inverse k n)).trans (Category.id_comp _))
  apply (cancel_epi (singularHomologyCubeBoundaryPairIso (Coeff k) (n + 1)).inv).1
  rw [Iso.inv_hom_id, singularHomologyCubeBoundaryPairIso_inv, cubeToSphereBoundary]
  simp only [Category.assoc]
  exact (congrArg ((singularHomologyDiskBoundaryPairIso (Coeff k) (n + 1)).inv ≫ ·) hc).trans
    ((congrArg ((singularHomologyDiskBoundaryPairIso (Coeff k) (n + 1)).inv ≫ ·)
      (disk_boundary_coordinate k n)).trans
      (Iso.inv_hom_id _))

end RelativeSphereClass

section OrdinaryMayerVietoris

private abbrev QSphere (n : ℕ) := TopCat.of (sphere (0 : PE.{u} (n + 1)) 1)
private abbrev KQ (k : Type u) [Ring k] (n : ℕ) := (singularChains k).obj (QSphere.{u} n)
private abbrev eqMap (n : ℕ) : TopCat.of (U.{u} (n + 1) ∩ V (n + 1) : Set (S (n + 2))) ⟶ QSphere n
  :=
  TopCat.ofHom (equatorHomotopyEquiv (pole (n + 1))).toFun
private abbrev lowerEqMap (n : ℕ) : TopCat.of (S.{u} (n + 1)) ⟶ QSphere n :=
  TopCat.ofHom ⟨(equatorIsometry (n + 1)).toLinearIsometry.unitSphereMap,
    (equatorIsometry (n + 1)).toLinearIsometry.continuous_unitSphereMap⟩

private lemma equator_diagram (n : ℕ) :
    TopCat.ofHom (upperOverlap.{u} (n + 1)) ≫ eqMap n =
      TopCat.ofHom (ContinuousMap.ofClass (radialHomeomorph (n + 1))) ≫ lowerEqMap n :=
  ConcreteCategory.hom_ext _ _ (equatorHomotopyEquiv_upperOverlap (n + 1))

variable (k : Type u) [Ring k] (n : ℕ)
private abbrev ordinaryδ : (KSphere k n).homology (n + 1) ⟶ (KI k n).homology n :=
  TopCat.mayerVietorisδ (Coeff k) (X := TopCat.of (S.{u} (n + 2)))
    (U := U (n + 1)) (V := V (n + 1)) isOpen_compl_singleton isOpen_compl_singleton
    (compl_singleton_union_compl_singleton_neg one_ne_zero (pole (n + 1))) (n + 1) n rfl
private abbrev equatorOrd : (KI k n).homology n ⟶ (KQ k n).homology n :=
  SSet.homologyMap (TopCat.toSSet.map (eqMap n)) (Coeff k) n

private lemma actual_ordinary_mv : ordinaryδ k n ((KSphere k n).homologyπ (n + 1) (sphereCycle k n))
  =
    (KI k n).homologyπ n (wCycle k n) := by
  have hc : SSet.homologyMap (incS n) (Coeff k) (n + 1) ≫ ordinaryδ k n =
      SSet.mayerVietorisδ (Coeff k) (cover_square n) (n + 1) n rfl := by
    exact TopCat.homologyMap_ι_comp_mayerVietorisδ (Coeff k)
      (X := TopCat.of (S.{u} (n + 2))) (U := U (n + 1)) (V := V (n + 1))
      isOpen_compl_singleton isOpen_compl_singleton
      (compl_singleton_union_compl_singleton_neg one_ne_zero (pole (n + 1))) (n + 1) n rfl
  calc
    _ = (SSet.homologyMap (incS n) (Coeff k) (n + 1) ≫ ordinaryδ k n)
        ((KS k n).homologyπ (n + 1) (zCycle k n)) :=
      (congrArg (ordinaryδ k n) (included_zClass k n)).symm.trans (ModuleCat.comp_apply _ _ _).symm
    _ = _ := (ConcreteCategory.congr_hom hc _).trans (actual_small_mv k n)

private lemma chosen_chain_equator (c : NormalizedCubicalChain (B.{u} (n + 1)) k n) :
    ((singularChains k).map (eqMap n)).f n
      (((cubicalToSingular k).app
        (TopCat.of (U.{u} (n + 1) ∩ V (n + 1) : Set (S (n + 2))))).f n
          (NormalizedCubicalChain.map k (upperOverlap (n + 1)) n c)) =
    ((singularChains k).map (lowerEqMap n)).f n
      (((singularChains k).map (TopCat.ofHom (ContinuousMap.ofClass (radialHomeomorph (n +
        1))))).f n
        (((cubicalToSingular k).app (TopCat.of (B.{u} (n + 1)))).f n c)) := by
  have h : (singularChains k).map (TopCat.ofHom (upperOverlap (n + 1))) ≫
      (singularChains k).map (eqMap n) =
    (singularChains k).map (TopCat.ofHom (ContinuousMap.ofClass (radialHomeomorph (n + 1)))) ≫
      (singularChains k).map (lowerEqMap n) := by
    rw [← Functor.map_comp, ← Functor.map_comp, equator_diagram]
  exact (congrArg (((singularChains k).map (eqMap n)).f n)
    (cubicalToSingular_app_f_map (TopCat.ofHom (upperOverlap (n + 1))) n c)).trans
      (congrArg (fun f ↦ f.f n (((cubicalToSingular k).app (TopCat.of (B.{u} (n + 1)))).f n c)) h)

private lemma wCycle_equator : HomologicalComplex.cyclesMap ((singularChains k).map (eqMap n)) n
  (wCycle k n) =
    (-1 : k) ^ (n + 1) • HomologicalComplex.cyclesMap ((singularChains k).map (lowerEqMap n)) n
      (sphereBoundaryCycle k n) := by
  apply (KQ k n).moduleCat_iCycles_injective n
  -- KQ is in the singular-chain presentation and wCycle in the SSet-chain presentation.
  erw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, wCycle_i, wNorm]
  have h := chosen_chain_equator k n (lowerBoundary k n)
  erw [map_smul, map_smul]
  rw [h]
  erw [map_smul, HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, sphereBoundaryCycle_i,
    lowerBoundary_i]

private lemma wClass_equator : equatorOrd k n ((KI k n).homologyπ n (wCycle k n)) =
    (-1 : k) ^ (n + 1) • HomologicalComplex.homologyMap ((singularChains k).map (lowerEqMap n)) n
      ((KUnitSphere k n).homologyπ n (sphereBoundaryCycle k n)) := by
  have hπ : (KI k n).homologyπ n ≫ equatorOrd k n =
      HomologicalComplex.cyclesMap ((singularChains k).map (eqMap n)) n ≫ (KQ k n).homologyπ n :=
    HomologicalComplex.homologyπ_naturality _ n
  have hl : (KQ k n).homologyπ n
      (HomologicalComplex.cyclesMap ((singularChains k).map (lowerEqMap n)) n (sphereBoundaryCycle k
        n)) =
      HomologicalComplex.homologyMap ((singularChains k).map (lowerEqMap n)) n
        ((KUnitSphere k n).homologyπ n (sphereBoundaryCycle k n)) :=
    (ModuleCat.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality
        ((singularChains k).map (lowerEqMap n)) n) (sphereBoundaryCycle k n)).symm.trans
          (ModuleCat.comp_apply _ _ _))
  exact ((ModuleCat.comp_apply _ _ _).symm.trans
    ((ConcreteCategory.congr_hom hπ (wCycle k n)).trans (ModuleCat.comp_apply _ _ _))).trans
      ((congrArg ((KQ k n).homologyπ n) (wCycle_equator k n)).trans
        (((KQ k n).homologyπ n).hom.map_smul _ _ |>.trans
          (congrArg (((-1 : k) ^ (n + 1)) • ·) hl)))

end OrdinaryMayerVietoris

section ReducedSuspension

variable (k : Type u) [Ring k] (n : ℕ)
private abbrev reducedCubeClass := cubeToSphereBoundary k n (relativeCubeClass k n)
private abbrev redLowerMap := (reducedSingularHomologyFunctor (Coeff k) n).map (lowerEqMap.{u} n)

private lemma sphereCycle_eq : sphereCycle k n = sphereBoundaryCycle k (n + 1) := by
  apply (KSphere k n).moduleCat_iCycles_injective (n + 1)
  rw [sphereCycle_i, sphereBoundaryCycle_i, fullBoundary_i]
  exact cubicalToSingular_app_f_map (TopCat.ofHom (ContinuousMap.ofClass (radialHomeomorph (n +
    2))))
    (n + 1)
    (fullBoundary k n)

private lemma upper_reduced_inclusion :
    (reducedSingularHomologyι (Coeff k) (n + 1)).app (TopCat.of (S.{u} (n + 2)))
      (reducedCubeClass k (n + 1)) = (KSphere k n).homologyπ (n + 1) (sphereCycle k n) := by
  exact (relativeCubeClass_reduced_boundary k (n + 1)).trans
    (congrArg ((KSphere k n).homologyπ (n + 1)) (sphereCycle_eq k n).symm)

private lemma suspension_comp_ι :
    (reducedSingularHomologySphereSuccIso (Coeff k) (pole.{u} (n + 1)) n).hom ≫
        (reducedSingularHomologyι (Coeff k) n).app (QSphere.{u} n) =
      (reducedSingularHomologyι (Coeff k) (n + 1)).app (TopCat.of (S.{u} (n + 2))) ≫
        ordinaryδ k n ≫ equatorOrd k n := by
  rw [reducedSingularHomologySphereSuccIso_hom]
  -- Reduced MV uses SSet homology; the reduced inclusion targets ordinary TopCat homology.
  erw [Category.assoc, Category.assoc,
    (reducedSingularHomologyι (Coeff k) n).naturality (eqMap n),
    TopCat.reducedMayerVietorisδ_comp_ι_assoc]
  rfl

private lemma lower_reduced_inclusion :
    (reducedSingularHomologyι (Coeff k) n).app (QSphere.{u} n)
      (redLowerMap k n (reducedCubeClass k n)) =
      HomologicalComplex.homologyMap ((singularChains k).map (lowerEqMap n)) n
        ((KUnitSphere k n).homologyπ n (sphereBoundaryCycle k n)) := by
  have h := ConcreteCategory.congr_hom
    ((reducedSingularHomologyι (Coeff k) n).naturality (lowerEqMap.{u} n))
      (reducedCubeClass k n)
  exact (ModuleCat.comp_apply _ _ _).symm.trans
    (h.trans ((ModuleCat.comp_apply _ _ _).trans
      (congrArg _ (relativeCubeClass_reduced_boundary k n))))

private theorem reduced_cube_recurrence :
    (reducedSingularHomologySphereSuccIso (Coeff k) (pole.{u} (n + 1)) n).hom
        (reducedCubeClass k (n + 1)) =
      (-1 : k) ^ (n + 1) • redLowerMap k n (reducedCubeClass k n) := by
  apply (ModuleCat.mono_iff_injective
    ((reducedSingularHomologyι (Coeff k) n).app (QSphere.{u} n))).1 inferInstance
  have h := ConcreteCategory.congr_hom (suspension_comp_ι k n) (reducedCubeClass k (n + 1))
  have hleft :
      (reducedSingularHomologyι (Coeff k) n).app (QSphere.{u} n)
        ((reducedSingularHomologySphereSuccIso (Coeff k) (pole.{u} (n + 1)) n).hom
          (reducedCubeClass k (n + 1))) =
      equatorOrd k n (ordinaryδ k n
        ((reducedSingularHomologyι (Coeff k) (n + 1)).app (TopCat.of (S.{u} (n + 2)))
          (reducedCubeClass k (n + 1)))) :=
    (ModuleCat.comp_apply _ _ _).symm.trans
      (h.trans ((ModuleCat.comp_apply _ _ _).trans (ModuleCat.comp_apply _ _ _)))
  have hupper := congrArg (fun x ↦ equatorOrd k n (ordinaryδ k n x))
    (upper_reduced_inclusion k n)
  have hmv := congrArg (equatorOrd k n) (actual_ordinary_mv k n)
  have hlower := congrArg (fun x : (KQ k n).homology n ↦ (-1 : k) ^ (n + 1) • x)
    (lower_reduced_inclusion k n).symm
  have hsmul := ((reducedSingularHomologyι (Coeff k) n).app (QSphere.{u} n)).hom.map_smul
    ((-1 : k) ^ (n + 1)) (redLowerMap k n (reducedCubeClass k n))
  exact hleft.trans (hupper.trans (hmv.trans ((wClass_equator k n).trans
    (hlower.trans hsmul.symm))))

end ReducedSuspension

section SelectedCoordinates

variable (k : Type u) [Ring k] (n : ℕ)

private lemma equator_basis_naturality : redLowerMap k n ≫
    (reducedSingularHomologySphereIso (Coeff k) (stdBasis (n + 2)).orthogonalLast).hom =
      (reducedSingularHomologySphereIso (Coeff k) (stdBasis (n + 1))).hom :=
  reducedSingularHomologySphereIso_hom_naturality (Coeff k) (stdBasis (n + 1))
    (stdBasis (n + 2)).orthogonalLast (equatorIsometry (n + 1)).toLinearIsometry
    (fun i ↦ by
      simp only [stdBasis, OrthonormalBasis.coe_reindex, Equiv.ulift_symm_apply,
        Function.comp_apply, EuclideanSpace.basisFun_apply]
      exact equatorIsometry_apply_basis.{u} (n + 1) i)

private lemma cubeCoordinateValue_eq : cubeCoordinateValue k n =
    (reducedSingularHomologySphereIso (Coeff k) (stdBasis (n + 1))).hom (reducedCubeClass k n) := by
  rw [cubeCoordinateValue]
  exact (ConcreteCategory.congr_hom (cube_coordinate k n).symm _).trans (ModuleCat.comp_apply _ _ _)

private theorem cubeCoordinateValue_succ : cubeCoordinateValue k (n + 1) =
    (-1 : k) ^ (n + 1) * cubeCoordinateValue k n := by
  rw [cubeCoordinateValue_eq, cubeCoordinateValue_eq,
    reducedSingularHomologySphereIso_succ, Iso.trans_hom]
  rw [ModuleCat.comp_apply]
  let β := (reducedSingularHomologySphereIso (Coeff k) (stdBasis (n + 2)).orthogonalLast).hom
  have hrec := congrArg β (reduced_cube_recurrence k n)
  have h := ConcreteCategory.congr_hom (equator_basis_naturality k n) (reducedCubeClass k n)
  exact hrec.trans ((β.hom.map_smul _ _).trans
    (congrArg (((-1 : k) ^ (n + 1)) • ·) ((ModuleCat.comp_apply _ _ _).symm.trans h)))

end SelectedCoordinates

section TriangularSign

variable (k : Type u) [Ring k]

private theorem cubeCoordinateValue_choose (n : ℕ) :
    cubeCoordinateValue k n = (-1 : k) ^ ((n + 1).choose 2) := by
  induction n with
  | zero => rw [cubeCoordinateValue_zero]; simp
  | succ n ih =>
    rw [cubeCoordinateValue_succ, ih]
    rw [Nat.choose_succ_succ' (n + 1) 1, Nat.choose_one_right]
    exact (pow_add (-1 : k) (n + 1) ((n + 1).choose 2)).symm

private theorem cubeCoordinateValue_triangular (n : ℕ) :
    cubeCoordinateValue k n = (-1 : k) ^ (n * (n + 1) / 2) := by
  rw [cubeCoordinateValue_choose, Nat.choose_two_right, Nat.add_sub_cancel,
    Nat.mul_comm (n + 1) n]

end TriangularSign

end CubeBoundary

/-- The identity `(n + 1)`-cube has coordinate `(-1)^(n(n+1)/2)` under the fixed native
relative singular homology isomorphism, over every ring. -/
theorem singularHomologyCubeBoundaryPairIso_hom_cubeBoundaryPairCycle
    (k : Type u) [Ring k] (n : ℕ) :
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (n + 1)).hom
      ((TopPair.singularCubicalHomologyIso k (cubeBoundaryPair.{u} (n + 1)) (n + 1)).inv
        (((cubeBoundaryPair.{u} (n + 1)).cubicalChainComplex k).homologyπ (n + 1)
          (cubeBoundaryPairCycle k n))) = (-1 : k) ^ (n * (n + 1) / 2) :=
  CubeBoundary.cubeCoordinateValue_triangular k n

/-- The literal identity-cube class is the triangular sign times the native selected
relative generator. The formula includes dimension one and arbitrary ring coefficients. -/
theorem singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle
    (k : Type u) [Ring k] (n : ℕ) :
    (TopPair.singularCubicalHomologyIso k (cubeBoundaryPair.{u} (n + 1)) (n + 1)).inv
      (((cubeBoundaryPair.{u} (n + 1)).cubicalChainComplex k).homologyπ (n + 1)
        (cubeBoundaryPairCycle k n)) =
      (-1 : k) ^ (n * (n + 1) / 2) •
        (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (n + 1)).inv (1 : k) := by
  apply (ModuleCat.mono_iff_injective
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (n + 1)).hom).1 inferInstance
  rw [map_smul, ModuleCat.hom_inv_apply, smul_eq_mul, mul_one]
  exact singularHomologyCubeBoundaryPairIso_hom_cubeBoundaryPairCycle k n

end TauCeti
