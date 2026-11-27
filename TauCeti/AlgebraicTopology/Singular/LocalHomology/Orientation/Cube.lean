/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.DiskSphere
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import Mathlib.Topology.Homotopy.Affine
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Cube.Generator
public import TauCeti.AlgebraicTopology.Singular.Cubical.Kunneth.Excisive
import TauCeti.Algebra.Ring.NegOnePow

/-!
# The oriented generators of cubes and their cross products

Let `ℝⁿ⁺¹` be the Euclidean space `EuclideanSpace ℝ (ULift (Fin (n + 1)))`, with its standard
orientation `TauCeti.stdULiftOrientation n`, and let `g` be the generator of the local homology
`Hₙ₊₁(ℝⁿ⁺¹, ℝⁿ⁺¹ ∖ {0}; R)` selected by this orientation in the identity chart
(`TauCeti.singularHomologyComplSingletonIsoOfOrientation`; with coefficients `ULift ℤ` its value
at `1` is the local orientation `Orientation.localOrientation`, by
`Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl`). This file compares `g`
with the fundamental classes of the disk and of the cube, and computes the cross product of two
such generators.

* **The disk.** The inclusion of the unit disk `(Dⁿ⁺¹, Sⁿ) ⟶ (ℝⁿ⁺¹, ℝⁿ⁺¹ ∖ {0})`
  (`TauCeti.diskBoundaryPairToComplZero`) carries the generator
  `TauCeti.singularHomologyDiskBoundaryPairIso` of the disk pair to `g`, with no sign
  (`singularHomologyDiskBoundaryPairIso_inv_comp_singularHomologyMap_diskBoundaryPairToComplZero`):
  both are read off the boundary sphere through the same sphere generator.
* **The cube.** The affine map `y ↦ 2y - 1` of the cube onto `[-1, 1]ⁿ⁺¹`
  (`TauCeti.cubeBoundaryPairToComplZero`) carries the generator
  `TauCeti.singularHomologyCubeBoundaryPairIso` of the cube pair to `g`
  (`singularHomologyCubeBoundaryPairIso_inv_comp_singularHomologyMap_cubeBoundaryPairToComplZero`):
  on the boundary of the cube it differs from the disk inclusion, read through the radial
  homeomorphism of the disk with the cube, by a positive factor, so the two are joined by the
  straight-line homotopy (`TauCeti.singularHomologyMap_cubeBoundaryPairToComplZero`). Since the
  identity cube is `(-1) ^ (n (n + 1) / 2)` times the generator of the cube pair
  (`TauCeti.singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle`), the identity cube
  of `Iⁿ⁺¹` represents `(-1) ^ (n (n + 1) / 2) • g`
  (`TauCeti.singularHomologyMap_cubeBoundaryPairToComplZero_cubeBoundaryPairCycle`): it is a
  fundamental chain of the cube relative to its boundary, for the standard orientation up to that
  sign.
* **Products.** Over a commutative ring `k`, the Künneth cross product of the generators of
  `ℝᵃ⁺¹` and `ℝᵇ⁺¹`, carried to `ℝᵃ⁺¹⁺ᵇ⁺¹` by the concatenation of coordinates
  (`TauCeti.euclideanULiftAppend`), is `(-1) ^ ((a + 1) (b + 1))` times the generator of
  `ℝᵃ⁺¹⁺ᵇ⁺¹`
  (`singularHomologyMap_euclideanULiftAppend_singularHomologyKunnethPair_stdULiftGenerator`).
  The standard orientation of `ℝᵃ⁺¹⁺ᵇ⁺¹` lists the coordinates of the first factor before those of
  the second, so the homological cross product of local orientations differs from the ordered
  product of orientations by the Koszul sign of the dimensions. The proof passes through cubes,
  where the cross product of the identity cubes is the identity cube on the nose
  (`TauCeti.NormalizedCubicalChain.map_appendHomeomorph_crossProduct_ofCube_id`), and the three
  signs `(-1) ^ (n (n + 1) / 2)` of the identity cubes combine to the Koszul sign.

These comparisons are the sign conventions needed to read integral fundamental chains of products
of oriented manifolds with corners, such as compactified trajectory spaces, as cross products of
the fundamental chains of the factors.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (local orientations) and Section 3.B (the cross product).
* W. S. Massey, *Singular Homology Theory*, Graduate Texts in Mathematics 70, Springer, 1980,
  Chapters II and VI (cubical chains and their cross product).
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, Lemma 2.2 (fundamental chains of products of trajectory spaces).
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module MonoidalCategory CartesianMonoidalCategory

open scoped unitInterval Topology

universe w v u

namespace TauCeti

/-! ### The disk -/

/-- The inclusion of the disk pair `(Dⁿ, Sⁿ⁻¹)` into `(ℝⁿ, ℝⁿ ∖ {0})`, for the Euclidean space
`EuclideanSpace ℝ (ULift (Fin n))` of the universe of the disk. -/
def diskBoundaryPairToComplZero (n : ℕ) :
    diskBoundaryPair.{w} n ⟶
      TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin n))))) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun x ↦ LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
        (Equiv.ulift.{w}.symm : Fin n ≃ ULift.{w} (Fin n))
        ((x : ULift.{w} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
          EuclideanSpace ℝ (Fin n)),
      (LinearIsometryEquiv.continuous _).comp (continuous_subtypeVal.comp continuous_uliftDown)⟩)
    (TopCat.ofHom ⟨fun s ↦ ⟨(diskBoundaryHomeomorph n s : EuclideanSpace ℝ (ULift.{w} (Fin n))),
        fun h ↦ by simpa [Set.mem_singleton_iff.1 h] using (diskBoundaryHomeomorph n s).property⟩,
      (continuous_subtypeVal.comp (diskBoundaryHomeomorph n).continuous).subtype_mk _⟩)
    (by
      ext ⟨⟨p, hp⟩⟩
      exact coe_diskBoundaryHomeomorph_apply _)

/-- The coordinates of `TauCeti.diskBoundaryPairToComplZero`: those of the point of the disk. -/
lemma diskBoundaryPairToComplZero_fst_apply_ofLp (n : ℕ) (x : (diskBoundaryPair.{w} n).fst)
    (i : ULift.{w} (Fin n)) :
    (TopPair.Hom.fst (diskBoundaryPairToComplZero n) x :
        EuclideanSpace ℝ (ULift.{w} (Fin n))).ofLp i =
      ((x : ULift.{w} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
        EuclideanSpace ℝ (Fin n)) i.down :=
  (rfl)

/-- On the boundary sphere, `TauCeti.diskBoundaryPairToComplZero` is
`TauCeti.diskBoundaryHomeomorph`. -/
lemma coe_diskBoundaryPairToComplZero_snd_apply (n : ℕ) (s : TopCat.diskBoundary.{w} n) :
    (TopPair.Hom.snd (diskBoundaryPairToComplZero n) s).val = diskBoundaryHomeomorph n s :=
  (rfl)

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- The standard orientation of `EuclideanSpace ℝ (ULift (Fin (n + 1)))`, given by its standard
basis in the order of `Fin (n + 1)`. -/
abbrev stdULiftOrientation (n : ℕ) :
    Orientation ℝ (EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))) (Fin (n + 1)) :=
  ((EuclideanSpace.basisFun (ULift.{w} (Fin (n + 1))) ℝ).reindex Equiv.ulift).toBasis.orientation

/-- The identification `Hₙ₊₁(ℝⁿ⁺¹, ℝⁿ⁺¹ ∖ {0}; R) ≅ R` selected by the standard orientation of
`EuclideanSpace ℝ (ULift (Fin (n + 1)))` in the identity chart. -/
abbrev stdULiftLocalHomologyIso (n : ℕ) :
    (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (n + 1))))))
      ).singularHomology R (n + 1) ≅ R :=
  singularHomologyComplSingletonIsoOfOrientation R
    (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))))
    (OpenPartialHomeomorph.mem_refl_source 0) (stdULiftOrientation.{w} n)
    (finrank_euclideanSpace_ulift_fin (n + 1))

/-- The generator of `Hₙ₊₁(ℝⁿ⁺¹, ℝⁿ⁺¹ ∖ {0}; k)` selected by the standard orientation of
`EuclideanSpace ℝ (ULift (Fin (n + 1)))`. -/
abbrev stdULiftGenerator (k : Type w) [Ring k] (n : ℕ) :
    ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (n + 1))))))
      |>.singularHomology (ModuleCat.of k k) (n + 1) : ModuleCat.{w} k)) :=
  (stdULiftLocalHomologyIso.{w} (ModuleCat.of k k) n).inv (1 : k)

/-- **The disk generator is the standard local generator.** The inclusion of the unit disk
`(Dⁿ⁺¹, Sⁿ) ⟶ (ℝⁿ⁺¹, ℝⁿ⁺¹ ∖ {0})` carries the generator of `Hₙ₊₁(Dⁿ⁺¹, Sⁿ; R)` to the generator of
`Hₙ₊₁(ℝⁿ⁺¹, ℝⁿ⁺¹ ∖ {0}; R)` selected by the standard orientation. -/
theorem singularHomologyDiskBoundaryPairIso_inv_comp_singularHomologyMap_diskBoundaryPairToComplZero
    (n : ℕ) :
    (singularHomologyDiskBoundaryPairIso R (n + 1)).inv ≫
        TopPair.singularHomologyMap (diskBoundaryPairToComplZero.{w} (n + 1)) R (n + 1) =
      (stdULiftLocalHomologyIso.{w} R n).inv := by
  rw [← cancel_mono (stdULiftLocalHomologyIso.{w} R n).hom,
    Iso.inv_hom_id, singularHomologyComplSingletonIsoOfOrientation_refl_hom, Category.assoc,
    ← TopPair.reducedSingularHomologyδ_naturality_assoc,
    reducedSingularHomologySphereIsoOfOrientation_eq R (stdULiftOrientation.{w} n)
      (finrank_euclideanSpace_ulift_fin (n + 1))
      ((EuclideanSpace.basisFun (ULift.{w} (Fin (n + 1))) ℝ).reindex Equiv.ulift) rfl]
  have hcomp : TopPair.Hom.snd (diskBoundaryPairToComplZero.{w} (n + 1)) ≫
      TopCat.ofHom (complSingletonHomotopyEquivSphere
        (0 : EuclideanSpace ℝ (ULift.{w} (Fin (n + 1))))).toFun =
      TopCat.ofHom (diskBoundaryHomeomorph (n + 1)).toHomotopyEquiv.toFun := by
    ext x : 2
    have hx : ‖(diskBoundaryHomeomorph (n + 1) x :
        EuclideanSpace ℝ (ULift.{w} (Fin (n + 1))))‖ = 1 :=
      mem_sphere_zero_iff_norm.1 (diskBoundaryHomeomorph (n + 1) x).property
    -- The point of the punctured space is typed through the pair `(ℝⁿ⁺¹, ℝⁿ⁺¹ ∖ {0})`, which is the
    -- complement of the origin only after unfolding `TopPair.ofSubset`.
    erw [coe_complSingletonHomotopyEquivSphere_apply, coe_diskBoundaryPairToComplZero_snd_apply,
      sub_zero, hx, inv_one, one_smul]
  -- The boundary sphere is presented as `TopCat.sphere n` by the disk generator and as the
  -- subspace of the disk pair here; the two presentations agree only up to unfolding.
  erw [← Functor.map_comp_assoc, hcomp]
  have h := (singularHomologyDiskBoundaryPairIso R (n + 1)).inv_hom_id
  rw [singularHomologyDiskBoundaryPairIso_succ_hom, reducedSingularHomologyTopCatSphereIso_hom] at h
  exact h

/-! ### The cube -/

/-- The affine identification `y ↦ 2y - 1` of the cube `Iⁿ` with `[-1, 1]ⁿ`, as a continuous map
into `EuclideanSpace ℝ (ULift (Fin n))`. -/
private def cubeAffineMap (n : ℕ) :
    C(ULift.{w} (I^(Fin n)), EuclideanSpace ℝ (ULift.{w} (Fin n))) :=
  ⟨fun y ↦ (EuclideanSpace.equiv (ULift.{w} (Fin n)) ℝ).symm (fun i ↦ 2 * (y.down i.down : ℝ) - 1),
    by fun_prop⟩

private lemma cubeAffineMap_mapsTo (n : ℕ) :
    Set.MapsTo (cubeAffineMap.{w} n) (ULift.down ⁻¹' Cube.boundary (Fin n)) {0}ᶜ := by
  rintro ⟨y⟩ ⟨i, hi⟩ h
  have := congrFun (congrArg (EuclideanSpace.equiv (ULift.{w} (Fin n)) ℝ)
    (Set.mem_singleton_iff.1 h)) (ULift.up i)
  rcases hi with hi | hi <;> simp only at hi <;> norm_num [cubeAffineMap, hi] at this

/-- The affine identification `y ↦ 2y - 1` of the cube `Iⁿ` with `[-1, 1]ⁿ`, as a map of pairs
`(Iⁿ, ∂Iⁿ) ⟶ (ℝⁿ, ℝⁿ ∖ {0})` into `EuclideanSpace ℝ (ULift (Fin n))`. -/
def cubeBoundaryPairToComplZero (n : ℕ) :
    cubeBoundaryPair.{w} n ⟶
      TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin n))))) :=
  TopPair.ofSubsetMap (TopCat.ofHom (cubeAffineMap n)) (cubeAffineMap_mapsTo n)

/-- The ambient map of `TauCeti.cubeBoundaryPairToComplZero` is `cubeAffineMap`. -/
private lemma cubeBoundaryPairToComplZero_fst_apply (n : ℕ) (y : (cubeBoundaryPair.{w} n).fst) :
    (TopPair.Hom.fst (cubeBoundaryPairToComplZero n) y : EuclideanSpace ℝ (ULift.{w} (Fin n))) =
      cubeAffineMap n y :=
  TopPair.ofSubsetMap_fst_apply _ _ y

/-- The coordinates of `TauCeti.cubeBoundaryPairToComplZero`: `y ↦ 2y - 1`. -/
@[simp]
lemma cubeBoundaryPairToComplZero_fst_apply_ofLp (n : ℕ) (y : (cubeBoundaryPair.{w} n).fst)
    (i : ULift.{w} (Fin n)) :
    (TopPair.Hom.fst (cubeBoundaryPairToComplZero n) y :
        EuclideanSpace ℝ (ULift.{w} (Fin n))).ofLp i = 2 * (y.down i.down : ℝ) - 1 := by
  rw [cubeBoundaryPairToComplZero_fst_apply]
  simp [cubeAffineMap]

/-- The disk pair carried into the cube and then onto `[-1, 1]ⁿ` is a nonnegative multiple of the
inclusion of the disk: the radial rescaling of the Euclidean ball onto the sup-norm ball. The values
are read in `EuclideanSpace ℝ (ULift (Fin n))` through `id`, since the ambient space of the pair is
that space only after unfolding `TopPair.ofSubset`. -/
private lemma fst_diskBoundaryPairToCube_comp_cubeBoundaryPairToComplZero_apply (n : ℕ)
    (x : TopCat.disk.{w} n) :
    ∃ s : ℝ, 0 ≤ s ∧
      @id (EuclideanSpace ℝ (ULift.{w} (Fin n)))
          (TopPair.Hom.fst (diskBoundaryPairToCube.{w} n ≫ cubeBoundaryPairToComplZero n) x) =
        s • @id (EuclideanSpace ℝ (ULift.{w} (Fin n)))
          (TopPair.Hom.fst (diskBoundaryPairToComplZero n) x) := by
  set v : EuclideanSpace ℝ (Fin n) :=
    ((x : ULift.{w} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down : EuclideanSpace ℝ (Fin n))
  refine ⟨gauge ((EuclideanSpace.equiv (Fin n) ℝ) '' closedBall 0 1)
      ((EuclideanSpace.equiv (Fin n) ℝ) v) /
    gauge (closedBall 0 1) ((EuclideanSpace.equiv (Fin n) ℝ) v),
    div_nonneg (gauge_nonneg _) (gauge_nonneg _), ?_⟩
  ext i
  simp only [id, TopPair.Hom.fst_comp]
  -- The composite is typed on the ambient space of the cube pair, the lifted cube only after
  -- unfolding `TopPair.ofSubset`.
  erw [ConcreteCategory.comp_apply, cubeBoundaryPairToComplZero_fst_apply_ofLp]
  have hc := diskBoundaryPairToCube_fst_apply_down.{w} x
  rw [hc]
  -- The scalar multiple is taken in the ambient space of the pair `(ℝⁿ, ℝⁿ ∖ {0})`, which is the
  -- Euclidean space only after unfolding `TopPair.ofSubset`.
  erw [PiLp.smul_apply, diskBoundaryPairToComplZero_fst_apply_ofLp]
  simp only [diskHomeomorphCube_apply, coe_cubeHomeomorphClosedBall_symm_apply,
    coe_diskHomeomorphClosedBall_apply, ContinuousLinearEquiv.unitBallHomeomorph_apply,
    gaugeRescale_def, zero_le_one, gauge_closedBall, div_one, Pi.smul_apply,
    PiLp.continuousLinearEquiv_apply, smul_eq_mul, v]
  ring

/-- The affine map of the cube onto `[-1, 1]ⁿ` and the inclusion of the disk, read on the cube
through the homeomorphism of the disk with the cube, induce the same map on relative homology:
they are joined by the straight-line homotopy, which avoids the origin on the boundary of the cube
since the two maps differ there by a positive factor. -/
theorem singularHomologyMap_cubeBoundaryPairToComplZero (n m : ℕ) :
    TopPair.singularHomologyMap (cubeBoundaryPairToComplZero.{w} n) R m =
      TopPair.singularHomologyMap
        ((diskBoundaryPairIsoCube.{w} n).inv ≫ diskBoundaryPairToComplZero n) R m := by
  set φ := (diskBoundaryPairIsoCube.{w} n).inv ≫ diskBoundaryPairToComplZero n
  let f₂ : C(ULift.{w} (I^(Fin n)), EuclideanSpace ℝ (ULift.{w} (Fin n))) :=
    (TopPair.Hom.fst φ).hom
  have hf₂ : Set.MapsTo (TopCat.ofHom f₂) (ULift.down ⁻¹' Cube.boundary (Fin n)) {0}ᶜ :=
    fun y hy ↦ TopPair.mapsTo_range_map_of_hom φ (by rwa [TopPair.range_ofSubset_map])
  have hφ : φ = TopPair.ofSubsetMap (TopCat.ofHom f₂) hf₂ :=
    TopPair.hom_ext_of_fst _ (TopPair.ofSubsetMap_fst _ _).symm
  rw [hφ, cubeBoundaryPairToComplZero]
  refine (TopPair.ofSubsetHomotopy (ContinuousMap.Homotopy.affine (cubeAffineMap.{w} n) f₂)
    ?_).congr_singularHomologyMap R m
  intro τ y hy h0
  -- The point of the disk corresponding to `y`.
  set x := TopPair.Hom.fst (diskBoundaryPairIsoCube.{w} n).inv y
  have hx : TopPair.Hom.fst (diskBoundaryPairToCube.{w} n) x = y := by
    rw [← diskBoundaryPairIsoCube_hom]
    exact ConcreteCategory.congr_hom
      (congrArg TopPair.Hom.fst (diskBoundaryPairIsoCube.{w} n).inv_hom_id) y
  obtain ⟨s, hs, hsx⟩ := fst_diskBoundaryPairToCube_comp_cubeBoundaryPairToComplZero_apply n x
  have h₂ := hf₂ hy
  set a : EuclideanSpace ℝ (ULift.{w} (Fin n)) :=
    TopPair.Hom.fst (diskBoundaryPairToComplZero n) x
  -- `f₂` is the ambient map of the composite `φ`, which sends `y` to `a` through `x`.
  have hf₂y : f₂ y = a := rfl
  have hcy : cubeAffineMap n y = s • a := by
    have h3 : cubeAffineMap n y = @id (EuclideanSpace ℝ (ULift.{w} (Fin n)))
        (TopPair.Hom.fst (diskBoundaryPairToCube.{w} n ≫ cubeBoundaryPairToComplZero n) x) := by
      rw [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply]
      exact ((cubeBoundaryPairToComplZero_fst_apply n _).trans (congrArg (cubeAffineMap n) hx)).symm
    rw [h3, hsx, id_eq]
  have ha : a ≠ 0 := h₂
  have hc0 : cubeAffineMap n y ≠ 0 := cubeAffineMap_mapsTo n hy
  have h0' : AffineMap.lineMap (cubeAffineMap n y) (f₂ y) (τ : ℝ) =
      (0 : EuclideanSpace ℝ (ULift.{w} (Fin n))) := h0
  simp only [AffineMap.lineMap_apply_module, hcy, hf₂y, smul_smul, ← add_smul, smul_eq_zero, ha,
    or_false] at h0'
  have hτ := unitInterval.nonneg τ
  have hτ' := unitInterval.le_one τ
  have hτ0 : (τ : ℝ) = 0 := by nlinarith [mul_nonneg (sub_nonneg.2 hτ') hs]
  rw [hτ0, sub_zero, one_mul, add_zero] at h0'
  exact hc0 (by rw [hcy, h0', zero_smul])

/-- **The cube generator is the standard local generator.** The affine map `y ↦ 2y - 1` of the
cube carries the generator of `Hₙ₊₁(Iⁿ⁺¹, ∂Iⁿ⁺¹; R)` to the generator of
`Hₙ₊₁(ℝⁿ⁺¹, ℝⁿ⁺¹ ∖ {0}; R)` selected by the standard orientation. -/
theorem singularHomologyCubeBoundaryPairIso_inv_comp_singularHomologyMap_cubeBoundaryPairToComplZero
    (n : ℕ) :
    (singularHomologyCubeBoundaryPairIso R (n + 1)).inv ≫
        TopPair.singularHomologyMap (cubeBoundaryPairToComplZero.{w} (n + 1)) R (n + 1) =
      (stdULiftLocalHomologyIso.{w} R n).inv := by
  have h : TopPair.singularHomologyMap (diskBoundaryPairIsoCube.{w} (n + 1)).hom R (n + 1) ≫
      TopPair.singularHomologyMap
        ((diskBoundaryPairIsoCube.{w} (n + 1)).inv ≫ diskBoundaryPairToComplZero (n + 1)) R
          (n + 1) =
      TopPair.singularHomologyMap (diskBoundaryPairToComplZero (n + 1)) R (n + 1) := by
    rw [← TopPair.singularHomologyMap_comp, Iso.hom_inv_id_assoc]
  rw [singularHomologyMap_cubeBoundaryPairToComplZero, singularHomologyCubeBoundaryPairIso_inv,
    Category.assoc, ← diskBoundaryPairIsoCube_hom, h]
  exact singularHomologyDiskBoundaryPairIso_inv_comp_singularHomologyMap_diskBoundaryPairToComplZero
    R n


/-- **The identity cube as an oriented fundamental chain.** The affine map `y ↦ 2y - 1` carries
the class of the identity cube of `(Iⁿ⁺¹, ∂Iⁿ⁺¹)`, read in singular homology with coefficients in
a ring `k`, to `(-1) ^ (n (n + 1) / 2)` times the generator of `Hₙ₊₁(ℝⁿ⁺¹, ℝⁿ⁺¹ ∖ {0}; k)` selected
by the standard orientation. -/
theorem singularHomologyMap_cubeBoundaryPairToComplZero_cubeBoundaryPairCycle (k : Type w) [Ring k]
    (n : ℕ) :
    TopPair.singularHomologyMap (cubeBoundaryPairToComplZero.{w} (n + 1)) (ModuleCat.of k k) (n + 1)
        ((TopPair.singularCubicalHomologyIso k (cubeBoundaryPair.{w} (n + 1)) (n + 1)).inv
          (((cubeBoundaryPair.{w} (n + 1)).cubicalChainComplex k).homologyπ (n + 1)
            (cubeBoundaryPairCycle k n))) =
      (-1 : k) ^ (n * (n + 1) / 2) • stdULiftGenerator k n := by
  rw [singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle, map_smul, stdULiftGenerator,
    ← singularHomologyCubeBoundaryPairIso_inv_comp_singularHomologyMap_cubeBoundaryPairToComplZero,
    ConcreteCategory.comp_apply]


/-! ### Products -/

section Product

variable (k : Type w) [CommRing k]

/-- The concatenation of coordinates as a linear homeomorphism: Mathlib's
`EuclideanSpace.sumEquivProd`, reindexed along
`ULift (Fin p) ⊕ ULift (Fin q) ≃ ULift (Fin (p + q))`. -/
private def euclideanULiftAppendEquiv (p q : ℕ) :
    (EuclideanSpace ℝ (ULift.{w} (Fin p)) × EuclideanSpace ℝ (ULift.{w} (Fin q))) ≃L[ℝ]
      EuclideanSpace ℝ (ULift.{w} (Fin (p + q))) :=
  EuclideanSpace.sumEquivProd.symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      ((Equiv.sumCongr Equiv.ulift.{w} Equiv.ulift.{w}).trans
        (finSumFinEquiv.trans Equiv.ulift.{w}.symm))).toContinuousLinearEquiv

/-- The concatenation of coordinates `ℝᵖ × ℝ^q → ℝᵖ⁺q` of the Euclidean spaces
`EuclideanSpace ℝ (ULift (Fin p))`, the coordinates of the first factor first. -/
def euclideanULiftAppend (p q : ℕ) :
    C(EuclideanSpace ℝ (ULift.{w} (Fin p)) × EuclideanSpace ℝ (ULift.{w} (Fin q)),
      EuclideanSpace ℝ (ULift.{w} (Fin (p + q)))) :=
  ⟨euclideanULiftAppendEquiv p q, (euclideanULiftAppendEquiv p q).continuous⟩

/-- The coordinates of `TauCeti.euclideanULiftAppend`: those of the first factor, then those of the
second. -/
@[simp]
lemma euclideanULiftAppend_apply_ofLp (p q : ℕ)
    (x : EuclideanSpace ℝ (ULift.{w} (Fin p)) × EuclideanSpace ℝ (ULift.{w} (Fin q)))
    (i : ULift.{w} (Fin (p + q))) :
    (euclideanULiftAppend p q x).ofLp i =
      Fin.append (fun j ↦ x.1 (ULift.up j)) (fun j ↦ x.2 (ULift.up j)) i.down := by
  obtain ⟨i⟩ := i
  induction i using Fin.addCases <;> simp [euclideanULiftAppend, euclideanULiftAppendEquiv]

/-- The concatenation of coordinates vanishes only at the origin, so it is a map of pairs
`(ℝᵖ × ℝ^q, (ℝᵖ ∖ {0}) × ℝ^q ∪ ℝᵖ × (ℝ^q ∖ {0})) ⟶ (ℝᵖ⁺q, ℝᵖ⁺q ∖ {0})`. -/
lemma euclideanULiftAppend_mapsTo (p q : ℕ) :
    Set.MapsTo (TopCat.ofHom (X := ↑(TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin p))) ⊗
        TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin q)))))
        (euclideanULiftAppend.{w} p q))
      (fst (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin p))))
          (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin q)))) ⁻¹' {0}ᶜ ∪
        snd (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin p))))
          (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin q)))) ⁻¹' {0}ᶜ)
      ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (p + q)))))) := by
  rintro ⟨x, y⟩ h h0
  have h0' : ((x, y) : EuclideanSpace ℝ (ULift.{w} (Fin p)) ×
      EuclideanSpace ℝ (ULift.{w} (Fin q))) = 0 :=
    (map_eq_zero_iff _ (euclideanULiftAppendEquiv.{w} p q).injective).1 h0
  rcases h with h | h
  · exact h (congrArg Prod.fst h0')
  · exact h (congrArg Prod.snd h0')

/-- The concatenation of coordinates as a map out of the product of the pairs
`(ℝᵖ, ℝᵖ ∖ {0})` and `(ℝ^q, ℝ^q ∖ {0})`, into `(ℝᵖ⁺q, ℝᵖ⁺q ∖ {0})`. -/
private abbrev euclideanULiftAppendPairHom (p q : ℕ) :=
  TopPair.ofSubsetMap
    (TopCat.ofHom (X := ↑((TopPair.ofSubset
        ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin p)))))).fst ⊗
      (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin q)))))).fst))
      (euclideanULiftAppend.{w} p q))
    ((euclideanULiftAppend_mapsTo p q).mono_left
      (Set.union_subset_union (Set.preimage_mono TopPair.range_ofSubset_map.subset)
        (Set.preimage_mono TopPair.range_ofSubset_map.subset)))

/-- The class of the affine cube `y ↦ 2y - 1` in `(ℝⁿ⁺¹, ℝⁿ⁺¹ ∖ {0})`, read in singular homology,
is `(-1) ^ (n (n + 1) / 2)` times the generator selected by the standard orientation. -/
private lemma singularCubicalHomologyIso_inv_cubeClass (m : ℕ) :
    (TopPair.singularCubicalHomologyIso k
        (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (m + 1)))))))
        (m + 1)).inv
      (HomologicalComplex.homologyMap
        (TopPair.cubicalChainComplexMap k (cubeBoundaryPairToComplZero.{w} (m + 1))) (m + 1)
        (((cubeBoundaryPair.{w} (m + 1)).cubicalChainComplex k).homologyπ (m + 1)
          (cubeBoundaryPairCycle k m))) =
      (-1 : k) ^ (m * (m + 1) / 2) • stdULiftGenerator k m := by
  rw [← ModuleCat.comp_apply, TopPair.singularCubicalHomologyIso_inv_naturality,
    ModuleCat.comp_apply]
  exact singularHomologyMap_cubeBoundaryPairToComplZero_cubeBoundaryPairCycle k m

/-- On cubes, the cross product of the affine cubes of `ℝᵖ` and `ℝ^q`, followed by the concatenation
of coordinates, is the affine cube of `ℝᵖ⁺q`. -/
private lemma euclideanULiftAppend_comp_crossProduct (p q : ℕ) :
    (euclideanULiftAppend.{w} p q).comp (SingularCube.crossProduct
        ((cubeAffineMap.{w} p).comp ⟨ULift.up, continuous_uliftUp⟩)
        ((cubeAffineMap.{w} q).comp ⟨ULift.up, continuous_uliftUp⟩)) =
      (cubeAffineMap.{w} (p + q)).comp ⟨ULift.up, continuous_uliftUp⟩ := by
  ext x : 1
  refine PiLp.ext fun i ↦ ?_
  obtain ⟨i⟩ := i
  induction i using Fin.addCases with
  | left j => simp [cubeAffineMap]
  | right j => simp [cubeAffineMap]

/-- **The cross product of the affine cubes.** In relative cubical homology, the cross product of
the classes of the affine cubes of `ℝᵃ⁺¹` and `ℝᵇ⁺¹`, carried to `ℝᵃ⁺¹⁺ᵇ⁺¹` by the concatenation
of coordinates, is the class of the affine cube of `ℝᵃ⁺¹⁺ᵇ⁺¹`: on chains the cross product of two
cubes is the cube of the concatenated coordinates. -/
private lemma homologyMap_cubicalChainComplexMap_cubeClass_cross (a b : ℕ) :
    HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
        (euclideanULiftAppendPairHom.{w} (a + 1) (b + 1))) (a + 1 + (b + 1))
      (HomologicalComplex.homologyMap
        ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (a + 1)))))))
          |>.cubicalChainComplexProdComparison k
          (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (b + 1))))))))
        (a + 1 + (b + 1))
        ((GradedObject.Monoidal.ιTensorObj _ _ (a + 1) (b + 1) (a + 1 + (b + 1)) rfl ≫
          cubicalHomologyKunnethPair k _ _ (a + 1 + (b + 1))).hom
          (HomologicalComplex.homologyMap
              (TopPair.cubicalChainComplexMap k (cubeBoundaryPairToComplZero.{w} (a + 1))) (a + 1)
              (((cubeBoundaryPair.{w} (a + 1)).cubicalChainComplex k).homologyπ (a + 1)
                (cubeBoundaryPairCycle k a)) ⊗ₜ
            HomologicalComplex.homologyMap
              (TopPair.cubicalChainComplexMap k (cubeBoundaryPairToComplZero.{w} (b + 1))) (b + 1)
              (((cubeBoundaryPair.{w} (b + 1)).cubicalChainComplex k).homologyπ (b + 1)
                (cubeBoundaryPairCycle k b))))) =
      HomologicalComplex.homologyMap
        (TopPair.cubicalChainComplexMap k (cubeBoundaryPairToComplZero.{w} (a + 1 + (b + 1))))
        (a + 1 + (b + 1))
        (((cubeBoundaryPair.{w} (a + 1 + (b + 1))).cubicalChainComplex k).homologyπ
          (a + 1 + (b + 1)) (cubeBoundaryPairCycle k (a + 1 + b))) := by
  have hA := (isCubicalRepresentative_ofCube_upCube k a).map
    (cubeBoundaryPairToComplZero.{w} (a + 1))
  have hB := (isCubicalRepresentative_ofCube_upCube k b).map
    (cubeBoundaryPairToComplZero.{w} (b + 1))
  have hL := (TopPair.IsCubicalRepresentative.crossProduct rfl hA hB).map
    (euclideanULiftAppendPairHom.{w} (a + 1) (b + 1))
  have hC := (isCubicalRepresentative_ofCube_upCube k (a + 1 + b)).map
    (cubeBoundaryPairToComplZero.{w} (a + 1 + (b + 1)))
  refine hL.unique ?_
  convert hC using 1
  -- The cubes live on the ambient spaces `P.fst` of the pairs, which are the spaces the chain maps
  -- act on (`TopCat.of`, or a tensor product of them) only after unfolding `TopPair.ofSubset`.
  erw [NormalizedCubicalChain.map_ofCube, NormalizedCubicalChain.map_ofCube,
    NormalizedCubicalChain.crossProduct_ofCube, NormalizedCubicalChain.cast_ofCube,
    NormalizedCubicalChain.map_ofCube, NormalizedCubicalChain.map_ofCube]
  refine congrArg (NormalizedCubicalChain.ofCube _ k) ?_
  simp only [cubeBoundaryPairToComplZero]
  -- The append map is typed out of `(ofSubset A).fst ⊗ (ofSubset B).fst`, which is the tensor
  -- product of the `TopCat.of` spaces only after unfolding `TopPair.ofSubset`.
  erw [TopPair.ofSubsetMap_fst, TopPair.ofSubsetMap_fst, TopPair.ofSubsetMap_fst,
    TopPair.ofSubsetMap_fst]
  -- As above: the cast cube lives on `(ofSubset A).fst ⊗ (ofSubset B).fst`, and rewriting it is
  -- type-correct for the append map only after unfolding `TopPair.ofSubset`.
  erw [SingularCube.cast_rfl]
  exact euclideanULiftAppend_comp_crossProduct (a + 1) (b + 1)

/-- **The cross product of standard local generators.** Over a commutative ring `k`, the Künneth
cross product of the generators of `Hₐ₊₁(ℝᵃ⁺¹, ℝᵃ⁺¹ ∖ {0}; k)` and `H_{b+1}(ℝᵇ⁺¹, ℝᵇ⁺¹ ∖ {0}; k)`
selected by the standard orientations, carried to `ℝᵃ⁺¹⁺ᵇ⁺¹` by the concatenation of coordinates,
is `(-1) ^ ((a + 1) (b + 1))` times the generator selected by the standard orientation of
`ℝᵃ⁺¹⁺ᵇ⁺¹`, whose basis lists the coordinates of the first factor first. -/
theorem singularHomologyMap_euclideanULiftAppend_singularHomologyKunnethPair_stdULiftGenerator
    (a b : ℕ) :
    TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (a + 1)))) ⊗
            TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (b + 1)))))
          (TopCat.ofHom (X := ↑(TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (a + 1)))) ⊗
            TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (b + 1))))))
            (euclideanULiftAppend.{w} (a + 1) (b + 1)))
          (euclideanULiftAppend_mapsTo (a + 1) (b + 1)))
        (ModuleCat.of k k) (a + 1 + (b + 1))
      ((GradedObject.Monoidal.ιTensorObj _ _ (a + 1) (b + 1) (a + 1 + (b + 1)) rfl ≫
          singularHomologyKunnethPair k
            ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (a + 1))))))
            ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (b + 1))))))
            (a + 1 + (b + 1))).hom
        (stdULiftGenerator k a ⊗ₜ stdULiftGenerator k b)) =
      (-1 : k) ^ ((a + 1) * (b + 1)) • stdULiftGenerator k (a + 1 + b) := by
  -- Each standard generator is a signed affine cube class.
  have hg (m : ℕ) : stdULiftGenerator k m = (-1 : k) ^ (m * (m + 1) / 2) •
      (TopPair.singularCubicalHomologyIso k
        (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (m + 1)))))))
        (m + 1)).inv
      (HomologicalComplex.homologyMap
        (TopPair.cubicalChainComplexMap k (cubeBoundaryPairToComplZero.{w} (m + 1))) (m + 1)
        (((cubeBoundaryPair.{w} (m + 1)).cubicalChainComplex k).homologyπ (m + 1)
          (cubeBoundaryPairCycle k m))) := by
    rw [singularCubicalHomologyIso_inv_cubeClass, smul_smul, ← mul_pow, neg_one_mul, neg_neg,
      one_pow, one_smul]
  -- The Künneth map reads the cubical Künneth class through the comparison with singular chains.
  have hK := congrArg (fun φ ↦ HomologicalComplex.homologyMap φ (a + 1 + (b + 1)))
    (cubicalChainComplexProdComparison_comp_cubicalToSingularRel k
      (A := ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (a + 1)))))))
      (B := ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (b + 1)))))))
      (euclideanULiftAppend.{w} (a + 1) (b + 1)) (euclideanULiftAppend_mapsTo (a + 1) (b + 1)))
  simp only [HomologicalComplex.homologyMap_comp] at hK
  have hB := homologyMap_cubicalChainComplexMap_cubeClass_cross k a b
  rw [ι_cubicalHomologyKunnethPair] at hB
  rw [hg a, hg b, hg (a + 1 + b), TensorProduct.smul_tmul_smul, map_smul, map_smul,
    ι_singularHomologyKunnethPair]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_tensorHom]
  rw [TensorProduct.map_tmul, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  have hK' := ConcreteCategory.congr_hom hK
    ((HomologicalComplex.homologyMap
      (cubicalCrossProductPair k (TopPair.ofSubset
        ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (a + 1)))))))
        (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (b + 1))))))))
        (a + 1 + (b + 1))).hom
      ((HomologicalComplex.homologyCross
          ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (a + 1)))))))
            |>.cubicalChainComplex k)
          ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (b + 1)))))))
            |>.cubicalChainComplex k) (a + 1) (b + 1) (a + 1 + (b + 1)) rfl).hom
        (HomologicalComplex.homologyMap
            (TopPair.cubicalChainComplexMap k (cubeBoundaryPairToComplZero.{w} (a + 1))) (a + 1)
            (((cubeBoundaryPair.{w} (a + 1)).cubicalChainComplex k).homologyπ (a + 1)
              (cubeBoundaryPairCycle k a)) ⊗ₜ
          HomologicalComplex.homologyMap
            (TopPair.cubicalChainComplexMap k (cubeBoundaryPairToComplZero.{w} (b + 1))) (b + 1)
            (((cubeBoundaryPair.{w} (b + 1)).cubicalChainComplex k).homologyπ (b + 1)
              (cubeBoundaryPairCycle k b)))))
  simp only [ConcreteCategory.comp_apply] at hK'
  -- `hK'` and `hB` type the append map on presentations of its source equal up to defeq.
  erw [← hK', hB, ← TopPair.singularCubicalHomologyIso_inv]
  rw [neg_one_pow_mul_succ_div_two_mul_neg_one_pow_mul_succ_div_two, smul_smul]
  -- The sides differ only in the degrees `a + 1 + (b + 1)` and `a + 1 + b + 1`, equal by `rfl`.
  rfl

end Product

end TauCeti
