/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.AlgebraicTopology.Sphere.Equator
public import TauCeti.Analysis.InnerProductSpace.OrthogonalLast
public import TauCeti.Geometry.Sphere.LinearIsometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Radial cube boundaries and the last-coordinate equator

The radial identification of the boundary of the cube with the unit sphere is the boundary
map of the disk-to-cube isomorphism, followed by the disk boundary homeomorphism.
The upper inclusion appends the coordinate one. Its image avoids both last-coordinate poles,
and the equator retraction of that image agrees with the lower radial map through the
basis-preserving isometry. The radial proportionality factor is positive.

## Main declarations

* `TauCeti.CubeBoundary.radialHomeomorph`: the radial homeomorphism between the cube boundary
  and the unit sphere.
* `TauCeti.CubeBoundary.upperInclusion`: append one to a point of the lower cube boundary.
* `TauCeti.CubeBoundary.equatorIsometry`: match the lower coordinate basis to the equator basis.
* `TauCeti.CubeBoundary.equatorHomotopyEquiv_upperOverlap`: the positive equator comparison.
-/

public section

noncomputable section
open CategoryTheory Metric Set
open scoped RealInnerProductSpace
universe u
namespace TauCeti.CubeBoundary

/-- The last-coordinate pole of the unit sphere, in the fixed coordinate basis. -/
-- Transparency identifies the dependent equator with the coordinate basis's `orthogonalLast`.
@[expose] def lastPole (n : ℕ) : sphere (0 : EuclideanSpace ℝ (ULift.{u} (Fin (n + 1)))) 1 :=
  ⟨((EuclideanSpace.basisFun (ULift.{u} (Fin (n + 1))) ℝ).reindex Equiv.ulift) (Fin.last n),
    mem_sphere_zero_iff_norm.mpr (OrthonormalBasis.norm_eq_one _ _)⟩

variable {n : ℕ}
/-- The radial homeomorphism from the cube boundary to the unit sphere. -/
def radialHomeomorph (n : ℕ) :
    (cubeBoundaryPair.{u} n).snd ≃ₜ sphere (0 : EuclideanSpace ℝ (ULift.{u} (Fin n))) 1 :=
  (TopCat.homeoOfIso (TopPair.proj₂.mapIso (diskBoundaryPairIsoCube.{u} n).symm)).trans
    (diskBoundaryHomeomorph.{u} n)

/-- The radial homeomorphism applies the disk boundary identification after the inverse
boundary map of the disk-to-cube isomorphism. -/
@[simp] theorem radialHomeomorph_apply (n : ℕ) (x : (cubeBoundaryPair.{u} n).snd) :
    radialHomeomorph n x = diskBoundaryHomeomorph.{u} n
      (TopPair.Hom.snd (diskBoundaryPairIsoCube.{u} n).inv x) := by
  rw [radialHomeomorph]
  rfl

/-- The inverse radial homeomorphism uses the boundary map of the disk-to-cube isomorphism. -/
theorem radialHomeomorph_symm_apply (n : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (ULift.{u} (Fin n))) 1) :
    (radialHomeomorph n).symm x = TopPair.Hom.snd (diskBoundaryPairIsoCube.{u} n).hom
      ((diskBoundaryHomeomorph.{u} n).symm x) := by
  rw [radialHomeomorph]
  rfl

/-- The inverse radial homeomorphism in cube coordinates. -/
@[simp] theorem radialHomeomorph_symm_apply_down
    (x : sphere (0 : EuclideanSpace ℝ (ULift.{u} (Fin n))) 1) :
    ((radialHomeomorph n).symm x).val.down = diskHomeomorphCube n
      (TopCat.diskBoundaryInclusion n ((diskBoundaryHomeomorph.{u} n).symm x)) := by
  rw [radialHomeomorph_symm_apply, diskBoundaryPairIsoCube_hom]
  exact diskBoundaryPairToCube_snd_apply_down ((diskBoundaryHomeomorph.{u} n).symm x)

/-- Inverse radial coordinates have the affine form `(r * yᵢ + 1) / 2` with `r > 0`. -/
theorem exists_pos_radialHomeomorph_symm_coordinates
    (x : sphere (0 : EuclideanSpace ℝ (ULift.{u} (Fin n))) 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ i : Fin n,
      (((radialHomeomorph n).symm x).val.down i : ℝ) =
        (r * (x : (EuclideanSpace ℝ (ULift.{u} (Fin n)))) (ULift.up i) + 1) / 2 := by
  let z := TopCat.diskBoundaryInclusion n ((diskBoundaryHomeomorph.{u} n).symm x)
  let y := (EuclideanSpace.equiv (Fin n) ℝ)
    ((z : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
      EuclideanSpace ℝ (Fin n))
  let r : ℝ := gauge ((EuclideanSpace.equiv (Fin n) ℝ) '' Metric.closedBall 0 1) y /
    gauge (Metric.closedBall (0 : Fin n → ℝ) 1) y
  have hr : 0 ≤ r := div_nonneg (gauge_nonneg _) (gauge_nonneg _)
  have hF : (diskHomeomorphClosedBall n z : Fin n → ℝ) = r • y := by
    rw [coe_diskHomeomorphClosedBall_apply, ContinuousLinearEquiv.unitBallHomeomorph_apply,
      gaugeRescale_def]
  have hnorm : ‖(diskHomeomorphClosedBall n z : Fin n → ℝ)‖ = 1 :=
    (norm_diskHomeomorphClosedBall_eq_one_iff z).2 ⟨_, rfl⟩
  have hrne : r ≠ 0 := by
    intro h
    rw [h, zero_smul] at hF
    rw [hF, norm_zero] at hnorm
    exact zero_ne_one hnorm
  refine ⟨r, lt_of_le_of_ne hr (Ne.symm hrne), fun i ↦ ?_⟩
  rw [radialHomeomorph_symm_apply_down, diskHomeomorphCube_apply,
    coe_cubeHomeomorphClosedBall_symm_apply, hF, Pi.smul_apply, smul_eq_mul]
  have hy : y i = (x : (EuclideanSpace ℝ (ULift.{u} (Fin n)))) (ULift.up i) :=
    diskBoundaryHomeomorph_symm_apply_down_apply x i
  rw [hy]
/-- Cube coordinates have the affine form `(r * yᵢ + 1) / 2` for the sphere image and `r > 0`. -/
theorem exists_pos_radialHomeomorph_coordinates (x : (cubeBoundaryPair.{u} n).snd) :
    ∃ r : ℝ, 0 < r ∧ ∀ i : Fin n,
      (x.val.down i : ℝ) = (r * (radialHomeomorph n x : (EuclideanSpace ℝ (ULift.{u} (Fin n))))
        (ULift.up
        i) + 1) / 2 := by
  have h := exists_pos_radialHomeomorph_symm_coordinates (radialHomeomorph n x)
  rw [Homeomorph.symm_apply_apply] at h
  exact h

/-- The last-coordinate pole has zero lower coordinates. -/
@[simp] theorem lastPole_apply_castSucc (n : ℕ) (i : Fin n) :
    ((lastPole n : (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))) (ULift.up i.castSucc)) = 0 := by
  simp [lastPole, OrthonormalBasis.reindex_apply, EuclideanSpace.basisFun_apply,
    Fin.castSucc_ne_last]

/-- The inclusion of the lower cube boundary into the upper face, appending one. -/
def upperInclusion (n : ℕ) : C((cubeBoundaryPair.{u} n).snd, (cubeBoundaryPair.{u} (n + 1)).snd)
  where
  toFun x := ⟨ULift.up (Fin.snoc x.val.down 1), ⟨Fin.last n, Or.inr
    (@Fin.snoc_last n (fun _ : Fin (n + 1) ↦ unitInterval) 1 x.val.down)⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_uliftUp.comp
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.snoc_last] using (continuous_const : Continuous fun _ : (cubeBoundaryPair.{u}
      n).snd ↦ (1 : unitInterval))
    · have h : Continuous (fun x : (cubeBoundaryPair.{u} n).snd ↦ x.val.down j) :=
        (continuous_apply j).comp (continuous_uliftDown.comp continuous_subtypeVal)
      simpa only [Fin.snoc_castSucc] using h

/-- The upper inclusion preserves every lower coordinate. -/
@[simp] theorem upperInclusion_apply_castSucc (n : ℕ) (x : (cubeBoundaryPair.{u} n).snd) (i :
  Fin n) :
    (upperInclusion n x).val.down i.castSucc = x.val.down i := by
  rw [upperInclusion]
  exact @Fin.snoc_castSucc n (fun _ : Fin (n + 1) ↦ unitInterval) 1 x.val.down i

/-- The appended coordinate of the upper inclusion is one. -/
@[simp] theorem upperInclusion_apply_last (n : ℕ) (x : (cubeBoundaryPair.{u} n).snd) :
    (upperInclusion n x).val.down (Fin.last n) = 1 := by
  rw [upperInclusion]
  exact @Fin.snoc_last n (fun _ : Fin (n + 1) ↦ unitInterval) 1 x.val.down

/-- The upper inclusion is given by `Fin.snoc` on cube coordinates. -/
lemma upperInclusion_apply_down (n : ℕ) (x : (cubeBoundaryPair.{u} n).snd) :
    (upperInclusion n x).val.down = Fin.snoc x.val.down 1 := by
  rw [upperInclusion]
  rfl

/-- The last pole has final coordinate one. -/
@[simp] lemma lastPole_apply_last (n : ℕ) : (lastPole.{u} n : (EuclideanSpace ℝ (ULift.{u} (Fin (n +
  1)))))
  (ULift.up (Fin.last n)) = 1 := by
  simp [lastPole, OrthonormalBasis.reindex_apply, EuclideanSpace.basisFun_apply]

/-- A noncentral lower coordinate excludes both last-coordinate poles. -/
lemma radialHomeomorph_mem_overlap_of_apply_castSucc_ne_half (n : ℕ) (x : (cubeBoundaryPair.{u} (n +
  1)).snd) (i : Fin n)
    (hi : (x.val.down i.castSucc : ℝ) ≠ 1 / 2) :
    radialHomeomorph (n + 1) x ∈
      ({lastPole n}ᶜ ∩ {-lastPole n}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))
        1)) := by
  obtain ⟨_, _, hc⟩ := exists_pos_radialHomeomorph_coordinates x
  constructor
  · intro he
    apply hi
    have h := hc i.castSucc
    simpa only [Set.mem_singleton_iff.mp he, lastPole_apply_castSucc, mul_zero, zero_add] using h
  · intro he
    apply hi
    have h := hc i.castSucc
    simpa only [Set.mem_singleton_iff.mp he, coe_neg_sphere, PiLp.neg_apply,
      lastPole_apply_castSucc, neg_zero, mul_zero, zero_add] using h

/-- A zero final coordinate excludes the positive last pole. -/
lemma radialHomeomorph_mem_compl_lastPole_of_last_eq_zero (n : ℕ) (x : (cubeBoundaryPair.{u} (n +
  1)).snd)
    (hx : (x.val.down (Fin.last n) : ℝ) = 0) : radialHomeomorph (n + 1) x ∈
      ({lastPole n}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (ULift.{u} (Fin (n + 1)))) 1)) := by
  intro he
  obtain ⟨a, ha, hc⟩ := exists_pos_radialHomeomorph_coordinates x
  have h := hc (Fin.last n)
  rw [Set.mem_singleton_iff.mp he, hx, lastPole_apply_last, mul_one] at h
  linarith

/-- A final coordinate one excludes the negative last pole. -/
lemma radialHomeomorph_mem_compl_neg_lastPole_of_last_eq_one (n : ℕ) (x : (cubeBoundaryPair.{u} (n +
  1)).snd)
    (hx : (x.val.down (Fin.last n) : ℝ) = 1) : radialHomeomorph (n + 1) x ∈
      ({-lastPole n}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (ULift.{u} (Fin (n + 1)))) 1)) := by
  intro he
  obtain ⟨a, ha, hc⟩ := exists_pos_radialHomeomorph_coordinates x
  have h := hc (Fin.last n)
  simp only [Set.mem_singleton_iff.mp he, hx, coe_neg_sphere, PiLp.neg_apply, lastPole_apply_last]
    at h
  linarith

/-- The upper boundary avoids both last-coordinate poles under the radial map. -/
theorem upperInclusion_mem_overlap (n : ℕ) (x : (cubeBoundaryPair.{u} n).snd) :
    radialHomeomorph (n + 1) (upperInclusion n x) ∈
      ({lastPole n}ᶜ ∩ {-lastPole n}ᶜ : Set (sphere (0 : (EuclideanSpace ℝ (ULift.{u} (Fin (n +
        1))))) 1)) := by
  obtain ⟨i, hi⟩ := x.property
  apply radialHomeomorph_mem_overlap_of_apply_castSucc_ne_half n (upperInclusion n x) i
  rw [upperInclusion_apply_castSucc]
  rcases hi with hi | hi <;> rw [hi] <;> norm_num

/-- The linear isometry matching the lower coordinate basis to the last-coordinate equator. -/
def equatorIsometry (n : ℕ) : (EuclideanSpace ℝ (ULift.{u} (Fin n))) ≃ₗᵢ[ℝ] ((ℝ ∙
  (lastPole n :
  (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))))ᗮ) :=
  ((EuclideanSpace.basisFun (ULift.{u} (Fin n)) ℝ).reindex Equiv.ulift).equiv
    (((EuclideanSpace.basisFun (ULift.{u} (Fin (n + 1))) ℝ).reindex
    Equiv.ulift).orthogonalLast) (Equiv.refl _)

/-- The equator isometry sends each lower coordinate basis vector to the corresponding
equator basis vector. -/
@[simp] theorem equatorIsometry_apply_basis (n : ℕ) (i : Fin n) :
    equatorIsometry.{u} n (EuclideanSpace.single (ULift.up i) 1) =
      ((EuclideanSpace.basisFun (ULift.{u} (Fin (n + 1))) ℝ).reindex
        Equiv.ulift).orthogonalLast i := by
  have h : equatorIsometry.{u} n
      (((EuclideanSpace.basisFun (ULift.{u} (Fin n)) ℝ).reindex Equiv.ulift) i) =
        ((EuclideanSpace.basisFun (ULift.{u} (Fin (n + 1))) ℝ).reindex
          Equiv.ulift).orthogonalLast i := by
    rw [equatorIsometry]
    exact OrthonormalBasis.equiv_apply_basis _ _ _ i
  simpa only [OrthonormalBasis.coe_reindex, Equiv.ulift_symm_apply, Function.comp_apply,
    EuclideanSpace.basisFun_apply] using h

/-- The upper boundary, read radially in the complement of the two poles. -/
def upperOverlap (n : ℕ) :
    C((cubeBoundaryPair.{u} n).snd, ({lastPole n}ᶜ ∩ {-lastPole n}ᶜ : Set (sphere (0 :
      (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))) 1))) where
  toFun x := ⟨radialHomeomorph (n + 1) (upperInclusion n x), upperInclusion_mem_overlap n x⟩
  continuous_toFun := ((radialHomeomorph (n + 1)).continuous.comp
    (upperInclusion n).continuous).subtype_mk (upperInclusion_mem_overlap n)

/-- The equator isometry preserves coordinate readings in the ordered bases. -/
lemma orthogonalLast_repr_equatorIsometry (n : ℕ) (y : (EuclideanSpace ℝ (ULift.{u} (Fin n)))) :
    ((EuclideanSpace.basisFun (ULift.{u} (Fin (n + 1))) ℝ).reindex
      Equiv.ulift).orthogonalLast.repr (equatorIsometry n y) = ((EuclideanSpace.basisFun
      (ULift.{u} (Fin n)) ℝ).reindex Equiv.ulift).repr y := by
  simp only [equatorIsometry, OrthonormalBasis.equiv, LinearIsometryEquiv.trans_apply]
  refine (LinearIsometryEquiv.apply_symm_apply _ _).trans ?_
  ext i
  rfl

/-- The upper overlap map is the radial image of the upper inclusion. -/
@[simp] lemma coe_upperOverlap_apply (n : ℕ) (x : (cubeBoundaryPair.{u} n).snd) :
    (upperOverlap n x : (sphere (0 : (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))) 1)) =
      radialHomeomorph (n + 1) (upperInclusion n x) := by
  rw [upperOverlap]
  rfl

private lemma inner_stdBasis {n : ℕ} (x : (EuclideanSpace ℝ (ULift.{u} (Fin n)))) (i : Fin n) :
    inner ℝ (((EuclideanSpace.basisFun (ULift.{u} (Fin n)) ℝ).reindex Equiv.ulift) i) x = x
      (ULift.up i) := by
  simp [OrthonormalBasis.reindex_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left]

private lemma projection_repr (n : ℕ) (y : (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))) (i : Fin n)
  :
    ((EuclideanSpace.basisFun (ULift.{u} (Fin (n + 1))) ℝ).reindex
      Equiv.ulift).orthogonalLast.repr (((ℝ ∙ (lastPole n : (EuclideanSpace ℝ (ULift.{u} (Fin (n +
      1))))))ᗮ).orthogonalProjectionOnto y) i =
      y (ULift.up i.castSucc) := by
  exact (OrthonormalBasis.repr_apply_apply ((EuclideanSpace.basisFun (ULift.{u} (Fin (n + 1)))
    ℝ).reindex Equiv.ulift).orthogonalLast _ i).trans
    ((Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _).trans
      ((congrArg (fun z : (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1)))) ↦ inner ℝ z y)
        (OrthonormalBasis.coe_orthogonalLast_apply ((EuclideanSpace.basisFun (ULift.{u} (Fin (n +
          1))) ℝ).reindex Equiv.ulift) i)).trans
        (inner_stdBasis y i.castSucc)))

private lemma positive_projection (n : ℕ) (x : (cubeBoundaryPair.{u} n).snd) :
    ∃ r : ℝ, 0 < r ∧ ((ℝ ∙ (lastPole n : (EuclideanSpace ℝ (ULift.{u} (Fin (n +
      1))))))ᗮ).orthogonalProjectionOnto
      (radialHomeomorph (n + 1) (upperInclusion n x) : (EuclideanSpace ℝ (ULift.{u} (Fin (n +
        1))))) =
        r • equatorIsometry n (radialHomeomorph n x : (EuclideanSpace ℝ (ULift.{u} (Fin n)))) := by
  obtain ⟨a, ha, hfull⟩ := exists_pos_radialHomeomorph_coordinates (upperInclusion n x)
  obtain ⟨b, hb, hlower⟩ := exists_pos_radialHomeomorph_coordinates x
  refine ⟨b / a, div_pos hb ha, ?_⟩
  apply ((EuclideanSpace.basisFun (ULift.{u} (Fin (n + 1))) ℝ).reindex
    Equiv.ulift).orthogonalLast.repr.injective
  apply PiLp.ext
  intro i
  erw [projection_repr]
  erw [map_smul, orthogonalLast_repr_equatorIsometry, PiLp.smul_apply, smul_eq_mul,
    OrthonormalBasis.repr_apply_apply, inner_stdBasis]
  have hf := hfull i.castSucc
  rw [upperInclusion_apply_castSucc] at hf
  have hl := hlower i
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff ha.ne').2
  nlinarith

/-- Retracting the upper boundary to the equator gives the positive lower radial map. -/
theorem equatorHomotopyEquiv_upperOverlap (n : ℕ) (x : (cubeBoundaryPair.{u} n).snd) :
    equatorHomotopyEquiv (lastPole n) (upperOverlap n x) =
      (equatorIsometry n).toLinearIsometry.unitSphereMap (radialHomeomorph n x) := by
  obtain ⟨r, hr, hp⟩ := positive_projection n x
  have hz : ((upperOverlap n x : (sphere (0 : (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))) 1)) :
    (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))) =
      (radialHomeomorph (n + 1) (upperInclusion n x) : (EuclideanSpace ℝ (ULift.{u} (Fin (n +
        1))))) :=
    congrArg (fun y : (sphere (0 : (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))) 1) ↦ (y :
      (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1)))))) (coe_upperOverlap_apply n x)
  have hc : ((ℝ ∙ (lastPole n : (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))))ᗮ).starProjection
      (radialHomeomorph (n + 1) (upperInclusion n x) : (EuclideanSpace ℝ (ULift.{u} (Fin (n +
        1))))) =
        r • (equatorIsometry n (radialHomeomorph n x : (EuclideanSpace ℝ (ULift.{u} (Fin n)))) :
          (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))) :=
    (Submodule.starProjection_apply _ _).trans
      (congrArg (fun y : ((ℝ ∙ (lastPole n : (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))))ᗮ) ↦ (y :
        (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1)))))) hp)
  have hn : ‖(equatorIsometry n (radialHomeomorph n x : (EuclideanSpace ℝ (ULift.{u} (Fin n)))) :
    (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1)))))‖ = 1 :=
    ((equatorIsometry n).norm_map _).trans
      (mem_sphere_zero_iff_norm.mp (radialHomeomorph n x).property)
  have hy : (((equatorIsometry n).toLinearIsometry.unitSphereMap
      (radialHomeomorph n x) : ((ℝ ∙ (lastPole n : (EuclideanSpace ℝ (ULift.{u} (Fin (n +
        1))))))ᗮ)) :
        (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))) =
      (equatorIsometry n (radialHomeomorph n x : (EuclideanSpace ℝ (ULift.{u} (Fin n)))) :
        (EuclideanSpace
        ℝ (ULift.{u} (Fin (n + 1))))) :=
    congrArg (fun y : ((ℝ ∙ (lastPole n : (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))))ᗮ) ↦ (y :
      (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))))
      (LinearIsometry.coe_unitSphereMap_apply _ _)
  apply Subtype.ext
  apply Subtype.ext
  exact (coe_equatorHomotopyEquiv_apply (lastPole n) (upperOverlap n x)).trans
    ((congrArg NormedSpace.normalize (congrArg (fun y : (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))
      ↦ ((ℝ ∙ (lastPole n : (EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))))ᗮ).starProjection y)
      hz)).trans
      ((congrArg NormedSpace.normalize hc).trans
        ((NormedSpace.normalize_smul_of_pos hr _).trans
          ((NormedSpace.normalize_eq_self_of_norm_eq_one hn).trans hy.symm))))

end TauCeti.CubeBoundary
