/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Triangulation.CoordinateClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Sphere

import TauCeti.AlgebraicTopology.Disk.CubeBoundary
import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
import TauCeti.Analysis.InnerProductSpace.Euclidean.Space
import TauCeti.Topology.Homotopy.Contractible
import TauCeti.Topology.Homotopy.PuncturedStarConvex

/-!
# The coordinate sphere class

For `m ≥ 0` and every ring `k`, this file constructs the normalized reference class
`[Sᵐ⁺¹] ∈ Hₘ₊₁(Sᵐ⁺¹; k)` of the sphere `Sᵐ⁺¹ = TopCat.sphere (m + 1) ⊆ ℝᵐ⁺²`, from the coordinate
cube class `[Iᵐ⁺¹, ∂Iᵐ⁺¹]` (`TauCeti.coordinateCubeClass`) and a positive chart at the first pole
`e₀ = TauCeti.sphereBasePoint m`.

* The **positive chart** `TauCeti.sphereChart` sends a vector `v` of the open unit ball of `ℝᵐ⁺¹`
  to `(√(1 - ‖v‖²), v)`. It is an open embedding onto the open hemisphere `x₀ > 0`
  (`TauCeti.isOpenEmbedding_sphereChart`, `TauCeti.range_sphereChart`) and sends `0` to `e₀`. The
  outward normal at `e₀` is `e₀`, and the chart coordinates follow it in the standard order, so the
  chart is positive for the outward-first orientation of the sphere.
* The **chart cube** `TauCeti.sphereChartCube` is the cube `Iᵐ⁺¹`, scaled into the ball by
  `t ↦ (tᵢ - 1 / 2) / (m + 1)` and carried to the sphere by the chart. As a map of pairs
  `(Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ (Sᵐ⁺¹, Sᵐ⁺¹ ∖ {e₀})` it induces isomorphisms on relative homology in every
  degree (`TauCeti.isIso_singularHomologyMap_sphereChartCubePairHom`): by excision along the open
  embeddings of the ball into the sphere and into `ℝᵐ⁺¹`, this reduces to `(ℝᵐ⁺¹, ℝᵐ⁺¹ ∖ {0})`,
  where radial projection carries the boundary of the scaled cube onto the unit sphere by the
  radial homeomorphism `TauCeti.CubeBoundary.radialHomeomorph`.
* The **local chart class** `TauCeti.sphereLocalChartClass k m` is the image of the coordinate cube
  class under the chart cube, in the local homology `Hₘ₊₁(Sᵐ⁺¹, Sᵐ⁺¹ ∖ {e₀}; k)`; it generates
  (`TauCeti.bijective_smul_sphereLocalChartClass`).
* The **coordinate sphere class** `TauCeti.coordinateSphereClass k m` is the unique class of
  `Hₘ₊₁(Sᵐ⁺¹; k)` whose image in the local homology at `e₀` is the local chart class
  (`TauCeti.singularHomologyToLocalHomology_coordinateSphereClass`,
  `TauCeti.eq_coordinateSphereClass_iff`). It exists and is unique because the map from
  `Hₘ₊₁(Sᵐ⁺¹; k)` to the local homology at a point is bijective
  (`TauCeti.bijective_singularHomologyToLocalHomology_topCatSphere`). It generates
  `Hₘ₊₁(Sᵐ⁺¹; k)` (`TauCeti.bijective_smul_coordinateSphereClass`) and is a fundamental class
  of the sphere (`TauCeti.isFundamentalClass_coordinateSphereClass`).

The coordinate sphere class is therefore a unit multiple of the standard generator
`TauCeti.singularHomologyTopCatSphereGenerator`, which is built by iterated suspension; this file
does not compute that unit. The zero-sphere, whose reference class lives in reduced homology, is
not treated here.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, local orientations and Lemma 3.27 on the top homology of a closed manifold, and
  Section 2.1, Theorem 2.20 (excision).
-/

public section

noncomputable section

open CategoryTheory Metric Set Topology
open scoped unitInterval

universe u

namespace TauCeti

section Chart

variable {m : ℕ}

/-- The point `(√(1 - ‖v‖²), v)` of `ℝᵐ⁺²`. -/
private def chartVec (v : EuclideanSpace ℝ (ULift.{u} (Fin (m + 1)))) :
    EuclideanSpace ℝ (Fin (m + 2)) :=
  WithLp.toLp 2 (Fin.cons (√(1 - ‖v‖ ^ 2)) fun i ↦ v (ULift.up i))

private lemma norm_chartVec {v : EuclideanSpace ℝ (ULift.{u} (Fin (m + 1)))} (hv : ‖v‖ ≤ 1) :
    ‖chartVec v‖ = 1 := by
  -- Relabelling the coordinates of `v` along `ULift` keeps the sum of their squares.
  have hsum : ∑ i : Fin (m + 1), v (ULift.up i) ^ 2 = ‖v‖ ^ 2 :=
    EuclideanSpace.sum_sq_apply_equiv Equiv.ulift.symm v
  have h : ‖chartVec v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
    simp only [chartVec, PiLp.toLp_apply, Fin.cons_zero, Fin.cons_succ]
    rw [hsum, Real.sq_sqrt (by nlinarith [norm_nonneg v]), sub_add_cancel]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

variable (m) in
/-- **The positive chart of the sphere at the first pole.** A vector `v` of the open unit ball of
`ℝᵐ⁺¹` goes to the point `(√(1 - ‖v‖²), v)` of `Sᵐ⁺¹ ⊆ ℝᵐ⁺²`. It is an open embedding onto the
open hemisphere `x₀ > 0` (`TauCeti.isOpenEmbedding_sphereChart`) and sends `0` to the first pole
`e₀ = TauCeti.sphereBasePoint m`. -/
def sphereChart : C(ball (0 : EuclideanSpace ℝ (ULift.{u} (Fin (m + 1)))) 1,
    TopCat.sphere.{u} (m + 1)) where
  toFun v := ULift.up ⟨chartVec v.val,
    mem_sphere_zero_iff_norm.2 (norm_chartVec (mem_ball_zero_iff.1 v.property).le)⟩
  continuous_toFun := by
    refine continuous_uliftUp.comp (Continuous.subtype_mk ?_ _)
    unfold chartVec
    fun_prop

/-- The first coordinate of `sphereChart m v` is `√(1 - ‖v‖²)`. -/
@[simp]
lemma sphereChart_apply_zero (v : ball (0 : EuclideanSpace ℝ (ULift.{u} (Fin (m + 1)))) 1) :
    ((sphereChart m v).down : EuclideanSpace ℝ (Fin (m + 2))) 0 = √(1 - ‖v.val‖ ^ 2) :=
  (rfl)

/-- The coordinate `i + 1` of `sphereChart m v` is the coordinate `i` of `v`. -/
@[simp]
lemma sphereChart_apply_succ (v : ball (0 : EuclideanSpace ℝ (ULift.{u} (Fin (m + 1)))) 1)
    (i : Fin (m + 1)) :
    ((sphereChart m v).down : EuclideanSpace ℝ (Fin (m + 2))) i.succ =
      (v : EuclideanSpace ℝ (ULift.{u} (Fin (m + 1)))) (ULift.up i) :=
  (rfl)

/-- The last `m + 1` coordinates of a point of `Sᵐ⁺¹`, the inverse of the chart. -/
private def chartProj (x : TopCat.sphere.{u} (m + 1)) :
    EuclideanSpace ℝ (ULift.{u} (Fin (m + 1))) :=
  WithLp.toLp 2 fun i ↦ (x.down : EuclideanSpace ℝ (Fin (m + 2))) i.down.succ

private lemma continuous_chartProj : Continuous (chartProj (m := m)) := by
  unfold chartProj
  fun_prop

private lemma chartProj_sphereChart
    (v : ball (0 : EuclideanSpace ℝ (ULift.{u} (Fin (m + 1)))) 1) :
    chartProj (sphereChart m v) = v := by
  ext i
  rfl

/-- Every point of `Sᵐ⁺¹` with positive first coordinate is in the image of the chart. -/
private lemma mem_range_sphereChart {x : TopCat.sphere.{u} (m + 1)}
    (hx : 0 < (x.down : EuclideanSpace ℝ (Fin (m + 2))) 0) : x ∈ range (sphereChart m) := by
  set y : EuclideanSpace ℝ (Fin (m + 2)) := ↑x.down
  have hy : ‖y‖ = 1 := mem_sphere_zero_iff_norm.1 x.down.property
  -- `‖y‖² = y₀² + ‖tail y‖²`, so the tail has norm `√(1 - y₀²) < 1`.
  have hsq : ‖chartProj x‖ ^ 2 = 1 - y 0 ^ 2 := by
    have h := EuclideanSpace.real_norm_sq_eq y
    rw [hy, Fin.sum_univ_succ] at h
    rw [← EuclideanSpace.sum_sq_apply_equiv Equiv.ulift.symm]
    simp only [chartProj, Equiv.ulift_symm_apply]
    linarith
  have hlt : ‖chartProj x‖ < 1 := by
    have : ‖chartProj x‖ ^ 2 < 1 ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 zero_le_one this
  refine ⟨⟨chartProj x, mem_ball_zero_iff.2 hlt⟩, ULift.ext (Subtype.ext ?_)⟩
  ext i
  refine Fin.cases ?_ (fun j ↦ rfl) i
  rw [sphereChart_apply_zero, hsq, sub_sub_cancel, Real.sqrt_sq hx.le]

variable (m) in
/-- **The positive chart is onto the open hemisphere** `x₀ > 0`. -/
theorem range_sphereChart :
    range (sphereChart m) = {x | 0 < (x.down : EuclideanSpace ℝ (Fin (m + 2))) 0} := by
  refine Set.ext fun x ↦ ⟨?_, mem_range_sphereChart⟩
  rintro ⟨v, rfl⟩
  rw [mem_ofPred_eq, sphereChart_apply_zero, Real.sqrt_pos]
  nlinarith [mem_ball_zero_iff.1 v.property, norm_nonneg v.val]

variable (m) in
/-- **The positive chart is an open embedding.** Its inverse on the open hemisphere `x₀ > 0` keeps
the last `m + 1` coordinates. -/
theorem isOpenEmbedding_sphereChart : IsOpenEmbedding (sphereChart.{u} m) where
  toIsInducing := IsInducing.of_comp (sphereChart m).continuous continuous_chartProj <| by
    rw [show chartProj ∘ sphereChart m = Subtype.val from funext chartProj_sphereChart]
    exact IsInducing.subtypeVal
  injective v w h := Subtype.ext <| by
    rw [← chartProj_sphereChart v, ← chartProj_sphereChart w, h]
  isOpen_range := by
    rw [range_sphereChart]
    exact isOpen_lt continuous_const (by fun_prop)

variable (m) in
/-- The positive chart sends the centre of the ball to the first pole `e₀`. -/
theorem sphereChart_zero : sphereChart.{u} m ⟨0, mem_ball_self one_pos⟩ = sphereBasePoint m := by
  refine ULift.ext (Subtype.ext ?_)
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [coe_sphereBasePoint_down]
  · simp [coe_sphereBasePoint_down, Fin.succ_ne_zero]

variable (m) in
/-- Only the centre of the ball is sent to the first pole. -/
theorem sphereChart_preimage_sphereBasePoint :
    sphereChart.{u} m ⁻¹' {sphereBasePoint m} = {⟨0, mem_ball_self one_pos⟩} := by
  rw [← sphereChart_zero, ← image_singleton,
    (isOpenEmbedding_sphereChart m).injective.preimage_image]

/-! ### The chart cube -/

/-- The positively scaled coordinate cube `t ↦ (tᵢ - 1 / 2) / (m + 1)` in `ℝᵐ⁺¹`. -/
private def cubeVec (t : I^(Fin (m + 1))) : EuclideanSpace ℝ (ULift.{u} (Fin (m + 1))) :=
  WithLp.toLp 2 fun i ↦ ((t i.down : ℝ) - 1 / 2) / (m + 1)

private lemma continuous_cubeVec : Continuous (cubeVec.{u} (m := m)) := by
  unfold cubeVec
  fun_prop

private lemma norm_cubeVec_lt (t : I^(Fin (m + 1))) : ‖cubeVec.{u} t‖ < 1 := by
  have hsq : ‖cubeVec.{u} t‖ ^ 2 ≤ 1 / 4 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i, (cubeVec.{u} t i) ^ 2
        ≤ ∑ _i : ULift.{u} (Fin (m + 1)), (1 / 4) / ((m : ℝ) + 1) ^ 2 := by
          gcongr with i
          have h0 := (t i.down).property.1
          have h1 := (t i.down).property.2
          rw [cubeVec, PiLp.toLp_apply, div_pow]
          gcongr
          nlinarith
      _ = 1 / (4 * (m + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_ulift, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          field_simp
      _ ≤ 1 / 4 := by gcongr; linarith
  nlinarith [norm_nonneg (cubeVec.{u} t)]

private lemma cubeVec_ne_zero {t : I^(Fin (m + 1))} (ht : t ∈ Cube.boundary (Fin (m + 1))) :
    cubeVec.{u} t ≠ 0 := by
  obtain ⟨i, hi⟩ := ht
  intro h
  have h' : (((t i : ℝ) - 1 / 2) / (m + 1)) = 0 := congrArg (fun v ↦ v (ULift.up i)) h
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  rcases hi with hi | hi <;> norm_num [hi, hm] at h'

/-- On the boundary of the cube, the scaled cube is a positive multiple of the radial
identification of the boundary with the unit sphere. -/
private lemma exists_pos_cubeVec_eq_smul (x : (cubeBoundaryPair.{u} (m + 1)).snd) :
    ∃ c : ℝ, 0 < c ∧ cubeVec.{u} x.val.down = c •
      (CubeBoundary.radialHomeomorph (m + 1) x : EuclideanSpace ℝ (ULift.{u} (Fin (m + 1)))) := by
  obtain ⟨r, hr, hx⟩ := CubeBoundary.exists_pos_radialHomeomorph_coordinates x
  refine ⟨r / (2 * (m + 1)), by positivity, ?_⟩
  ext i
  rw [cubeVec, PiLp.toLp_apply, hx i.down]
  simp only [PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The scaled cube as a map of pairs `(Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ (ℝᵐ⁺¹, ℝᵐ⁺¹ ∖ {0})`. -/
private def cubeToEuclidean :
    cubeBoundaryPair.{u} (m + 1) ⟶
      TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (ULift.{u} (Fin (m + 1)))))) :=
  cubeBoundaryPairHom ⟨cubeVec, continuous_cubeVec⟩ fun _ ht ↦ by
    rw [TopPair.range_ofSubset_map]
    exact cubeVec_ne_zero ht

section Coefficients

variable {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Abelian C] (R : C)

/-- The scaled cube induces isomorphisms `Hₖ(Iᵐ⁺¹, ∂Iᵐ⁺¹) ≅ Hₖ(ℝᵐ⁺¹, ℝᵐ⁺¹ ∖ {0})`: both ambient
spaces are contractible, and radial projection carries the boundary of the scaled cube onto the
unit sphere by the radial homeomorphism. -/
private lemma isIso_singularHomologyMap_cubeToEuclidean (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (cubeToEuclidean.{u} (m := m)) R k) := by
  set E := EuclideanSpace ℝ (ULift.{u} (Fin (m + 1)))
  -- The ambient map is a map between contractible spaces, hence a homotopy equivalence.
  let e₁ : ContinuousMap.HomotopyEquiv (cubeBoundaryPair.{u} (m + 1)).fst E :=
    { toFun := (⟨cubeVec, continuous_cubeVec⟩ : C(I^(Fin (m + 1)), E)).comp
        ⟨ULift.down, continuous_uliftDown⟩
      invFun := ContinuousMap.const _ (ULift.up fun _ ↦ 0)
      left_inv := ContinuousMap.homotopic_of_contractibleSpace _ _
      right_inv := ContinuousMap.homotopic_of_contractibleSpace _ _ }
  have he₁ : TopPair.Hom.fst (cubeToEuclidean.{u} (m := m)) = TopCat.ofHom e₁.toFun :=
    TopCat.ext fun x ↦ cubeBoundaryPairHom_fst_apply _ _ x
  have hfst (n : ℕ) : IsIso (SSet.homologyMap
      (TopCat.toSSet.map (TopPair.Hom.fst (cubeToEuclidean.{u} (m := m)))) R n) :=
    he₁ ▸ e₁.isIso_homologyMap R n
  -- On the boundary, radial projection of the scaled cube is the radial homeomorphism.
  let ρ := complSingletonHomotopyEquivSphere (0 : E)
  let g : (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).snd ⟶ TopCat.of (sphere (0 : E) 1) :=
    TopCat.ofHom ρ.toFun
  have hρ : TopPair.Hom.snd (cubeToEuclidean.{u} (m := m)) ≫ g =
      TopCat.ofHom (CubeBoundary.radialHomeomorph.{u} (m + 1) :
        C((cubeBoundaryPair.{u} (m + 1)).snd, sphere (0 : E) 1)) := by
    refine TopCat.ext fun x ↦ Subtype.ext ?_
    obtain ⟨c, hc, hx⟩ := exists_pos_cubeVec_eq_smul x
    -- The boundary point goes to `cubeVec x`, a positive multiple of a unit vector.
    have hval : (TopPair.Hom.snd (cubeToEuclidean.{u} (m := m)) x).val = cubeVec x.val.down :=
      -- After `he₁`, both sides are `cubeVec x.val.down` by definition of `e₁`.
      (TopPair.Hom.w_apply (cubeToEuclidean.{u} (m := m)) x).trans (by rw [he₁]; rfl)
    have h := coe_complSingletonHomotopyEquivSphere_apply (0 : E)
      (TopPair.Hom.snd (cubeToEuclidean.{u} (m := m)) x)
    rw [sub_zero, hval, hx] at h
    -- `g` is `TopCat.ofHom ρ.toFun`, which evaluates to `ρ` by definition.
    change (ρ.toFun (TopPair.Hom.snd (cubeToEuclidean.{u} (m := m)) x) : E) = _
    simpa [norm_smul, abs_of_pos hc, smul_smul, hc.ne'] using h
  have hsnd (n : ℕ) : IsIso (SSet.homologyMap
      (TopCat.toSSet.map (TopPair.Hom.snd (cubeToEuclidean.{u} (m := m)))) R n) := by
    have hg : IsIso (SSet.homologyMap (TopCat.toSSet.map g) R n) := ρ.isIso_homologyMap R n
    have h₂ : IsIso (SSet.homologyMap (TopCat.toSSet.map
        (TopPair.Hom.snd (cubeToEuclidean.{u} (m := m)))) R n ≫
          SSet.homologyMap (TopCat.toSSet.map g) R n) := by
      rw [← SSet.homologyMap_comp, ← Functor.map_comp, hρ]
      exact (CubeBoundary.radialHomeomorph.{u} (m + 1)).toHomotopyEquiv.isIso_homologyMap R n
    exact IsIso.of_isIso_comp_right _ (SSet.homologyMap (TopCat.toSSet.map g) R n)
  exact TopPair.isIso_singularHomologyMap_of_isIso R _ k (hfst k) (hsnd k) (fun n _ ↦ hfst n)
    fun n _ ↦ hsnd n

end Coefficients

/-- The scaled cube in the open unit ball. -/
private def cubeToBallMap :
    C(I^(Fin (m + 1)), ball (0 : EuclideanSpace ℝ (ULift.{u} (Fin (m + 1)))) 1) :=
  ⟨fun t ↦ ⟨cubeVec t, mem_ball_zero_iff.2 (norm_cubeVec_lt t)⟩,
    continuous_cubeVec.subtype_mk _⟩

/-- The scaled cube as a map of pairs `(Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ (B, B ∖ {0})` into the open unit ball. -/
private def cubeToBall :
    cubeBoundaryPair.{u} (m + 1) ⟶ TopPair.ofSubset ({⟨0, mem_ball_self one_pos⟩}ᶜ :
      Set (TopCat.of (ball (0 : EuclideanSpace ℝ (ULift.{u} (Fin (m + 1)))) 1))) :=
  cubeBoundaryPairHom cubeToBallMap fun _ ht ↦ by
    rw [TopPair.range_ofSubset_map]
    exact fun h ↦ cubeVec_ne_zero ht (congrArg Subtype.val h)

private lemma cubeToBall_fst_apply (x : (cubeBoundaryPair.{u} (m + 1)).fst) :
    TopPair.Hom.fst (cubeToBall.{u} (m := m)) x = cubeToBallMap x.down :=
  cubeBoundaryPairHom_fst_apply _ _ x

variable (m) in
/-- **The positively scaled chart cube** of `Sᵐ⁺¹` at the first pole: the cube `Iᵐ⁺¹` carried
into the open unit ball of `ℝᵐ⁺¹` by `t ↦ (tᵢ - 1 / 2) / (m + 1)`, a positive multiple of the
coordinate map `t ↦ 2t - 1` onto the sup-norm ball, and then into the sphere by the positive chart
`TauCeti.sphereChart` (`TauCeti.sphereChartCube_apply_zero`, `TauCeti.sphereChartCube_apply_succ`).
-/
def sphereChartCube : C(I^(Fin (m + 1)), TopCat.sphere.{u} (m + 1)) :=
  (sphereChart m).comp cubeToBallMap

/-- The first coordinate of the chart cube at `t` is `√(1 - ∑ᵢ ((tᵢ - 1 / 2) / (m + 1))²)`, the
positive square root determined by the other coordinates (`sphereChartCube_apply_succ`). -/
@[simp]
lemma sphereChartCube_apply_zero (t : I^(Fin (m + 1))) :
    ((sphereChartCube.{u} m t).down : EuclideanSpace ℝ (Fin (m + 2))) 0 =
      √(1 - ∑ i : Fin (m + 1), (((t i : ℝ) - 1 / 2) / (m + 1)) ^ 2) := by
  -- By definition the first coordinate is `√(1 - ‖cubeVec t‖²)`.
  change √(1 - ‖cubeVec.{u} t‖ ^ 2) = _
  rw [← EuclideanSpace.sum_sq_apply_equiv Equiv.ulift.symm]
  rfl

/-- The coordinate `i + 1` of the chart cube at `t` is `(tᵢ - 1 / 2) / (m + 1)`. -/
@[simp]
lemma sphereChartCube_apply_succ (t : I^(Fin (m + 1))) (i : Fin (m + 1)) :
    ((sphereChartCube.{u} m t).down : EuclideanSpace ℝ (Fin (m + 2))) i.succ =
      ((t i : ℝ) - 1 / 2) / (m + 1) :=
  (rfl)

/-- The chart cube sends the boundary of the cube off the first pole. -/
theorem sphereChartCube_ne_sphereBasePoint {t : I^(Fin (m + 1))}
    (ht : t ∈ Cube.boundary (Fin (m + 1))) : sphereChartCube m t ≠ sphereBasePoint.{u} m := by
  rw [← sphereChart_zero]
  exact fun h ↦ cubeVec_ne_zero ht
    (congrArg Subtype.val ((isOpenEmbedding_sphereChart m).injective h))

variable (m) in
/-- The chart cube as a map of pairs `(Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ (Sᵐ⁺¹, Sᵐ⁺¹ ∖ {e₀})`. -/
def sphereChartCubePairHom :
    cubeBoundaryPair.{u} (m + 1) ⟶
      TopPair.ofSubset ({sphereBasePoint m}ᶜ : Set (TopCat.sphere.{u} (m + 1))) :=
  cubeBoundaryPairHom (sphereChartCube m) fun _ ht ↦ by
    rw [TopPair.range_ofSubset_map]
    exact sphereChartCube_ne_sphereBasePoint ht

/-- The ambient map of the chart cube pair map is the chart cube. -/
@[simp]
lemma sphereChartCubePairHom_fst_apply (x : (cubeBoundaryPair.{u} (m + 1)).fst) :
    TopPair.Hom.fst (sphereChartCubePairHom.{u} m) x = sphereChartCube m x.down :=
  cubeBoundaryPairHom_fst_apply _ _ x

section Coefficients

variable {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Abelian C] (R : C)

/-- A cube pair map `c` into `(X, X ∖ {x})` that is the scaled cube in the ball followed by a map
`f` of the ball factors in homology through the local homology map of `f`. -/
private lemma singularHomologyMap_cubeBoundaryPairHom_eq_comp {X : Type u} [TopologicalSpace X]
    (f : C(ball (0 : EuclideanSpace ℝ (ULift.{u} (Fin (m + 1)))) 1, X)) {x : X}
    (hf : f ⁻¹' {x} ⊆ {⟨0, mem_ball_self one_pos⟩}) (c : C(I^(Fin (m + 1)), X))
    (hc : MapsTo c (Cube.boundary (Fin (m + 1)))
      (range (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of X))).map))
    (hfc : ∀ t, f (cubeToBallMap t) = c t) (k : ℕ) :
    TopPair.singularHomologyMap (cubeBoundaryPairHom c hc) R k =
      TopPair.singularHomologyMap (cubeToBall.{u} (m := m)) R k ≫ localHomologyMap R f hf k := by
  rw [localHomologyMap_def, ← TopPair.singularHomologyMap_comp]
  refine congrArg (TopPair.singularHomologyMap · R k) (TopPair.hom_ext_of_fst _
    (TopCat.ext fun t ↦ ?_))
  rw [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply, TopPair.ofSubsetMap_fst_apply,
    cubeToBall_fst_apply]
  exact (cubeBoundaryPairHom_fst_apply (P := TopPair.ofSubset ({x}ᶜ : Set (TopCat.of X))) c hc
    t).trans (hfc t.down).symm

variable (m) in
/-- **The chart cube computes the local homology of the sphere at the first pole**: it induces
isomorphisms `Hₖ(Iᵐ⁺¹, ∂Iᵐ⁺¹) ≅ Hₖ(Sᵐ⁺¹, Sᵐ⁺¹ ∖ {e₀})` in every degree, for every coefficient
object. -/
theorem isIso_singularHomologyMap_sphereChartCubePairHom (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (sphereChartCubePairHom.{u} m) R k) := by
  -- The chart and the inclusion of the open ball into `ℝᵐ⁺¹` are open embeddings, so by excision
  -- both identify local homology at the centre of the ball with that of the sphere at `e₀` and
  -- with that of `ℝᵐ⁺¹` at `0`; the scaled cube computes the latter.
  set B := ball (0 : EuclideanSpace ℝ (ULift.{u} (Fin (m + 1)))) 1
  let b₀ : B := ⟨0, mem_ball_self one_pos⟩
  let ι : C(B, EuclideanSpace ℝ (ULift.{u} (Fin (m + 1)))) :=
    ⟨Subtype.val, continuous_subtypeVal⟩
  have hι : ι ⁻¹' {0} = {b₀} := Set.ext fun v ↦ by
    simp only [mem_preimage, mem_singleton_iff]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  have hφ : sphereChart.{u} m ⁻¹' {sphereBasePoint m} = {b₀} :=
    sphereChart_preimage_sphereBasePoint m
  -- Both open embeddings induce isomorphisms of local homology.
  have hιiso := isIso_localHomologyMap R ι isOpen_ball.isOpenEmbedding_subtypeVal hι
    isClosed_singleton (singleton_subset_iff.2 ⟨b₀, rfl⟩) k
  have hφiso := isIso_localHomologyMap R (sphereChart.{u} m) (isOpenEmbedding_sphereChart m) hφ
    isClosed_singleton (singleton_subset_iff.2 ⟨b₀, sphereChart_zero m⟩) k
  -- The cube maps factor through the cube in the ball: the scaled cube in the ball is `cubeVec`
  -- with its norm bound, and the chart cube is by definition the chart after it, so both
  -- factorizations hold pointwise by `rfl`.
  have hE : TopPair.singularHomologyMap (cubeToEuclidean.{u} (m := m)) R k =
      TopPair.singularHomologyMap (cubeToBall.{u} (m := m)) R k ≫
        localHomologyMap R ι hι.subset k :=
    singularHomologyMap_cubeBoundaryPairHom_eq_comp R ι hι.subset _ _ (fun _ ↦ rfl) k
  have hS : TopPair.singularHomologyMap (sphereChartCubePairHom.{u} m) R k =
      TopPair.singularHomologyMap (cubeToBall.{u} (m := m)) R k ≫
        localHomologyMap R (sphereChart.{u} m) hφ.subset k :=
    singularHomologyMap_cubeBoundaryPairHom_eq_comp R (sphereChart.{u} m) hφ.subset _ _
      (fun _ ↦ rfl) k
  have hB : IsIso (TopPair.singularHomologyMap (cubeToBall.{u} (m := m)) R k) := by
    have := isIso_singularHomologyMap_cubeToEuclidean.{u} (m := m) R k
    rw [hE] at this
    exact IsIso.of_isIso_comp_right _ (localHomologyMap R ι hι.subset k)
  rw [hS]
  infer_instance

end Coefficients

end Chart

/-! ### The local chart class and the sphere class -/

section Class

variable (k : Type u) [Ring k] (m : ℕ)

/-- **The local chart class** of `Sᵐ⁺¹` at the first pole `e₀`: the image of the coordinate cube
class `[Iᵐ⁺¹, ∂Iᵐ⁺¹]` (`TauCeti.coordinateCubeClass`) under the positively scaled chart cube
`TauCeti.sphereChartCube`, in the local homology `Hₘ₊₁(Sᵐ⁺¹, Sᵐ⁺¹ ∖ {e₀}; k)`. -/
def sphereLocalChartClass :
    (localHomology (ModuleCat.of k k) ({sphereBasePoint.{u} m} : Set (TopCat.sphere.{u} (m + 1)))
      (m + 1) : ModuleCat.{u} k) :=
  TopPair.singularHomologyMap (sphereChartCubePairHom m) (ModuleCat.of k k) (m + 1)
    (coordinateCubeClass k m)

/-- The defining formula of `TauCeti.sphereLocalChartClass`. -/
lemma sphereLocalChartClass_def :
    sphereLocalChartClass k m = TopPair.singularHomologyMap (sphereChartCubePairHom m)
      (ModuleCat.of k k) (m + 1) (coordinateCubeClass k m) :=
  (rfl)

/-- **The local chart class generates** the local homology of `Sᵐ⁺¹` at the first pole:
`a ↦ a • [e₀]_chart` is a bijection from `k` onto `Hₘ₊₁(Sᵐ⁺¹, Sᵐ⁺¹ ∖ {e₀}; k)`. -/
theorem bijective_smul_sphereLocalChartClass :
    Function.Bijective fun a : k ↦ a • sphereLocalChartClass k m := by
  have := isIso_singularHomologyMap_sphereChartCubePairHom (m := m) (R := ModuleCat.of k k)
    (k := m + 1)
  convert (ConcreteCategory.bijective_of_isIso
    (TopPair.singularHomologyMap (sphereChartCubePairHom m) (ModuleCat.of k k) (m + 1))).comp
      (bijective_smul_coordinateCubeClass k m) using 1
  funext a
  exact (map_smul _ a _).symm

/-- The map `Hₘ₊₁(Sᵐ⁺¹; k) → Hₘ₊₁(Sᵐ⁺¹, Sᵐ⁺¹ ∖ {e₀}; k)` to the local homology at the first pole,
as a linear equivalence. -/
private def toLocalEquiv :=
  LinearEquiv.ofBijective _ (bijective_singularHomologyToLocalHomology_topCatSphere
    (ModuleCat.of k k) m (sphereBasePoint.{u} m))

/-- **The coordinate sphere class** `[Sᵐ⁺¹] ∈ Hₘ₊₁(Sᵐ⁺¹; k)`: the unique class whose image in
the local homology at the first pole `e₀` is the local chart class
(`TauCeti.singularHomologyToLocalHomology_coordinateSphereClass`,
`TauCeti.eq_coordinateSphereClass_iff`). -/
def coordinateSphereClass :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) (m + 1)).obj
      (ModuleCat.of k k)).obj (TopCat.sphere.{u} (m + 1)) :=
  (toLocalEquiv k m).symm (sphereLocalChartClass k m)

/-- **The local image of the coordinate sphere class** at the first pole is the local chart
class. -/
theorem singularHomologyToLocalHomology_coordinateSphereClass :
    singularHomologyToLocalHomology (ModuleCat.of k k) (sphereBasePoint.{u} m) (m + 1)
      (coordinateSphereClass k m) = sphereLocalChartClass k m :=
  (toLocalEquiv k m).apply_symm_apply _

/-- **Uniqueness of the coordinate sphere class**: a class of `Hₘ₊₁(Sᵐ⁺¹; k)` is the coordinate
sphere class exactly when its image in the local homology at the first pole is the local chart
class. -/
theorem eq_coordinateSphereClass_iff
    (z : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) (m + 1)).obj
      (ModuleCat.of k k)).obj (TopCat.sphere.{u} (m + 1))) :
    z = coordinateSphereClass k m ↔
      singularHomologyToLocalHomology (ModuleCat.of k k) (sphereBasePoint.{u} m) (m + 1) z =
        sphereLocalChartClass k m := by
  rw [← singularHomologyToLocalHomology_coordinateSphereClass]
  exact (bijective_singularHomologyToLocalHomology_topCatSphere (ModuleCat.of k k) m
    (sphereBasePoint m)).1.eq_iff.symm

/-- **The coordinate sphere class generates**: `a ↦ a • [Sᵐ⁺¹]` is a bijection from `k` onto
`Hₘ₊₁(Sᵐ⁺¹; k)`. -/
theorem bijective_smul_coordinateSphereClass :
    Function.Bijective fun a : k ↦ a • coordinateSphereClass k m := by
  set e := toLocalEquiv k m
  have hf : (fun a : k ↦ a • coordinateSphereClass k m) =
      e.symm ∘ fun a : k ↦ a • sphereLocalChartClass k m :=
    funext fun a ↦ (map_smul e.symm a _).symm
  rw [hf]
  exact e.symm.bijective.comp (bijective_smul_sphereLocalChartClass k m)

/-- **The coordinate sphere class is a fundamental class** of `Sᵐ⁺¹`: its image in the local
homology at every point generates. -/
theorem isFundamentalClass_coordinateSphereClass :
    IsFundamentalClass (M := TopCat.sphere.{u} (m + 1)) (N := ModuleCat.of k k) (n := m + 1)
      (coordinateSphereClass k m) := by
  obtain ⟨s, hs⟩ := (bijective_smul_coordinateSphereClass k m).2
    (singularHomologyTopCatSphereGenerator k m)
  have h := isFundamentalClass_singularHomologyTopCatSphereGenerator k m
  rw [← hs] at h
  exact h.of_smul

end Class


end TauCeti
