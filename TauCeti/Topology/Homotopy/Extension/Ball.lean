/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Basic
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Homotopy.Affine

/-!
# The unit sphere is a closed cofibration in the closed unit ball

The unit sphere of a real seminormed space has the homotopy extension property inside the closed
unit ball.  Concretely, the cylinder `I × D` over the closed unit ball `D` retracts onto
`{0} × D ∪ I × S`, where `S` is the unit sphere, by radial projection away from the point of the
cylinder axis at height `2`: the ray from that point through `(t, x)` leaves the cylinder either
through its bottom face or through its side, and the retraction sends `(t, x)` to that exit
point.

This is the basic example of a closed cofibration.  It is the geometric input for the homotopy
extension property of the inclusion of a skeleton of a CW complex into the next one, whose cells
are attached along maps defined on such spheres.

As a consequence, a map out of the unit sphere is null-homotopic exactly when it extends over the
closed unit ball: a null-homotopy is extended from the sphere to the ball, starting at a constant
map, and conversely the closed ball is contractible.  This is the criterion for extending a map
over a cell attached along a sphere.

The retraction also compresses maps of pairs.  If a map `g` of the closed unit ball sending the
sphere into `B` is homotopic, through such maps, to a map into `B`, then `g` is homotopic relative
to the sphere to a map into `B`.  This is how vanishing relative homotopy groups give the
hypothesis of the compression lemma for CW complexes.

## Main declarations

* `TauCeti.ballRadialDen`, `TauCeti.ballRadialProjection`: the shared radial denominator and
  projection in ambient coordinates, also used for the bottom-and-sides deformation of cubes.
* `TauCeti.ballRadialProjection_spec`, `TauCeti.ballRadialProjection_eq_self`,
  `TauCeti.ballRadialProjection_fst_le`: the projection lands on the bottom and sides, fixes that
  subspace and does not raise heights.
* `TauCeti.hasHomotopyExtensionProperty_sphere_closedBall`: **the unit sphere has the homotopy
  extension property inside the closed unit ball.**
* `ContinuousMap.nullhomotopic_iff_exists_extension_closedBall`,
  `ContinuousMap.homotopicRel_const_singleton_sphere_iff_exists_extension_closedBall`,
  `ContinuousMap.homotopicRel_const_singleton_sphere_iff_nullhomotopic`: free and pointed
  null-homotopy of a map out of the unit sphere agree with extension over the closed unit ball.
* `ContinuousMap.HomotopicWith.exists_homotopicRel_range_subset`: a map of pairs homotopic through
  maps of pairs to a map into `B` is homotopic relative to the sphere to a map into `B`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, proof of Proposition 0.16, which retracts `Dⁿ × I` onto `Dⁿ × {0} ∪ ∂Dⁿ × I` by
  radial projection from the point `(0, 2)`; Section 4.1, the compression criterion preceding
  Theorem 4.3, for compressing maps of pairs.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set unitInterval

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The denominator for radial projection from height two onto the bottom and sides of the
unit-ball cylinder. It is shared with the radial deformation of finite cubes. -/
def ballRadialDen (p : I × closedBall (0 : E) 1) : ℝ :=
  max (2 - (p.1 : ℝ)) (2 * ‖(p.2 : E)‖)

omit [NormedSpace ℝ E] in
theorem ballRadialDen_def (p : I × closedBall (0 : E) 1) :
    ballRadialDen p = max (2 - (p.1 : ℝ)) (2 * ‖(p.2 : E)‖) := (rfl)

omit [NormedSpace ℝ E] in
private lemma ballRadialProjection_den_pos (p : I × closedBall (0 : E) 1) :
    0 < max (2 - (p.1 : ℝ)) (2 * ‖(p.2 : E)‖) :=
  lt_of_lt_of_le (by have := p.1.2.2; linarith) (le_max_left _ _)

/-- Radial projection of the cylinder over the closed unit ball away from the point at height `2`
on its axis, written in the ambient coordinates `ℝ × E`. The scale factor is the smaller of the
factors needed to reach the bottom face and the side of the cylinder. Taking the maximum in the
denominator gives a single continuous formula, including at the cylinder axis. -/
def ballRadialProjection (p : I × closedBall (0 : E) 1) : ℝ × E :=
  (2 - 2 * (2 - (p.1 : ℝ)) / ballRadialDen p, (2 / ballRadialDen p) • (p.2 : E))

theorem ballRadialProjection_def (p : I × closedBall (0 : E) 1) :
    ballRadialProjection p =
      (2 - 2 * (2 - (p.1 : ℝ)) / ballRadialDen p,
        (2 / ballRadialDen p) • (p.2 : E)) := (rfl)

theorem continuous_ballRadialProjection : Continuous (ballRadialProjection (E := E)) := by
  have hd : Continuous fun p : I × closedBall (0 : E) 1 =>
      max (2 - (p.1 : ℝ)) (2 * ‖(p.2 : E)‖) := by fun_prop
  have hne p := (ballRadialProjection_den_pos (E := E) p).ne'
  exact (continuous_const.sub ((by fun_prop : Continuous fun p : I × closedBall (0 : E) 1 =>
    2 * (2 - (p.1 : ℝ))).div hd hne)).prodMk
      ((continuous_const.div hd hne).smul (by fun_prop))

/-- The radial projection lands in the cylinder, and in the union of its bottom face with the
part of the cylinder lying over the sphere. -/
theorem ballRadialProjection_spec (p : I × closedBall (0 : E) 1) :
    (ballRadialProjection p).1 ∈ I ∧ (ballRadialProjection p).2 ∈ closedBall (0 : E) 1 ∧
      ((ballRadialProjection p).1 = 0 ∨ (ballRadialProjection p).2 ∈ sphere (0 : E) 1) := by
  have ht0 := p.1.2.1
  have ht1 := p.1.2.2
  have hn1 := mem_closedBall_zero_iff.1 p.2.2
  have hd := ballRadialProjection_den_pos p
  have hd1 := le_max_left (2 - (p.1 : ℝ)) (2 * ‖(p.2 : E)‖)
  have hd2 := le_max_right (2 - (p.1 : ℝ)) (2 * ‖(p.2 : E)‖)
  have hdle : max (2 - (p.1 : ℝ)) (2 * ‖(p.2 : E)‖) ≤ 2 :=
    max_le (by linarith) (by linarith)
  have hnorm : ‖(ballRadialProjection p).2‖ =
      2 * ‖(p.2 : E)‖ / max (2 - (p.1 : ℝ)) (2 * ‖(p.2 : E)‖) := by
    simp [ballRadialProjection, ballRadialDen, norm_smul, Real.norm_eq_abs, abs_of_pos hd,
      div_mul_eq_mul_div]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [ballRadialProjection, ballRadialDen]
    constructor
    · rw [sub_nonneg, div_le_iff₀ hd]
      linarith
    · rw [sub_le_comm, le_div_iff₀ hd]
      linarith
  · rw [mem_closedBall_zero_iff, hnorm, div_le_one hd]
    exact hd2
  · rcases le_total (2 * ‖(p.2 : E)‖) (2 - (p.1 : ℝ)) with h | h
    · left
      simp [ballRadialProjection, ballRadialDen, max_eq_left h,
        ne_of_gt (by linarith : 0 < 2 - (p.1 : ℝ))]
    · right
      rw [mem_sphere_zero_iff_norm, hnorm, max_eq_right h, div_self]
      simpa [max_eq_right h] using hd.ne'

/-- The radial projection away from height `2` does not raise the height of a point of the
cylinder. -/
theorem ballRadialProjection_fst_le (p : I × closedBall (0 : E) 1) :
    (ballRadialProjection p).1 ≤ p.1 := by
  have hd := ballRadialProjection_den_pos p
  have ht1 := p.1.2.2
  have hn1 := mem_closedBall_zero_iff.1 p.2.2
  have hdle : max (2 - (p.1 : ℝ)) (2 * ‖(p.2 : E)‖) ≤ 2 :=
    max_le (by linarith [p.1.2.1]) (by linarith)
  simp only [ballRadialProjection, ballRadialDen]
  rw [sub_le_comm, le_div_iff₀ hd]
  nlinarith

/-- The radial projection fixes the bottom face of the cylinder and the part of the cylinder
lying over the sphere. -/
@[simp]
theorem ballRadialProjection_eq_self (p : I × closedBall (0 : E) 1)
    (hp : p ∈ cylinderExtensionDomain (Subtype.val ⁻¹' sphere (0 : E) 1)) :
    ballRadialProjection p = ((p.1 : ℝ), (p.2 : E)) := by
  have hd : max (2 - (p.1 : ℝ)) (2 * ‖(p.2 : E)‖) = 2 := by
    rcases mem_cylinderExtensionDomain_iff.1 hp with h0 | hs
    · have ht : (p.1 : ℝ) = 0 := congrArg Subtype.val h0
      have hn := mem_closedBall_zero_iff.1 p.2.2
      simp only [ht, sub_zero]
      exact max_eq_left (by linarith)
    · rw [mem_sphere_zero_iff_norm.1 hs, mul_one]
      exact max_eq_right (by have := p.1.2.1; linarith)
  simp only [ballRadialProjection, ballRadialDen, hd,
    div_self (by norm_num : (2 : ℝ) ≠ 0), one_smul]
  congr 1
  ring

/-- The retraction of the cylinder over the closed unit ball onto the union of its bottom face
with the part lying over the unit sphere. -/
private def ballCylinderRetraction :
    C(I × closedBall (0 : E) 1, I × closedBall (0 : E) 1) where
  toFun p := (⟨(ballRadialProjection p).1, (ballRadialProjection_spec p).1⟩,
    ⟨(ballRadialProjection p).2, (ballRadialProjection_spec p).2.1⟩)
  continuous_toFun :=
    (continuous_ballRadialProjection.fst.subtype_mk _).prodMk
      (continuous_ballRadialProjection.snd.subtype_mk _)

/-- The retraction read off in the ambient coordinates of the cylinder. -/
private lemma ballCylinderRetraction_apply (p : I × closedBall (0 : E) 1) :
    ballCylinderRetraction p =
      (⟨(ballRadialProjection p).1, (ballRadialProjection_spec p).1⟩,
        ⟨(ballRadialProjection p).2, (ballRadialProjection_spec p).2.1⟩) := rfl

/-- **The unit sphere of a real seminormed space has the homotopy extension property inside the
closed unit ball**: the inclusion of the unit sphere is a closed cofibration. -/
theorem hasHomotopyExtensionProperty_sphere_closedBall :
    HasHomotopyExtensionProperty
      (Subtype.val ⁻¹' sphere (0 : E) 1 : Set (closedBall (0 : E) 1)) := by
  refine hasHomotopyExtensionProperty_of_retraction
    (isClosed_sphere.preimage continuous_subtype_val) (r := ballCylinderRetraction)
    (fun p => ?_) (fun p hp => ?_)
  · rw [mem_cylinderExtensionDomain_iff, ballCylinderRetraction_apply]
    obtain h0 | hs := (ballRadialProjection_spec p).2.2
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr hs
  · have h := ballRadialProjection_eq_self p hp
    rw [ballCylinderRetraction_apply]
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

end TauCeti

namespace ContinuousMap

open Metric Set unitInterval

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {Y : Type*} [TopologicalSpace Y]

/-- **A map out of the unit sphere is null-homotopic exactly when it extends over the closed unit
ball.** -/
theorem nullhomotopic_iff_exists_extension_closedBall (g : C(sphere (0 : E) 1, Y)) :
    g.Nullhomotopic ↔ ∃ G : C(closedBall (0 : E) 1, Y),
      ∀ y : sphere (0 : E) 1, G ⟨y, sphere_subset_closedBall y.2⟩ = g y := by
  constructor
  · -- Extend a homotopy from a constant map to `g` over the closed ball, starting at the constant
    -- map, and take its final stage.
    rintro ⟨c, hc⟩
    let H := hc.some.symm
    obtain ⟨K, -, hK⟩ :=
      TauCeti.hasHomotopyExtensionProperty_sphere_closedBall.exists_extension_of_isClosed
        (isClosed_sphere.preimage continuous_subtype_val) (ContinuousMap.const _ c)
        (H.toContinuousMap.comp ⟨fun p : I × (Subtype.val ⁻¹' sphere (0 : E) 1 :
          Set (closedBall (0 : E) 1)) ↦ (p.1, (⟨p.2.1.1, p.2.2⟩ : sphere (0 : E) 1)), by fun_prop⟩)
        fun a ↦ H.apply_zero _
    exact ⟨⟨fun x ↦ K (1, x), by fun_prop⟩, fun y ↦
      (hK 1 ⟨⟨y, sphere_subset_closedBall y.2⟩, y.2⟩).trans (H.apply_one y)⟩
  · -- The closed ball is contractible, so every map out of it is null-homotopic.
    rintro ⟨G, hG⟩
    have : ContractibleSpace (closedBall (0 : E) 1) :=
      (convex_closedBall 0 1).contractibleSpace ⟨0, mem_closedBall_self zero_le_one⟩
    let ι : C(sphere (0 : E) 1, closedBall (0 : E) 1) :=
      ⟨fun y ↦ ⟨y, sphere_subset_closedBall y.2⟩, by fun_prop⟩
    have hg : g = (G.comp (ContinuousMap.id _)).comp ι := by
      ext y
      exact (hG y).symm
    rw [hg]
    exact ((id_nullhomotopic _).comp_right G).comp_left ι

private def closedBallAffine {Z : Type*} [TopologicalSpace Z]
    (f g : C(Z, closedBall (0 : E) 1)) : f.Homotopy g :=
  let f' : C(Z, E) := ⟨fun z ↦ (f z : E), by fun_prop⟩
  let g' : C(Z, E) := ⟨fun z ↦ (g z : E), by fun_prop⟩
  { toFun p := ⟨Homotopy.affine f' g' p,
      (convex_closedBall (0 : E) 1).segment_subset (f p.2).2 (g p.2).2
        (Path.range_segment (f p.2 : E) (g p.2 : E) ▸ Set.mem_range_self p.1)⟩
    continuous_toFun := (Homotopy.affine f' g').continuous.subtype_mk _
    map_zero_left z := Subtype.ext ((Homotopy.affine f' g').apply_zero z)
    map_one_left z := Subtype.ext ((Homotopy.affine f' g').apply_one z) }

private lemma closedBallAffine_eq_of_eq {Z : Type*} [TopologicalSpace Z]
    {f g : C(Z, closedBall (0 : E) 1)} (t : I) {z : Z} (hz : f z = g z) :
    closedBallAffine f g (t, z) = f z := by
  ext
  have h : (closedBallAffine f g (t, z) : E) = Path.segment (f z : E) (g z : E) t := rfl
  simp [h, hz]

/-- **A map out of the unit sphere is homotopic relative to a base point to a constant map
exactly when it extends over the closed unit ball.** -/
theorem homotopicRel_const_singleton_sphere_iff_exists_extension_closedBall
    (g : C(sphere (0 : E) 1, Y)) (s₀ : sphere (0 : E) 1) :
    g.HomotopicRel (ContinuousMap.const _ (g s₀)) {s₀} ↔
      ∃ G : C(closedBall (0 : E) 1, Y),
        ∀ y : sphere (0 : E) 1, G ⟨y, sphere_subset_closedBall y.2⟩ = g y := by
  constructor
  · intro h
    exact g.nullhomotopic_iff_exists_extension_closedBall.mp ⟨g s₀, h.homotopic⟩
  · rintro ⟨G, hG⟩
    -- Straight-line segments inside the convex closed ball deform every point to `s₀`.
    let ι : C(sphere (0 : E) 1, closedBall (0 : E) 1) :=
      ⟨fun y ↦ ⟨y, sphere_subset_closedBall y.2⟩, by fun_prop⟩
    let H := closedBallAffine ι (ContinuousMap.const _ (ι s₀))
    refine ⟨{
      toContinuousMap := G.comp H.toContinuousMap
      map_zero_left y := by simp [H.apply_zero, ι, hG y]
      map_one_left y := by simp [H.apply_one, ι, hG s₀]
      prop' t y hy := by
        rw [mem_singleton_iff.mp hy]
        have ht : H (t, s₀) = ι s₀ := closedBallAffine_eq_of_eq t rfl
        simpa [ht, ι] using hG s₀ }⟩

/-- **Pointed and free null-homotopy agree on the unit sphere** of a real seminormed space. -/
theorem homotopicRel_const_singleton_sphere_iff_nullhomotopic
    (g : C(sphere (0 : E) 1, Y)) (s₀ : sphere (0 : E) 1) :
    g.HomotopicRel (ContinuousMap.const _ (g s₀)) {s₀} ↔ g.Nullhomotopic :=
  (g.homotopicRel_const_singleton_sphere_iff_exists_extension_closedBall s₀).trans
    g.nullhomotopic_iff_exists_extension_closedBall.symm

namespace HomotopicWith

/-- **Compressing a map of pairs relative to the sphere.** Let `g` map the closed unit ball of a
real seminormed space into `Y`, and let `B ⊆ Y`. If `g` is homotopic, through maps sending the unit
sphere into `B`, to a map with values in `B`, then `g` is homotopic relative to the unit sphere to
a map with values in `B`. -/
theorem exists_homotopicRel_range_subset {B : Set Y} {g g₁ : C(closedBall (0 : E) 1, Y)}
    (h : g.HomotopicWith g₁ fun f ↦ MapsTo f {x | (x : E) ∈ sphere 0 1} B)
    (h₁ : range g₁ ⊆ B) :
    ∃ g' : C(closedBall (0 : E) 1, Y),
      g.HomotopicRel g' {x | (x : E) ∈ sphere 0 1} ∧ range g' ⊆ B := by
  -- Run the homotopy backwards, so that it is `g` at time `1` and has values in `B` on the bottom
  -- face `{0} × D` and on `I × S` of the cylinder `I × D`.  The retraction `r` of the cylinder
  -- onto these two pieces carries the top face `{1} × D` onto them, fixing `{1} × S`, and the
  -- homotopy is pulled back along the straight segments from `(1, x)` to `r (1, x)`.
  obtain ⟨F⟩ := h
  obtain ⟨r, hr, hr'⟩ :=
    (TauCeti.hasHomotopyExtensionProperty_sphere_closedBall (E := E)).exists_retraction
  let r₁ : C(closedBall (0 : E) 1, closedBall (0 : E) 1) := ⟨fun x ↦ (r (1, x)).2, by fun_prop⟩
  let H := closedBallAffine (ContinuousMap.id _) r₁
  have hS {x : closedBall (0 : E) 1} (hx : (x : E) ∈ sphere 0 1) : r (1, x) = (1, x) :=
    hr' _ (TauCeti.mem_cylinderExtensionDomain_of_mem hx)
  refine ⟨⟨fun x ↦ F.symm (r (1, x)), by fun_prop⟩,
    ⟨{ toFun p := F.symm (σ (p.1 * σ (r (1, p.2)).1), H p)
       continuous_toFun := by fun_prop
       map_zero_left x := by simp [H.apply_zero, F.symm.apply_one]
       map_one_left x := by simp [H.apply_one, r₁]
       prop' t x hx := by
         have hrx : ContinuousMap.id (closedBall (0 : E) 1) x = r₁ x :=
           congrArg Prod.snd (hS hx).symm
         simp [H, hS hx, closedBallAffine_eq_of_eq t hrx] }⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain h0 | hs := TauCeti.mem_cylinderExtensionDomain_iff.1 (hr (1, x))
  · simpa [h0, F.symm.apply_zero] using h₁ (mem_range_self _)
  · exact F.symm.prop _ hs

end HomotopicWith

end ContinuousMap
