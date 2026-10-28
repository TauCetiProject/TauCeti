/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.Topology.Homotopy.HomotopyEquiv
import TauCeti.Topology.Homotopy.PuncturedStarConvex

/-!
# The open unit square

The open unit square `Ioo 0 1 ×ˢ Ioo 0 1` in `I × I` is the interior of a 2-cell whose
characteristic map is defined on the square `I × I`. This file records its two basic homotopical
properties: it is simply connected, and it stays path connected when one point is removed.

Both are transported from the open square in `ℝ × ℝ` along the inclusion `I × I → ℝ × ℝ`. That
square is convex, hence contractible; with one point removed it deforms onto a small sphere about
the point (`StarConvex.sphereHomotopyEquiv`), which is path connected.

The square with its centre removed deforms onto its boundary, radially from the centre
(`unitInterval.radialPush`). In the sup norm of `ℝ × ℝ` the boundary of the square is the sphere
of radius `1 / 2` about the centre, so this is the radial deformation `StarConvex.radialHomotopy`
of a punctured star-convex set onto a sphere. It is the deformation that pushes a space with
2-cells attached, minus one point in each open cell, back onto the space the cells are attached
to.

## Main definitions

* `unitInterval.squareCentre`: the centre of the unit square.
* `unitInterval.radialPush`: the radial deformation of the punctured square onto its boundary.

## Main results

* `unitInterval.notMem_Ioo_prod_Ioo_iff`: the boundary of the square is the union of its four
  edges.
* `unitInterval.image_prodMap_val_Ioo_prod_Ioo`: the inclusion `I × I → ℝ × ℝ` carries the open
  unit square onto the open unit square.
* `unitInterval.isSimplyConnected_Ioo_prod_Ioo`: the open unit square is simply connected.
* `unitInterval.isPathConnected_Ioo_prod_Ioo_diff_singleton`: the open unit square with one point
  removed is path connected.
* `unitInterval.radialPush_zero`, `unitInterval.radialPush_of_notMem`,
  `unitInterval.radialPush_one_notMem`, `unitInterval.continuousAt_radialPush`: the radial
  deformation starts at the identity, fixes the boundary, ends on the boundary, and is continuous
  away from the centre. It also fixes the centre (`unitInterval.radialPush_squareCentre`).
-/

public section

open Metric Set Topology

namespace unitInterval

/-- A point of the unit square outside the open square lies on one of its four edges. -/
theorem notMem_Ioo_prod_Ioo_iff {q : I × I} :
    q ∉ Ioo (0 : I) 1 ×ˢ Ioo (0 : I) 1 ↔ q.1 = 0 ∨ q.1 = 1 ∨ q.2 = 0 ∨ q.2 = 1 := by
  simp only [mem_prod, mem_Ioo, not_and_or, not_lt, le_zero_iff, ← or_assoc]
  simp only [le_one'.ge_iff_eq', or_assoc, eq_comm (a := (1 : I))]

/-- The inclusion `I × I → ℝ × ℝ` carries the open unit square onto the open unit square. -/
theorem image_prodMap_val_Ioo_prod_Ioo :
    Prod.map Subtype.val Subtype.val '' (Ioo (0 : I) 1 ×ˢ Ioo (0 : I) 1) =
      Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  rw [prodMap_image_prod, image_subtype_val_Ioo, Icc.coe_zero, Icc.coe_one]

/-- **The open unit square is simply connected.** -/
theorem isSimplyConnected_Ioo_prod_Ioo : IsSimplyConnected (Ioo (0 : I) 1 ×ˢ Ioo (0 : I) 1) := by
  rw [← (IsEmbedding.subtypeVal.prodMap IsEmbedding.subtypeVal).isSimplyConnected_image,
    image_prodMap_val_Ioo_prod_Ioo]
  have := ((convex_Ioo (0 : ℝ) 1).prod (convex_Ioo (0 : ℝ) 1)).contractibleSpace
    ⟨(1 / 2, 1 / 2), by norm_num, by norm_num⟩
  exact SimplyConnectedSpace.ofContractible _

/-- **The open unit square with one point removed is path connected.** In `ℝ × ℝ` it is a
convex set punctured at `p`, which deforms onto a small sphere about `p`
(`StarConvex.sphereHomotopyEquiv`), and that sphere is path connected. -/
theorem isPathConnected_Ioo_prod_Ioo_diff_singleton {p : I × I}
    (hp : p ∈ Ioo (0 : I) 1 ×ˢ Ioo (0 : I) 1) :
    IsPathConnected (Ioo (0 : I) 1 ×ˢ Ioo (0 : I) 1 \ {p}) := by
  rw [(IsInducing.subtypeVal.prodMap IsInducing.subtypeVal).isPathConnected_iff,
    image_sdiff (Subtype.val_injective.prodMap Subtype.val_injective), image_singleton,
    image_prodMap_val_Ioo_prod_Ioo]
  have hp' : Prod.map Subtype.val Subtype.val p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 :=
    image_prodMap_val_Ioo_prod_Ioo ▸ mem_image_of_mem _ hp
  set u := Prod.map Subtype.val Subtype.val p
  obtain ⟨⟨hu₀, hu₁⟩, hv₀, hv₁⟩ := hp'
  -- A sphere about `u` small enough to stay inside the open square.
  set m := min (min u.1 (1 - u.1)) (min u.2 (1 - u.2))
  have hm : 0 < m := lt_min (lt_min hu₀ (by linarith)) (lt_min hv₀ (by linarith))
  have hS : sphere u (m / 2) ⊆ Ioo 0 1 ×ˢ Ioo 0 1 := by
    intro z hz
    rw [mem_sphere, Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hz
    have h₁ := abs_le.1 ((le_max_left _ _).trans hz.le)
    have h₂ := abs_le.1 ((le_max_right _ _).trans hz.le)
    have := min_le_left (min u.1 (1 - u.1)) (min u.2 (1 - u.2))
    have := min_le_right (min u.1 (1 - u.1)) (min u.2 (1 - u.2))
    have := min_le_left u.1 (1 - u.1)
    have := min_le_right u.1 (1 - u.1)
    have := min_le_left u.2 (1 - u.2)
    have := min_le_right u.2 (1 - u.2)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hsphere : PathConnectedSpace (sphere u (m / 2)) :=
    isPathConnected_iff_pathConnectedSpace.1
      (isPathConnected_sphere (by simp [one_add_one_eq_two]) u (half_pos hm).le)
  exact isPathConnected_iff_pathConnectedSpace.2
    (((convex_Ioo (0 : ℝ) 1).prod (convex_Ioo (0 : ℝ) 1)).starConvex
      ⟨⟨hu₀, hu₁⟩, hv₀, hv₁⟩ |>.sphereHomotopyEquiv (half_pos hm) hS).pathConnectedSpace

/-! ### The radial deformation of the punctured square onto its boundary

In `ℝ × ℝ`, whose norm is the sup norm, the sphere of radius `1 / 2` about the centre of the unit
square is the boundary of the square. So the radial deformation of the punctured square onto its
boundary is the radial deformation `StarConvex.radialHomotopy` of a punctured star-convex set onto
a sphere about the puncture, read through the inclusion `I × I → ℝ × ℝ`. -/

/-- The centre `(1 / 2, 1 / 2)` of the unit square. -/
noncomputable def squareCentre : I × I :=
  (⟨1 / 2, by norm_num, by norm_num⟩, ⟨1 / 2, by norm_num, by norm_num⟩)

@[simp]
theorem coe_squareCentre_fst : (squareCentre.1 : ℝ) = 1 / 2 := (rfl)

@[simp]
theorem coe_squareCentre_snd : (squareCentre.2 : ℝ) = 1 / 2 := (rfl)

theorem squareCentre_mem_Ioo_prod_Ioo : squareCentre ∈ Ioo (0 : I) 1 ×ˢ Ioo (0 : I) 1 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [← Subtype.coe_lt_coe] <;> norm_num [squareCentre]

/-- Clamping `ℝ × ℝ` onto the unit square, a left inverse of the inclusion. -/
private noncomputable def clamp (z : ℝ × ℝ) : I × I :=
  (projIcc 0 1 zero_le_one z.1, projIcc 0 1 zero_le_one z.2)

private lemma continuous_clamp : Continuous clamp := by
  unfold clamp
  fun_prop

private lemma clamp_prodMap_val (q : I × I) : clamp (Prod.map Subtype.val Subtype.val q) = q := by
  ext <;> simp [clamp]

private lemma prodMap_val_clamp {z : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    Prod.map Subtype.val Subtype.val (clamp z) = z := by
  obtain ⟨a, b⟩ := z
  simp [clamp, projIcc_of_mem _ hz.1, projIcc_of_mem _ hz.2]

private lemma starConvex_Icc_prod_Icc :
    StarConvex ℝ (Prod.map Subtype.val Subtype.val squareCentre) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
  ((convex_Icc 0 1).prod (convex_Icc 0 1)).starConvex ⟨squareCentre.1.2, squareCentre.2.2⟩

/-- In the sup norm, a point is at distance `1 / 2` from the centre exactly when one of its
coordinates is at distance `1 / 2` from `1 / 2` and the other at most that. -/
private lemma dist_centre (z : ℝ × ℝ) :
    dist z (Prod.map Subtype.val Subtype.val squareCentre) =
      max |z.1 - 1 / 2| |z.2 - 1 / 2| := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  rfl

private lemma sphere_subset_Icc_prod_Icc :
    sphere (Prod.map Subtype.val Subtype.val squareCentre) (1 / 2) ⊆
      Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  intro z hz
  rw [mem_sphere, dist_centre] at hz
  have h₁ := abs_le.1 ((le_max_left _ _).trans hz.le)
  have h₂ := abs_le.1 ((le_max_right _ _).trans hz.le)
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- A point of the unit square is on the sphere of radius `1 / 2` about the centre exactly when
it is on the boundary of the square. -/
private lemma prodMap_val_mem_sphere_iff (q : I × I) :
    Prod.map Subtype.val Subtype.val q ∈ sphere (Prod.map Subtype.val Subtype.val squareCentre)
      (1 / 2) ↔ q ∉ Ioo (0 : I) 1 ×ˢ Ioo (0 : I) 1 := by
  obtain ⟨⟨a, ha₀, ha₁⟩, ⟨b, hb₀, hb₁⟩⟩ := q
  rw [mem_sphere, dist_centre, mem_prod, mem_Ioo, mem_Ioo, ← Subtype.coe_lt_coe,
    ← Subtype.coe_lt_coe, ← Subtype.coe_lt_coe, ← Subtype.coe_lt_coe]
  simp only [Prod.map_apply, Icc.coe_zero, Icc.coe_one]
  constructor
  · intro h ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    rcases max_choice |a - 1 / 2| |b - 1 / 2| with h' | h' <;> rw [h'] at h <;>
      rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.1 h with h'' | h'' <;> linarith
  · intro h
    refine le_antisymm (max_le (abs_le.2 ⟨by linarith, by linarith⟩)
      (abs_le.2 ⟨by linarith, by linarith⟩)) ?_
    by_contra h'
    refine h ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
      linarith [le_abs_self (a - 1 / 2), neg_abs_le (a - 1 / 2), le_abs_self (b - 1 / 2),
        neg_abs_le (b - 1 / 2), le_max_left |a - 1 / 2| |b - 1 / 2|,
        le_max_right |a - 1 / 2| |b - 1 / 2|]

/-- The radial deformation of the punctured square onto its boundary, in `ℝ × ℝ`, starting at
the radial projection and ending at the identity. -/
private noncomputable abbrev realRadialHomotopy :=
  starConvex_Icc_prod_Icc.radialHomotopy (by norm_num : (0 : ℝ) < 1 / 2) sphere_subset_Icc_prod_Icc

/-- A point of the unit square other than the centre, as a point of the punctured square in
`ℝ × ℝ`. -/
private def toPunctured {q : I × I} (hq : q ≠ squareCentre) :
    ↥(Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 \ {Prod.map Subtype.val Subtype.val squareCentre}) :=
  ⟨Prod.map Subtype.val Subtype.val q, ⟨q.1.2, q.2.2⟩,
    (Subtype.val_injective.prodMap Subtype.val_injective).ne hq⟩

/-- The **radial deformation** of the unit square with its centre removed onto its boundary, at
time `t`: a point `q` other than the centre moves along the ray from the centre through `q`, from
`q` at time `0` to the boundary of the square at time `1`, and points of the boundary do not
move. It is `StarConvex.radialHomotopy` run backwards, for the sup norm on `ℝ × ℝ`. The centre
itself, where the deformation is not continuous, is sent to itself. -/
noncomputable def radialPush (t : I) (q : I × I) : I × I :=
  if hq : q = squareCentre then q else clamp (realRadialHomotopy (σ t, toPunctured hq))

/-- At time `0` the radial deformation is the identity. -/
@[simp]
theorem radialPush_zero (q : I × I) : radialPush 0 q = q := by
  by_cases hq : q = squareCentre
  · simp [radialPush, hq]
  · simp only [radialPush, hq, ↓reduceDIte]
    rw [symm_zero, ContinuousMap.Homotopy.apply_one]
    exact clamp_prodMap_val q

/-- The radial deformation fixes the centre of the square. -/
@[simp]
theorem radialPush_squareCentre (t : I) : radialPush t squareCentre = squareCentre := by
  simp [radialPush]

/-- The radial deformation fixes the boundary of the square. -/
@[simp]
theorem radialPush_of_notMem {q : I × I} (hq : q ∉ Ioo (0 : I) 1 ×ˢ Ioo (0 : I) 1) (t : I) :
    radialPush t q = q := by
  have hqc : q ≠ squareCentre := fun h => hq (h ▸ squareCentre_mem_Ioo_prod_Ioo)
  -- On the boundary, `q` is a point of the sphere of radius `1 / 2`, which the deformation fixes.
  have hx : toPunctured hqc = TauCeti.sphereInclusionDiffSingleton (by norm_num)
      sphere_subset_Icc_prod_Icc ⟨_, (prodMap_val_mem_sphere_iff q).2 hq⟩ :=
    Subtype.ext (by rw [TauCeti.coe_sphereInclusionDiffSingleton_apply]; rfl)
  simp only [radialPush, hqc, ↓reduceDIte]
  rw [hx, StarConvex.radialHomotopy_apply_sphereInclusion,
    TauCeti.coe_sphereInclusionDiffSingleton_apply]
  exact clamp_prodMap_val q

/-- At time `1` the radial deformation sends every point other than the centre to the boundary
of the square. -/
theorem radialPush_one_notMem {q : I × I} (hq : q ≠ squareCentre) :
    radialPush 1 q ∉ Ioo (0 : I) 1 ×ˢ Ioo (0 : I) 1 := by
  simp only [radialPush, hq, ↓reduceDIte]
  rw [symm_one, ContinuousMap.Homotopy.apply_zero, ContinuousMap.comp_apply,
    TauCeti.coe_sphereInclusionDiffSingleton_apply]
  set z := TauCeti.radialProjectionToSphere (V := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (toPunctured hq)
  rw [← prodMap_val_mem_sphere_iff, prodMap_val_clamp (sphere_subset_Icc_prod_Icc z.2)]
  exact z.2

/-- The radial deformation is continuous in the time and the point away from the centre. -/
theorem continuousAt_radialPush {t : I} {q : I × I} (hq : q ≠ squareCentre) :
    ContinuousAt (fun p : I × (I × I) => radialPush p.1 p.2) (t, q) := by
  have hO : IsOpen {p : I × (I × I) | p.2 ≠ squareCentre} :=
    isOpen_ne_fun continuous_snd continuous_const
  refine ContinuousOn.continuousAt ?_ (hO.mem_nhds hq)
  rw [continuousOn_iff_continuous_domRestrict]
  have h : {p : I × (I × I) | p.2 ≠ squareCentre}.domRestrict (fun p => radialPush p.1 p.2) =
      fun p => clamp (realRadialHomotopy (σ p.1.1, toPunctured p.2)) :=
    funext fun p => by
      have hp : (p : I × (I × I)).2 ≠ squareCentre := p.2
      simp only [domRestrict_apply, radialPush, hp, ↓reduceDIte]
  rw [h]
  refine continuous_clamp.comp (continuous_subtype_val.comp (realRadialHomotopy.continuous.comp
    ((continuous_symm.comp (continuous_fst.comp continuous_subtype_val)).prodMk ?_)))
  exact ((continuous_subtype_val.prodMap continuous_subtype_val).comp
    (continuous_snd.comp continuous_subtype_val)).subtype_mk _

end unitInterval
