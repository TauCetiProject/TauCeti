/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Basic
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Analysis.Convex.Contractible

/-!
# The unit sphere is a closed cofibration in the closed unit ball

The unit sphere of a real seminormed space has the homotopy extension property inside the closed
unit ball.  Concretely, the cylinder `I × D` over the closed unit ball `D` retracts onto
`{0} × D ∪ I × S`, where `S` is the unit sphere, by radial projection away from the point of the
cylinder axis at height `2`: the ray from that point through `(t, x)` leaves the cylinder either
through its bottom face or through its side, and the retraction sends `(t, x)` to that exit
point.

The same radial projection, read on the values of a gauge, works fibre by fibre: if `ρ` is
continuous on a set `D` with `0 ≤ ρ ≤ 1` there, and `D` carries scalings `φ c` with
`ρ (φ c x) = c * ρ x`, then the level `{ρ = 1}` has the homotopy extension property in `D`. For a
vector bundle, with a fibre gauge and fibrewise scalar multiplication, this says that a sphere
bundle is a closed cofibration in its disc bundle; the unit ball is the case of a single fibre.

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
* `TauCeti.ballRadialDen_pos`, `TauCeti.continuous_ballRadialDen`: the denominator is positive
  and continuous.
* `TauCeti.ballRadialProjection_spec`, `TauCeti.ballRadialProjection_eq_self`,
  `TauCeti.ballRadialProjection_fst_le`: the projection lands on the bottom and sides, fixes that
  subspace and does not raise heights.
* `TauCeti.hasHomotopyExtensionProperty_setOf_eq_one`: **the unit level of a scaling gauge has the
  homotopy extension property in its unit disc**, for instance a sphere bundle in its disc bundle.
* `TauCeti.hasHomotopyExtensionProperty_sphere_closedBall`: **the unit sphere has the homotopy
  extension property inside the closed unit ball.**
* `ContinuousMap.nullhomotopic_iff_exists_extension_closedBall`: a map out of the unit sphere is
  null-homotopic exactly when it extends over the closed unit ball.
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
/-- The radial denominator is positive. -/
theorem ballRadialDen_pos (p : I × closedBall (0 : E) 1) : 0 < ballRadialDen p := by
  rw [ballRadialDen_def]
  exact lt_of_lt_of_le (by have := p.1.property.2; linarith) (le_max_left _ _)

omit [NormedSpace ℝ E] in
/-- The radial denominator is continuous. -/
theorem continuous_ballRadialDen : Continuous (ballRadialDen (E := E)) :=
  (by fun_prop : Continuous fun p : I × closedBall (0 : E) 1 ↦
    max (2 - (p.1 : ℝ)) (2 * ‖(p.2 : E)‖)).congr fun p ↦ (ballRadialDen_def p).symm

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
  have hd := continuous_ballRadialDen (E := E)
  have hne p := (ballRadialDen_pos (E := E) p).ne'
  exact (continuous_const.sub ((by fun_prop : Continuous fun p : I × closedBall (0 : E) 1 =>
    2 * (2 - (p.1 : ℝ))).div hd hne)).prodMk
      ((continuous_const.div hd hne).smul (by fun_prop))

/-- The radial projection lands in the cylinder, and in the union of its bottom face with the
part of the cylinder lying over the sphere. -/
theorem ballRadialProjection_spec (p : I × closedBall (0 : E) 1) :
    (ballRadialProjection p).1 ∈ I ∧ (ballRadialProjection p).2 ∈ closedBall (0 : E) 1 ∧
      ((ballRadialProjection p).1 = 0 ∨ (ballRadialProjection p).2 ∈ sphere (0 : E) 1) := by
  have ht0 := p.1.property.1
  have ht1 := p.1.property.2
  have hn1 := mem_closedBall_zero_iff.1 p.2.property
  have hd := ballRadialDen_pos p
  rw [ballRadialDen_def] at hd
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
  have hd := ballRadialDen_pos p
  rw [ballRadialDen_def] at hd
  have ht1 := p.1.property.2
  have hn1 := mem_closedBall_zero_iff.1 p.2.property
  have hdle : max (2 - (p.1 : ℝ)) (2 * ‖(p.2 : E)‖) ≤ 2 :=
    max_le (by linarith [p.1.property.1]) (by linarith)
  simp only [ballRadialProjection, ballRadialDen]
  rw [sub_le_comm, le_div_iff₀ hd]
  nlinarith

omit [NormedSpace ℝ E] in
/-- On the bottom face of the cylinder and on the part lying over the sphere, the radial
denominator is `2`. -/
private lemma ballRadialDen_eq_two (p : I × closedBall (0 : E) 1)
    (hp : p ∈ cylinderExtensionDomain (Subtype.val ⁻¹' sphere (0 : E) 1)) :
    ballRadialDen p = 2 := by
  rcases mem_cylinderExtensionDomain_iff.1 hp with h0 | hs
  · have ht : (p.1 : ℝ) = 0 := congrArg Subtype.val h0
    have hn := mem_closedBall_zero_iff.1 p.2.property
    rw [ballRadialDen_def, ht, sub_zero]
    exact max_eq_left (by linarith)
  · rw [ballRadialDen_def, mem_sphere_zero_iff_norm.1 hs, mul_one]
    exact max_eq_right (by have := p.1.property.1; linarith)

/-- The radial projection fixes the bottom face of the cylinder and the part of the cylinder
lying over the sphere. -/
@[simp]
theorem ballRadialProjection_eq_self (p : I × closedBall (0 : E) 1)
    (hp : p ∈ cylinderExtensionDomain (Subtype.val ⁻¹' sphere (0 : E) 1)) :
    ballRadialProjection p = ((p.1 : ℝ), (p.2 : E)) := by
  simp only [ballRadialProjection, ballRadialDen_eq_two p hp,
    div_self (by norm_num : (2 : ℝ) ≠ 0), one_smul]
  congr 1
  ring

section Gauge

/-- A point `(t, s)`, `s ≥ 0`, of the cylinder over the unit interval of `ℝ` lies on the bottom
face or over the sphere exactly when `t = 0` or `s = 1`. -/
private lemma mem_cylinderExtensionDomain_sphere_iff {t : I} {s : closedBall (0 : ℝ) 1}
    (hs : 0 ≤ (s : ℝ)) :
    (t, s) ∈ cylinderExtensionDomain (Subtype.val ⁻¹' sphere (0 : ℝ) 1) ↔ t = 0 ∨ (s : ℝ) = 1 := by
  rw [mem_cylinderExtensionDomain_iff, mem_preimage, mem_sphere_zero_iff_norm,
    Real.norm_of_nonneg hs]

variable {X : Type u} [TopologicalSpace X]

/-- **The unit sphere of a scaling gauge has the homotopy extension property in its unit disc.**
Let `ρ` be a function on `X`, continuous on a subset `D` on which `0 ≤ ρ ≤ 1`, and let `φ c` be
scalings, jointly continuous in `c ≥ 0` and the point of `D`, such that for `c ≥ 0` with
`c * ρ x ≤ 1` the point `φ c x` lies in `D` with `ρ (φ c x) = c * ρ x`, and `φ 1` is the identity
on `D`. Then the level `{ρ = 1}` has the homotopy extension property in `D`.

For a vector bundle with a fibre gauge `ρ` and the fibrewise scalar multiplication `φ`, this is the
homotopy extension property of the sphere bundle `{ρ = 1}` in the disc bundle `{ρ ≤ 1}`; the closed
unit ball of a normed space, with its norm, is the case of a single fibre
(`TauCeti.hasHomotopyExtensionProperty_sphere_closedBall`). -/
theorem hasHomotopyExtensionProperty_setOf_eq_one {D : Set X} {ρ : X → ℝ}
    (hρ : ContinuousOn ρ D) (hρD : ∀ x ∈ D, 0 ≤ ρ x ∧ ρ x ≤ 1) {φ : ℝ → X → X}
    (hφ : ContinuousOn (fun p : ℝ × X ↦ φ p.1 p.2) (Ici 0 ×ˢ D))
    (hφD : ∀ x ∈ D, ∀ c, 0 ≤ c → c * ρ x ≤ 1 → φ c x ∈ D ∧ ρ (φ c x) = c * ρ x)
    (hφ1 : ∀ x ∈ D, φ 1 x = x) :
    HasHomotopyExtensionProperty {x : D | ρ x = 1} := by
  -- `I × D` retracts onto `{0} × D ∪ I × {ρ = 1}` by the radial projection of the cylinder of `ℝ`
  -- read on `(t, ρ x)`: it gives the height, and `x` is rescaled by `φ` to give `ρ`.
  -- The value of `ρ`, as a point of the closed unit ball of `ℝ`.
  have hmem (x : D) : ρ x ∈ closedBall (0 : ℝ) 1 :=
    mem_closedBall_zero_iff.2 ((Real.norm_of_nonneg (hρD x x.property).1).trans_le
        (hρD x x.property).2)
  let ρD : C(D, closedBall (0 : ℝ) 1) :=
    ⟨fun x ↦ ⟨ρ x, hmem x⟩, (continuousOn_iff_continuous_domRestrict.1 hρ).subtype_mk hmem⟩
  have hρD_apply (x : D) : (ρD x : ℝ) = ρ x := rfl
  let p : I × D → I × closedBall (0 : ℝ) 1 := fun q ↦ (q.1, ρD q.2)
  have hp_apply (q : I × D) : (p q).2 = ρD q.2 := rfl
  have hpc : Continuous p := by fun_prop
  -- The scale `c q = 2 / ballRadialDen (p q)` carries `ρ` to the second coordinate of the
  -- radial projection.
  let c : I × D → ℝ := fun q ↦ 2 / ballRadialDen (p q)
  have hc_apply (q : I × D) : c q = 2 / ballRadialDen (p q) := rfl
  have hc0 (q : I × D) : 0 ≤ c q := div_nonneg zero_le_two (ballRadialDen_pos _).le
  have hcρ (q : I × D) : c q * ρ q.2 = (ballRadialProjection (p q)).2 := by
    rw [ballRadialProjection_def, smul_eq_mul, hp_apply, hρD_apply, hc_apply]
  have hcρ1 (q : I × D) : c q * ρ q.2 ≤ 1 := by
    rw [hcρ]
    exact (Real.le_norm_self _).trans (mem_closedBall_zero_iff.1 (ballRadialProjection_spec _).2.1)
  have hcc : Continuous c := continuous_const.div (continuous_ballRadialDen.comp hpc)
    fun q ↦ (ballRadialDen_pos (p q)).ne'
  have hφD' (q : I × D) := hφD q.2 q.2.property (c q) (hc0 q) (hcρ1 q)
  let r : C(I × D, I × D) :=
    ⟨fun q ↦ (⟨(ballRadialProjection (p q)).1, (ballRadialProjection_spec (p q)).1⟩,
      ⟨φ (c q) q.2, (hφD' q).1⟩),
      ((continuous_ballRadialProjection.comp hpc).fst.subtype_mk _).prodMk
        ((hφ.comp_continuous (hcc.prodMk (continuous_subtypeVal.comp continuous_snd))
          fun q ↦ ⟨hc0 q, q.2.property⟩).subtype_mk _)⟩
  have hr₁ (q : I × D) : ((r q).1 : ℝ) = (ballRadialProjection (p q)).1 := rfl
  have hr₂ (q : I × D) : ((r q).2 : X) = φ (c q) q.2 := rfl
  refine hasHomotopyExtensionProperty_of_retraction
    (isClosed_eq (continuousOn_iff_continuous_domRestrict.1 hρ) continuous_const) (r := r)
    (fun q ↦ mem_cylinderExtensionDomain_iff.2 ?_) (fun q hq ↦ ?_)
  · -- The projection lands on the bottom face or over the level `{ρ = 1}`.
    rcases (ballRadialProjection_spec (p q)).2.2 with h0 | hs
    · exact Or.inl (Subtype.ext ((hr₁ q).trans h0))
    · rw [mem_sphere_zero_iff_norm, Real.norm_eq_abs, ← hcρ,
        abs_of_nonneg (mul_nonneg (hc0 q) (hρD _ q.2.property).1)] at hs
      exact Or.inr ((congrArg ρ (hr₂ q)).trans ((hφD' q).2.trans hs))
  · -- On the bottom face and over `{ρ = 1}` the denominator is `2`, so `r` is the identity.
    have hq' : p q ∈ cylinderExtensionDomain (Subtype.val ⁻¹' sphere (0 : ℝ) 1) :=
      (mem_cylinderExtensionDomain_sphere_iff (hρD _ q.2.property).1).2
        (mem_cylinderExtensionDomain_iff.1 hq)
    have hc1 : c q = 1 := by
      rw [hc_apply, ballRadialDen_eq_two _ hq', div_self two_ne_zero]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact (hr₁ q).trans (congrArg Prod.fst (ballRadialProjection_eq_self (p q) hq'))
    · rw [hr₂, hc1, hφ1 _ q.2.property]

end Gauge

/-- **The unit sphere of a real seminormed space has the homotopy extension property inside the
closed unit ball**: the inclusion of the unit sphere is a closed cofibration. -/
theorem hasHomotopyExtensionProperty_sphere_closedBall :
    HasHomotopyExtensionProperty
      (Subtype.val ⁻¹' sphere (0 : E) 1 : Set (closedBall (0 : E) 1)) := by
  have h := hasHomotopyExtensionProperty_setOf_eq_one (D := closedBall (0 : E) 1)
    continuous_norm.continuousOn
    (fun x hx ↦ ⟨norm_nonneg x, mem_closedBall_zero_iff.1 hx⟩)
    (φ := fun c x ↦ c • x) continuous_smul.continuousOn
    (fun x _ c hc hcx ↦ by
      rw [norm_smul, Real.norm_of_nonneg hc]
      exact ⟨mem_closedBall_zero_iff.2 (by rwa [norm_smul, Real.norm_of_nonneg hc]), rfl⟩)
    (fun x _ ↦ one_smul ℝ x)
  convert h using 1
  ext x
  exact mem_sphere_zero_iff_norm

end TauCeti

namespace ContinuousMap

open Metric Set unitInterval

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {Y : Type*} [TopologicalSpace Y]

/-- **A map out of the unit sphere is null-homotopic exactly when it extends over the closed unit
ball.** -/
theorem nullhomotopic_iff_exists_extension_closedBall (g : C(sphere (0 : E) 1, Y)) :
    g.Nullhomotopic ↔ ∃ G : C(closedBall (0 : E) 1, Y),
      ∀ y : sphere (0 : E) 1, G ⟨y, sphere_subset_closedBall y.property⟩ = g y := by
  constructor
  · -- Extend a homotopy from a constant map to `g` over the closed ball, starting at the constant
    -- map, and take its final stage.
    rintro ⟨c, hc⟩
    let H := hc.some.symm
    obtain ⟨K, -, hK⟩ :=
      TauCeti.hasHomotopyExtensionProperty_sphere_closedBall.exists_extension_of_isClosed
        (isClosed_sphere.preimage continuous_subtypeVal) (ContinuousMap.const _ c)
        (H.toContinuousMap.comp ⟨fun p : I × (Subtype.val ⁻¹' sphere (0 : E) 1 :
          Set (closedBall (0 : E) 1)) ↦ (p.1, (⟨p.2.val.val, p.2.property⟩ : sphere (0 : E) 1)),
              by fun_prop⟩)
        fun a ↦ H.apply_zero _
    exact ⟨⟨fun x ↦ K (1, x), by fun_prop⟩, fun y ↦
      (hK 1 ⟨⟨y, sphere_subset_closedBall y.property⟩, y.property⟩).trans (H.apply_one y)⟩
  · -- The closed ball is contractible, so every map out of it is null-homotopic.
    rintro ⟨G, hG⟩
    let ι : C(sphere (0 : E) 1, closedBall (0 : E) 1) :=
      ⟨fun y ↦ ⟨y, sphere_subset_closedBall y.property⟩, by fun_prop⟩
    have hg : g = (G.comp (ContinuousMap.id _)).comp ι := by
      ext y
      exact (hG y).symm
    rw [hg]
    exact ((id_nullhomotopic _).comp_right G).comp_left ι

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
  have hseg (p : I × closedBall (0 : E) 1) :
      (1 - (p.1 : ℝ)) • (p.2 : E) + (p.1 : ℝ) • ((r (1, p.2)).2 : E) ∈ closedBall (0 : E) 1 :=
    convex_closedBall (0 : E) 1 p.2.property (r (1, p.2)).2.property (sub_nonneg.2 p.1.property.2)
        p.1.property.1
      (by ring)
  have hS {x : closedBall (0 : E) 1} (hx : (x : E) ∈ sphere 0 1) : r (1, x) = (1, x) :=
    hr' _ (TauCeti.mem_cylinderExtensionDomain_of_mem hx)
  refine ⟨⟨fun x ↦ F.symm (r (1, x)), by fun_prop⟩,
    ⟨{ toFun p := F.symm (σ (p.1 * σ (r (1, p.2)).1), ⟨_, hseg p⟩)
       continuous_toFun := by fun_prop
       map_zero_left x := by simp [F.symm.apply_one]
       map_one_left x := by simp
       prop' t x hx := by simp [hS hx, ← add_smul] }⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain h0 | hs := TauCeti.mem_cylinderExtensionDomain_iff.1 (hr (1, x))
  · simpa [h0, F.symm.apply_zero] using h₁ (mem_range_self _)
  · exact F.symm.prop _ hs

end HomotopicWith

end ContinuousMap
