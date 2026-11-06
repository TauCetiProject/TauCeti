/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.LowDimTopology.SeifertFibration
public import TauCeti.Topology.Category.TopCat.DisjointOpens

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.Analysis.Calculus.Bilinear
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.MetricSpace.HausdorffDimension
import TauCeti.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Analysis.Normed.Module.Ball.LinearIsometry
import TauCeti.Geometry.Manifold.TubularNeighborhood.Euclidean
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Solid torus neighbourhoods of knots

A *solid torus neighbourhood* of a loop `f : S¹ → X` is an embedding `Φ` of the closed solid torus
`D² × S¹` into `X` whose core `{0} × S¹` traces `f` and which maps the open solid torus onto an
open subset of `X`. In Rolfsen's terminology `Φ` is a framing of the solid torus it parametrizes,
with meridians `w ↦ Φ (w, z)` and longitude `z ↦ Φ (1, z)`; it need not be the preferred framing.
Removing the image of the open solid torus from `X` leaves the *exterior* of the knot, a closed
set whose frontier is the torus `Φ (S¹ × S¹)` when `X` is Hausdorff. This is the input to Dehn
surgery, which glues a solid torus back onto this boundary torus along a homeomorphism specified
by a slope on it.

The main theorem is that every `C²` embedded circle in `ℝ³` has solid torus neighbourhoods, inside
any prescribed neighbourhood of the circle. By the tubular neighbourhood theorem
`TauCeti.exists_isOpenEmbedding_normalTube`, the normal vectors of length less than some `ε` embed
openly into `ℝ³` by `(z, v) ↦ f z + v`. It remains to trivialize the normal bundle, that is, to
choose a continuous orthonormal frame `(n₁ z, n₂ z)` of the normal plane at every `z`. The tangent
lines of the circle form the image of a `C¹` map from a plane, which has dense complement in `ℝ³`,
so some vector `a` is tangent to the circle nowhere; `n₁ z` is the normalized projection of `a`
onto the normal plane, and `n₂ z` is the cross product of the unit tangent with `n₁ z`. Then
`Φ (w, z) = f z + r • (re w • n₁ z + im w • n₂ z)` for a small `r > 0`.

This `Φ` is differentiable at its core point `(0, 1)` when read as
`(u, t) ↦ Φ (u, exp (t i))` (`TauCeti.SolidTorus.coreReading`), with injective derivative
`(u, t) ↦ t • τ + r • (re u • n₁ 1 + im u • n₂ 1)` for the velocity `τ` of `f` at `1`, although the
frame is only continuous: the frame is multiplied by `u`, which vanishes on the core. This is what
lets the orientation of a solid torus neighbourhood be read off its derivative at the core.

## Main definitions

* `TauCeti.IsSolidTorusNeighborhood f Φ`: `Φ : D² × S¹ → X` is a solid torus neighbourhood of
  the loop `f`.
* `TauCeti.SolidTorus.boundaryInclusion`: the inclusion of the boundary torus `S¹ × S¹` into the
  solid torus.
* `TauCeti.SolidTorus.twist`: the meridian-disc twist `(w, z) ↦ (w zⁿ, z)`.
* `TauCeti.SolidTorus.coreReading Φ`: a map `Φ` from the solid torus read near the core point
  `(0, 1)` as `(u, t) ↦ Φ (u, exp (t i))` on `ℂ × ℝ`.
* `TauCeti.SolidTorus.conjDisc`: the reflection `(u, w) ↦ (conj u, w)` of the solid torus.

## Main results

* `TauCeti.SolidTorus.extendsDisjointOpens_boundaryInclusion`: the inclusion of the boundary torus
  into the solid torus extends disjoint open sets, through open collars.
* `TauCeti.IsSolidTorusNeighborhood.frontier_image`: the frontier of the image of the open solid
  torus, which is also the frontier of the knot exterior, is the image of the boundary torus
  when the ambient space is Hausdorff.
* `TauCeti.IsSolidTorusNeighborhood.isEmbedding_comp_boundaryInclusion`: the boundary torus
  `S¹ × S¹` embeds.
* `TauCeti.IsSolidTorusNeighborhood.comp`: solid torus neighbourhoods are carried along open
  embeddings of the ambient space.
* `TauCeti.IsSolidTorusNeighborhood.comp_prodMap`: and along reparametrizations of the loop by
  homeomorphisms of the circle.
* `TauCeti.IsSolidTorusNeighborhood.apply_mem_range_iff`: a point of the solid torus lies on the
  knot exactly when it lies on the core.
* `TauCeti.IsSolidTorusNeighborhood.frontier_subset_compl_range`: the boundary torus of the exterior
  misses the knot.
* `TauCeti.IsSolidTorusNeighborhood.exteriorFrontierHomeomorph`: the framing identifies the torus
  with the frontier of the exterior.
* `TauCeti.IsSolidTorusNeighborhood.comp_conjDisc`: reflecting the disc of a solid torus
  neighbourhood gives a solid torus neighbourhood of the same loop.
* `TauCeti.exists_isSolidTorusNeighborhood`: a `C²` embedded circle in `ℝ³` has a solid torus
  neighbourhood inside any neighbourhood of its image.
* `TauCeti.exists_isSolidTorusNeighborhood_hasFDerivAt_coreReading`: such a neighbourhood can be
  chosen with an injective derivative at its core point.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Section 2E (solid tori, framings,
  meridians and longitudes) and Section 9F (Dehn surgery along tubular neighbourhoods).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Theorem 6.24 (tubular neighbourhoods).
-/

public section

open Set Metric Function Topology WithLp
open scoped Matrix
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

/-! ### Solid torus neighbourhoods -/

section General

/-- The inclusion of the boundary torus `S¹ × S¹ = ∂D² × S¹` into the solid torus `D² × S¹`. -/
def SolidTorus.boundaryInclusion (q : Circle × Circle) : SolidTorus :=
  (⟨q.1, mem_closedBall_zero_iff.mpr (Circle.norm_coe q.1).le⟩, q.2)

@[simp]
theorem SolidTorus.coe_boundaryInclusion_fst (q : Circle × Circle) :
    ((SolidTorus.boundaryInclusion q).1 : ℂ) = q.1 :=
  (rfl)

@[simp]
theorem SolidTorus.boundaryInclusion_snd (q : Circle × Circle) :
    (SolidTorus.boundaryInclusion q).2 = q.2 :=
  (rfl)

/-- The boundary torus is embedded in the solid torus. -/
theorem SolidTorus.isEmbedding_boundaryInclusion : IsEmbedding SolidTorus.boundaryInclusion :=
  (IsEmbedding.subtypeVal.codRestrict (closedBall (0 : ℂ) 1)
    fun z : Circle => mem_closedBall_zero_iff.mpr (Circle.norm_coe z).le).prodMap IsEmbedding.id

/-- The inclusion of the boundary torus into the solid torus extends disjoint open sets: an open
subset `U` of `S¹ × S¹` is the trace of the open collar of points `(w, z)` with `1 / 2 < ‖w‖` and
`(w / ‖w‖, z) ∈ U`, and the collars over disjoint sets are disjoint
(`TauCeti.TopCat.extendsDisjointOpens_of_continuousOn` with the radial projection). -/
theorem SolidTorus.extendsDisjointOpens_boundaryInclusion :
    TopCat.extendsDisjointOpens (TopCat.ofHom
      ⟨SolidTorus.boundaryInclusion, SolidTorus.isEmbedding_boundaryInclusion.continuous⟩) := by
  have hw : Continuous fun p : SolidTorus ↦ (p.1 : ℂ) := continuous_subtype_val.comp continuous_fst
  refine TopCat.extendsDisjointOpens_of_continuousOn _
    (μ := fun q : Circle × Circle ↦ ((q.1 : ℂ), q.2)) (IsInducing.subtypeVal.prodMap .id)
    (N := {p | 1 / 2 < ‖(p.1 : ℂ)‖}) (ρ := fun p ↦ (‖(p.1 : ℂ)‖⁻¹ • (p.1 : ℂ), p.2))
    (isOpen_lt continuous_const hw.norm)
    (((ContinuousOn.inv₀ hw.norm.continuousOn fun p hp ↦ (lt_trans (by norm_num) hp).ne').smul
      hw.continuousOn).prodMk continuous_snd.continuousOn) (fun q ↦ ?_) (fun p hp ↦ ?_)
    (fun q ↦ ?_)
  · simp [show (2⁻¹ : ℝ) < 1 by norm_num]
  · have h₁ : ‖‖(p.1 : ℂ)‖⁻¹ • (p.1 : ℂ)‖ = 1 :=
      norm_smul_inv_norm (𝕜 := ℝ) (norm_pos_iff.1 (lt_trans (by norm_num) hp))
    exact ⟨(⟨_, mem_sphere_zero_iff_norm.2 h₁⟩, p.2), rfl⟩
  · simp

/-- The boundary torus is the set of points `(w, z)` of the solid torus with `‖w‖ = 1`. -/
theorem SolidTorus.range_boundaryInclusion :
    range SolidTorus.boundaryInclusion = {p : SolidTorus | ‖(p.1 : ℂ)‖ = 1} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simp
  · intro hp
    exact ⟨(⟨p.1, mem_sphere_zero_iff_norm.mpr hp⟩, p.2), rfl⟩

/-- The underlying map `(w, z) ↦ (w zⁿ, z)` of `TauCeti.SolidTorus.twist`. -/
private noncomputable def SolidTorus.twistMap (n : ℤ) (p : SolidTorus) : SolidTorus :=
  (⟨(p.1 : ℂ) * ((p.2 ^ n : Circle) : ℂ), by
    rw [mem_closedBall_zero_iff, norm_mul, Circle.norm_coe, mul_one]
    exact mem_closedBall_zero_iff.mp p.1.2⟩, p.2)

private theorem SolidTorus.twistMap_twistMap (m n : ℤ) (p : SolidTorus) :
    twistMap n (twistMap m p) = twistMap (m + n) p :=
  Prod.ext (Subtype.ext (by simp only [twistMap, mul_assoc, ← Circle.coe_mul, ← zpow_add])) rfl

private theorem SolidTorus.twistMap_zero (p : SolidTorus) : twistMap 0 p = p :=
  Prod.ext (Subtype.ext (by simp [twistMap])) rfl

private theorem SolidTorus.continuous_twistMap (n : ℤ) : Continuous (twistMap n) :=
  (((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp
    ((continuous_zpow (G := Circle) n).comp continuous_snd))).subtype_mk _).prodMk continuous_snd

/-- The twist `(w, z) ↦ (w zⁿ, z)` of the solid torus `D² × S¹` along its meridian discs. -/
noncomputable def SolidTorus.twist (n : ℤ) : SolidTorus ≃ₜ SolidTorus where
  toFun := twistMap n
  invFun := twistMap (-n)
  left_inv p := by rw [twistMap_twistMap, add_neg_cancel, twistMap_zero]
  right_inv p := by rw [twistMap_twistMap, neg_add_cancel, twistMap_zero]
  continuous_toFun := continuous_twistMap n
  continuous_invFun := continuous_twistMap (-n)

/-- The meridian-disc twist multiplies the disc coordinate by `zⁿ`. -/
@[simp]
theorem SolidTorus.coe_twist_apply_fst (n : ℤ) (p : SolidTorus) :
    ((twist n p).1 : ℂ) = p.1 * ((p.2 ^ n : Circle) : ℂ) :=
  (rfl)

/-- The meridian-disc twist preserves the circle coordinate. -/
@[simp]
theorem SolidTorus.twist_apply_snd (n : ℤ) (p : SolidTorus) : (twist n p).2 = p.2 :=
  (rfl)

/-- The zero twist is the identity homeomorphism. -/
@[simp]
theorem SolidTorus.twist_zero : twist 0 = Homeomorph.refl SolidTorus := by
  ext1 p
  exact twistMap_zero p

/-- Successive meridian-disc twists add their twisting numbers. -/
theorem SolidTorus.twist_add (m n : ℤ) : twist (m + n) = (twist m).trans (twist n) := by
  ext1 p
  exact (twistMap_twistMap m n p).symm

/-- The inverse meridian-disc twist has the opposite twisting number. -/
@[simp]
theorem SolidTorus.twist_symm (n : ℤ) : (twist n).symm = twist (-n) := by
  ext1 p
  rfl

/-- The twist restricts on the boundary torus to `(a, b) ↦ (a bⁿ, b)`. -/
@[simp]
theorem SolidTorus.twist_boundaryInclusion (n : ℤ) (q : Circle × Circle) :
    twist n (boundaryInclusion q) = boundaryInclusion (q.1 * q.2 ^ n, q.2) := by
  exact Prod.ext (Subtype.ext (by simp [boundaryInclusion])) rfl

/-- The open solid torus is dense in the closed solid torus. -/
theorem SolidTorus.closure_setOf_norm_lt_one :
    closure {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1} = univ := by
  have hS : {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1} =
      (((↑) : closedBall (0 : ℂ) 1 → ℂ) ⁻¹' ball 0 1) ×ˢ univ := by
    ext p
    simp
  rw [hS, closure_prod_eq, closure_univ, IsInducing.subtypeVal.closure_eq_preimage_closure_image,
    image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr ball_subset_closedBall,
    closure_ball _ one_ne_zero]
  ext p
  simp

/-- A map `Φ` from the solid torus, read near the point `(0, 1)` of its core as the map
`(u, t) ↦ Φ (u, exp (t i))` on `ℂ × ℝ`. It is extended by `0` off the closed unit disc, which does
not affect its germ at the origin; so the derivative of this reading at the origin is the
derivative of `Φ` at the core point `(0, 1)` in the coordinates `(u, t)`. -/
noncomputable def SolidTorus.coreReading {F : Type*} [Zero F] (Φ : SolidTorus → F) (v : ℂ × ℝ) :
    F :=
  if hv : ‖v.1‖ ≤ 1 then Φ (⟨v.1, mem_closedBall_zero_iff.2 hv⟩, Circle.exp v.2) else 0

section CoreReading

variable {F : Type*} [Zero F]

/-- On the closed unit disc the reading of `Φ` is `(u, t) ↦ Φ (u, exp (t i))`. -/
theorem SolidTorus.coreReading_of_norm_le (Φ : SolidTorus → F) {v : ℂ × ℝ} (hv : ‖v.1‖ ≤ 1) :
    coreReading Φ v = Φ (⟨v.1, mem_closedBall_zero_iff.2 hv⟩, Circle.exp v.2) := by
  simp only [coreReading, hv, ↓reduceDIte]

/-- Off the closed unit disc the reading of `Φ` is `0`. -/
theorem SolidTorus.coreReading_of_not_norm_le (Φ : SolidTorus → F) {v : ℂ × ℝ}
    (hv : ¬‖v.1‖ ≤ 1) : coreReading Φ v = 0 := by
  simp only [coreReading, hv, ↓reduceDIte]

/-- At the origin the reading of `Φ` is the core point `Φ (0, 1)`. -/
@[simp]
theorem SolidTorus.coreReading_zero (Φ : SolidTorus → F) : coreReading Φ 0 = Φ (0, 1) := by
  rw [coreReading_of_norm_le Φ (by simp)]
  congr
  simp

/-- Near the origin the reading of `Φ` is `(u, t) ↦ Φ (u, exp (t i))`. -/
theorem SolidTorus.eventually_coreReading_eq (Φ : SolidTorus → F) :
    ∀ᶠ v in 𝓝 (0 : ℂ × ℝ), ∃ hv : ‖v.1‖ ≤ 1,
      coreReading Φ v = Φ (⟨v.1, mem_closedBall_zero_iff.2 hv⟩, Circle.exp v.2) := by
  have hball : {v : ℂ × ℝ | ‖v.1‖ < 1} ∈ 𝓝 (0 : ℂ × ℝ) :=
    (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).mem_nhds (by simp)
  filter_upwards [hball] with v hv
  exact ⟨hv.le, coreReading_of_norm_le Φ hv.le⟩

/-- Near the origin the reading of `g ∘ Φ` is `g` composed with the reading of `Φ`. -/
theorem SolidTorus.coreReading_comp_eventuallyEq {F' : Type*} [Zero F'] (g : F → F')
    (Φ : SolidTorus → F) : coreReading (g ∘ Φ) =ᶠ[𝓝 0] g ∘ coreReading Φ := by
  filter_upwards [eventually_coreReading_eq (g ∘ Φ), eventually_coreReading_eq Φ] with v
    ⟨_, h₁⟩ ⟨_, h₂⟩
  rw [h₁, Function.comp_apply, Function.comp_apply, h₂]

end CoreReading

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- `Φ : D² × S¹ → X` is a **solid torus neighbourhood** of the loop `f : S¹ → X` when it is an
embedding whose core `{0} × S¹` traces `f`, and which maps the open solid torus
`{w | ‖w‖ < 1} × S¹` onto an open subset of `X`. The complement of that open subset is the
exterior of the knot `f`, and when `X` is Hausdorff its frontier is the boundary torus
(`TauCeti.IsSolidTorusNeighborhood.frontier_image`). -/
structure IsSolidTorusNeighborhood (f : Circle → X) (Φ : SolidTorus → X) : Prop where
  /-- The solid torus is embedded. -/
  isEmbedding : IsEmbedding Φ
  /-- The core circle of the solid torus traces the loop. -/
  apply_zero : ∀ z, Φ (0, z) = f z
  /-- The open solid torus is mapped onto an open set. -/
  isOpen_image : IsOpen (Φ '' {p | ‖(p.1 : ℂ)‖ < 1})

namespace IsSolidTorusNeighborhood

variable {f : Circle → X} {Φ : SolidTorus → X}

/-- The loop runs inside the image of the open solid torus. -/
theorem range_subset_image (h : IsSolidTorusNeighborhood f Φ) :
    range f ⊆ Φ '' {p | ‖(p.1 : ℂ)‖ < 1} := by
  rintro _ ⟨z, rfl⟩
  exact ⟨(0, z), by simp, h.apply_zero z⟩

/-- The solid torus is a neighbourhood of the loop. -/
theorem range_mem_nhdsSet (h : IsSolidTorusNeighborhood f Φ) : range Φ ∈ 𝓝ˢ (range f) :=
  Filter.mem_of_superset (h.isOpen_image.mem_nhdsSet.mpr h.range_subset_image)
    (image_subset_range _ _)

/-- A point of the solid torus lies on the knot exactly when it lies on the core `{0} × S¹`. -/
theorem apply_mem_range_iff (h : IsSolidTorusNeighborhood f Φ) (p : SolidTorus) :
    Φ p ∈ range f ↔ (p.1 : ℂ) = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    rw [← h.apply_zero z] at hz
    rw [← h.isEmbedding.injective hz]
    rfl
  · intro hp
    refine ⟨p.2, ?_⟩
    rw [← h.apply_zero]
    exact congrArg Φ (Prod.ext (Subtype.ext hp.symm) rfl)

/-- A solid torus neighbourhood in a Hausdorff space is a closed embedding. -/
theorem isClosedEmbedding [T2Space X] (h : IsSolidTorusNeighborhood f Φ) :
    IsClosedEmbedding Φ :=
  h.isEmbedding.continuous.isClosedEmbedding h.isEmbedding.injective

/-- A loop with a solid torus neighbourhood has compact image, the image of the core circle. -/
theorem isCompact_range (h : IsSolidTorusNeighborhood f Φ) : IsCompact (range f) := by
  have hcore : f = fun z ↦ Φ (0, z) := funext fun z ↦ (h.apply_zero z).symm
  rw [hcore]
  exact _root_.isCompact_range
    (h.isEmbedding.continuous.comp (continuous_const.prodMk continuous_id))

/-- A loop with a solid torus neighbourhood in a Hausdorff space has closed image. -/
theorem isClosed_range [T2Space X] (h : IsSolidTorusNeighborhood f Φ) : IsClosed (range f) :=
  h.isCompact_range.isClosed

/-- A solid torus neighbourhood is carried along an open embedding of the ambient space, such as
the inclusion of an open subset or a homeomorphism. -/
theorem comp {e : X → Y} (he : IsOpenEmbedding e) (h : IsSolidTorusNeighborhood f Φ) :
    IsSolidTorusNeighborhood (e ∘ f) (e ∘ Φ) where
  isEmbedding := he.isEmbedding.comp h.isEmbedding
  apply_zero z := congrArg e (h.apply_zero z)
  isOpen_image := by
    rw [image_comp]
    exact he.isOpenMap _ h.isOpen_image

/-- A solid torus neighbourhood is carried along a reparametrization of the loop by a
homeomorphism `g` of the circle: `(w, z) ↦ Φ (w, g z)` is a solid torus neighbourhood of `f ∘ g`. -/
theorem comp_prodMap (h : IsSolidTorusNeighborhood f Φ) (g : Circle ≃ₜ Circle) :
    IsSolidTorusNeighborhood (f ∘ g) (Φ ∘ Prod.map id g) where
  isEmbedding := h.isEmbedding.comp ((Homeomorph.refl _).prodCongr g).isEmbedding
  apply_zero z := h.apply_zero (g z)
  isOpen_image := by
    rw [image_comp]
    convert h.isOpen_image using 2
    exact ((Homeomorph.refl _).prodCongr g).image_eq_preimage_symm _

/-- In a Hausdorff ambient space, the frontier of the image of the open solid torus is the image
of the boundary torus `{w | ‖w‖ = 1} × S¹`. This set is also the frontier of the exterior of the
knot, the complement of the image of the open solid torus. -/
theorem frontier_image [T2Space X] (h : IsSolidTorusNeighborhood f Φ) :
    frontier (Φ '' {p | ‖(p.1 : ℂ)‖ < 1}) = range (Φ ∘ SolidTorus.boundaryInclusion) := by
  rw [h.isOpen_image.frontier_eq, h.isClosedEmbedding.closure_image_eq,
    SolidTorus.closure_setOf_norm_lt_one, ← image_sdiff h.isEmbedding.injective, range_comp,
    SolidTorus.range_boundaryInclusion]
  congr 1
  ext p
  have hp : ‖(p.1 : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp p.1.2
  simp only [mem_sdiff, mem_univ, mem_ofPred_eq, true_and, not_lt]
  exact ⟨fun h' => le_antisymm hp h', fun h' => h'.ge⟩

/-- The boundary torus of a solid torus neighbourhood is embedded: by
`TauCeti.IsSolidTorusNeighborhood.frontier_image`, the frontier of the knot exterior is a
torus when the ambient space is Hausdorff. -/
theorem isEmbedding_comp_boundaryInclusion (h : IsSolidTorusNeighborhood f Φ) :
    IsEmbedding (Φ ∘ SolidTorus.boundaryInclusion) :=
  h.isEmbedding.comp SolidTorus.isEmbedding_boundaryInclusion

/-- The boundary torus of the knot exterior is disjoint from the knot. -/
theorem frontier_subset_compl_range [T2Space X] (h : IsSolidTorusNeighborhood f Φ) :
    frontier (Φ '' {p | ‖(p.1 : ℂ)‖ < 1})ᶜ ⊆ (range f)ᶜ := by
  rw [frontier_compl, h.frontier_image]
  rintro _ ⟨q, rfl⟩
  rw [mem_compl_iff, comp_apply, h.apply_mem_range_iff, ← norm_eq_zero,
    SolidTorus.coe_boundaryInclusion_fst, Circle.norm_coe]
  exact one_ne_zero

/-- The framing identifies the boundary torus with the frontier of the knot exterior,
the complement of the image of the open solid torus. -/
noncomputable def exteriorFrontierHomeomorph [T2Space X] (h : IsSolidTorusNeighborhood f Φ) :
    Circle × Circle ≃ₜ frontier (Φ '' {p | ‖(p.1 : ℂ)‖ < 1})ᶜ :=
  h.isEmbedding_comp_boundaryInclusion.toHomeomorph.trans
    (Homeomorph.setCongr (by rw [frontier_compl, h.frontier_image]))

/-- The frontier parametrization is the restriction of the solid torus framing. -/
@[simp]
theorem coe_exteriorFrontierHomeomorph_apply [T2Space X]
    (h : IsSolidTorusNeighborhood f Φ) (q : Circle × Circle) :
    (h.exteriorFrontierHomeomorph q : X) = Φ (SolidTorus.boundaryInclusion q) := by
  simp only [exteriorFrontierHomeomorph, Homeomorph.trans_apply,
    Homeomorph.setCongr_apply, IsEmbedding.toHomeomorph_apply_coe, Function.comp_apply]

end IsSolidTorusNeighborhood

/-! ### Reflecting the disc -/

section ConjDisc

open scoped ComplexConjugate

/-- The reflection `(u, w) ↦ (conj u, w)` of the solid torus. Precomposing a solid torus with it
reverses its orientation at the core point, see `SolidTorusNeighborhood/Orientation.lean`. -/
noncomputable def SolidTorus.conjDisc : SolidTorus ≃ₜ SolidTorus where
  toFun p := (Complex.conjLIE.toLinearIsometry.unitClosedBallMap p.1, p.2)
  invFun p := (Complex.conjLIE.toLinearIsometry.unitClosedBallMap p.1, p.2)
  left_inv p := Prod.ext (Subtype.ext (by simp)) rfl
  right_inv p := Prod.ext (Subtype.ext (by simp)) rfl
  continuous_toFun :=
    ((LinearIsometry.continuous_unitClosedBallMap _).comp continuous_fst).prodMk continuous_snd
  continuous_invFun :=
    ((LinearIsometry.continuous_unitClosedBallMap _).comp continuous_fst).prodMk continuous_snd

namespace SolidTorus

/-- The reflection conjugates the disc coordinate. -/
@[simp]
theorem coe_conjDisc_fst (p : SolidTorus) : ((conjDisc p).1 : ℂ) = conj (p.1 : ℂ) := by
  simp [conjDisc]

/-- The reflection keeps the circle coordinate. -/
@[simp]
theorem conjDisc_snd (p : SolidTorus) : (conjDisc p).2 = p.2 :=
  (rfl)

/-- The reflection is an involution. -/
@[simp]
theorem conjDisc_conjDisc (p : SolidTorus) : conjDisc (conjDisc p) = p :=
  conjDisc.symm_apply_apply p

/-- The reflection fixes the core circle. -/
@[simp]
theorem conjDisc_zero (z : Circle) : conjDisc (0, z) = (0, z) :=
  Prod.ext (Subtype.ext (by simp)) (by simp)

end SolidTorus

/-- Precomposing a solid torus neighbourhood with the reflection `(u, w) ↦ (conj u, w)` gives a
solid torus neighbourhood of the same loop. -/
theorem IsSolidTorusNeighborhood.comp_conjDisc {X : Type*} [TopologicalSpace X]
    {f : Circle → X} {Φ : SolidTorus → X} (h : IsSolidTorusNeighborhood f Φ) :
    IsSolidTorusNeighborhood f (Φ ∘ SolidTorus.conjDisc) where
  isEmbedding := h.isEmbedding.comp SolidTorus.conjDisc.isEmbedding
  apply_zero z := by
    rw [Function.comp_apply, SolidTorus.conjDisc_zero, h.apply_zero]
  isOpen_image := by
    have himage : SolidTorus.conjDisc '' {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1} =
        {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1} := by
      ext p
      refine ⟨?_, fun hp ↦ ⟨SolidTorus.conjDisc p, by simpa using hp,
        SolidTorus.conjDisc_conjDisc p⟩⟩
      rintro ⟨q, hq, rfl⟩
      simpa using hq
    rw [Set.image_comp, himage]
    exact h.isOpen_image

end ConjDisc

end General

/-! ### Existence for embedded circles in `ℝ³` -/

section Euclidean

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The velocity of a loop `f` at `z`, for the counterclockwise unit-speed parametrization of the
circle. -/
private noncomputable def tangentVector (f : Circle → V) (z : Circle) : V :=
  deriv (fun θ => f (z * Circle.exp θ)) 0

private theorem tangentVector_circleExp (f : Circle → V) (t : ℝ) :
    tangentVector f (Circle.exp t) = deriv (f ∘ Circle.exp) t := by
  rw [tangentVector]
  simp_rw [← Circle.exp_add]
  simpa using deriv_comp_const_add (f ∘ Circle.exp) t 0

private theorem continuous_tangentVector {f : Circle → V} (hf : ContMDiff (𝓡 1) 𝓘(ℝ, V) 2 f) :
    Continuous (tangentVector f) := by
  rw [(Circle.isCoveringMap_exp.isQuotientMap Circle.exp_surjective).continuous_iff]
  have hγ : ContDiff ℝ 2 (f ∘ Circle.exp) :=
    contMDiff_iff_contDiff.mp (hf.comp contMDiff_circleExp)
  convert hγ.continuous_deriv one_le_two using 1
  ext1 t
  exact tangentVector_circleExp f t

/-- The velocity of a `C¹` immersed loop is nonzero, and the normal space is its orthogonal
complement. -/
private theorem tangentVector_ne_zero_and_mem_normalSubspace_iff {f : Circle → V}
    (hf : ContMDiff (𝓡 1) 𝓘(ℝ, V) 1 f) (himm : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, V) f z))
    (z : Circle) :
    tangentVector f z ≠ 0 ∧
      ∀ v, v ∈ normalSubspace (𝓡 1) f z ↔ ⟪tangentVector f z, v⟫ = 0 := by
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  obtain ⟨hne, hrange⟩ :=
    deriv_comp_circleExp_ne_zero_and_range_mfderiv hf himm t
  rw [tangentVector_circleExp]
  refine ⟨hne, fun v => ?_⟩
  rw [normalSubspace, hrange]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right

/-- Some vector is nowhere tangent to a `C²` loop in a space of dimension at least three: the
tangent lines of the loop form the image of a `C¹` map from the plane. -/
private theorem exists_forall_notMem_span_tangentVector
    (hV : 2 < Module.finrank ℝ V) {f : Circle → V} (hf : ContMDiff (𝓡 1) 𝓘(ℝ, V) 2 f) :
    ∃ a : V, ∀ z, a ∉ ℝ ∙ tangentVector f z := by
  have hγ : ContDiff ℝ (1 + 1) (f ∘ Circle.exp) :=
    contMDiff_iff_contDiff.mp (hf.comp contMDiff_circleExp)
  have hd : Differentiable ℝ (deriv (f ∘ Circle.exp)) :=
    (contDiff_succ_iff_deriv.mp hγ).2.2.differentiable one_ne_zero
  set F : ℝ × ℝ → V := fun p => p.1 • deriv (f ∘ Circle.exp) p.2
  have hF : Differentiable ℝ F := differentiable_fst.smul (hd.comp differentiable_snd)
  obtain ⟨a, ha⟩ := (hF.dense_compl_range_of_finrank_lt_finrank (by simpa using hV)).nonempty
  refine ⟨a, fun z hz => ?_⟩
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  rw [tangentVector_circleExp] at hz
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hz
  exact ha ⟨(s, t), hs⟩

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A `C²` immersed circle in `ℝ³` has a continuous orthonormal frame `n₁, n₂` of its normal
planes. The first vector is the normalized normal component of a vector `a` that is nowhere
tangent to the circle, and the second is the cross product of the unit tangent with the first. -/
private theorem exists_normalFrame {f : Circle → ℝ³} (hf : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ³) 2 f)
    (himm : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ³) f z)) :
    ∃ n₁ n₂ : Circle → ℝ³, Continuous n₁ ∧ Continuous n₂ ∧ ∀ z,
      ‖n₁ z‖ = 1 ∧ ‖n₂ z‖ = 1 ∧ ⟪n₁ z, n₂ z⟫ = 0 ∧
      ∀ v, v ∈ normalSubspace (𝓡 1) f z ↔ v = ⟪n₁ z, v⟫ • n₁ z + ⟪n₂ z, v⟫ • n₂ z := by
  have hτ := tangentVector_ne_zero_and_mem_normalSubspace_iff (hf.of_le one_le_two) himm
  obtain ⟨a, ha⟩ := exists_forall_notMem_span_tangentVector (by simp) hf
  -- The unit tangent `u`, and the component `p` of `a` orthogonal to it.
  set u : Circle → ℝ³ := fun z => ‖tangentVector f z‖⁻¹ • tangentVector f z
  set p : Circle → ℝ³ := fun z => a - ⟪u z, a⟫ • u z
  have hu : ∀ z, ‖u z‖ = 1 := fun z => norm_smul_inv_norm (hτ z).1
  have hp : ∀ z, p z ≠ 0 := fun z h0 => ha z <| by
    rw [sub_eq_zero] at h0
    rw [h0]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hup : ∀ z, ⟪u z, p z⟫ = 0 := fun z => by
    simp only [p, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow,
      mul_one, sub_self]
  have hnormal : ∀ z v, v ∈ normalSubspace (𝓡 1) f z ↔ ⟪u z, v⟫ = 0 := fun z v => by
    rw [(hτ z).2, real_inner_smul_left, mul_eq_zero, inv_eq_zero, norm_eq_zero]
    simp [(hτ z).1]
  have hcu : Continuous u :=
    ((continuous_tangentVector hf).norm.inv₀ fun z => norm_ne_zero_iff.mpr (hτ z).1).smul
      (continuous_tangentVector hf)
  have hcp : Continuous p := by fun_prop
  set n₁ : Circle → ℝ³ := fun z => ‖p z‖⁻¹ • p z
  have hn₁ : ∀ z, ‖n₁ z‖ = 1 := fun z => norm_smul_inv_norm (hp z)
  have hun₁ : ∀ z, ⟪u z, n₁ z⟫ = 0 := fun z => by
    simp only [n₁, real_inner_smul_right, hup, mul_zero]
  have hcn₁ : Continuous n₁ := (hcp.norm.inv₀ fun z => norm_ne_zero_iff.mpr (hp z)).smul hcp
  clear_value u p n₁
  refine ⟨n₁, fun z => toLp 2 (ofLp (u z) ⨯₃ ofLp (n₁ z)), hcn₁, ?_, fun z => ?_⟩
  · refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    fin_cases i <;> simp only [cross_apply] <;> fun_prop
  · obtain ⟨hc, huc, hnc, hdecomp⟩ := cross_orthonormal (hu z) (hn₁ z) (hun₁ z)
    refine ⟨hn₁ z, hc, hnc, fun v => ⟨fun hv => hdecomp v ((hnormal z v).mp hv), fun hv => ?_⟩⟩
    rw [hnormal, hv, inner_add_right, real_inner_smul_right, real_inner_smul_right, hun₁, huc]
    ring

/-- A `C²` immersed circle in `ℝ³` has a family of linear isometries `ψ z : ℂ →ₗᵢ[ℝ] ℝ³` onto
its normal planes, continuous as a family of continuous linear maps:
`ψ z w = re w • n₁ z + im w • n₂ z` for the frame of `exists_normalFrame`. -/
private theorem exists_normalDisc {f : Circle → ℝ³} (hf : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ³) 2 f)
    (himm : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ³) f z)) :
    ∃ ψ : Circle → ℂ →ₗᵢ[ℝ] ℝ³, Continuous (fun z => (ψ z).toContinuousLinearMap) ∧ ∀ z,
      (∀ w, ψ z w ∈ normalSubspace (𝓡 1) f z) ∧
      ∀ v ∈ normalSubspace (𝓡 1) f z, ∃ w, ψ z w = v := by
  obtain ⟨n₁, n₂, hc₁, hc₂, hn⟩ := exists_normalFrame hf himm
  -- The coordinates of `ψ z w` in the frame are the real and imaginary parts of `w`.
  have h₁ : ∀ z (w : ℂ), ⟪n₁ z, w.re • n₁ z + w.im • n₂ z⟫ = w.re := fun z w => by
    simp [inner_add_right, real_inner_smul_right, (hn z).1, (hn z).2.2.1]
  have h₂ : ∀ z (w : ℂ), ⟪n₂ z, w.re • n₁ z + w.im • n₂ z⟫ = w.im := fun z w => by
    simp [inner_add_right, real_inner_smul_right, (hn z).2.1, real_inner_comm (n₁ z),
      (hn z).2.2.1]
  -- The continuous linear maps `φ z`, which are isometries by the orthonormality of the frame.
  let φ : Circle → ℂ →L[ℝ] ℝ³ := fun z =>
    Complex.reCLM.smulRight (n₁ z) + Complex.imCLM.smulRight (n₂ z)
  have hφ (z : Circle) (w : ℂ) : φ z w = w.re • n₁ z + w.im • n₂ z := by simp [φ]
  let ψ : Circle → ℂ →ₗᵢ[ℝ] ℝ³ := fun z =>
    { toLinearMap := φ z
      norm_map' := fun w => by
        rw [ContinuousLinearMap.coe_coe, hφ, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
          Complex.sq_norm, Complex.normSq_apply, ← real_inner_self_eq_norm_sq, inner_add_left,
          real_inner_smul_left, real_inner_smul_left, h₁, h₂] }
  refine ⟨ψ, ((ContinuousLinearMap.smulRightL ℝ ℂ ℝ³ Complex.reCLM).continuous.comp hc₁).add
    ((ContinuousLinearMap.smulRightL ℝ ℂ ℝ³ Complex.imCLM).continuous.comp hc₂),
    fun z => ⟨fun w => ?_, fun v hv => ⟨⟪n₁ z, v⟫ + ⟪n₂ z, v⟫ * Complex.I, ?_⟩⟩⟩
  · rw [(hn z).2.2.2, LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe, hφ, h₁, h₂]
  · rw [(hn z).2.2.2] at hv
    rw [LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe, hφ]
    simpa using hv.symm

/-- Let `ψ` be a continuous family of continuous linear maps `ψ z : ℂ → V` along a `C²` immersed
circle `f`, with `ψ 1` injective and valued in the normal plane at `1`. For `r ≠ 0`, the tube
`(u, t) ↦ f (exp (t i)) + r • ψ (exp (t i)) u` is differentiable at the origin with injective
derivative `(u, t) ↦ t • τ + r • ψ 1 u`, for the velocity `τ` of `f` at `1`. -/
private theorem exists_hasFDerivAt_tube {f : Circle → V} (hf : ContMDiff (𝓡 1) 𝓘(ℝ, V) 2 f)
    (himm : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, V) f z)) {ψ : Circle → ℂ →L[ℝ] V}
    (hψc : Continuous ψ) (hψn : ∀ w, ψ 1 w ∈ normalSubspace (𝓡 1) f 1) (hψinj : Injective (ψ 1))
    {r : ℝ} (hr : r ≠ 0) :
    ∃ L : ℂ × ℝ →L[ℝ] V,
      HasFDerivAt (fun v : ℂ × ℝ => f (Circle.exp v.2) + r • ψ (Circle.exp v.2) v.1) L 0 ∧
        Injective L := by
  -- The first term has derivative `t ↦ t • τ`, and the second is linear in `u` with coefficients
  -- continuous in `t`.
  set τ := tangentVector f 1
  have hγ : HasDerivAt (f ∘ Circle.exp) τ 0 := by
    have hd : ContDiff ℝ 2 (f ∘ Circle.exp) :=
      contMDiff_iff_contDiff.mp (hf.comp contMDiff_circleExp)
    have := (hd.differentiable two_ne_zero 0).hasDerivAt
    rwa [← tangentVector_circleExp, Circle.exp_zero] at this
  have hA : ContinuousAt (fun t : ℝ => r • ψ (Circle.exp t)) 0 :=
    ((hψc.comp Circle.exp.continuous).const_smul r).continuousAt
  have hlin : HasFDerivAt (fun q : ℂ × ℝ => (r • ψ (Circle.exp q.2)) q.1)
      ((r • ψ (Circle.exp 0)).comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) 0 := by
    simpa only [Prod.mk_zero_zero] using hA.hasFDerivAt_clm_apply_zero
  have hcore := (HasFDerivAt.comp (x := (0 : ℂ × ℝ)) (g := f ∘ Circle.exp)
    hγ.hasFDerivAt (hasFDerivAt_snd (𝕜 := ℝ) (E := ℂ) (F := ℝ))).add hlin
  refine ⟨_, hcore.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => by simp),
    (injective_iff_map_eq_zero _).2 fun x hx => ?_⟩
  -- `τ` is nonzero and orthogonal to the normal plane containing the values of `ψ 1`.
  obtain ⟨hτ, hτn⟩ := tangentVector_ne_zero_and_mem_normalSubspace_iff (hf.of_le one_le_two) himm 1
  replace hx : x.2 • τ + r • ψ 1 x.1 = 0 := by simpa using hx
  have ht : x.2 = 0 := by
    have hτψ : ⟪τ, ψ 1 x.1⟫ = 0 := (hτn _).1 (hψn x.1)
    have h := congrArg (fun y => ⟪τ, y⟫) hx
    simp only [inner_add_right, real_inner_smul_right, hτψ, real_inner_self_eq_norm_sq,
      mul_zero, add_zero, inner_zero_right] at h
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 (norm_ne_zero_iff.mpr hτ))
  rw [ht, zero_smul, zero_add, smul_eq_zero] at hx
  exact Prod.ext (hψinj ((hx.resolve_left hr).trans (map_zero _).symm)) ht

/-- **Solid torus neighbourhoods of knots in `ℝ³`, with their derivative at the core.** A `C²`
embedded circle `f` in `ℝ³` has a solid torus neighbourhood `Φ` inside any neighbourhood of its
image, whose reading `(u, t) ↦ Φ (u, exp (t i))` at the core point `(0, 1)`
(`TauCeti.SolidTorus.coreReading`) is differentiable at the origin with injective derivative. -/
theorem exists_isSolidTorusNeighborhood_hasFDerivAt_coreReading {f : Circle → ℝ³}
    (hf : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ³) 2 f) (himm : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ³) f z))
    (hinj : Injective f) {U : Set ℝ³} (hU : U ∈ 𝓝ˢ (range f)) :
    ∃ Φ : SolidTorus → ℝ³, IsSolidTorusNeighborhood f Φ ∧ range Φ ⊆ U ∧
      ∃ L : ℂ × ℝ →L[ℝ] ℝ³, HasFDerivAt (SolidTorus.coreReading Φ) L 0 ∧ Injective L := by
  -- The tubular neighbourhood of radius `ε`, and a radius `r < ε` keeping the tube inside `U`.
  obtain ⟨ε, hε, hemb⟩ := exists_isOpenEmbedding_normalTube hf himm hinj
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_range hf.continuous).exists_thickening_subset_open
    isOpen_interior (subset_interior_iff_mem_nhdsSet.mpr hU)
  obtain ⟨r, hr, hrmin⟩ := exists_between (lt_min hε hδ)
  obtain ⟨hrε, hrδ⟩ := lt_min_iff.mp hrmin
  -- `Φ (w, z)` is the point `r w` of the normal disc at `z`.
  obtain ⟨ψ, hψc, hψ⟩ := exists_normalDisc hf himm
  have hψc' : Continuous fun q : SolidTorus => ψ q.2 q.1 :=
    (hψc.comp continuous_snd).clm_apply (continuous_subtype_val.comp continuous_fst)
  have hnorm : ∀ q : SolidTorus, ‖r • ψ q.2 q.1‖ = r * ‖(q.1 : ℂ)‖ := fun q => by
    rw [norm_smul, (ψ q.2).norm_map, Real.norm_of_nonneg hr.le]
  have hle : ∀ q : SolidTorus, ‖r • ψ q.2 q.1‖ ≤ r := fun q => by
    rw [hnorm]
    exact mul_le_of_le_one_right hr.le (mem_closedBall_zero_iff.mp q.1.2)
  have hmem : ∀ q : SolidTorus, (q.2, r • ψ q.2 q.1) ∈ normalTube (𝓡 1) f ε := fun q =>
    mem_normalTube.mpr ⟨Submodule.smul_mem _ _ ((hψ q.2).1 _), (hle q).trans_lt hrε⟩
  have hinj : Injective fun q : SolidTorus => f q.2 + r • ψ q.2 q.1 := fun q q' h => by
    have h' := hemb.injective (a₁ := ⟨_, hmem q⟩) (a₂ := ⟨_, hmem q'⟩) h
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at h'
    obtain ⟨h₂, h₁⟩ := h'
    rw [h₂] at h₁
    exact Prod.ext (Subtype.ext ((ψ _).injective (smul_right_injective _ hr.ne' h₁))) h₂
  refine ⟨fun q => f q.2 + r • ψ q.2 q.1, ⟨((hf.continuous.comp continuous_snd).add
    (hψc'.const_smul r)).isClosedEmbedding hinj |>.isEmbedding, fun z => ?_, ?_⟩, ?_, ?_⟩
  · dsimp only
    rw [Metric.unitClosedBall.coe_zero, map_zero, smul_zero, add_zero]
  · -- The open solid torus is mapped onto the normal vectors of length less than `r`.
    convert hemb.isOpenMap {q | ‖(q : Circle × ℝ³).2‖ < r}
      (isOpen_lt (continuous_norm.comp (continuous_snd.comp continuous_subtype_val))
        continuous_const) using 1
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨_, hmem q⟩, ?_, rfl⟩
      rw [mem_ofPred_eq, hnorm]
      exact mul_lt_of_lt_one_right hr hq
    · rintro ⟨⟨⟨z, v⟩, hzv⟩, hvr, rfl⟩
      rw [mem_ofPred_eq] at hvr
      obtain ⟨w, hw⟩ := (hψ z).2 _ (Submodule.smul_mem _ r⁻¹ (mem_normalTube.mp hzv).1)
      have hwn : ‖w‖ < 1 := by
        rw [← (ψ z).norm_map, hw, norm_smul, norm_inv, Real.norm_of_nonneg hr.le]
        exact (inv_mul_lt_one₀ hr).mpr hvr
      refine ⟨(⟨w, mem_closedBall_zero_iff.mpr hwn.le⟩, z), hwn, ?_⟩
      simp [hw, smul_smul, mul_inv_cancel₀ hr.ne']
  · rintro _ ⟨q, rfl⟩
    refine interior_subset (hδU (mem_thickening_iff.mpr ⟨f q.2, mem_range_self _, ?_⟩))
    rw [dist_eq_norm, add_sub_cancel_left]
    exact (hle q).trans_lt hrδ
  · -- Near the origin the reading is the tube `(u, t) ↦ f (exp (t i)) + r • ψ (exp (t i)) u`.
    obtain ⟨L, hL, hLinj⟩ := exists_hasFDerivAt_tube hf himm hψc (hψ 1).1 (ψ 1).injective hr.ne'
    refine ⟨L, hL.congr_of_eventuallyEq ?_, hLinj⟩
    filter_upwards [SolidTorus.eventually_coreReading_eq
      (fun q : SolidTorus => f q.2 + r • ψ q.2 q.1)] with v ⟨_, hv⟩
    simp [hv]

/-- **Solid torus neighbourhoods of knots in `ℝ³`.** A `C²` embedded circle in `ℝ³` has a solid
torus neighbourhood inside any neighbourhood of its image. -/
theorem exists_isSolidTorusNeighborhood {f : Circle → ℝ³} (hf : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ³) 2 f)
    (himm : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ³) f z)) (hinj : Injective f)
    {U : Set ℝ³} (hU : U ∈ 𝓝ˢ (range f)) :
    ∃ Φ : SolidTorus → ℝ³, IsSolidTorusNeighborhood f Φ ∧ range Φ ⊆ U :=
  let ⟨Φ, hΦ, hΦU, _⟩ := exists_isSolidTorusNeighborhood_hasFDerivAt_coreReading hf himm hinj hU
  ⟨Φ, hΦ, hΦU⟩

end Euclidean

end TauCeti
