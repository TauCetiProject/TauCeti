/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.LowDimTopology.SeifertFibration

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.MetricSpace.HausdorffDimension
import TauCeti.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.TubularNeighborhood.Euclidean

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

## Main definitions

* `TauCeti.IsSolidTorusNeighborhood f Φ`: `Φ : D² × S¹ → X` is a solid torus neighbourhood of
  the loop `f`.
* `TauCeti.SolidTorus.boundaryInclusion`: the inclusion of the boundary torus `S¹ × S¹` into the
  solid torus.

## Main results

* `TauCeti.IsSolidTorusNeighborhood.frontier_image`: the frontier of the image of the open solid
  torus, which is also the frontier of the knot exterior, is the image of the boundary torus
  when the ambient space is Hausdorff.
* `TauCeti.IsSolidTorusNeighborhood.isEmbedding_comp_boundaryInclusion`: the boundary torus
  `S¹ × S¹` embeds.
* `TauCeti.IsSolidTorusNeighborhood.comp`: solid torus neighbourhoods are carried along open
  embeddings of the ambient space.
* `TauCeti.exists_isSolidTorusNeighborhood`: a `C²` embedded circle in `ℝ³` has a solid torus
  neighbourhood inside any neighbourhood of its image.

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

/-- The boundary torus is the set of points `(w, z)` of the solid torus with `‖w‖ = 1`. -/
theorem SolidTorus.range_boundaryInclusion :
    range SolidTorus.boundaryInclusion = {p : SolidTorus | ‖(p.1 : ℂ)‖ = 1} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simp
  · intro hp
    exact ⟨(⟨p.1, mem_sphere_zero_iff_norm.mpr hp⟩, p.2), rfl⟩

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

/-- A solid torus neighbourhood in a Hausdorff space is a closed embedding. -/
theorem isClosedEmbedding [T2Space X] (h : IsSolidTorusNeighborhood f Φ) :
    IsClosedEmbedding Φ :=
  h.isEmbedding.continuous.isClosedEmbedding h.isEmbedding.injective

/-- A solid torus neighbourhood is carried along an open embedding of the ambient space, such as
the inclusion of an open subset or a homeomorphism. -/
theorem comp {e : X → Y} (he : IsOpenEmbedding e) (h : IsSolidTorusNeighborhood f Φ) :
    IsSolidTorusNeighborhood (e ∘ f) (e ∘ Φ) where
  isEmbedding := he.isEmbedding.comp h.isEmbedding
  apply_zero z := congrArg e (h.apply_zero z)
  isOpen_image := by
    rw [image_comp]
    exact he.isOpenMap _ h.isOpen_image

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

end IsSolidTorusNeighborhood

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

/-- The velocity of a `C²` immersed loop is nonzero, and the normal space is its orthogonal
complement. -/
private theorem tangentVector_ne_zero_and_mem_normalSubspace_iff {f : Circle → V}
    (hf : ContMDiff (𝓡 1) 𝓘(ℝ, V) 2 f) (himm : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, V) f z))
    (z : Circle) :
    tangentVector f z ≠ 0 ∧
      ∀ v, v ∈ normalSubspace (𝓡 1) f z ↔ ⟪tangentVector f z, v⟫ = 0 := by
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  obtain ⟨hne, hrange⟩ :=
    deriv_comp_circleExp_ne_zero_and_range_mfderiv (hf.of_le one_le_two) himm t
  rw [tangentVector_circleExp]
  refine ⟨hne, fun v => ?_⟩
  set D : EuclideanSpace ℝ (Fin 1) →L[ℝ] V := mfderiv (𝓡 1) 𝓘(ℝ, V) f (Circle.exp t)
  rw [mem_normalSubspace_iff]
  constructor
  · intro hv
    obtain ⟨w, hw⟩ : deriv (f ∘ Circle.exp) t ∈ (D : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] V).range :=
      hrange ▸ Submodule.mem_span_singleton_self _
    rw [real_inner_comm, ← hw]
    exact hv w
  · intro hv w
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (hrange ▸ LinearMap.mem_range_self (D : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] V) w)
    refine (congrArg (fun x => ⟪v, x⟫) hc.symm).trans ?_
    rw [real_inner_smul_right, real_inner_comm, hv, mul_zero]

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
  have hτ := tangentVector_ne_zero_and_mem_normalSubspace_iff hf himm
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
    have h₁ : Continuous fun z => ofLp (u z) := (PiLp.continuous_ofLp 2 _).comp hcu
    have h₂ : Continuous fun z => ofLp (n₁ z) := (PiLp.continuous_ofLp 2 _).comp hcn₁
    fin_cases i <;> simp only [cross_apply] <;> fun_prop
  · obtain ⟨hc, huc, hnc, hdecomp⟩ := cross_orthonormal (hu z) (hn₁ z) (hun₁ z)
    refine ⟨hn₁ z, hc, hnc, fun v => ⟨fun hv => hdecomp v ((hnormal z v).mp hv), fun hv => ?_⟩⟩
    rw [hnormal, hv, inner_add_right, real_inner_smul_right, real_inner_smul_right, hun₁, huc]
    ring

/-- A `C²` immersed circle in `ℝ³` has a continuous family of linear isometries `ψ z : ℂ → ℝ³`
onto its normal planes: `ψ z w = re w • n₁ z + im w • n₂ z` for the frame of
`exists_normalFrame`. -/
private theorem exists_normalDisc {f : Circle → ℝ³} (hf : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ³) 2 f)
    (himm : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ³) f z)) :
    ∃ ψ : Circle → ℂ → ℝ³, Continuous (fun q : SolidTorus => ψ q.2 q.1) ∧ ∀ z,
      (∀ w, ψ z w ∈ normalSubspace (𝓡 1) f z) ∧ (∀ w, ‖ψ z w‖ = ‖w‖) ∧ Injective (ψ z) ∧
      ∀ v ∈ normalSubspace (𝓡 1) f z, ∃ w, ψ z w = v := by
  obtain ⟨n₁, n₂, hc₁, hc₂, hn⟩ := exists_normalFrame hf himm
  -- The coordinates of `ψ z w` in the frame are the real and imaginary parts of `w`.
  have h₁ : ∀ z (w : ℂ), ⟪n₁ z, w.re • n₁ z + w.im • n₂ z⟫ = w.re := fun z w => by
    simp [inner_add_right, real_inner_smul_right, (hn z).1, (hn z).2.2.1]
  have h₂ : ∀ z (w : ℂ), ⟪n₂ z, w.re • n₁ z + w.im • n₂ z⟫ = w.im := fun z w => by
    simp [inner_add_right, real_inner_smul_right, (hn z).2.1, real_inner_comm (n₁ z),
      (hn z).2.2.1]
  refine ⟨fun z w => w.re • n₁ z + w.im • n₂ z, by fun_prop, fun z => ⟨fun w => ?_, fun w => ?_,
    fun w w' h => ?_, fun v hv => ⟨⟪n₁ z, v⟫ + ⟪n₂ z, v⟫ * Complex.I, ?_⟩⟩⟩
  · rw [(hn z).2.2.2, h₁, h₂]
  · rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply,
      ← real_inner_self_eq_norm_sq, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      h₁, h₂]
  · dsimp only at h
    exact Complex.ext ((h₁ z w).symm.trans (h ▸ h₁ z w')) ((h₂ z w).symm.trans (h ▸ h₂ z w'))
  · rw [(hn z).2.2.2] at hv
    simp [← hv]

/-- **Solid torus neighbourhoods of knots in `ℝ³`.** A `C²` embedded circle in `ℝ³` has a solid
torus neighbourhood inside any neighbourhood of its image. -/
theorem exists_isSolidTorusNeighborhood {f : Circle → ℝ³} (hf : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ³) 2 f)
    (himm : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ³) f z)) (hinj : Injective f)
    {U : Set ℝ³} (hU : U ∈ 𝓝ˢ (range f)) :
    ∃ Φ : SolidTorus → ℝ³, IsSolidTorusNeighborhood f Φ ∧ range Φ ⊆ U := by
  -- The tubular neighbourhood of radius `ε`, and a radius `r < ε` keeping the tube inside `U`.
  obtain ⟨ε, hε, hemb⟩ := exists_isOpenEmbedding_normalTube hf himm hinj
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_range hf.continuous).exists_thickening_subset_open
    isOpen_interior (subset_interior_iff_mem_nhdsSet.mpr hU)
  obtain ⟨r, hr, hrε, hrδ⟩ : ∃ r, 0 < r ∧ r < ε ∧ r < δ :=
    ⟨min (ε / 2) (δ / 2), lt_min (half_pos hε) (half_pos hδ),
      (min_le_left _ _).trans_lt (half_lt_self hε), (min_le_right _ _).trans_lt (half_lt_self hδ)⟩
  -- `Φ (w, z)` is the point `r w` of the normal disc at `z`.
  obtain ⟨ψ, hψc, hψ⟩ := exists_normalDisc hf himm
  have hnorm : ∀ q : SolidTorus, ‖r • ψ q.2 q.1‖ = r * ‖(q.1 : ℂ)‖ := fun q => by
    rw [norm_smul, (hψ q.2).2.1, Real.norm_of_nonneg hr.le]
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
    exact Prod.ext (Subtype.ext ((hψ _).2.2.1 (smul_right_injective _ hr.ne' h₁))) h₂
  refine ⟨fun q => f q.2 + r • ψ q.2 q.1, ⟨((hf.continuous.comp continuous_snd).add
    (hψc.const_smul r)).isClosedEmbedding hinj |>.isEmbedding, fun z => ?_, ?_⟩, ?_⟩
  · dsimp only
    rw [Metric.unitClosedBall.coe_zero, norm_eq_zero.mp (((hψ z).2.1 0).trans norm_zero),
      smul_zero, add_zero]
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
      obtain ⟨w, hw⟩ := (hψ z).2.2.2 _ (Submodule.smul_mem _ r⁻¹ (mem_normalTube.mp hzv).1)
      have hwn : ‖w‖ < 1 := by
        rw [← (hψ z).2.1, hw, norm_smul, norm_inv, Real.norm_of_nonneg hr.le]
        exact (inv_mul_lt_one₀ hr).mpr hvr
      refine ⟨(⟨w, mem_closedBall_zero_iff.mpr hwn.le⟩, z), hwn, ?_⟩
      simp [hw, smul_smul, mul_inv_cancel₀ hr.ne']
  · rintro _ ⟨q, rfl⟩
    refine interior_subset (hδU (mem_thickening_iff.mpr ⟨f q.2, mem_range_self _, ?_⟩))
    rw [dist_eq_norm, add_sub_cancel_left]
    exact (hle q).trans_lt hrδ

end Euclidean

end TauCeti
