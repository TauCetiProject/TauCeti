/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Dimension
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization
import TauCeti.Geometry.Convex.ConvexSpace.Defs

/-!
# Top simplices of smooth triangulations

Let `κ : |K| ≃ₜ M` be a `Cⁿ` triangulation (`1 ≤ n`) of a manifold modelled on a
finite-dimensional real space `E`, and let `σ` be a top simplex, one with `dim E + 1` vertices.
Its open simplex `σ°`, the points of `|K|` whose carrier is `σ`, has open image `κ(σ°)` in `M`.
Read on the plane of `σ` through a point of `σ°`, `κ` is a `Cⁿ` local diffeomorphism there, and
the barycentric coordinates of `κ⁻¹` are `Cⁿ` on `κ(σ°)`. As `κ` is `Cⁿ` in barycentric
coordinates on the closed simplex by definition of a smooth triangulation, these two results
say that `κ` restricts to a `Cⁿ` diffeomorphism of `σ°` onto `κ(σ°)`.

Openness is combinatorial: `σ` is maximal (`TauCeti.IsSmoothTriangulation.maximal_of_card_eq`),
and the open simplex of a maximal face is open
(`AbstractSimplicialComplex.isOpen_setOf_support_eq_of_maximal`). For the inverse, near a point
`x₀ ∈ σ°` we parametrize the plane of `σ` by its direction space, the vectors of `σ → ℝ` with
coordinate sum zero, which has dimension `|σ| - 1 = dim E`. The immersion condition makes the
differential of the parametrized map injective there, so the inverse function theorem for
manifolds (`TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv`) gives a `Cⁿ` local inverse, and
the injectivity of `κ` identifies it with `κ⁻¹`. No hypothesis on the boundary of `M` is needed:
the inverse function theorem only asks for an interior point of the source, here a vector space.

## Main results

* `TauCeti.IsSimplexImmersion.exists_isLocalDiffeomorphAt`: a `Cⁿ` immersion of a simplex with
  `dim E + 1` vertices, read on the plane of the simplex through a point of its open simplex, is a
  `Cⁿ` local diffeomorphism at that point.
* `TauCeti.IsSmoothTriangulation.isOpen_image_setOf_support_eq`: the image `κ(σ°)` of the open
  simplex of a top simplex is open.
* `TauCeti.IsSmoothTriangulation.exists_isLocalDiffeomorphAt`: read on the plane of a top simplex
  through a point of its open simplex, `κ` is a `Cⁿ` local diffeomorphism at that point.
* `TauCeti.IsSmoothTriangulation.contMDiffOn_coordinates_symm`: the barycentric coordinates of
  `κ⁻¹` on the vertices of a top simplex are `Cⁿ` on `κ(σ°)`.
-/

public section

open Set Function Module AbstractSimplicialComplex TauCeti.SetLike
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {ι : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}
  {K : AbstractSimplicialComplex ι} {κ : Realization K ≃ₜ M}

/-- The points of the plane through `w₀` parallel to the simplex on `σ` with positive
coordinates form an open set of directions. -/
private theorem isOpen_setOf_add_pos {σ : Finset ι} (w₀ : σ → ℝ) :
    IsOpen {v : singleParityCheckCode ℝ σ | ∀ a, 0 < (w₀ + v) a} := by
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun a => isOpen_lt continuous_const
    ((continuous_apply a).comp (continuous_const.add continuous_subtypeVal))

/-- A point of the plane of the simplex on `σ` with positive coordinates lies in the simplex. -/
private theorem add_mem_range_weights {σ : Finset ι} {w₀ : σ → ℝ} (hw₀ : ∑ a, w₀ a = 1)
    {v : singleParityCheckCode ℝ σ} (hv : ∀ a, 0 < (w₀ + v) a) :
    w₀ + v ∈ range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights := by
  rw [Convexity.StdSimplex.mem_range_toFun_comp_weights_iff]
  refine ⟨fun a => (hv a).le, ?_⟩
  simp only [Pi.add_apply, Finset.sum_add_distrib, hw₀]
  simpa using (mem_singleParityCheckCode ℝ σ).mp v.property

/-- Translating the directions of the simplex on `σ` by `w₀` is smooth. -/
private theorem contMDiff_const_add_coe {σ : Finset ι} (w₀ : σ → ℝ) :
    ContMDiff 𝓘(ℝ, singleParityCheckCode ℝ σ) 𝓘(ℝ, σ → ℝ) n
      (fun v : singleParityCheckCode ℝ σ => w₀ + (v : σ → ℝ)) :=
  ContDiff.contMDiff (contDiff_const.add (singleParityCheckCode ℝ σ).subtypeL.contDiff)

namespace IsSimplexImmersion

/-- **A top-dimensional simplex immersion is a local diffeomorphism on its open simplex.** Let
`g` be a `Cⁿ` immersion (`1 ≤ n`) of the closed simplex on `σ` into a manifold modelled on `E`,
with `|σ| = dim E + 1`, and let `w₀` be a point of the open simplex (positive coordinates summing
to one). Then `g` has a coordinate form `F` on the closed simplex such that `v ↦ F (w₀ + v)`, on
the directions `v` of the plane of `σ` (the vectors of `σ → ℝ` with coordinate sum zero), is a
`Cⁿ` local diffeomorphism at `0`. -/
theorem exists_isLocalDiffeomorphAt [IsManifold I n M] {σ : Finset ι}
    {g : StandardSimplex σ → M} (h : IsSimplexImmersion I n g) (hn : 1 ≤ n)
    (hcard : σ.card = finrank ℝ E + 1) {w₀ : σ → ℝ} (hpos : ∀ a, 0 < w₀ a)
    (hw₀ : ∑ a, w₀ a = 1) :
    ∃ F : (σ → ℝ) → M, (∀ x : StandardSimplex σ, F (fun a => x.val a) = g x) ∧
      IsLocalDiffeomorphAt 𝓘(ℝ, singleParityCheckCode ℝ σ) I n
        (fun v : singleParityCheckCode ℝ σ => F (w₀ + (v : σ → ℝ))) 0 := by
  obtain ⟨F, hFg, hF, hF'⟩ := isSimplexImmersion_iff.mp h
  refine ⟨F, hFg, ?_⟩
  set V := singleParityCheckCode ℝ σ
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have h0U : (0 : V) ∈ {v : V | ∀ a, 0 < (w₀ + v) a} := by simpa using hpos
  have hgU : MapsTo (fun v : V => w₀ + (v : σ → ℝ)) {v : V | ∀ a, 0 < (w₀ + v) a}
      (range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights) :=
    fun v hv => add_mem_range_weights hw₀ hv
  -- The derivative of `F` within the simplex at `w₀`, injective on the directions `V`.
  obtain ⟨t₀, ht₀ : ⇑t₀.weights = w₀ + ((0 : V) : σ → ℝ)⟩ := hgU h0U
  obtain ⟨F', hF'd, hF'inj⟩ := hF' t₀
  have hgd : HasMFDerivAt 𝓘(ℝ, V) 𝓘(ℝ, σ → ℝ) (fun v : V => w₀ + (v : σ → ℝ)) 0 V.subtypeL :=
    (V.subtypeL.hasFDerivAt.const_add w₀).hasMFDerivAt
  have hΨd : HasMFDerivAt 𝓘(ℝ, V) I (fun v : V => F (w₀ + (v : σ → ℝ))) 0 (F'.comp V.subtypeL) :=
    (HasMFDerivWithinAt.comp (f := fun v : V => w₀ + (v : σ → ℝ)) 0 (ht₀ ▸ hF'd)
      hgd.hasMFDerivWithinAt hgU).hasMFDerivAt
      ((isOpen_setOf_add_pos w₀).mem_nhds h0U)
  refine isLocalDiffeomorphAt_of_injective_mfderiv
    (hF.comp (contMDiff_const_add_coe w₀).contMDiffOn hgU)
    (isOpen_setOf_add_pos w₀) h0U BoundarylessManifold.isInteriorPoint hn ?_ ?_
  · rw [hΨd.mfderiv]
    rintro (v : V) (v' : V) hvv'
    have hsum : ∑ a, ((v : σ → ℝ) - v') a = 0 := by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib]
      rw [(mem_singleParityCheckCode ℝ σ).mp v.property,
        (mem_singleParityCheckCode ℝ σ).mp v'.property, sub_zero]
    have hzero : F' ((v : σ → ℝ) - v') = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hvv'
    exact Subtype.ext (sub_eq_zero.mp (hF'inj _ hsum hzero))
  · rw [finrank_singleParityCheckCode, Fintype.card_coe]
    omega

end IsSimplexImmersion

namespace IsSmoothTriangulation

/-- In a smooth triangulation of a manifold modelled on a finite-dimensional space `E`, the image
of the open simplex of a face with `dim E + 1` vertices is open. -/
theorem isOpen_image_setOf_support_eq (h : IsSmoothTriangulation I n κ) {σ : Finset ι}
    (hσ : σ ∈ K) (hcard : σ.card = finrank ℝ E + 1) :
    IsOpen (κ '' {x : Realization K | x.val.support = σ}) :=
  κ.isOpenMap _ (K.isOpen_setOf_support_eq_of_maximal (h.maximal_of_card_eq hσ hcard))

/-- The barycentric coordinates of a point of the open simplex on `σ` are positive on `σ` and
sum to one there. -/
private theorem coordinates_pos_and_sum_eq_one {σ : Finset ι} {x₀ : Realization K}
    (hx₀ : x₀.val.support = σ) :
    (∀ a : σ, 0 < x₀.val a) ∧ ∑ a : σ, x₀.val a = 1 :=
  ⟨fun a => Realization.pos_of_mem_support K x₀ (hx₀ ▸ a.property),
    (Finset.sum_coe_sort σ (fun a => x₀.val a)).trans
      (Realization.sum_eq_one_of_support_subset K x₀ hx₀.le)⟩

/-- **A smooth triangulation is a local diffeomorphism on each open top simplex.** In a `Cⁿ`
triangulation `κ` (`1 ≤ n`) of a manifold modelled on a finite-dimensional space `E`, let `σ` be
a face with `dim E + 1` vertices and `x₀` a point of its open simplex. Then `κ` has a coordinate
form `F` on the closed simplex of `σ` such that `v ↦ F (x₀ + v)`, on the directions `v` of the
plane of `σ` (the vectors of `σ → ℝ` with coordinate sum zero), is a `Cⁿ` local diffeomorphism at
`0`, where `x₀` stands for its barycentric coordinates on `σ`. -/
theorem exists_isLocalDiffeomorphAt [IsManifold I n M] (h : IsSmoothTriangulation I n κ)
    (hn : 1 ≤ n) {σ : Finset ι} (hσ : σ ∈ K) (hcard : σ.card = finrank ℝ E + 1)
    {x₀ : Realization K} (hx₀ : x₀.val.support = σ) :
    ∃ F : (σ → ℝ) → M,
      (∀ x : StandardSimplex σ, F (fun a => x.val a) = κ (faceInclusion K ⟨σ, hσ⟩ x)) ∧
        IsLocalDiffeomorphAt 𝓘(ℝ, singleParityCheckCode ℝ σ) I n
          (fun v : singleParityCheckCode ℝ σ => F ((fun a : σ => x₀.val a) + (v : σ → ℝ))) 0 := by
  obtain ⟨hpos, hw₀⟩ := coordinates_pos_and_sum_eq_one hx₀
  exact (isSmoothTriangulation_iff.mp h ⟨σ, hσ⟩).exists_isLocalDiffeomorphAt hn hcard hpos hw₀

/-- The barycentric coordinates of `κ⁻¹` invert the coordinate form `F` of `κ` on a closed
simplex. -/
private theorem coordinates_symm_apply_eq {σ : Finset ι} (hσ : σ ∈ K) {F : (σ → ℝ) → M}
    (hFg : ∀ x : StandardSimplex σ, F (fun a => x.val a) = κ (faceInclusion K ⟨σ, hσ⟩ x))
    {w : σ → ℝ} (hw : w ∈ range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights) :
    (fun a : σ => (κ.symm (F w)).val a) = w := by
  rw [← Finset.range_standardSimplex_coordinates] at hw
  obtain ⟨x, rfl⟩ := hw
  rw [hFg x, Homeomorph.symm_apply_apply]
  exact funext fun a => by rw [faceInclusion_val]

/-- **The barycentric coordinates of `κ⁻¹` are `Cⁿ` on an open top simplex.** In a `Cⁿ`
triangulation `κ` (`1 ≤ n`) of a manifold modelled on a finite-dimensional space `E`, let `σ` be
a face with `dim E + 1` vertices. Then the barycentric coordinates of `κ⁻¹` on the vertices of `σ`
are `Cⁿ` on the image of the open simplex of `σ`. -/
theorem contMDiffOn_coordinates_symm [IsManifold I n M] (h : IsSmoothTriangulation I n κ)
    (hn : 1 ≤ n) {σ : Finset ι} (hσ : σ ∈ K) (hcard : σ.card = finrank ℝ E + 1) :
    ContMDiffOn I 𝓘(ℝ, σ → ℝ) n (fun y : M => fun a : σ => (κ.symm y).val a)
      (κ '' {x : Realization K | x.val.support = σ}) := by
  rintro _ ⟨x₀, hx₀, rfl⟩
  refine ContMDiffAt.contMDiffWithinAt ?_
  obtain ⟨F, hFg, hloc⟩ := h.exists_isLocalDiffeomorphAt hn hσ hcard hx₀
  obtain ⟨hpos, hw₀⟩ := coordinates_pos_and_sum_eq_one hx₀
  -- `F` read on the plane of `σ` through the coordinates `w₀` of `x₀`.
  set w₀ : σ → ℝ := fun a => x₀.val a
  have hF0 : F (w₀ + ((0 : singleParityCheckCode ℝ σ) : σ → ℝ)) = κ x₀ := by
    have hmem := Realization.mem_convexHull_of_support_subset K x₀ hx₀.le
    simpa only [faceInclusion_mk_val, ZeroMemClass.coe_zero, add_zero, w₀] using
      hFg ⟨x₀.val, hmem⟩
  rw [← hF0]
  -- The local inverse `φ` given by the inverse function theorem stays in the open simplex.
  set φ := hloc.localInverse
  have hφ0 : φ (F (w₀ + ((0 : singleParityCheckCode ℝ σ) : σ → ℝ))) = 0 :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hφU : φ ⁻¹' {v : singleParityCheckCode ℝ σ | ∀ a, 0 < (w₀ + v) a} ∈
      𝓝 (F (w₀ + ((0 : singleParityCheckCode ℝ σ) : σ → ℝ))) :=
    hloc.continuousAt_localInverse.preimage_mem_nhds
      (by rw [hφ0]; exact (isOpen_setOf_add_pos w₀).mem_nhds (by simpa using hpos))
  -- The coordinates of `κ⁻¹` agree with `w₀ + φ` there.
  have heq : (fun y : M => fun a : σ => (κ.symm y).val a)
      =ᶠ[𝓝 (F (w₀ + ((0 : singleParityCheckCode ℝ σ) : σ → ℝ)))]
      fun y => w₀ + (φ y : σ → ℝ) := by
    filter_upwards [hφU, hloc.localInverse_eventuallyEq_right] with y hyU hyF
    simp only [comp_apply, id_eq] at hyF
    rw [← coordinates_symm_apply_eq hσ hFg (w := w₀ + (φ y : σ → ℝ))
      (add_mem_range_weights hw₀ hyU), hyF]
  exact ((contMDiff_const_add_coe w₀).contMDiffAt.comp _
    hloc.contMDiffAt_localInverse).congr_of_eventuallyEq heq

end IsSmoothTriangulation

end TauCeti
