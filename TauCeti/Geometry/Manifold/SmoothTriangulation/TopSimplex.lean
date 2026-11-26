/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Dimension
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic
import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization
import TauCeti.Geometry.Convex.ConvexSpace.Defs
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Top simplices of smooth triangulations

Let `κ : |K| ≃ₜ M` be a `Cⁿ` triangulation (`1 ≤ n`) of a manifold modelled on a
finite-dimensional real space `E`, and let `σ` be a top simplex, one with `dim E + 1` vertices.
Its open simplex `σ°`, the points of `|K|` whose carrier is `σ`, has open image `κ(σ°)` in `M`,
and `κ` restricts to a `Cⁿ` diffeomorphism of `σ°` onto `κ(σ°)`: on the closed simplex, `κ` is
`Cⁿ` in barycentric coordinates by definition of a smooth triangulation, and the barycentric
coordinates of `κ⁻¹` are `Cⁿ` on `κ(σ°)`.

Openness is combinatorial: `σ` is maximal, since no face has more than `dim E + 1` vertices
(`TauCeti.IsSmoothTriangulation.card_le`), and the open simplex of a maximal face is the
intersection of the open stars of its vertices. For the inverse, near a point `x₀ ∈ σ°` we
parametrize the plane of `σ` by its direction space, the vectors of `σ → ℝ` with coordinate sum
zero, which has dimension `|σ| - 1 = dim E`. The immersion condition makes the differential of
the parametrized map injective there, so the inverse function theorem for manifolds
(`TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv`) gives a `Cⁿ` local inverse, and the
injectivity of `κ` identifies it with `κ⁻¹`. No hypothesis on the boundary of `M` is needed: the
local inverse function theorem shows that `κ(σ°)` consists of interior points.

This is the fourth bullet of QuasiregularMaps §6.1.

## Main results

* `AbstractSimplicialComplex.isOpen_setOf_support_eq_of_maximal`: the open simplex of a maximal
  face is open in the realization.
* `TauCeti.IsSmoothTriangulation.maximal_of_card_eq`: a face of a smooth triangulation with
  `dim E + 1` vertices is maximal.
* `TauCeti.IsSmoothTriangulation.isOpen_image_setOf_support_eq`: the image `κ(σ°)` of the open
  simplex of a top simplex is open.
* `TauCeti.IsSmoothTriangulation.contMDiffOn_coordinates_symm`: the barycentric coordinates of
  `κ⁻¹` on the vertices of a top simplex are `Cⁿ` on `κ(σ°)`.
-/

public section

open Set Function Module AbstractSimplicialComplex TauCeti.SetLike
open scoped Manifold ContDiff Topology

namespace AbstractSimplicialComplex

variable {ι : Type*} (K : AbstractSimplicialComplex ι)

/-- The open simplex of a maximal face, the points whose carrier is that face, is open: by
maximality it is the intersection of the open stars of the vertices of the face. -/
theorem isOpen_setOf_support_eq_of_maximal {σ : Finset ι} (hσ : Maximal (· ∈ K) σ) :
    IsOpen {x : Realization K | x.val.support = σ} := by
  convert K.isOpen_biInter_openStarRealization σ using 1
  ext x
  rw [mem_biInter_openStarRealization_iff]
  exact ⟨fun h => h.ge, fun h => (hσ.2 (support_mem K x) h).antisymm h⟩

end AbstractSimplicialComplex

namespace TauCeti

variable {ι : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}
  {K : AbstractSimplicialComplex ι} {κ : Realization K ≃ₜ M}

namespace IsSmoothTriangulation

/-- In a smooth triangulation of a manifold modelled on a finite-dimensional space `E`, a face
with `dim E + 1` vertices is maximal. -/
theorem maximal_of_card_eq (h : IsSmoothTriangulation I n κ) {σ : Finset ι} (hσ : σ ∈ K)
    (hcard : σ.card = finrank ℝ E + 1) : Maximal (· ∈ K) σ :=
  ⟨hσ, fun τ hτ hστ => (Finset.eq_of_subset_of_card_le hστ (by
    have := h.card_le hτ
    omega)).ge⟩

/-- In a smooth triangulation of a manifold modelled on a finite-dimensional space `E`, the image
of the open simplex of a face with `dim E + 1` vertices is open. -/
theorem isOpen_image_setOf_support_eq (h : IsSmoothTriangulation I n κ) {σ : Finset ι}
    (hσ : σ ∈ K) (hcard : σ.card = finrank ℝ E + 1) :
    IsOpen (κ '' {x : Realization K | x.val.support = σ}) :=
  κ.isOpenMap _ (K.isOpen_setOf_support_eq_of_maximal (h.maximal_of_card_eq hσ hcard))

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

/-- A map from the open simplex on `σ` to a manifold modelled on `E`, `Cⁿ` within the closed
simplex with derivatives injective on the directions of the simplex, is a `Cⁿ` local
diffeomorphism at each point of the open simplex when `|σ| = dim E + 1`, read on the plane of the
simplex through that point. -/
private theorem isLocalDiffeomorphAt_comp_add [IsManifold I n M] {σ : Finset ι}
    {F : (σ → ℝ) → M}
    (hF : ContMDiffOn 𝓘(ℝ, σ → ℝ) I n F (range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights))
    (hF' : ∀ t : Convexity.StdSimplex ℝ σ, ∃ F' : (σ → ℝ) →L[ℝ] E,
      HasMFDerivWithinAt 𝓘(ℝ, σ → ℝ) I F
        (range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights) t.weights F' ∧
        ∀ v : σ → ℝ, ∑ a, v a = 0 → F' v = 0 → v = 0)
    (hn : 1 ≤ n) (hcard : σ.card = finrank ℝ E + 1) {w₀ : σ → ℝ} (hpos : ∀ a, 0 < w₀ a)
    (hw₀ : ∑ a, w₀ a = 1) :
    IsLocalDiffeomorphAt 𝓘(ℝ, singleParityCheckCode ℝ σ) I n
      (fun v : singleParityCheckCode ℝ σ => F (w₀ + (v : σ → ℝ))) 0 := by
  set V := singleParityCheckCode ℝ σ
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have h0U : (0 : V) ∈ {v : V | ∀ a, 0 < (w₀ + v) a} := by simpa using hpos
  have hgU : MapsTo (fun v : V => w₀ + (v : σ → ℝ)) {v : V | ∀ a, 0 < (w₀ + v) a}
      (range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights) :=
    fun v hv => add_mem_range_weights hw₀ hv
  have hg : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, σ → ℝ) n (fun v : V => w₀ + (v : σ → ℝ)) :=
    ContDiff.contMDiff (contDiff_const.add V.subtypeL.contDiff)
  -- The derivative of `F` within the simplex at `w₀`, injective on the directions `V`.
  obtain ⟨t₀, ht₀⟩ := hgU h0U
  obtain ⟨F', hF'd, hF'inj⟩ := hF' t₀
  have hF'g : ∀ p, ⇑t₀.weights = p → HasMFDerivWithinAt 𝓘(ℝ, σ → ℝ) I F
      (range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights) p F' := by
    rintro _ rfl
    exact hF'd
  have hgd : HasMFDerivAt 𝓘(ℝ, V) 𝓘(ℝ, σ → ℝ) (fun v : V => w₀ + (v : σ → ℝ)) 0 V.subtypeL :=
    (V.subtypeL.hasFDerivAt.const_add w₀).hasMFDerivAt
  have hΨd : HasMFDerivAt 𝓘(ℝ, V) I (fun v : V => F (w₀ + (v : σ → ℝ))) 0 (F'.comp V.subtypeL) :=
    (HasMFDerivWithinAt.comp (f := fun v : V => w₀ + (v : σ → ℝ)) 0 (hF'g _ ht₀)
      hgd.hasMFDerivWithinAt hgU).hasMFDerivAt
      ((isOpen_setOf_add_pos w₀).mem_nhds h0U)
  refine isLocalDiffeomorphAt_of_injective_mfderiv (hF.comp hg.contMDiffOn hgU)
    (isOpen_setOf_add_pos w₀) h0U BoundarylessManifold.isInteriorPoint hn ?_ ?_
  · rw [hΨd.mfderiv]
    intro v v' hvv'
    change V at v v'
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

/-- The barycentric coordinates of `κ⁻¹` invert the coordinate form `F` of `κ` on a closed
simplex. -/
private theorem coordinates_symm_apply_eq {σ : Finset ι} (hσ : σ ∈ K) {F : (σ → ℝ) → M}
    (hFg : ∀ x : StandardSimplex σ, F (fun a => x.val a) = (κ ∘ faceInclusion K ⟨σ, hσ⟩) x)
    {w : σ → ℝ} (hw : w ∈ range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights) :
    (fun a : σ => (κ.symm (F w)).val a) = w := by
  rw [← Finset.range_standardSimplex_coordinates] at hw
  obtain ⟨x, rfl⟩ := hw
  rw [hFg x, comp_apply, Homeomorph.symm_apply_apply]
  exact funext fun a => by rw [faceInclusion_val]

/-- **A smooth triangulation is a diffeomorphism on each open top simplex.** In a `Cⁿ`
triangulation `κ` (`1 ≤ n`) of a manifold modelled on a finite-dimensional space `E`, let `σ` be
a face with `dim E + 1` vertices. Then the barycentric coordinates of `κ⁻¹` on the vertices of `σ`
are `Cⁿ` on the image of the open simplex of `σ`. Since `κ` is `Cⁿ` in barycentric coordinates on
the closed simplex, `κ` restricts to a `Cⁿ` diffeomorphism of the open simplex onto its image. -/
theorem contMDiffOn_coordinates_symm [IsManifold I n M] (h : IsSmoothTriangulation I n κ)
    (hn : 1 ≤ n) {σ : Finset ι} (hσ : σ ∈ K) (hcard : σ.card = finrank ℝ E + 1) :
    ContMDiffOn I 𝓘(ℝ, σ → ℝ) n (fun y : M => fun a : σ => (κ.symm y).val a)
      (κ '' {x : Realization K | x.val.support = σ}) := by
  rintro _ ⟨x₀, hx₀, rfl⟩
  refine ContMDiffAt.contMDiffWithinAt ?_
  obtain ⟨F, hFg, hF, hF'⟩ := isSimplexImmersion_iff.mp (isSmoothTriangulation_iff.mp h ⟨σ, hσ⟩)
  -- Parametrize the plane of `σ` through the coordinates `w₀` of `x₀`.
  set w₀ : σ → ℝ := fun a => x₀.val a
  have hw₀ : ∑ a, w₀ a = 1 := by
    rw [Finset.sum_coe_sort σ (fun a => x₀.val a)]
    exact Realization.sum_eq_one_of_support_subset K x₀ hx₀.le
  have hpos : ∀ a, 0 < w₀ a := fun a => Realization.pos_of_mem_support K x₀ (hx₀ ▸ a.property)
  set V := singleParityCheckCode ℝ σ
  set Ψ : V → M := fun v => F (w₀ + (v : σ → ℝ))
  have hloc : IsLocalDiffeomorphAt 𝓘(ℝ, V) I n Ψ 0 :=
    isLocalDiffeomorphAt_comp_add hF hF' hn hcard hpos hw₀
  have hΨ0 : Ψ 0 = κ x₀ := by
    have hmem := Realization.mem_convexHull_of_support_subset K x₀ hx₀.le
    simpa [Ψ, w₀] using hFg ⟨x₀.val, hmem⟩
  rw [← hΨ0]
  -- The local inverse `φ` given by the inverse function theorem stays in the open simplex.
  set φ := hloc.localInverse
  have hφ0 : φ (Ψ 0) = 0 := hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hφU : φ ⁻¹' {v : V | ∀ a, 0 < (w₀ + v) a} ∈ 𝓝 (Ψ 0) :=
    hloc.continuousAt_localInverse.preimage_mem_nhds
      (by rw [hφ0]; exact (isOpen_setOf_add_pos w₀).mem_nhds (by simpa using hpos))
  -- The coordinates of `κ⁻¹` agree with `w₀ + φ` there.
  have heq : (fun y : M => fun a : σ => (κ.symm y).val a) =ᶠ[𝓝 (Ψ 0)]
      fun y => w₀ + (φ y : σ → ℝ) := by
    filter_upwards [hφU, hloc.localInverse_eventuallyEq_right] with y hyU hyΨ
    have hy : F (w₀ + (φ y : σ → ℝ)) = y := hyΨ
    rw [← coordinates_symm_apply_eq hσ hFg (add_mem_range_weights hw₀ hyU), hy]
  have hg : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, σ → ℝ) n (fun v : V => w₀ + (v : σ → ℝ)) :=
    ContDiff.contMDiff (contDiff_const.add V.subtypeL.contDiff)
  exact (hg.contMDiffAt.comp _ hloc.contMDiffAt_localInverse).congr_of_eventuallyEq heq

end IsSmoothTriangulation

end TauCeti
