/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
import Mathlib.Analysis.Convex.PathConnected
import TauCeti.Analysis.Convex.Cone.Caratheodory
import TauCeti.Analysis.Convex.Halfspace

/-!
# Local convexity of the weight model

Let `α : ι → 𝔱*` be a finite family of weights and let
`μ(q, p) = -½ Σ_i (q_i² + p_i²) α_i` be the moment map of the weight model on `ℂ^ι`
(`TauCeti.weightMomentMap`), the local model of a Hamiltonian torus action near a fixed point.
This file proves the two local properties of `μ` from which the local-to-global principle of
Condevaux–Dazord–Molino and Hilgert–Neeb–Plank deduces convexity of the image and connectedness of
the fibres of a proper moment map: `μ` is open onto its image cone, and its fibres, also inside
small invariant balls, are preconnected.

Both reduce to the map `Φ(q, p) = ((q_i² + p_i²) / 2)_i` of half squared radii
(`TauCeti.halfSqRadii`), onto the closed orthant of `ℝ^ι`, since `μ = L ∘ Φ` for the linear map
`L a = Σ_i a_i (-α_i)` (`TauCeti.weightMomentMap_eq_linearCombination_comp_halfSqRadii`).

* Polar coordinates `z_i = √(2 s_i) e^{i θ_i}` exhibit `Φ⁻¹(S)`, for a convex set `S`, as the image
  of the preconnected set `ℝ^ι × (S ∩ [0, ∞)^ι)`; so `Φ⁻¹(S)` is preconnected
  (`TauCeti.isPreconnected_preimage_halfSqRadii`). The preimage of a convex set under `L` is
  convex, so every preimage `μ⁻¹(S)` of a convex set is preconnected
  (`TauCeti.isPreconnected_preimage_weightMomentMap`); in particular every fibre of `μ` is. The
  same holds inside each invariant ball `‖q‖² + ‖p‖² < r`, which is the preimage under `Φ` of a
  half-space (`TauCeti.preimage_halfSqRadii_setOf_sum_lt`,
  `TauCeti.isPreconnected_preimage_weightMomentMap_inter`). As `Φ` maps the ball onto the part of
  the orthant below that half-space, `μ` maps it onto a convex set
  (`TauCeti.convex_image_weightMomentMap_setOf_lt`).
* Rescaling each coordinate `z_i` by `√(s_i / Φ_i(z))`, or replacing a vanishing one by `√(2 s_i)`,
  gives a continuous local section of `Φ` through any point, so `Φ` is open onto the orthant
  (`TauCeti.image_halfSqRadii_mem_nhdsWithin`). A linear map is relatively open from the
  orthant onto its image (`LinearMap.image_inter_Ici_mem_nhdsWithin`), so `μ` sends every
  neighbourhood of a point `z` onto a neighbourhood of `μ(z)` in the moment cone
  (`TauCeti.image_mem_nhdsWithin_range_weightMomentMap`).

No hypothesis on the weights is needed: they may be zero, repeated or linearly dependent. For
dependent weights the fibres of `μ` are no longer single orbits of the torus, but they remain
preconnected.

## Main results

* `TauCeti.isPreconnected_preimage_halfSqRadii`: the preimage of a convex set under the half
  squared radii is preconnected.
* `TauCeti.image_halfSqRadii_mem_nhdsWithin`: the half squared radii are open onto the closed
  orthant.
* `TauCeti.convex_range_weightMomentMap`: the image of `μ` is convex.
* `TauCeti.isPreconnected_preimage_weightMomentMap`,
  `TauCeti.isPreconnected_preimage_singleton_weightMomentMap`: preimages of convex sets, and in
  particular fibres, of `μ` are preconnected.
* `TauCeti.isPreconnected_preimage_weightMomentMap_inter`: the same inside every invariant ball.
* `TauCeti.convex_image_weightMomentMap_setOf_lt`: the image of every invariant ball is convex.
* `TauCeti.image_mem_nhdsWithin_range_weightMomentMap`: `μ` is open onto its image.

## References

* J. Hilgert, K.-H. Neeb and W. Plank, *Symplectic convexity theorems and coadjoint orbits*,
  Compositio Math. 94 (1994), 129–180, Theorem 3.10 (the local-to-global principle) and
  Theorem 4.1 (the local convexity data of moment maps).
* T. Condevaux, P. Dazord and P. Molino, *Géométrie du moment*, Travaux du Séminaire Sud-Rhodanien
  de Géométrie I, Publ. Dép. Math. Nouvelle Sér. B 88-1, Univ. Claude-Bernard, Lyon (1988),
  131–160.
* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Math. 1764, Springer
  (2001), Section 27.
-/

public section

open Filter Set Topology Real

namespace TauCeti

variable {ι : Type*}

/-! ### The half squared radii -/

/-- **Preimages of convex sets under the half squared radii are preconnected.** For a convex set
`S ⊆ ℝ^ι`, the points of `ℂ^ι` whose half squared radii `(q_i² + p_i²) / 2` lie in `S` form a
preconnected set. -/
theorem isPreconnected_preimage_halfSqRadii {S : Set (ι → ℝ)} (hS : Convex ℝ S) :
    IsPreconnected (halfSqRadii ⁻¹' S) := by
  -- Polar coordinates `z_i = √(2 s_i) e^{i θ_i}`, with angles `θ` and half squared radii `s`.
  let P : (ι → ℝ) × (ι → ℝ) → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι := fun y ↦
    (WithLp.toLp 2 fun i ↦ √(2 * y.2 i) * cos (y.1 i),
      WithLp.toLp 2 fun i ↦ √(2 * y.2 i) * sin (y.1 i))
  have hP : Continuous P := by fun_prop
  have himage : P '' (univ ×ˢ (S ∩ Ici 0)) = halfSqRadii ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, ⟨-, hyS, hy0⟩, rfl⟩
      rw [mem_preimage]
      convert hyS using 1
      ext i
      have h2 : √(2 * y.2 i) ^ 2 = 2 * y.2 i := sq_sqrt (mul_nonneg zero_le_two (hy0 i))
      simp only [P, halfSqRadii_apply]
      linear_combination (√(2 * y.2 i) ^ 2 / 2) * sin_sq_add_cos_sq (y.1 i) + h2 / 2
    · intro hx
      -- The angles are the arguments of the coordinates `q_i + i p_i`.
      refine ⟨(fun i ↦ Complex.arg ⟨x.1 i, x.2 i⟩, halfSqRadii x),
        ⟨mem_univ _, hx, halfSqRadii_nonneg x⟩, ?_⟩
      have hnorm (i : ι) : √(2 * halfSqRadii x i) = ‖(⟨x.1 i, x.2 i⟩ : ℂ)‖ := by
        rw [halfSqRadii_apply, Complex.norm_def, Complex.normSq_mk]
        congr 1
        ring
      ext i
      · simp only [P, hnorm, Complex.norm_mul_cos_arg]
      · simp only [P, hnorm, Complex.norm_mul_sin_arg]
  rw [← himage]
  exact (isPreconnected_univ.prod (hS.inter (convex_Ici 0)).isPreconnected).image _
    hP.continuousOn

/-- The invariant ball `‖q‖² + ‖p‖² < r` of `ℂ^ι` is the preimage under the half squared radii of
the half-space `Σ_i s_i < r / 2`. -/
theorem preimage_halfSqRadii_setOf_sum_lt [Fintype ι] (r : ℝ) :
    halfSqRadii ⁻¹' {s | ∑ i, s i < r / 2} =
      {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι | ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 < r} := by
  ext x
  simp only [mem_ofPred_eq, mem_preimage, halfSqRadii_apply]
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, ← Finset.sum_div,
    Finset.sum_add_distrib]
  constructor <;> intro h <;> linarith

/-- **The half squared radii are open onto the orthant.** The map
`(q, p) ↦ ((q_i² + p_i²) / 2)_i` sends every neighbourhood of a point of `ℂ^ι` onto a
neighbourhood of its image in the closed orthant `Ici 0` of `ℝ^ι`. -/
theorem image_halfSqRadii_mem_nhdsWithin (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    {N : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)} (hN : N ∈ 𝓝 x) :
    halfSqRadii '' N ∈ 𝓝[Ici 0] halfSqRadii x := by
  set r := halfSqRadii x with hr
  -- A continuous section `σ` of `halfSqRadii` over the orthant through `x`: rescale the nonzero
  -- coordinates of `x`, and fill in the vanishing ones along the real axis.
  let σ : (ι → ℝ) → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι := fun s ↦
    (WithLp.toLp 2 fun i ↦ if r i = 0 then √(2 * s i) else x.1 i * √(s i / r i),
      WithLp.toLp 2 fun i ↦ if r i = 0 then 0 else x.2 i * √(s i / r i))
  have hσ : Continuous σ := by
    refine .prodMk ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_))
      ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_)) <;>
      split_ifs <;> fun_prop
  -- A vanishing half squared radius forces both coordinates to vanish.
  have hz (i : ι) (h : r i = 0) : x.1 i = 0 ∧ x.2 i = 0 := by
    rw [hr, halfSqRadii_apply] at h
    constructor <;> nlinarith [sq_nonneg (x.1 i), sq_nonneg (x.2 i)]
  have hσx : σ r = x := by
    ext i <;> by_cases h : r i = 0
    · simp [σ, h, (hz i h).1]
    · simp [σ, h]
    · simp [σ, h, (hz i h).2]
    · simp [σ, h]
  have hΦσ : ∀ s : ι → ℝ, 0 ≤ s → halfSqRadii (σ s) = s := fun s hs ↦ by
    ext i
    have hsi : 0 ≤ s i := hs i
    by_cases h : r i = 0
    · simp only [halfSqRadii_apply, σ, h, ite_true]
      rw [sq_sqrt (by linarith)]
      ring
    · have hpos : 0 < r i := lt_of_le_of_ne (halfSqRadii_nonneg x i) (Ne.symm h)
      simp only [halfSqRadii_apply, σ, h, ite_false, mul_pow,
        sq_sqrt (div_nonneg hsi hpos.le)]
      field_simp [hpos.ne']
      simp only [hr, halfSqRadii_apply]
      ring
  have hpre : σ ⁻¹' N ∈ 𝓝 r := hσ.continuousAt.preimage_mem_nhds (by rwa [hσx])
  exact mem_of_superset (inter_mem_nhdsWithin (Ici 0) hpre) fun s ⟨hs, hsN⟩ ↦
    ⟨σ s, hsN, hΦσ s hs⟩

/-! ### The moment map of the weight model -/

variable [Fintype ι] {𝔱 : Type*} [NormedAddCommGroup 𝔱] [NormedSpace ℝ 𝔱]

/-- The image of the moment map of the weight model is convex. -/
theorem convex_range_weightMomentMap (α : ι → StrongDual ℝ 𝔱) :
    Convex ℝ (range (weightMomentMap α)) := by
  rw [range_weightMomentMap]
  exact PointedCone.convex _

/-- **Preimages of convex sets under the weight model moment map are preconnected.** For every
convex set `S ⊆ 𝔱*`, the set of points of `ℂ^ι` mapped into `S` by
`μ(q, p) = -½ Σ_i (q_i² + p_i²) α_i` is preconnected, for arbitrary weights `α`. -/
theorem isPreconnected_preimage_weightMomentMap (α : ι → StrongDual ℝ 𝔱)
    {S : Set (StrongDual ℝ 𝔱)} (hS : Convex ℝ S) : IsPreconnected (weightMomentMap α ⁻¹' S) := by
  rw [weightMomentMap_eq_linearCombination_comp_halfSqRadii, preimage_comp]
  exact isPreconnected_preimage_halfSqRadii (hS.linear_preimage _)

/-- **The fibres of the weight model moment map are preconnected**, for arbitrary weights. -/
theorem isPreconnected_preimage_singleton_weightMomentMap (α : ι → StrongDual ℝ 𝔱)
    (ν : StrongDual ℝ 𝔱) : IsPreconnected (weightMomentMap α ⁻¹' {ν}) :=
  isPreconnected_preimage_weightMomentMap α (convex_singleton ν)

/-- **Preconnected preimages in invariant balls.** Inside every invariant ball
`‖q‖² + ‖p‖² < r` of `ℂ^ι`, the points mapped into a convex set `S ⊆ 𝔱*`, in particular the points
of a fibre, form a preconnected set. -/
theorem isPreconnected_preimage_weightMomentMap_inter (α : ι → StrongDual ℝ 𝔱)
    {S : Set (StrongDual ℝ 𝔱)} (hS : Convex ℝ S) (r : ℝ) :
    IsPreconnected (weightMomentMap α ⁻¹' S ∩ {x | ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 < r}) := by
  rw [← preimage_halfSqRadii_setOf_sum_lt, weightMomentMap_eq_linearCombination_comp_halfSqRadii,
    preimage_comp, ← preimage_inter]
  exact isPreconnected_preimage_halfSqRadii ((hS.linear_preimage _).inter (convex_setOf_sum_lt _))

/-- **The image of an invariant ball is convex.** The moment map
`μ(q, p) = -½ Σ_i (q_i² + p_i²) α_i` of the weight model sends every invariant ball
`‖q‖² + ‖p‖² < r` of `ℂ^ι` onto a convex set, for arbitrary weights `α`. -/
theorem convex_image_weightMomentMap_setOf_lt (α : ι → StrongDual ℝ 𝔱) (r : ℝ) :
    Convex ℝ (weightMomentMap α '' {x | ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 < r}) := by
  -- The half squared radii send the ball onto the part of the orthant below a half-space.
  rw [← preimage_halfSqRadii_setOf_sum_lt, weightMomentMap_eq_linearCombination_comp_halfSqRadii,
    image_comp, image_preimage_eq_inter_range, range_halfSqRadii]
  exact ((convex_setOf_sum_lt _).inter (convex_Ici 0)).linear_image _

/-- **The weight model moment map is open onto its image.** The moment map
`μ(q, p) = -½ Σ_i (q_i² + p_i²) α_i` sends every neighbourhood of a point `z` of `ℂ^ι` onto a
neighbourhood of `μ(z)` in the moment cone, the image of `μ`, for arbitrary weights `α`. -/
theorem image_mem_nhdsWithin_range_weightMomentMap (α : ι → StrongDual ℝ 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    {N : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)} (hN : N ∈ 𝓝 x) :
    weightMomentMap α '' N ∈ 𝓝[range (weightMomentMap α)] (weightMomentMap α x) := by
  rw [weightMomentMap_eq_linearCombination_comp_halfSqRadii, range_comp, range_halfSqRadii,
    image_comp]
  obtain ⟨N', hN', hN'N⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1
    (image_halfSqRadii_mem_nhdsWithin x hN)
  exact mem_of_superset
    ((Fintype.linearCombination ℝ (-α)).image_inter_Ici_mem_nhdsWithin
      (range_halfSqRadii.subset (mem_range_self x)) hN')
    (image_mono hN'N)

end TauCeti
