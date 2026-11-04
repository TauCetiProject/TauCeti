/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import TauCeti.AlgebraicTopology.Singular.Straightening

/-!
# Straight simplices in the hyperboloid model of hyperbolic space

Equip `ℝ × E`, for a real normed space `E`, with the Minkowski square norm
`TauCeti.minkowskiNormSq (t, x) = t² - ‖x‖²`. The upper sheet of the unit hyperboloid,
`TauCeti.hyperboloid E = {(t, x) | t > 0, t² - ‖x‖² = 1}`, lies in the open future light cone
`TauCeti.futureCone E = {(t, x) | ‖x‖ < t}`, which is convex, and the radial projection
`v ↦ v / √(t² - ‖x‖²)` (`TauCeti.hyperboloidNormalize`) retracts the cone onto the hyperboloid.
When `E` is an inner product space of dimension `n`, the hyperboloid with the metric induced by
the Minkowski form is hyperbolic `n`-space, its geodesics are its intersections with planes
through the origin, and its isometries are the linear maps of `ℝ × E` preserving the Minkowski
form and the future cone.

This presents the hyperboloid as a retract of a convex set
(`TauCeti.hyperboloidConvexRetract`), so `TauCeti.ConvexRetract.straighten` straightens its
singular simplices: a singular simplex with vertices `v₀, …, vₖ` becomes the straight simplex
`t ↦ (∑ tᵢ vᵢ) / √(minkowskiNormSq (∑ tᵢ vᵢ))`, the radial projection of the linear simplex in the
cone, whose image is the geodesic simplex spanned by the vertices. The straight-line homotopy
`TauCeti.ConvexRetract.straightenHomotopy` joins every singular simplex to its straightening.

A continuous linear map `L` of `ℝ × E` preserving the Minkowski square norm and the future cone
restricts to a self-map `TauCeti.hyperboloidMap` of the hyperboloid and commutes with the radial
projection, so straightening and its homotopy commute with it
(`TauCeti.straighten_comp_toSSet_map_hyperboloidMap`,
`TauCeti.cylinderMap_comp_toSSet_map_hyperboloidMap`). This equivariance under isometries is the
property of straightening that the Gromov–Thurston proportionality theorem uses, to make the
straightening descend to singular chains of a closed hyperbolic manifold, the quotient of the
hyperboloid by a discrete group of isometries; neither that descent nor the identification of
the hyperboloid with other models of hyperbolic space is carried out here.

## References

* W. P. Thurston, *The Geometry and Topology of Three-Manifolds*, Princeton lecture notes
  (1978–1980), Sections 2.2 (the hyperboloid model) and 6.1 (straight simplices).
* R. Benedetti, C. Petronio, *Lectures on Hyperbolic Geometry*, Springer Universitext (1992),
  Section A.2 (the hyperboloid model) and Chapter C (straightening).
* J. Ratcliffe, *Foundations of Hyperbolic Manifolds*, Springer GTM 149, 3rd ed. (2019),
  Sections 3.2 (the hyperboloid model) and 4.1 (Lorentz transformations).
-/

public section

noncomputable section

open Set CategoryTheory MonoidalCategory

open scoped Simplicial

universe u

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E]

/-- The **Minkowski square norm** `t² - ‖x‖²` of a vector `(t, x)` of `ℝ × E`. -/
def minkowskiNormSq (v : ℝ × E) : ℝ :=
  v.1 ^ 2 - ‖v.2‖ ^ 2

lemma minkowskiNormSq_def (v : ℝ × E) : minkowskiNormSq v = v.1 ^ 2 - ‖v.2‖ ^ 2 :=
  (rfl)

@[fun_prop]
lemma continuous_minkowskiNormSq : Continuous (minkowskiNormSq : ℝ × E → ℝ) := by
  unfold minkowskiNormSq
  fun_prop

variable (E) in
/-- The **open future light cone** `{(t, x) | ‖x‖ < t}` of `ℝ × E`. -/
def futureCone : Set (ℝ × E) :=
  {v | ‖v.2‖ < v.1}

@[simp]
lemma mem_futureCone {v : ℝ × E} : v ∈ futureCone E ↔ ‖v.2‖ < v.1 :=
  Iff.rfl

/-- Vectors of the future cone have positive Minkowski square norm. -/
lemma minkowskiNormSq_pos {v : ℝ × E} (hv : v ∈ futureCone E) : 0 < minkowskiNormSq v := by
  rw [minkowskiNormSq_def, sub_pos]
  exact pow_lt_pow_left₀ hv (norm_nonneg _) two_ne_zero

variable (E) in
/-- The upper sheet `{(t, x) | t > 0, t² - ‖x‖² = 1}` of the unit hyperboloid in `ℝ × E`: for an
inner product space `E`, the hyperboloid model of hyperbolic space. -/
def hyperboloid : Set (ℝ × E) :=
  {v | 0 < v.1 ∧ minkowskiNormSq v = 1}

@[simp]
lemma mem_hyperboloid {v : ℝ × E} : v ∈ hyperboloid E ↔ 0 < v.1 ∧ minkowskiNormSq v = 1 :=
  Iff.rfl

lemma hyperboloid_subset_futureCone : hyperboloid E ⊆ futureCone E := by
  rintro v ⟨hv, hq⟩
  rw [minkowskiNormSq_def] at hq
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hv.le two_ne_zero).1 (by linarith)

variable [NormedSpace ℝ E]

@[simp]
lemma minkowskiNormSq_smul (c : ℝ) (v : ℝ × E) :
    minkowskiNormSq (c • v) = c ^ 2 * minkowskiNormSq v := by
  simp only [minkowskiNormSq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

lemma convex_futureCone : Convex ℝ (futureCone E) := by
  simpa [futureCone] using
    (convexOn_univ_norm (E := E)).convex_strict_epigraph.linear_preimage
      (LinearEquiv.prodComm ℝ ℝ E).toLinearMap

/-- The **radial projection** `v ↦ v / √(minkowskiNormSq v)`, which retracts the future cone onto
the hyperboloid. -/
def hyperboloidNormalize (v : ℝ × E) : ℝ × E :=
  (√(minkowskiNormSq v))⁻¹ • v

/-- The formula for radial projection onto the unit hyperboloid. -/
lemma hyperboloidNormalize_def (v : ℝ × E) :
    hyperboloidNormalize v = (√(minkowskiNormSq v))⁻¹ • v :=
  (rfl)

lemma hyperboloidNormalize_mem {v : ℝ × E} (hv : v ∈ futureCone E) :
    hyperboloidNormalize v ∈ hyperboloid E := by
  have hq := minkowskiNormSq_pos hv
  have hs : 0 < √(minkowskiNormSq v) := Real.sqrt_pos.2 hq
  refine ⟨?_, ?_⟩
  · simp only [hyperboloidNormalize, Prod.smul_fst, smul_eq_mul]
    exact mul_pos (inv_pos.2 hs) ((norm_nonneg _).trans_lt hv)
  · rw [hyperboloidNormalize, minkowskiNormSq_smul, inv_pow, Real.sq_sqrt hq.le,
      inv_mul_cancel₀ hq.ne']

@[simp]
lemma hyperboloidNormalize_of_mem {v : ℝ × E} (hv : v ∈ hyperboloid E) :
    hyperboloidNormalize v = v := by
  rw [hyperboloidNormalize, hv.2, Real.sqrt_one, inv_one, one_smul]

lemma continuousOn_hyperboloidNormalize :
    ContinuousOn (hyperboloidNormalize : ℝ × E → ℝ × E) (futureCone E) :=
  ((Real.continuous_sqrt.comp continuous_minkowskiNormSq).continuousOn.inv₀
    fun _ hv ↦ (Real.sqrt_pos.2 (minkowskiNormSq_pos hv)).ne').smul continuousOn_id

variable (E) in
-- Expose the carrier so the retraction accepts points of `futureCone E` without transport.
/-- The hyperboloid as a retract of the future cone, along the radial projection. -/
@[expose]
def hyperboloidConvexRetract : ConvexRetract (hyperboloid E) (ℝ × E) where
  carrier := futureCone E
  convex := convex_futureCone
  embed := ⟨Subtype.val, continuous_subtype_val⟩
  embed_mem v := hyperboloid_subset_futureCone v.2
  retraction := ⟨fun v ↦ ⟨hyperboloidNormalize v, hyperboloidNormalize_mem v.2⟩,
    (continuousOn_hyperboloidNormalize.comp_continuous continuous_subtype_val
      Subtype.prop).subtype_mk _⟩
  retraction_embed v := Subtype.ext (hyperboloidNormalize_of_mem v.2)

lemma hyperboloidConvexRetract_carrier : (hyperboloidConvexRetract E).carrier = futureCone E :=
  (rfl)

@[simp]
lemma hyperboloidConvexRetract_embed_apply (v : hyperboloid E) :
    (hyperboloidConvexRetract E).embed v = v :=
  (rfl)

@[simp]
lemma coe_hyperboloidConvexRetract_retraction_apply (v : futureCone E) :
    ((hyperboloidConvexRetract E).retraction v : ℝ × E) = hyperboloidNormalize (v : ℝ × E) :=
  (rfl)

/-! ### Lorentz transformations -/

section Lorentz

variable {L : (ℝ × E) →L[ℝ] ℝ × E} (hq : ∀ v, minkowskiNormSq (L v) = minkowskiNormSq v)
  (hL : MapsTo L (futureCone E) (futureCone E))
include hq

/-- A linear map preserving the Minkowski square norm commutes with the radial projection. -/
lemma hyperboloidNormalize_map (v : ℝ × E) :
    hyperboloidNormalize (L v) = L (hyperboloidNormalize v) := by
  rw [hyperboloidNormalize, hyperboloidNormalize, hq, map_smul]

include hL

lemma map_mem_hyperboloid {v : ℝ × E} (hv : v ∈ hyperboloid E) : L v ∈ hyperboloid E :=
  ⟨(norm_nonneg _).trans_lt (hL (hyperboloid_subset_futureCone hv)), (hq v).trans hv.2⟩

/-- The self-map of the hyperboloid induced by a continuous linear map of `ℝ × E` preserving the
Minkowski square norm and the future cone. -/
def hyperboloidMap : C(hyperboloid E, hyperboloid E) :=
  ⟨fun v ↦ ⟨L v, map_mem_hyperboloid hq hL v.2⟩,
    (L.continuous.comp continuous_subtype_val).subtype_mk _⟩

@[simp]
lemma coe_hyperboloidMap_apply (v : hyperboloid E) : (hyperboloidMap hq hL v : ℝ × E) = L v :=
  (rfl)

/-- **Straightening in hyperbolic space commutes with isometries**: a continuous linear map of
`ℝ × E` preserving the Minkowski square norm and the future cone commutes with straightening of
singular simplices of the hyperboloid. -/
theorem straighten_comp_toSSet_map_hyperboloidMap :
    (hyperboloidConvexRetract E).straighten ≫
        TopCat.toSSet.map (TopCat.ofHom (hyperboloidMap hq hL)) =
      TopCat.toSSet.map (TopCat.ofHom (hyperboloidMap hq hL)) ≫
        (hyperboloidConvexRetract E).straighten :=
  ConvexRetract.straighten_comp_toSSet_map _ (L := L.toLinearMap.toAffineMap) (fun _ ↦ rfl) hL
    fun v _ ↦ Subtype.ext (hyperboloidNormalize_map hq v)

/-- A continuous linear map of `ℝ × E` preserving the Minkowski square norm and the future cone
commutes with the straight-line homotopy from singular simplices of the hyperboloid to their
straightenings. -/
theorem cylinderMap_comp_toSSet_map_hyperboloidMap :
    (hyperboloidConvexRetract E).cylinderMap ≫
        TopCat.toSSet.map (TopCat.ofHom (hyperboloidMap hq hL)) =
      TopCat.toSSet.map (TopCat.ofHom (hyperboloidMap hq hL)) ▷ Δ[1] ≫
        (hyperboloidConvexRetract E).cylinderMap :=
  ConvexRetract.cylinderMap_comp_toSSet_map _ (L := L.toLinearMap.toAffineMap) (fun _ ↦ rfl) hL
    fun v _ ↦ Subtype.ext (hyperboloidNormalize_map hq v)

end Lorentz

end TauCeti
