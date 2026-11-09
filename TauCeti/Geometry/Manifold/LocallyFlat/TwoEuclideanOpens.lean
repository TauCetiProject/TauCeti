/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
public import TauCeti.Geometry.Manifold.Boundary.BallExterior
import Mathlib.Topology.Compactification.OnePoint.Sphere
import TauCeti.Analysis.InnerProductSpace.Hemisphere
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Analysis.Normed.Module.Ball.Radial.Equiv
import TauCeti.Topology.Circle.Schoenflies
import TauCeti.Topology.ConnectedComponents

/-!
# A coordinate sphere in a compact space covered by two Euclidean open sets

Let `X` be a compact Hausdorff space covered by two open sets `U` and `V`, with a homeomorphism
`eU : U ≃ₜ E` onto a finite-dimensional real normed space. A space covered by two open sets each
homeomorphic to `E` is a sphere (Milnor 1959, Corollary 1; Rosen 1960, Lemma 1), and this file
supplies the parts of that argument which surround Brown's generalized Schoenflies theorem.

The compact set `X \ V` lies in `U`, so its coordinates are bounded: `‖eU x‖ < R` for some `R ≥ 0`
(`TauCeti.exists_nonneg_forall_notMem_norm_lt`). Every point of `U` with coordinates of norm at
least `R` then lies in `V`, so the exterior of the open coordinate ball of radius `R` lies in `V`
(`TauCeti.ballExterior_subset_of_forall_notMem_norm_lt`). The radial map
`(x, t) ↦ eU⁻¹ ((R + exp t) • x)` on the product of the unit sphere of `E` with the real line is
an open embedding into `V`
(`Homeomorph.coordinateSphereBicollar`), so it is a bicollar of the coordinate sphere of radius
`R + 1`, its slice `t = 0` (`Homeomorph.isBicollar_coordinateSphereBicollar`).

Now let `j : V → Sᵐ` be an open embedding into the unit sphere of a real normed space of dimension
`dim E + 1`, such as the inclusion of `V ≃ₜ E` into its one-point compactification. The image `Σ`
of the coordinate sphere separates `Sᵐ` into exactly two components
(`TauCeti.natCard_connectedComponents_sphere_compl_range_eq_two`). They are the image of the points
of `V` outside the closed coordinate ball of radius `R + 1`, and the complement of the image of the
points of `V` outside the open coordinate ball, which contains the points of `Sᵐ` outside `j(V)`.
The closure of the first component is the image under `j` of the complement `C` in `X` of the open
coordinate ball, its exterior `TauCeti.ballExterior` under `Subtype.val ∘ eU.symm`, a compact subset
of `V` (`Homeomorph.closure_connectedComponentIn_compl_range_coordinateSphereBicollar`).

Brown's theorem, applied to the bicollar of `Σ` in `Sᵐ`, identifies that closure with a closed
`m`-cell whose boundary sphere is `Σ`. The closed coordinate ball of radius `R + 1` is another
closed `m`-cell with boundary the coordinate sphere, and `X` is the union of the two cells glued
along their common boundary, which is a sphere
(`Topology.IsOpenEmbedding.nonempty_homeomorph_sphere_of_ballExterior`, by
`TauCeti.nonempty_homeomorph_sphere_of_union_closedBall`).

In dimension one, `Σ` is a pair of points of the circle and the generalized Schoenflies theorem is
elementary (`TauCeti.exists_closure_homeomorph_closedBall_of_finrank_eq_one`), so the argument is
complete: a compact Hausdorff space covered by two open sets homeomorphic to a one-dimensional
space is a circle
(`TauCeti.nonempty_homeomorph_sphere_of_two_euclidean_opens_of_finrank_eq_one`).

## Main declarations

* `TauCeti.exists_nonneg_forall_notMem_norm_lt`: the coordinates of the points of `U` outside `V`
  are bounded.
* `TauCeti.ballExterior_subset_of_forall_notMem_norm_lt`: the exterior of a coordinate ball
  containing those coordinates lies in `V`.
* `Homeomorph.coordinateSphereBicollar`: the radial bicollar `(x, t) ↦ eU⁻¹ ((R + exp t) • x)`
  of the coordinate sphere of radius `R + 1`, as a map into `V`.
* `Homeomorph.isBicollar_coordinateSphereBicollar`: it is a bicollar.
* `Homeomorph.range_coordinateSphereBicollar_mk_zero`: its zero slice is the coordinate sphere.
* `Homeomorph.connectedComponentIn_compl_range_coordinateSphereBicollar_of_mem` and
  `Homeomorph.connectedComponentIn_compl_range_coordinateSphereBicollar_of_notMem`: the two
  connected components of the complement of the coordinate sphere in `Sᵐ`.
* `Homeomorph.closure_connectedComponentIn_compl_range_coordinateSphereBicollar`: the closure of the
  outer component is the image of the exterior of the open coordinate ball.
* `Topology.IsOpenEmbedding.nonempty_homeomorph_sphere_of_ballExterior`: if the exterior of the
  open coordinate ball is a closed disc bounded by the coordinate sphere, `X` is a sphere.
* `TauCeti.nonempty_homeomorph_sphere_of_two_euclidean_opens_of_finrank_eq_one`: the two-open-cell
  lemma in dimension one.

## References

* J. Milnor, *Sommes de variétés différentiables et structures différentiables des sphères*,
  Bull. Soc. Math. France 87 (1959), 439–444, Theorem 1 and Corollary 1.
* R. H. Rosen, *A weak form of the star conjecture for manifolds*, Notices Amer. Math. Soc. 7
  (1960), abstract 570-28, p. 380, Lemma 1.
* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76.
-/

public section

open Function Metric Module Set Topology

namespace TauCeti

variable {X E F : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {U V : Set X} {R : ℝ}

omit [NormedSpace ℝ E] in
/-- In a compact space covered by open sets `U` and `V`, the points of `U` outside `V` have
bounded coordinates in any homeomorphism `eU : U ≃ₜ E` with a normed space. -/
theorem exists_nonneg_forall_notMem_norm_lt [CompactSpace X] (hV : IsOpen V)
    (hUV : U ∪ V = univ) (eU : U ≃ₜ E) : ∃ R, 0 ≤ R ∧ ∀ x : U, (x : X) ∉ V → ‖eU x‖ < R := by
  have hK : IsCompact ((↑) ⁻¹' Vᶜ : Set U) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.2 fun x hx ↦ (eq_univ_iff_forall.1 hUV x).resolve_right hx]
    exact hV.isClosed_compl.isCompact
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn eU.continuous.continuousOn
  exact ⟨max C 0 + 1, by positivity, fun x hx ↦ (hC x hx).trans_lt (by linarith [le_max_left C 0])⟩

omit [NormedSpace ℝ E] in
/-- In a space covered by `U` and `V`, if `r` bounds the coordinates of the points of `U` outside
`V` in `eU : U ≃ₜ E`, then the exterior of the open coordinate ball of radius `r` lies in `V`. -/
theorem ballExterior_subset_of_forall_notMem_norm_lt (hUV : U ∪ V = univ) {eU : U ≃ₜ E} {r : ℝ}
    (hr : ∀ x : U, (x : X) ∉ V → ‖eU x‖ < r) : ballExterior (Subtype.val ∘ eU.symm) r ⊆ V :=
  fun x hx ↦ by
    by_contra hxV
    have hxU : x ∈ U := (eq_univ_iff_forall.1 hUV x).resolve_right hxV
    exact mem_ballExterior.1 hx ⟨eU ⟨x, hxU⟩, mem_ball_zero_iff.2 (hr ⟨x, hxU⟩ hxV), by simp⟩

end TauCeti

namespace Homeomorph

open TauCeti

variable {X E F : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {U V : Set X} {R : ℝ}

/-- The radial bicollar of a coordinate sphere. Let `eU : U ≃ₜ E` and let `R` bound the
coordinates of the points of `U` outside `V`. Then `(x, t) ↦ eU⁻¹ ((R + exp t) • x)`, for `x` in
the unit sphere of `E`, takes values in `V`. For `R ≥ 0` it is a bicollar of the coordinate sphere
of radius `R + 1` (`Homeomorph.isBicollar_coordinateSphereBicollar`). -/
noncomputable def coordinateSphereBicollar (eU : U ≃ₜ E)
    (hR : ∀ x : U, (x : X) ∉ V → ‖eU x‖ < R) (p : sphere (0 : E) 1 × ℝ) : V :=
  ⟨eU.symm ((R + Real.exp p.2) • (p.1 : E)), by
    by_contra h
    have := hR _ h
    rw [Homeomorph.apply_symm_apply, norm_smul, norm_eq_of_mem_sphere, mul_one,
      Real.norm_eq_abs] at this
    linarith [le_abs_self (R + Real.exp p.2), Real.exp_pos p.2]⟩

variable (eU : U ≃ₜ E) (hR : ∀ x : U, (x : X) ∉ V → ‖eU x‖ < R)

/-- The point of `X` at time `t` above `x` on the radial bicollar has coordinates
`(R + exp t) • x`. -/
@[simp]
theorem coe_coordinateSphereBicollar (p : sphere (0 : E) 1 × ℝ) :
    (coordinateSphereBicollar eU hR p : X) = eU.symm ((R + Real.exp p.2) • (p.1 : E)) :=
  (rfl)

/-- A point of the bicollar lies in the image of a set of coordinates exactly when its radial
coordinate vector does. -/
private theorem coordinateSphereBicollar_mem_image_iff (s : Set E) (p : sphere (0 : E) 1 × ℝ) :
    (coordinateSphereBicollar eU hR p : X) ∈ (Subtype.val ∘ eU.symm) '' s ↔
      (R + Real.exp p.2) • (p.1 : E) ∈ s := by
  rw [coe_coordinateSphereBicollar, image_comp, Subtype.val_injective.mem_set_image,
    eU.symm.injective.mem_set_image]

/-- For `R ≥ 0` the radial coordinate vector `(R + exp t) • x` has norm `R + exp t`. -/
private theorem norm_add_exp_smul (hR0 : 0 ≤ R) (p : sphere (0 : E) 1 × ℝ) :
    ‖(R + Real.exp p.2) • (p.1 : E)‖ = R + Real.exp p.2 := by
  rw [norm_smul, norm_eq_of_mem_sphere, mul_one, Real.norm_of_nonneg (by positivity)]

/-- The radial bicollar of a coordinate sphere is an open embedding into `V`. -/
theorem isOpenEmbedding_coordinateSphereBicollar (hU : IsOpen U) (hV : IsOpen V) (hR0 : 0 ≤ R) :
    IsOpenEmbedding (coordinateSphereBicollar eU hR) := by
  refine (IsOpenEmbedding.of_comp_iff _ hV.isOpenEmbedding_subtypeVal).1 ?_
  have hρ : IsOpenEmbedding fun t : ℝ ↦ R + Real.exp t :=
    (Homeomorph.addLeft R).isOpenEmbedding.comp Real.isOpenEmbedding_exp
  exact hU.isOpenEmbedding_subtypeVal.comp (eU.symm.isOpenEmbedding.comp
    (hρ.smul_coe_sphere fun t ↦ by positivity))

/-- **The radial bicollar of a coordinate sphere.** For `R ≥ 0`, the map
`(x, t) ↦ eU⁻¹ ((R + exp t) • x)` into `V` is a bicollar of its zero slice, the coordinate sphere
of radius `R + 1`. -/
theorem isBicollar_coordinateSphereBicollar (hU : IsOpen U) (hV : IsOpen V) (hR0 : 0 ≤ R) :
    IsBicollar (fun x ↦ coordinateSphereBicollar eU hR (x, 0)) (coordinateSphereBicollar eU hR) :=
  ⟨isOpenEmbedding_coordinateSphereBicollar eU hR hU hV hR0, fun _ ↦ rfl⟩

/-- The zero slice of the radial bicollar is the coordinate sphere of radius `R + 1`. -/
theorem range_coordinateSphereBicollar_mk_zero (hR0 : 0 ≤ R) :
    range (fun x ↦ coordinateSphereBicollar eU hR (x, 0)) =
      Subtype.val ⁻¹' ((Subtype.val ∘ eU.symm) '' sphere (0 : E) (R + 1)) := by
  rw [← range_smul_coe_sphere (by linarith : (0 : ℝ) < R + 1), ← range_comp,
    ← Subtype.val_injective.preimage_image (range _), ← range_comp]
  simp only [comp_def, coe_coordinateSphereBicollar, Real.exp_zero]

section Separation

/-! In this section `C` is the image under `j` of the points of `V` in the exterior of the open
coordinate ball of radius `R + 1`, and `P` is the image of the points of `V` outside the closed
coordinate ball. They describe the two sides of the image `Σ` of the coordinate sphere. -/

variable {Y : Type*} [TopologicalSpace Y] {j : V → Y}

/-- The radial bicollar runs, at positive times, through the points of `V` outside the closed
coordinate ball of radius `R + 1`. -/
private theorem coordinateSphereBicollar_notMem_closedBall (hR0 : 0 ≤ R)
    (p : sphere (0 : E) 1 × ℝ) (hp : 0 < p.2) : (coordinateSphereBicollar eU hR p : X) ∉
      (Subtype.val ∘ eU.symm) '' closedBall (0 : E) (R + 1) := by
  rw [coordinateSphereBicollar_mem_image_iff, mem_closedBall_zero_iff, norm_add_exp_smul hR0,
    not_le, add_lt_add_iff_left]
  exact Real.one_lt_exp_iff.2 hp

/-- The radial bicollar runs, at negative times, through the open coordinate ball of radius
`R + 1`. -/
private theorem coordinateSphereBicollar_mem_ball (hR0 : 0 ≤ R) (p : sphere (0 : E) 1 × ℝ)
    (hp : p.2 < 0) : (coordinateSphereBicollar eU hR p : X) ∈
      (Subtype.val ∘ eU.symm) '' ball (0 : E) (R + 1) := by
  rw [coordinateSphereBicollar_mem_image_iff, mem_ball_zero_iff, norm_add_exp_smul hR0,
    add_lt_add_iff_left]
  exact Real.exp_lt_one_iff.2 hp

omit [TopologicalSpace Y] in
/-- The side `C` of `Σ` is the union of the other side `P` with `Σ`. -/
private theorem image_preimage_ballExterior_eq_union (hR0 : 0 ≤ R) :
    j '' (Subtype.val ⁻¹' ballExterior (Subtype.val ∘ eU.symm) (R + 1)) =
      j '' (Subtype.val ⁻¹' ((Subtype.val ∘ eU.symm) '' closedBall (0 : E) (R + 1))ᶜ) ∪
        range (j ∘ fun x ↦ coordinateSphereBicollar eU hR (x, 0)) := by
  rw [range_comp, range_coordinateSphereBicollar_mk_zero eU hR hR0, ← image_union,
    ← preimage_union, ← ballExterior_sdiff_image_sphere, sdiff_union_of_subset]
  exact fun x hx ↦ mem_ballExterior.2 (disjoint_left.1 (disjoint_image_of_injective
    (Subtype.val_injective.comp eU.symm.injective) sphere_disjoint_ball) hx)

omit [TopologicalSpace Y] in
/-- The complement of `Σ` is the union of the side `P` and the complement of the side `C`. -/
private theorem compl_range_coordinateSphereBicollar_eq_union (hR0 : 0 ≤ R)
    (hj : Injective j) : (range (j ∘ fun x ↦ coordinateSphereBicollar eU hR (x, 0)))ᶜ =
      j '' (Subtype.val ⁻¹' ((Subtype.val ∘ eU.symm) '' closedBall (0 : E) (R + 1))ᶜ) ∪
        (j '' (Subtype.val ⁻¹' ballExterior (Subtype.val ∘ eU.symm) (R + 1)))ᶜ := by
  have hPS : Disjoint
      (j '' (Subtype.val ⁻¹' ((Subtype.val ∘ eU.symm) '' closedBall (0 : E) (R + 1))ᶜ))
      (range (j ∘ fun x ↦ coordinateSphereBicollar eU hR (x, 0))) := by
    rw [range_comp, range_coordinateSphereBicollar_mk_zero eU hR hR0]
    exact disjoint_image_of_injective hj ((disjoint_compl_left_iff_subset.2
      (image_mono sphere_subset_closedBall)).preimage _)
  ext y
  have : y ∈ _ → y ∉ _ := fun h ↦ disjoint_left.1 hPS h
  rw [image_preimage_ballExterior_eq_union eU hR hR0, mem_compl_iff, mem_union, mem_compl_iff,
    mem_union]
  tauto

/-- The side `P` of `Σ` is open. -/
private theorem isOpen_image_preimage_compl_closedBall [T2Space X] [FiniteDimensional ℝ E]
    (hj : IsOpenEmbedding j) :
    IsOpen (j '' (Subtype.val ⁻¹' ((Subtype.val ∘ eU.symm) '' closedBall (0 : E) (R + 1))ᶜ)) :=
  hj.isOpenMap _ (((isCompact_closedBall _ _).image (continuous_subtype_val.comp
    eU.symm.continuous)).isClosed.isOpen_compl.preimage continuous_subtype_val)

omit [NormedSpace ℝ E] in
include hR in
/-- The side `C` of `Σ` is compact: the exterior of the coordinate ball is compact in `X`, and it
lies in `V`. -/
private theorem isCompact_image_preimage_ballExterior [CompactSpace X] (hU : IsOpen U)
    (hUV : U ∪ V = univ) (hj : Continuous j) :
    IsCompact (j '' (Subtype.val ⁻¹' ballExterior (Subtype.val ∘ eU.symm) (R + 1))) := by
  refine IsCompact.image ?_ hj
  rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2
    (ballExterior_subset_of_forall_notMem_norm_lt hUV fun x hx ↦ (hR x hx).trans (by linarith))]
  exact (hU.isOpenEmbedding_subtypeVal.comp eU.symm.isOpenEmbedding).isCompact_ballExterior

omit [TopologicalSpace Y] in
include hR in
/-- The side `P` of `Σ` is nonempty. -/
private theorem nonempty_image_preimage_compl_closedBall [Nontrivial E] (hR0 : 0 ≤ R) :
    (j '' (Subtype.val ⁻¹' ((Subtype.val ∘ eU.symm) '' closedBall (0 : E) (R + 1))ᶜ)).Nonempty :=
  have ⟨x, hx⟩ : (sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
  ⟨_, mem_image_of_mem j (coordinateSphereBicollar_notMem_closedBall eU hR hR0 (⟨x, hx⟩, 1)
    one_pos)⟩

omit [TopologicalSpace Y] in
include hR in
/-- The complement of the side `C` of `Σ` is nonempty. -/
private theorem nonempty_compl_image_preimage_ballExterior [Nontrivial E] (hR0 : 0 ≤ R)
    (hj : Injective j) :
    (j '' (Subtype.val ⁻¹' ballExterior (Subtype.val ∘ eU.symm) (R + 1)))ᶜ.Nonempty :=
  have ⟨x, hx⟩ : (sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
  ⟨j (coordinateSphereBicollar eU hR (⟨x, hx⟩, -1)), fun h ↦
    mem_ballExterior.1 (mem_preimage.1 (hj.mem_set_image.1 h))
      (coordinateSphereBicollar_mem_ball eU hR hR0 (⟨x, hx⟩, -1) (by norm_num))⟩

include hR in
/-- The side `C` of `Σ` is the closure of the side `P`: `Σ` lies in the closure of the outer side
of its bicollar. -/
private theorem closure_image_preimage_compl_closedBall [CompactSpace X] [T2Space Y]
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ) (hR0 : 0 ≤ R)
    (hj : IsOpenEmbedding j) :
    closure (j '' (Subtype.val ⁻¹' ((Subtype.val ∘ eU.symm) '' closedBall (0 : E) (R + 1))ᶜ)) =
      j '' (Subtype.val ⁻¹' ballExterior (Subtype.val ∘ eU.symm) (R + 1)) := by
  have hb := (isBicollar_coordinateSphereBicollar eU hR hU hV hR0).isOpenEmbedding_comp hj
  rw [image_preimage_ballExterior_eq_union eU hR hR0]
  refine (closure_minimal subset_union_left ?_).antisymm (union_subset subset_closure ?_)
  · rw [← image_preimage_ballExterior_eq_union eU hR hR0]
    exact (isCompact_image_preimage_ballExterior eU hR hU hUV hj.continuous).isClosed
  rintro _ ⟨x, rfl⟩
  refine closure_mono ?_ (hb.apply_mem_closure_image (s := Ioi 0) (by simp) x)
  rintro _ ⟨p, hp, rfl⟩
  exact mem_image_of_mem j (coordinateSphereBicollar_notMem_closedBall eU hR hR0 p hp.2)

end Separation

section Sphere

variable [CompactSpace X] [T2Space X] [FiniteDimensional ℝ E] [Nontrivial E]
  (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ) (hR0 : 0 ≤ R)
  (hEF : finrank ℝ F = finrank ℝ E + 1) {j : V → sphere (0 : F) 1} (hj : IsOpenEmbedding j)
include hU hV hUV hR0 hEF hj

/-- **The outer component of the complement of a coordinate sphere.** Let `j` embed `V` openly in
the unit sphere `Sᵐ` of a real normed space of dimension `dim E + 1`. The image of the points of
`V` outside the closed coordinate ball of radius `R + 1` is a connected component of the
complement in `Sᵐ` of the image of the coordinate sphere. -/
theorem connectedComponentIn_compl_range_coordinateSphereBicollar_of_mem {y : sphere (0 : F) 1}
    (hy : y ∈ j '' (Subtype.val ⁻¹' ((Subtype.val ∘ eU.symm) '' closedBall (0 : E) (R + 1))ᶜ)) :
    connectedComponentIn (range (j ∘ fun x ↦ coordinateSphereBicollar eU hR (x, 0)))ᶜ y =
      j '' (Subtype.val ⁻¹' ((Subtype.val ∘ eU.symm) '' closedBall (0 : E) (R + 1))ᶜ) := by
  have hb := (isBicollar_coordinateSphereBicollar eU hR hU hV hR0).isOpenEmbedding_comp hj
  exact connectedComponentIn_eq_of_natCard_eq_two
    (natCard_connectedComponents_sphere_compl_range_eq_two hEF hb.continuous hb.injective)
    (isOpen_image_preimage_compl_closedBall eU hj)
    (isCompact_image_preimage_ballExterior eU hR hU hUV hj.continuous).isClosed.isOpen_compl
    (disjoint_compl_right_iff_subset.2
      (image_preimage_ballExterior_eq_union eU hR hR0 ▸ subset_union_left))
    (compl_range_coordinateSphereBicollar_eq_union eU hR hR0 hj.injective).symm
    (nonempty_compl_image_preimage_ballExterior eU hR hR0 hj.injective) hy

/-- **The inner component of the complement of a coordinate sphere.** Let `j` embed `V` openly in
the unit sphere `Sᵐ` of a real normed space of dimension `dim E + 1`. The points of `Sᵐ` outside
the image of the points of `V` in the exterior `TauCeti.ballExterior` of the open coordinate ball
of radius `R + 1` form a connected component of the complement of the image of the coordinate
sphere. This component contains the image of the points of `V` inside the open coordinate ball,
and every point of `Sᵐ` outside the image of `j`. -/
theorem connectedComponentIn_compl_range_coordinateSphereBicollar_of_notMem {y : sphere (0 : F) 1}
    (hy : y ∉ j '' (Subtype.val ⁻¹' ballExterior (Subtype.val ∘ eU.symm) (R + 1))) :
    connectedComponentIn (range (j ∘ fun x ↦ coordinateSphereBicollar eU hR (x, 0)))ᶜ y =
      (j '' (Subtype.val ⁻¹' ballExterior (Subtype.val ∘ eU.symm) (R + 1)))ᶜ := by
  have hb := (isBicollar_coordinateSphereBicollar eU hR hU hV hR0).isOpenEmbedding_comp hj
  exact connectedComponentIn_eq_of_natCard_eq_two
    (natCard_connectedComponents_sphere_compl_range_eq_two hEF hb.continuous hb.injective)
    (isCompact_image_preimage_ballExterior eU hR hU hUV hj.continuous).isClosed.isOpen_compl
    (isOpen_image_preimage_compl_closedBall eU hj)
    (disjoint_compl_left_iff_subset.2
      (image_preimage_ballExterior_eq_union eU hR hR0 ▸ subset_union_left))
    (by rw [compl_range_coordinateSphereBicollar_eq_union eU hR hR0 hj.injective, union_comm])
    (nonempty_image_preimage_compl_closedBall eU hR hR0) hy

/-- **The closure of the outer component is the exterior of the open coordinate ball.** Let `j`
embed `V` openly in the unit sphere `Sᵐ` of a real normed space of dimension `dim E + 1`. For a
point `y` of the image of the points of `V` outside the closed coordinate ball of radius `R + 1`,
the closure of the connected component of `y` in the complement of the image of the coordinate
sphere is the image under `j` of the exterior `TauCeti.ballExterior` in `X` of the open
coordinate ball, which lies in `V`. -/
theorem closure_connectedComponentIn_compl_range_coordinateSphereBicollar {y : sphere (0 : F) 1}
    (hy : y ∈ j '' (Subtype.val ⁻¹' ((Subtype.val ∘ eU.symm) '' closedBall (0 : E) (R + 1))ᶜ)) :
    closure (connectedComponentIn (range (j ∘ fun x ↦ coordinateSphereBicollar eU hR (x, 0)))ᶜ y) =
      j '' (Subtype.val ⁻¹' ballExterior (Subtype.val ∘ eU.symm) (R + 1)) := by
  rw [connectedComponentIn_compl_range_coordinateSphereBicollar_of_mem eU hR hU hV hUV hR0 hEF hj
    hy, closure_image_preimage_compl_closedBall eU hR hU hV hUV hR0 hj]

end Sphere

end Homeomorph

namespace Topology.IsOpenEmbedding

open TauCeti

variable {X E F : Type*} [TopologicalSpace X] [T2Space X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : E → X} {r : ℝ}

/-- **A closed coordinate ball and a closed disc glued along their boundaries form a sphere.**
Let `φ : E → X` be an open embedding of a finite-dimensional real normed space into a Hausdorff
space, and let `r > 0`. Suppose the exterior `TauCeti.ballExterior φ r` of the open coordinate ball
of radius `r` is homeomorphic to the closed unit ball of `E` by a homeomorphism carrying the
coordinate sphere `φ '' sphere 0 r` onto the unit sphere. Then `X` is homeomorphic to the unit
sphere of any real normed space of dimension `dim E + 1`. The two discs are the closed coordinate
ball and its exterior; the gluing homeomorphism of their boundary spheres is arbitrary. -/
theorem nonempty_homeomorph_sphere_of_ballExterior (hφ : IsOpenEmbedding φ) (hr : 0 < r)
    (hF : finrank ℝ F = finrank ℝ E + 1) (e : ballExterior φ r ≃ₜ closedBall (0 : E) 1)
    (he : ∀ x : ballExterior φ r, (x : X) ∈ φ '' sphere 0 r ↔ ‖(e x : E)‖ = 1) :
    Nonempty (X ≃ₜ sphere (0 : F) 1) := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  set n := finrank ℝ E
  have hn : finrank ℝ E = finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simp [n]
  let D := closedBallHomeomorphOfFinrankEq hn
  have hD (v : closedBall (0 : E) 1) : ‖(D v : EuclideanSpace ℝ (Fin n))‖ = 1 ↔ ‖(v : E)‖ = 1 :=
    by simp [D, ContinuousLinearEquiv.norm_unitBallHomeomorph_eq_one_iff]
  -- The closed coordinate ball, rescaled to the closed unit ball.
  let S : closedBall (0 : E) r ≃ₜ closedBall (0 : E) 1 :=
    (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')).subtype fun v ↦ by
      simp [norm_smul, abs_of_pos hr, inv_mul_le_iff₀ hr]
  let eA : φ '' closedBall 0 r ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    ((hφ.isEmbedding.homeomorphImage _).symm.trans S).trans D
  have hAB : φ '' closedBall 0 r ∪ ballExterior φ r = univ :=
    eq_univ_of_forall fun x ↦ (em (x ∈ φ '' ball 0 r)).elim
      (fun hx ↦ Or.inl (image_mono ball_subset_closedBall hx))
      fun hx ↦ Or.inr (mem_ballExterior.2 hx)
  -- A point of the coordinate ball lies in the exterior exactly when it is on the sphere.
  have hAe (x : φ '' closedBall 0 r) :
      (x : X) ∈ ballExterior φ r ↔ ‖(eA x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    obtain ⟨v, rfl⟩ := (hφ.isEmbedding.homeomorphImage (closedBall 0 r)).surjective x
    have hv : ‖(v : E)‖ ≤ r := mem_closedBall_zero_iff.1 v.2
    simp only [eA, Homeomorph.trans_apply, Homeomorph.symm_apply_apply, hD, S,
      Homeomorph.subtype_apply_coe, Homeomorph.smulOfNeZero_apply]
    -- `IsEmbedding.homeomorphImage` has no lemma for its underlying point, which is `φ v` by
    -- definition.
    change φ v ∈ _ ↔ _
    rw [mem_ballExterior, hφ.injective.mem_set_image, mem_ball_zero_iff, not_lt, norm_smul,
      norm_inv, Real.norm_of_nonneg hr.le, inv_mul_eq_one₀ hr.ne']
    exact ⟨fun h ↦ (hv.antisymm h).symm, fun h ↦ h.symm.ge⟩
  -- A point of the exterior lies in the coordinate ball exactly when it is on the sphere.
  have hBe (x : ballExterior φ r) :
      (x : X) ∈ φ '' closedBall 0 r ↔ ‖((e.trans D) x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    rw [Homeomorph.trans_apply, hD, ← he]
    refine ⟨fun ⟨v, hv, hvx⟩ ↦ ⟨v, ?_, hvx⟩, fun h ↦ image_mono sphere_subset_closedBall h⟩
    have hvb : v ∉ ball (0 : E) r := fun h ↦ mem_ballExterior.1 x.2 ⟨v, h, hvx⟩
    rw [mem_ball_zero_iff, not_lt] at hvb
    exact mem_sphere_zero_iff_norm.2 ((mem_closedBall_zero_iff.1 hv).antisymm hvb)
  obtain ⟨g⟩ := nonempty_homeomorph_sphere_of_union_closedBall
    (E := EuclideanSpace ℝ (Fin (n + 1))) (by simp)
    ((isCompact_closedBall (0 : E) r).image hφ.continuous).isClosed hφ.isClosed_ballExterior hAB
    eA (e.trans D) hAe hBe
  exact ⟨g.trans (sphereHomeomorphOfFinrankEq (by simp [hF, n]))⟩

end Topology.IsOpenEmbedding

namespace TauCeti

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {U V : Set X}

/-- **A compact space covered by two open arcs is a circle.** Let `X` be a compact Hausdorff space
covered by two open sets `U` and `V`, each homeomorphic to a one-dimensional real normed space `E`.
Then `X` is homeomorphic to the unit sphere of any two-dimensional real normed space.

This is the one-dimensional case of the two-open-cell lemma (Milnor 1959, Corollary 1; Rosen
1960, Lemma 1). The closed coordinate ball of radius `R + 1` in `U`, with `R` bounding the
coordinates of `X \ V`, is one closed arc. Its exterior `C` lies in `V`, and in the circle
`OnePoint V` its image is the closure of a complementary component of the image of the coordinate
sphere, a pair of points. By the generalized Schoenflies theorem in dimension one
(`TauCeti.exists_closure_homeomorph_closedBall_of_finrank_eq_one`), `C` is therefore another closed
arc bounded by the same two points, and `X` is a circle by
`Topology.IsOpenEmbedding.nonempty_homeomorph_sphere_of_ballExterior`. -/
theorem nonempty_homeomorph_sphere_of_two_euclidean_opens_of_finrank_eq_one {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hE : finrank ℝ E = 1) (hF : finrank ℝ F = 2)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ) (eU : U ≃ₜ E) (eV : V ≃ₜ E) :
    Nonempty (X ≃ₜ sphere (0 : F) 1) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  obtain ⟨R, hR0, hR⟩ := exists_nonneg_forall_notMem_norm_lt hV hUV eU
  have hφ : IsOpenEmbedding (Subtype.val ∘ eU.symm) :=
    hU.isOpenEmbedding_subtypeVal.comp eU.symm.isOpenEmbedding
  -- The open embedding of `V` into the circle `S¹`, its one-point compactification.
  let j : V → sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    onePointEquivSphereOfFinrankEq (V := E) (ι := Fin 2) (by simp [hE]) ∘
      ((↑) : E → OnePoint E) ∘ eV
  have hj : IsOpenEmbedding j := (Homeomorph.isOpenEmbedding _).comp
    (OnePoint.isOpenEmbedding_coe.comp eV.isOpenEmbedding)
  have hEF : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = finrank ℝ E + 1 := by simp [hE]
  -- The bicollar of the coordinate sphere of radius `R + 1`, and its image `σ` in the circle.
  let b := Homeomorph.coordinateSphereBicollar eU hR
  have hb := Homeomorph.isOpenEmbedding_coordinateSphereBicollar eU hR hU hV hR0
  let β (p : sphere (0 : E) 1 × Icc (-1 : ℝ) 1) := j (b (p.1, p.2))
  have hβ : Continuous β := hj.continuous.comp (hb.continuous.comp (by fun_prop))
  have hβinj : Injective β := fun p q h ↦ by
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj (hb.injective (hj.injective h))
    exact Prod.ext h₁ (Subtype.ext h₂)
  set σ := range (j ∘ fun x ↦ b (x, 0)) with hσ_def
  have hσ : β '' (univ ×ˢ {t : Icc (-1 : ℝ) 1 | (t : ℝ) = 0}) = σ := by
    ext y
    refine ⟨?_, fun ⟨x, hx⟩ ↦ ⟨(x, ⟨0, by norm_num⟩), ⟨mem_univ _, rfl⟩, hx⟩⟩
    rintro ⟨⟨x, t⟩, ⟨-, ht⟩, rfl⟩
    have ht' : (t : ℝ) = 0 := ht
    exact ⟨x, by simp only [β, comp_apply, ht']⟩
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hdisj, hunion, -, -, hAe, hBe, -⟩ :=
    exists_closure_homeomorph_closedBall_of_finrank_eq_one hE (by simp) hβ hβinj
  rw [hσ] at hunion hAe hBe
  -- A point `y` on the outer side of `σ`; its component in the complement of `σ` is `A` or `B`.
  obtain ⟨u⟩ : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  set y := j (b (u, 1))
  have hy : y ∈ j '' (Subtype.val ⁻¹' ((Subtype.val ∘ eU.symm) '' closedBall (0 : E) (R + 1))ᶜ) :=
    mem_image_of_mem j (Homeomorph.coordinateSphereBicollar_notMem_closedBall eU hR hR0 (u, 1)
      one_pos)
  have hyσ : y ∈ σᶜ := fun ⟨x, hx⟩ ↦ one_ne_zero (congrArg Prod.snd (hb.injective
    (hj.injective hx))).symm
  have hcomp {S T : Set (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)} (hS : IsOpen S)
      (hT : IsOpen T) (hSc : IsConnected S) (hST : Disjoint S T) (hSTu : S ∪ T = σᶜ)
      (hyS : y ∈ S) : connectedComponentIn σᶜ y = S :=
    (isPreconnected_connectedComponentIn.subset_left_of_subset_union hS hT hST
      (hSTu ▸ connectedComponentIn_subset _ _) ⟨y, mem_connectedComponentIn hyσ, hyS⟩).antisymm
      (hSc.isPreconnected.subset_connectedComponentIn hyS (hSTu ▸ subset_union_left))
  -- The exterior `C` of the open coordinate ball lies in `V`, and `j` identifies it with the
  -- closure of the component of `y`, a closed arc bounded by `σ`.
  have hCV : ballExterior (Subtype.val ∘ eU.symm) (R + 1) ⊆ V :=
    ballExterior_subset_of_forall_notMem_norm_lt hUV fun x hx ↦ (hR x hx).trans (by linarith)
  have hk := hj.isEmbedding.comp (IsEmbedding.inclusion hCV)
  have hrange : range (j ∘ inclusion hCV) = closure (connectedComponentIn σᶜ y) := by
    rw [Homeomorph.closure_connectedComponentIn_compl_range_coordinateSphereBicollar eU hR hU hV
      hUV hR0 hEF hj hy, range_comp, range_inclusion]
    rfl
  obtain ⟨e, he⟩ : ∃ e : range (j ∘ inclusion hCV) ≃ₜ closedBall (0 : E) 1,
      ∀ z : range (j ∘ inclusion hCV), (z : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ∈ σ ↔
        ‖(e z : E)‖ = 1 := by
    rw [hrange]
    rcases (hunion ▸ hyσ : y ∈ A ∪ B) with hyA | hyB
    · rw [hcomp hAo hBo hAc hdisj hunion hyA]
      exact hAe
    · rw [hcomp hBo hAo hBc hdisj.symm (union_comm A B ▸ hunion) hyB]
      exact hBe
  refine hφ.nonempty_homeomorph_sphere_of_ballExterior (by linarith) (by omega)
    (hk.toHomeomorph.trans e) fun x ↦ ?_
  rw [Homeomorph.trans_apply, ← he, IsEmbedding.toHomeomorph_apply_coe, hσ_def, range_comp,
    comp_apply, hj.injective.mem_set_image,
    Homeomorph.range_coordinateSphereBicollar_mk_zero eU hR hR0, mem_preimage, coe_inclusion hCV]

end TauCeti
