/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
public import TauCeti.Geometry.Manifold.Boundary.BallExterior
import Mathlib.Topology.Compactification.OnePoint.Sphere
import TauCeti.Analysis.InnerProductSpace.Hemisphere
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Analysis.Normed.Module.Ball.Radial.Equiv
import TauCeti.Geometry.Manifold.LocallyFlat.Separation
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.Schoenflies.Disc

/-!
# A compact space covered by two Euclidean open sets is a sphere

Let `X` be a compact Hausdorff space covered by two open sets `U` and `V`, with a homeomorphism
`eU : U ≃ₜ E` onto a finite-dimensional real normed space. A space covered by two open sets each
homeomorphic to `E`, of dimension `m > 0`, is homeomorphic to the sphere `Sᵐ` (Milnor 1959,
Corollary 1; Rosen 1960, Lemma 1). This file proves it
(`TauCeti.nonempty_homeomorph_sphere_of_two_euclidean_opens`), by bicollaring a coordinate sphere
in `U ∩ V` and applying Brown's generalized Schoenflies theorem. It is the topological input of the
recognition of the sphere from a smooth function with exactly two, possibly degenerate, critical
points.

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

Brown's theorem (`TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn_compl_range`),
applied to the bicollar of `Σ` in `Sᵐ`, identifies that closure with a closed `m`-cell whose
boundary sphere is `Σ`. The closed coordinate ball of radius `R + 1` is another closed `m`-cell
with boundary the coordinate sphere, and `X` is the union of the two cells glued along their
common boundary, which is a sphere by `TauCeti.nonempty_homeomorph_sphere_of_union_closedBall`.

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
* `TauCeti.nonempty_homeomorph_sphere_of_two_euclidean_opens`: a compact Hausdorff space covered by
  two open sets homeomorphic to `E`, with `dim E > 0`, is homeomorphic to the sphere `Sᵐ`.

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
  have hC := isCompact_image_preimage_ballExterior eU hR hU hUV hj.continuous
  have hcompl := compl_range_coordinateSphereBicollar_eq_union eU hR hR0 hj.injective
  rw [image_preimage_ballExterior_eq_union eU hR hR0] at hC hcompl ⊢
  exact ((isBicollar_coordinateSphereBicollar eU hR hU hV hR0).isOpenEmbedding_comp
    hj).closure_eq_union_range hC.isClosed.isOpen_compl
    (disjoint_compl_right_iff_subset.2 subset_union_left) hcompl (s := Ioi 0) (by simp)
    fun p hp ↦ mem_image_of_mem j (coordinateSphereBicollar_notMem_closedBall eU hR hR0 p hp.2)

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

namespace TauCeti

open Homeomorph

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompactSpace X] [T2Space X] {U V : Set X} {R : ℝ}

/-- **The outer cell.** In a compact Hausdorff space covered by open sets `U ≃ₜ E` and `V ≃ₜ E`,
with `dim E > 0` and `R ≥ 0` bounding the coordinates of the points of `U` outside `V`, the
exterior of the open coordinate ball of radius `R + 1` is a closed disc whose boundary sphere is the
coordinate sphere. This is Brown's generalized Schoenflies theorem, applied to the image of the
coordinate sphere in the one-point compactification of `V`. -/
private theorem exists_homeomorph_ballExterior_closedBall (hE : 0 < finrank ℝ E) (hU : IsOpen U)
    (hV : IsOpen V) (hUV : U ∪ V = univ) (eU : U ≃ₜ E) (eV : V ≃ₜ E) (hR0 : 0 ≤ R)
    (hR : ∀ x : U, (x : X) ∉ V → ‖eU x‖ < R) :
    ∃ e : ballExterior (Subtype.val ∘ eU.symm) (R + 1) ≃ₜ closedBall (0 : E) 1,
      ∀ x, ‖(e x : E)‖ = 1 ↔ (x : X) ∈ (Subtype.val ∘ eU.symm) '' sphere (0 : E) (R + 1) := by
  have : FiniteDimensional ℝ E := .of_finrank_pos hE
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hE
  -- Embed `V ≃ₜ E` openly in the sphere `Sᵐ`, as the complement of a point.
  let Φ : OnePoint E ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  let j : V → sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1 := Φ ∘ (↑) ∘ eV
  have hj : IsOpenEmbedding j :=
    Φ.isOpenEmbedding.comp (OnePoint.isOpenEmbedding_coe.comp eV.isOpenEmbedding)
  have hEF : finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) = finrank ℝ E + 1 := by simp
  have hb := (isBicollar_coordinateSphereBicollar eU hR hU hV hR0).isOpenEmbedding_comp hj
  -- A point `y` outside the closed coordinate ball lies off the image `Σ` of the coordinate sphere.
  obtain ⟨x₀⟩ : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  set y := j (coordinateSphereBicollar eU hR (x₀, 1))
  have hy : y ∈ j '' (Subtype.val ⁻¹'
      ((Subtype.val ∘ eU.symm) '' closedBall (0 : E) (R + 1))ᶜ) :=
    mem_image_of_mem j (coordinateSphereBicollar_notMem_closedBall eU hR hR0 (x₀, 1) one_pos)
  have hyS : y ∉ range (j ∘ fun x ↦ coordinateSphereBicollar eU hR (x, 0)) := by
    have hcompl := compl_range_coordinateSphereBicollar_eq_union eU hR hR0 hj.injective
    exact (Set.ext_iff.1 hcompl y).2 (Or.inl hy)
  obtain ⟨h, -, hh⟩ := hb.exists_homeomorph_closure_connectedComponentIn_compl_range hEF hE hyS
  have hcl := closure_connectedComponentIn_compl_range_coordinateSphereBicollar eU hR hU hV hUV
    hR0 hEF hj hy
  -- The exterior `C` lies in `V`, and `j` carries it homeomorphically onto the closure of the
  -- component of `y`.
  set C := ballExterior (Subtype.val ∘ eU.symm) (R + 1)
  have hCV : C ⊆ V :=
    ballExterior_subset_of_forall_notMem_norm_lt hUV fun x hx ↦ (hR x hx).trans (by linarith)
  have hK (c : C) : (j ∘ inclusion hCV) c ∈ closure (connectedComponentIn
      (range (j ∘ fun x ↦ coordinateSphereBicollar eU hR (x, 0)))ᶜ y) :=
    hcl ▸ mem_image_of_mem j (show inclusion hCV c ∈ Subtype.val ⁻¹' C from c.2)
  have hψ := (hj.isEmbedding.comp (IsEmbedding.inclusion hCV)).codRestrict _ hK
  have hsurj : Surjective (codRestrict _ _ hK) := fun z ↦ by
    obtain ⟨v, hv, hvz⟩ : (z : sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1) ∈
        j '' (Subtype.val ⁻¹' C) := hcl ▸ z.2
    exact ⟨⟨v, hv⟩, Subtype.ext hvz⟩
  refine ⟨(hψ.toHomeomorphOfSurjective hsurj).trans h, fun c ↦ ?_⟩
  rw [Homeomorph.trans_apply, IsEmbedding.toHomeomorphOfSurjective_apply,
    ← mem_sphere_zero_iff_norm, hh, val_codRestrict_apply, comp_apply, range_comp,
    hj.injective.mem_set_image, range_coordinateSphereBicollar_mk_zero eU hR hR0, mem_preimage,
    coe_inclusion]

/-- **A compact space covered by two Euclidean open sets is a sphere** (Milnor 1959, Corollary 1;
Rosen 1960, Lemma 1). Let `X` be a compact Hausdorff space covered by two open sets `U` and `V`,
each homeomorphic to a real normed space `E` of finite dimension `m > 0`. Then `X` is homeomorphic
to the unit sphere `Sᵐ` of any real inner product space of dimension `m + 1`.

The two homeomorphisms are arbitrary; in particular no compatibility on `U ∩ V` is assumed. The
hypothesis `m > 0` cannot be dropped: a point is covered by two copies of `ℝ⁰` and is not `S⁰`. -/
theorem nonempty_homeomorph_sphere_of_two_euclidean_opens {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] (hE : 0 < finrank ℝ E) (hG : finrank ℝ G = finrank ℝ E + 1)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ) (eU : U ≃ₜ E) (eV : V ≃ₜ E) :
    Nonempty (X ≃ₜ sphere (0 : G) 1) := by
  have : FiniteDimensional ℝ E := .of_finrank_pos hE
  obtain ⟨R, hR0, hR⟩ := exists_nonneg_forall_notMem_norm_lt hV hUV eU
  set φ : E → X := Subtype.val ∘ eU.symm
  obtain ⟨eC, heC⟩ := exists_homeomorph_ballExterior_closedBall hE hU hV hUV eU eV hR0 hR
  have hφ : IsOpenEmbedding φ := hU.isOpenEmbedding_subtypeVal.comp eU.symm.isOpenEmbedding
  -- The closed coordinate ball `D` of radius `R + 1` is the inner cell.
  set D := φ '' closedBall (0 : E) (R + 1)
  have hD (v : closedBall (0 : E) (R + 1)) : (φ ∘ Subtype.val) v ∈ D := mem_image_of_mem φ v.2
  have hψ := (hφ.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict D hD
  have hsurj : Surjective (codRestrict _ D hD) := fun ⟨_, v, hv, hvx⟩ ↦
    ⟨⟨v, hv⟩, Subtype.ext hvx⟩
  obtain ⟨S, hS⟩ := exists_homeomorph_closedBall_one_norm_eq (V := E)
    (by linarith : (0 : ℝ) < R + 1)
  -- Both cells are carried to the closed unit ball of a Euclidean space.
  have hm : finrank ℝ E = finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E))) := by simp
  let T := closedBallHomeomorphOfFinrankEq hm
  have hT (v : closedBall (0 : E) 1) :
      ‖(T v : EuclideanSpace ℝ (Fin (finrank ℝ E)))‖ = 1 ↔ ‖(v : E)‖ = 1 := by
    simp [T]
  refine nonempty_homeomorph_sphere_of_union_closedBall (by rw [hG, finrank_euclideanSpace_fin])
    ((isCompact_closedBall _ _).image hφ.continuous).isClosed hφ.isClosed_ballExterior
    (eq_univ_of_forall fun x ↦ ?_) (((hψ.toHomeomorphOfSurjective hsurj).symm.trans S).trans T)
    (eC.trans T) (fun x ↦ ?_) (fun x ↦ ?_)
  · by_cases hx : x ∈ φ '' ball (0 : E) (R + 1)
    exacts [.inl (image_mono ball_subset_closedBall hx), .inr (mem_ballExterior.2 hx)]
  · -- A point of `D` lies in the exterior exactly when its coordinates have norm `R + 1`.
    obtain ⟨v, rfl⟩ := hsurj x
    rw [← IsEmbedding.toHomeomorphOfSurjective_apply hψ hsurj, Homeomorph.trans_apply,
      Homeomorph.trans_apply, Homeomorph.symm_apply_apply, hT, hS,
      IsEmbedding.toHomeomorphOfSurjective_apply, val_codRestrict_apply, mem_ballExterior,
      comp_apply, hφ.injective.mem_set_image, mem_ball_zero_iff, not_lt]
    exact ⟨fun h ↦ le_antisymm (mem_closedBall_zero_iff.1 v.2) h, fun h ↦ h.ge⟩
  · -- A point of the exterior lies in `D` exactly when it lies on the coordinate sphere.
    rw [Homeomorph.trans_apply, hT, heC]
    refine ⟨fun hxD ↦ by_contra fun hxS ↦ ?_, fun h ↦ image_mono sphere_subset_closedBall h⟩
    exact (Set.ext_iff.1 (ballExterior_sdiff_image_sphere φ (R + 1)) x).1 ⟨x.2, hxS⟩ hxD

end TauCeti
