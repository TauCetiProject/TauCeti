/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
public import TauCeti.Geometry.Manifold.Boundary.BallExterior
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Analysis.Normed.Module.Ball.Radial.Equiv
import TauCeti.Topology.ConnectedComponents

/-!
# A coordinate sphere in a compact space covered by two Euclidean open sets

Let `X` be a compact Hausdorff space covered by two open sets `U` and `V`, with a homeomorphism
`eU : U ≃ₜ E` onto a finite-dimensional real normed space. A space covered by two open sets each
homeomorphic to `E` is a sphere (Milnor 1959, Corollary 1; Rosen 1960, Lemma 1), and this file
supplies the part of that argument which precedes Brown's generalized Schoenflies theorem.

The compact set `X \ V` lies in `U`, so its coordinates are bounded: `‖eU x‖ < R` for some `R ≥ 0`
(`TauCeti.exists_nonneg_forall_notMem_norm_lt`). Every point of `U` with coordinates of norm at
least `R` then lies in `V`. The radial map `(x, t) ↦ eU⁻¹ ((R + exp t) • x)` on the product of the
unit sphere of `E` with the real line is an open embedding into `V`
(`TauCeti.coordinateSphereBicollar`), so it is a bicollar of the coordinate sphere of radius
`R + 1`, its slice `t = 0` (`TauCeti.isBicollar_coordinateSphereBicollar`).

Now let `j : V → Sᵐ` be an open embedding into the unit sphere of a real normed space of dimension
`dim E + 1`, such as the inclusion of `V ≃ₜ E` into its one-point compactification. The image `Σ`
of the coordinate sphere separates `Sᵐ` into exactly two components
(`TauCeti.natCard_connectedComponents_sphere_compl_range_eq_two`). They are the image of the points
of `V` outside the closed coordinate ball of radius `R + 1`, and the complement of the image of the
points of `V` outside the open coordinate ball, which contains the points of `Sᵐ` outside `j(V)`.
The closure of the first component is the image under `j` of the complement `C` in `X` of the open
coordinate ball, its exterior `TauCeti.ballExterior` under `Subtype.val ∘ eU.symm`, a compact subset
of `V` (`TauCeti.closure_connectedComponentIn_compl_range_coordinateSphereBicollar`).

Brown's theorem, applied to the bicollar of `Σ` in `Sᵐ`, identifies that closure with a closed
`m`-cell whose boundary sphere is `Σ`. The closed coordinate ball of radius `R + 1` is another
closed `m`-cell with boundary the coordinate sphere, and `X` is the union of the two cells glued
along their common boundary, which is a sphere by
`TauCeti.nonempty_homeomorph_sphere_of_union_closedBall`.

## Main declarations

* `TauCeti.exists_nonneg_forall_notMem_norm_lt`: the coordinates of the points of `U` outside `V`
  are bounded.
* `TauCeti.coordinateSphereBicollar`: the radial bicollar `(x, t) ↦ eU⁻¹ ((R + exp t) • x)` of the
  coordinate sphere of radius `R + 1`, as a map into `V`.
* `TauCeti.isBicollar_coordinateSphereBicollar`: it is a bicollar.
* `TauCeti.range_coordinateSphereBicollar_mk_zero`: its zero slice is the coordinate sphere.
* `TauCeti.connectedComponentIn_compl_range_coordinateSphereBicollar_of_mem` and
  `TauCeti.connectedComponentIn_compl_range_coordinateSphereBicollar_of_notMem`: the two connected
  components of the complement of the coordinate sphere in `Sᵐ`.
* `TauCeti.closure_connectedComponentIn_compl_range_coordinateSphereBicollar`: the closure of the
  outer component is the image of the exterior of the open coordinate ball.

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

/-- The radial bicollar of a coordinate sphere. Let `eU : U ≃ₜ E` and let `R` bound the
coordinates of the points of `U` outside `V`. Then `(x, t) ↦ eU⁻¹ ((R + exp t) • x)`, for `x` in
the unit sphere of `E`, takes values in `V`. For `R ≥ 0` it is a bicollar of the coordinate sphere
of radius `R + 1` (`TauCeti.isBicollar_coordinateSphereBicollar`). -/
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
  have hsub : ballExterior (Subtype.val ∘ eU.symm) (R + 1) ⊆ V := fun x hx ↦ by
    by_contra hxV
    have hxU : x ∈ U := (eq_univ_iff_forall.1 hUV x).resolve_right hxV
    exact mem_ballExterior.1 hx
      ⟨eU ⟨x, hxU⟩, mem_ball_zero_iff.2 ((hR ⟨x, hxU⟩ hxV).trans (by linarith)), by simp⟩
  refine IsCompact.image ?_ hj
  rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hsub]
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

end TauCeti
