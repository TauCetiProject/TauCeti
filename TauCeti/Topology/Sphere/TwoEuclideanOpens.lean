/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar
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
(`TauCeti.coordinateSphereCollar`), so it is a bicollar of the coordinate sphere of radius
`R + 1`, its slice `t = 0` (`TauCeti.isBicollar_coordinateSphereCollar`).

Now let `j : V → Sᵐ` be an open embedding into the unit sphere of a real normed space of dimension
`dim E + 1`, such as the inclusion of `V ≃ₜ E` into its one-point compactification. The image `Σ`
of the coordinate sphere separates `Sᵐ` into exactly two components
(`TauCeti.natCard_connectedComponents_sphere_compl_range_eq_two`). They are the image of the points
of `V` outside the closed coordinate ball of radius `R + 1`, and the complement of the image of the
points of `V` outside the open coordinate ball, which contains the points of `Sᵐ` outside `j(V)`.
The closure of the first component is the image under `j` of the complement `C` in `X` of the open
coordinate ball, a compact subset of `V`
(`TauCeti.closure_connectedComponentIn_compl_range_coordinateSphereCollar`).

Brown's theorem, applied to the bicollar of `Σ` in `Sᵐ`, identifies that closure with a closed
`m`-cell whose boundary sphere is `Σ`. The closed coordinate ball of radius `R + 1` is another
closed `m`-cell with boundary the coordinate sphere, and `X` is the union of the two cells glued
along their common boundary, which is a sphere by
`TauCeti.nonempty_homeomorph_sphere_of_union_closedBall`.

## Main declarations

* `TauCeti.exists_nonneg_forall_notMem_norm_lt`: the coordinates of the points of `U` outside `V`
  are bounded.
* `TauCeti.coordinateSphereCollar`: the radial bicollar `(x, t) ↦ eU⁻¹ ((R + exp t) • x)` of the
  coordinate sphere of radius `R + 1`, as a map into `V`.
* `TauCeti.isBicollar_coordinateSphereCollar`: it is a bicollar.
* `TauCeti.range_coordinateSphereCollar_mk_zero`: its zero slice is the coordinate sphere.
* `TauCeti.connectedComponentIn_compl_range_coordinateSphereCollar_of_mem` and
  `TauCeti.connectedComponentIn_compl_range_coordinateSphereCollar_of_notMem`: the two connected
  components of the complement of the coordinate sphere in `Sᵐ`.
* `TauCeti.closure_connectedComponentIn_compl_range_coordinateSphereCollar`: the closure of the
  outer component is the image of the complement of the open coordinate ball.

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
of radius `R + 1` (`TauCeti.isBicollar_coordinateSphereCollar`). -/
noncomputable def coordinateSphereCollar (eU : U ≃ₜ E)
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
theorem coe_coordinateSphereCollar (p : sphere (0 : E) 1 × ℝ) :
    (coordinateSphereCollar eU hR p : X) = eU.symm ((R + Real.exp p.2) • (p.1 : E)) :=
  (rfl)

/-- A point of the bicollar lies in the image of a set of coordinates exactly when its radial
coordinate vector does. -/
private theorem coordinateSphereCollar_mem_image_iff (s : Set E) (p : sphere (0 : E) 1 × ℝ) :
    (coordinateSphereCollar eU hR p : X) ∈ ((↑) '' (eU ⁻¹' s) : Set X) ↔
      (R + Real.exp p.2) • (p.1 : E) ∈ s := by
  rw [coe_coordinateSphereCollar, Subtype.val_injective.mem_set_image, mem_preimage,
    Homeomorph.apply_symm_apply]

/-- For `R ≥ 0` the radial coordinate vector `(R + exp t) • x` has norm `R + exp t`. -/
private theorem norm_add_exp_smul (hR0 : 0 ≤ R) (p : sphere (0 : E) 1 × ℝ) :
    ‖(R + Real.exp p.2) • (p.1 : E)‖ = R + Real.exp p.2 := by
  rw [norm_smul, norm_eq_of_mem_sphere, mul_one, Real.norm_of_nonneg (by positivity)]

/-- The radial bicollar of a coordinate sphere is an open embedding into `V`. -/
theorem isOpenEmbedding_coordinateSphereCollar (hU : IsOpen U) (hV : IsOpen V) (hR0 : 0 ≤ R) :
    IsOpenEmbedding (coordinateSphereCollar eU hR) := by
  refine (IsOpenEmbedding.of_comp_iff _ hV.isOpenEmbedding_subtypeVal).1 ?_
  have hρ : IsOpenEmbedding fun t : ℝ ↦ R + Real.exp t :=
    (Homeomorph.addLeft R).isOpenEmbedding.comp Real.isOpenEmbedding_exp
  exact hU.isOpenEmbedding_subtypeVal.comp (eU.symm.isOpenEmbedding.comp
    (hρ.smul_coe_sphere fun t ↦ by positivity))

/-- **The radial bicollar of a coordinate sphere.** For `R ≥ 0`, the map
`(x, t) ↦ eU⁻¹ ((R + exp t) • x)` into `V` is a bicollar of its zero slice, the coordinate sphere
of radius `R + 1`. -/
theorem isBicollar_coordinateSphereCollar (hU : IsOpen U) (hV : IsOpen V) (hR0 : 0 ≤ R) :
    IsBicollar (fun x ↦ coordinateSphereCollar eU hR (x, 0)) (coordinateSphereCollar eU hR) :=
  ⟨isOpenEmbedding_coordinateSphereCollar eU hR hU hV hR0, fun _ ↦ rfl⟩

/-- The zero slice of the radial bicollar is the coordinate sphere of radius `R + 1`. -/
theorem range_coordinateSphereCollar_mk_zero (hR0 : 0 ≤ R) :
    range (fun x ↦ coordinateSphereCollar eU hR (x, 0)) =
      {v : V | (v : X) ∈ ((↑) '' (eU ⁻¹' sphere (0 : E) (R + 1)) : Set X)} := by
  ext v
  refine ⟨?_, fun ⟨u, hu, huv⟩ ↦ ?_⟩
  · rintro ⟨x, rfl⟩
    rw [mem_ofPred_eq, coordinateSphereCollar_mem_image_iff, mem_sphere_zero_iff_norm,
      norm_add_exp_smul hR0, Real.exp_zero]
  · -- The point `u` has coordinates `(R + 1) • x` with `x` on the unit sphere.
    have hpos : (0 : ℝ) < R + 1 := by linarith
    have hu' : ‖eU u‖ = R + 1 := mem_sphere_zero_iff_norm.1 hu
    refine ⟨⟨(R + 1)⁻¹ • eU u, ?_⟩, Subtype.ext ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, hu', Real.norm_of_nonneg (inv_nonneg.2 hpos.le),
        inv_mul_cancel₀ hpos.ne']
    · rw [coe_coordinateSphereCollar, Real.exp_zero, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul,
        Homeomorph.symm_apply_apply, huv]

section Separation

variable {Y : Type*} [TopologicalSpace Y] {j : V → Y}

/-- The radial bicollar runs, at positive times, through the points of `V` outside the closed
coordinate ball of radius `R + 1`. -/
private theorem coordinateSphereCollar_notMem_closedBall (hR0 : 0 ≤ R) (p : sphere (0 : E) 1 × ℝ)
    (hp : 0 < p.2) : (coordinateSphereCollar eU hR p : X) ∉
      ((↑) '' (eU ⁻¹' closedBall (0 : E) (R + 1)) : Set X) := by
  rw [coordinateSphereCollar_mem_image_iff, mem_closedBall_zero_iff, norm_add_exp_smul hR0,
    not_le, add_lt_add_iff_left]
  exact Real.one_lt_exp_iff.2 hp

/-- The radial bicollar runs, at negative times, through the open coordinate ball of radius
`R + 1`. -/
private theorem coordinateSphereCollar_mem_ball (hR0 : 0 ≤ R) (p : sphere (0 : E) 1 × ℝ)
    (hp : p.2 < 0) : (coordinateSphereCollar eU hR p : X) ∈
      ((↑) '' (eU ⁻¹' ball (0 : E) (R + 1)) : Set X) := by
  rw [coordinateSphereCollar_mem_image_iff, mem_ball_zero_iff, norm_add_exp_smul hR0,
    add_lt_add_iff_left]
  exact Real.exp_lt_one_iff.2 hp

variable [CompactSpace X]

omit [NormedSpace ℝ E] in
include hR in
/-- The points of `V` outside an open coordinate ball of radius at least `R` form a compact set:
they are the complement in `X` of that ball, which lies in `V`. -/
private theorem isCompact_setOf_notMem_ball (hU : IsOpen U) (hUV : U ∪ V = univ) {r : ℝ}
    (hRr : R ≤ r) :
    IsCompact {v : V | (v : X) ∉ ((↑) '' (eU ⁻¹' ball (0 : E) r) : Set X)} := by
  set B : Set X := (↑) '' (eU ⁻¹' ball (0 : E) r)
  have hB : IsOpen B := hU.isOpenMap_subtype_val _ (isOpen_ball.preimage eU.continuous)
  have hBV : Bᶜ ⊆ V := fun x hx ↦ by
    by_contra hxV
    have hxU : x ∈ U := (eq_univ_iff_forall.1 hUV x).resolve_right hxV
    exact hx ⟨⟨x, hxU⟩, mem_ball_zero_iff.2 ((hR ⟨x, hxU⟩ hxV).trans_le hRr), rfl⟩
  have hBc : ((↑) '' {v : V | (v : X) ∉ B} : Set X) = Bᶜ := by
    ext x
    refine ⟨?_, fun hx ↦ ⟨⟨x, hBV hx⟩, hx, rfl⟩⟩
    rintro ⟨v, hv, rfl⟩
    exact hv
  rw [Subtype.isCompact_iff, hBc]
  exact hB.isClosed_compl.isCompact

/-- The facts behind the separation by the coordinate sphere. In `Y`, the complement of the image
`S` of the coordinate sphere of radius `R + 1` is the disjoint union of two nonempty open sets: the
image `P` of the points of `V` outside the closed coordinate ball, and the complement of the image
`C` of the points of `V` outside the open coordinate ball. Moreover `C` is the closure of `P`. -/
private theorem separation_coordinateSphereCollar [T2Space X] [T2Space Y] [FiniteDimensional ℝ E]
    [Nontrivial E] (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ) (hR0 : 0 ≤ R)
    (hj : IsOpenEmbedding j) :
    let P := j '' {v : V | (v : X) ∉ ((↑) '' (eU ⁻¹' closedBall (0 : E) (R + 1)) : Set X)}
    let C := j '' {v : V | (v : X) ∉ ((↑) '' (eU ⁻¹' ball (0 : E) (R + 1)) : Set X)}
    (range (j ∘ fun x ↦ coordinateSphereCollar eU hR (x, 0)))ᶜ = P ∪ Cᶜ ∧ IsOpen P ∧ IsOpen Cᶜ ∧
      Disjoint P Cᶜ ∧ P.Nonempty ∧ Cᶜ.Nonempty ∧ closure P = C := by
  set B : Set X := (↑) '' (eU ⁻¹' ball (0 : E) (R + 1))
  set D : Set X := (↑) '' (eU ⁻¹' closedBall (0 : E) (R + 1))
  set S : Set X := (↑) '' (eU ⁻¹' sphere (0 : E) (R + 1))
  intro P C
  have hb : IsBicollar (j ∘ fun x ↦ coordinateSphereCollar eU hR (x, 0))
      (j ∘ coordinateSphereCollar eU hR) :=
    (isBicollar_coordinateSphereCollar eU hR hU hV hR0).isOpenEmbedding_comp hj
  have hS : range (j ∘ fun x ↦ coordinateSphereCollar eU hR (x, 0)) = j '' {v : V | (v : X) ∈ S} :=
    by rw [range_comp, range_coordinateSphereCollar_mk_zero eU hR hR0]
  -- In `X`, the closed coordinate ball is the disjoint union of the open ball and the sphere.
  have hD : D = B ∪ S := by
    simp only [B, D, S, ← ball_union_sphere, preimage_union, image_union]
  have hBS : Disjoint B S := by
    refine disjoint_left.2 ?_
    rintro _ ⟨u, hu, rfl⟩ ⟨u', hu', huu'⟩
    obtain rfl := Subtype.val_injective huu'
    exact (mem_ball_zero_iff.1 hu).ne (mem_sphere_zero_iff_norm.1 hu')
  have hCPS : C = P ∪ j '' {v : V | (v : X) ∈ S} := by
    simp only [C, P, ← image_union]
    congr 1
    ext v
    have : (v : X) ∈ B → (v : X) ∉ S := fun h ↦ disjoint_left.1 hBS h
    simp only [mem_ofPred_eq, mem_union, hD]
    tauto
  have hPS : Disjoint P (j '' {v : V | (v : X) ∈ S}) :=
    disjoint_image_of_injective hj.injective (disjoint_left.2 fun v hv hvS ↦ hv (hD ▸ Or.inr hvS))
  have hPC : P ⊆ C := hCPS ▸ subset_union_left
  have hCcomp : IsCompact C := (isCompact_setOf_notMem_ball eU hR hU hUV (by linarith)).image
    hj.continuous
  -- The closed coordinate ball is compact, hence closed in `X`.
  have hDclosed : IsClosed D := by
    simp only [D, ← Homeomorph.image_symm, image_image]
    exact ((isCompact_closedBall _ _).image
      (continuous_subtype_val.comp eU.symm.continuous)).isClosed
  obtain ⟨x, hx⟩ : (sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
  refine ⟨?_, hj.isOpenMap _ (hDclosed.isOpen_compl.preimage continuous_subtype_val),
    hCcomp.isClosed.isOpen_compl, disjoint_compl_right_iff_subset.2 hPC,
    ⟨_, mem_image_of_mem j (coordinateSphereCollar_notMem_closedBall eU hR hR0 (⟨x, hx⟩, 1)
      one_pos)⟩,
    ⟨_, fun h ↦ (hj.injective.mem_set_image.1 h) (coordinateSphereCollar_mem_ball eU hR hR0
      (⟨x, hx⟩, -1) (by norm_num))⟩, ?_⟩
  · ext y
    have : y ∈ P → y ∉ j '' {v : V | (v : X) ∈ S} := fun h ↦ disjoint_left.1 hPS h
    rw [hS, mem_compl_iff, mem_union, mem_compl_iff, hCPS, mem_union]
    tauto
  · -- The sphere lies in the closure of the outer side of its bicollar.
    refine (closure_minimal hPC hCcomp.isClosed).antisymm ?_
    rw [hCPS, ← hS]
    refine union_subset subset_closure ?_
    rintro _ ⟨x, rfl⟩
    refine closure_mono ?_ (hb.apply_mem_closure_image (s := Ioi 0) (by simp) x)
    rintro _ ⟨p, hp, rfl⟩
    exact mem_image_of_mem j (coordinateSphereCollar_notMem_closedBall eU hR hR0 p hp.2)

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
theorem connectedComponentIn_compl_range_coordinateSphereCollar_of_mem {y : sphere (0 : F) 1}
    (hy : y ∈ j '' {v : V | (v : X) ∉ ((↑) '' (eU ⁻¹' closedBall (0 : E) (R + 1)) : Set X)}) :
    connectedComponentIn (range (j ∘ fun x ↦ coordinateSphereCollar eU hR (x, 0)))ᶜ y =
      j '' {v : V | (v : X) ∉ ((↑) '' (eU ⁻¹' closedBall (0 : E) (R + 1)) : Set X)} := by
  obtain ⟨hcompl, hP, hC, hPC, -, hCne, -⟩ :=
    separation_coordinateSphereCollar eU hR hU hV hUV hR0 hj
  have hb := (isBicollar_coordinateSphereCollar eU hR hU hV hR0).isOpenEmbedding_comp hj
  exact connectedComponentIn_eq_of_natCard_eq_two
    (natCard_connectedComponents_sphere_compl_range_eq_two hEF hb.continuous hb.injective)
    hP hC hPC hcompl.symm hCne hy

/-- **The inner component of the complement of a coordinate sphere.** Let `j` embed `V` openly in
the unit sphere `Sᵐ` of a real normed space of dimension `dim E + 1`. The points of `Sᵐ` outside
the image of the points of `V` outside the open coordinate ball of radius `R + 1` form a connected
component of the complement of the image of the coordinate sphere. This component contains the
image of the points of `V` inside the open coordinate ball, and every point of `Sᵐ` outside the
image of `j`. -/
theorem connectedComponentIn_compl_range_coordinateSphereCollar_of_notMem {y : sphere (0 : F) 1}
    (hy : y ∉ j '' {v : V | (v : X) ∉ ((↑) '' (eU ⁻¹' ball (0 : E) (R + 1)) : Set X)}) :
    connectedComponentIn (range (j ∘ fun x ↦ coordinateSphereCollar eU hR (x, 0)))ᶜ y =
      (j '' {v : V | (v : X) ∉ ((↑) '' (eU ⁻¹' ball (0 : E) (R + 1)) : Set X)})ᶜ := by
  obtain ⟨hcompl, hP, hC, hPC, hPne, -, -⟩ :=
    separation_coordinateSphereCollar eU hR hU hV hUV hR0 hj
  have hb := (isBicollar_coordinateSphereCollar eU hR hU hV hR0).isOpenEmbedding_comp hj
  exact connectedComponentIn_eq_of_natCard_eq_two
    (natCard_connectedComponents_sphere_compl_range_eq_two hEF hb.continuous hb.injective)
    hC hP hPC.symm (by rw [hcompl, union_comm]) hPne hy

/-- **The closure of the outer component is the complement of the open coordinate ball.** Let `j`
embed `V` openly in the unit sphere `Sᵐ` of a real normed space of dimension `dim E + 1`. For a
point `y` of the image of the points of `V` outside the closed coordinate ball of radius `R + 1`,
the closure of the connected component of `y` in the complement of the image of the coordinate
sphere is the image under `j` of the complement in `X` of the open coordinate ball, which lies
in `V`. -/
theorem closure_connectedComponentIn_compl_range_coordinateSphereCollar {y : sphere (0 : F) 1}
    (hy : y ∈ j '' {v : V | (v : X) ∉ ((↑) '' (eU ⁻¹' closedBall (0 : E) (R + 1)) : Set X)}) :
    closure (connectedComponentIn (range (j ∘ fun x ↦ coordinateSphereCollar eU hR (x, 0)))ᶜ y) =
      j '' {v : V | (v : X) ∉ ((↑) '' (eU ⁻¹' ball (0 : E) (R + 1)) : Set X)} := by
  obtain ⟨-, -, -, -, -, -, hclosure⟩ := separation_coordinateSphereCollar eU hR hU hV hUV hR0 hj
  rw [connectedComponentIn_compl_range_coordinateSphereCollar_of_mem eU hR hU hV hUV hR0 hEF hj hy,
    hclosure]

end Sphere

end TauCeti
