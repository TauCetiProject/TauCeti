/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.AffineSpace.Basis
public import TauCeti.LinearAlgebra.AffineSpace.Matrix

/-!
# Affine normalization of convex bodies

A convex body in an `n`-dimensional real affine space can be moved by an affine equivalence to a
position between two balls whose radii depend only on the space. This is the normalization that
lets estimates for convex sets be proved for sets of unit size and transferred back; in the
regularity theory of the Monge–Ampère equation it is applied to the sections
`{y | u y < u x + ⟪p, y - x⟫ + h}` of a convex function `u`.

The normalization comes from a simplex of maximal volume. Let `K` be a compact set whose affine
span is the whole `n`-dimensional space, and choose `n + 1` points of `K` spanning a simplex of
maximal volume, where volume is measured by the absolute value of the determinant of the matrix of
barycentric coordinates relative to a fixed affine basis (the determinant itself is the signed
volume). Replacing the vertex `b i` by a point `x` multiplies this determinant by the barycentric
coordinate `b.coord i x` (`AffineBasis.det_toMatrix_update`), so maximality of its absolute value
forces `|b.coord i x| ≤ 1` for every `x ∈ K`
(`IsCompact.exists_affineBasis_abs_coord_le_one`).

In terms of the simplex `Δ = convexHull (range b)` with centroid `c`, the points whose barycentric
coordinates are all at most `1` form the image of `Δ` under the homothety of ratio `-n` about `c`
(`AffineBasis.mem_image_homothety_convexHull_iff`). Thus every compact spanning `K` contains the
vertices of a simplex `Δ` and lies inside its homothetic image of ratio `-n`
(`IsCompact.exists_affineBasis_subset_image_homothety_convexHull`); when `K` is convex it contains
`Δ` itself. Mapping `Δ` to a fixed reference simplex by an affine equivalence then gives the
normalization by balls (`TauCeti.exists_affineEquiv_ball_subset_image_subset_ball`).

John's theorem gives the sharper statement in which the simplex is replaced by the ellipsoid of
maximal volume and the ratio `-n` by `n`, or by `√n` for centrally symmetric bodies. For the
normalization, a ratio depending only on the dimension suffices.

## Main statements

* `IsCompact.exists_affineBasis_abs_coord_le_one`: a compact set spanning a finite-dimensional real
  affine space contains an affine basis relative to which all its points have barycentric
  coordinates in `[-1, 1]`;
* `AffineBasis.mem_image_homothety_convexHull_iff`: the image of the simplex of an affine basis
  under the homothety of ratio `-n` about its centroid is the set of points whose barycentric
  coordinates are at most `1`;
* `IsCompact.exists_affineBasis_subset_image_homothety_convexHull`: a compact spanning set contains
  the vertices of a simplex and lies in the image of that simplex under the homothety of ratio `-n`
  about its centroid;
* `TauCeti.exists_affineEquiv_ball_subset_image_subset_ball`: in a finite-dimensional real normed
  space there is `r > 0` such that every bounded convex set with nonempty interior is mapped by
  some affine equivalence to a set between the balls of radii `r` and `1` about `0`.

## References

* F. John, *Extremum problems with inequalities as subsidiary conditions*, Studies and Essays
  Presented to R. Courant on his 60th Birthday, Interscience, 1948, 187–204.
* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §1.8 (normalized convex sets).
* K. Ball, *An elementary introduction to modern convex geometry*, in *Flavors of Geometry*,
  MSRI Publications 31, Cambridge University Press, 1997, Lecture 3.
-/

public section

open Set Module Metric

/-! ### A simplex of maximal volume -/

section Compact

variable {ι V P : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [PseudoMetricSpace P] [NormedAddTorsor V P]

/-- **Affine bases with bounded barycentric coordinates.** A compact set `K` whose affine span is
the whole finite-dimensional real affine space contains an affine basis `b`, indexed by any type
with `finrank + 1` elements, such that every point of `K` has all its barycentric coordinates
relative to `b` in `[-1, 1]`. -/
theorem IsCompact.exists_affineBasis_abs_coord_le_one {K : Set P} (hK : IsCompact K)
    (hspan : affineSpan ℝ K = ⊤) (hι : Fintype.card ι = finrank ℝ V + 1) :
    ∃ b : AffineBasis ι ℝ P, (∀ i, b i ∈ K) ∧ ∀ x ∈ K, ∀ i, |b.coord i x| ≤ 1 := by
  classical
  -- A reference affine basis with vertices in `K`.
  obtain ⟨s, hsK, b₀, hb₀⟩ := AffineBasis.exists_affine_subbasis hspan
  lift s to Finset P using b₀.setFinite
  let b₁ : AffineBasis ι ℝ P :=
    b₀.reindex (Fintype.equivOfCardEq (by rw [hι, ← b₀.card_eq_finrank_add_one]))
  have hb₁ : ∀ i, b₁ i ∈ K := fun i => by
    simp only [b₁, AffineBasis.reindex_apply, hb₀]
    exact hsK (Subtype.prop _)
  -- Choose vertices in `K` maximizing the volume `|det|` relative to `b₁`.
  let f : (ι → P) → ℝ := fun q => |(b₁.toMatrix q).det|
  -- Continuity goes through the linear part: Mathlib's `continuous_barycentric_coord` assumes
  -- `MetricSpace P`, which this pseudometric setting does not provide.
  have hcoord : ∀ j, Continuous (b₁.coord j) := fun j =>
    AffineMap.continuous_linear_iff.1 (b₁.coord j).linear.continuous_of_finiteDimensional
  have hf : Continuous f :=
    ((continuous_matrix fun i j => (hcoord j).comp (continuous_apply i)).matrix_det).abs
  obtain ⟨q, hqK, hq⟩ := (isCompact_univ_pi fun _ => hK).exists_isMaxOn
    ⟨b₁, fun i _ => hb₁ i⟩ hf.continuousOn
  have hfq : 0 < f q := by
    have hb₁K : (b₁ : ι → P) ∈ univ.pi fun _ => K := fun i _ => hb₁ i
    have := hq hb₁K
    simp only [mem_ofPred_eq, b₁.toMatrix_self, Matrix.det_one, abs_one, f] at this
    linarith
  -- A family of points of nonzero volume is an affine basis.
  obtain ⟨hind, htot⟩ := (b₁.isUnit_toMatrix_iff q).1 <|
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (abs_pos.1 hfq))
  let b : AffineBasis ι ℝ P := ⟨q, hind, htot⟩
  have hbq : (b : ι → P) = q := rfl
  have hbK : ∀ j, b j ∈ K := fun j => hbq ▸ hqK j (mem_univ j)
  refine ⟨b, hbK, fun x hx i => ?_⟩
  -- Replacing the vertex `b i` by `x` multiplies the volume by `|b.coord i x|`.
  have hle : f (Function.update b i x) ≤ f b := by
    rw [hbq]
    refine hq fun j _ => ?_
    rcases eq_or_ne j i with rfl | hj
    · simpa using hx
    · simpa [hj, hbq] using hbK j
  have hupdate : f (Function.update b i x) = f b * |b.coord i x| := by
    simp only [f, b₁.det_toMatrix_update b, abs_mul]
  rw [hupdate] at hle
  exact (mul_le_iff_le_one_right (hbq ▸ hfq)).1 hle

end Compact

/-! ### The homothetic image of a simplex -/

section Homothety

variable {ι k E : Type*} [Fintype ι] [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [Module k E] (b : AffineBasis ι k E)

/-- The image of the simplex spanned by an affine basis of an `n`-dimensional space under the
homothety of ratio `-n` about its centroid is the set of points whose barycentric coordinates are
all at most `1`. -/
theorem AffineBasis.mem_image_homothety_convexHull_iff {x : E} :
    x ∈ AffineMap.homothety (Finset.univ.centroid k b) (-(finrank k E : k)) ''
        convexHull k (range b) ↔ ∀ i, b.coord i x ≤ 1 := by
  have hn : (0 : k) ≤ finrank k E := Nat.cast_nonneg _
  have hn1 : (finrank k E : k) + 1 ≠ 0 := by positivity
  constructor
  · rintro ⟨z, hz, rfl⟩ i
    rw [b.convexHull_eq_nonneg_coord] at hz
    rw [b.coord_homothety_centroid, b.card_eq_finrank_add_one, Nat.cast_add_one,
      div_eq_one_iff_eq hn1 |>.2 (by ring)]
    nlinarith [hz i]
  · intro hx
    rcases hn.eq_or_lt with h0 | hpos
    · -- In dimension zero the homothety is constant and the space is a point.
      have : Subsingleton E := by
        have := b.finiteDimensional
        exact finrank_zero_iff.1 (by exact_mod_cast h0.symm)
      obtain ⟨i⟩ := b.nonempty
      exact ⟨b i, subset_convexHull k _ (mem_range_self i), Subsingleton.elim _ _⟩
    · refine ⟨AffineMap.homothety (Finset.univ.centroid k b) (-(finrank k E : k)⁻¹) x, ?_, ?_⟩
      · rw [b.convexHull_eq_nonneg_coord]
        intro i
        rw [b.coord_homothety_centroid, b.card_eq_finrank_add_one, Nat.cast_add_one]
        have := hx i
        field_simp
        nlinarith
      · rw [← AffineMap.homothety_mul_apply, neg_mul_neg, mul_inv_cancel₀ hpos.ne',
          AffineMap.homothety_one, AffineMap.id_apply]

end Homothety

section CompactHomothety

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Affine normalization of compact sets.** A compact set `K` whose affine span is the whole
`n`-dimensional real normed space contains the vertices of a simplex `Δ` and lies in the image of
`Δ` under the homothety of ratio `-n` about the centroid of `Δ`. When `K` is convex, it also
contains `Δ`, by `convexHull_min`. -/
theorem IsCompact.exists_affineBasis_subset_image_homothety_convexHull {K : Set E}
    (hK : IsCompact K) (hspan : affineSpan ℝ K = ⊤) (hι : Fintype.card ι = finrank ℝ E + 1) :
    ∃ b : AffineBasis ι ℝ E, (∀ i, b i ∈ K) ∧
      K ⊆ AffineMap.homothety (Finset.univ.centroid ℝ b) (-(finrank ℝ E : ℝ)) ''
        convexHull ℝ (range b) := by
  obtain ⟨b, hbK, hb⟩ := hK.exists_affineBasis_abs_coord_le_one hspan hι
  exact ⟨b, hbK, fun x hx => b.mem_image_homothety_convexHull_iff.2 fun i =>
    (le_abs_self _).trans (hb x hx i)⟩

end CompactHomothety

/-! ### Normalization by balls -/

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable (E) in
/-- **Normalization of convex bodies.** In a finite-dimensional real normed space `E` there is a
radius `r > 0`, depending only on `E`, such that every bounded convex set `s` with nonempty
interior is mapped by some affine equivalence `T` to a set between the balls of radii `r` and `1`
about `0`. -/
theorem exists_affineEquiv_ball_subset_image_subset_ball :
    ∃ r > 0, ∀ s : Set E, Convex ℝ s → Bornology.IsBounded s → (interior s).Nonempty →
      ∃ T : E ≃ᵃ[ℝ] E, ball 0 r ⊆ T '' s ∧ T '' s ⊆ ball 0 1 := by
  -- A reference simplex: its interior contains a ball about its centroid `c`, and the points with
  -- barycentric coordinates in `[-1, 1]` lie in the ball of radius `∑ i, ‖b₁ i‖` about `0`.
  let ι := Fin (finrank ℝ E + 1)
  have hι : Fintype.card ι = finrank ℝ E + 1 := Fintype.card_fin _
  obtain ⟨b₁⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional (k := ℝ) (P := E) hι
  set c := Finset.univ.centroid ℝ b₁
  have hc : c ∈ interior (convexHull ℝ (range b₁)) := b₁.centroid_mem_interior_convexHull
  rw [b₁.interior_convexHull] at hc
  have hopen : IsOpen {y | ∀ i, 0 < b₁.coord i y} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      (continuous_barycentric_coord b₁ i)
  obtain ⟨ρ, hρ, hball⟩ := isOpen_iff.1 hopen c hc
  have hbound : ∀ y, (∀ i, |b₁.coord i y| ≤ 1) → ‖y‖ ≤ ∑ i, ‖b₁ i‖ := fun y hy => by
    conv_lhs => rw [← b₁.linear_combination_coord_eq_self y]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hy i)
  set R := ∑ i, ‖b₁ i‖ + ‖c‖ + 1
  have hR : 0 < R := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => norm_nonneg (b₁ i)
    have := norm_nonneg c
    linarith
  refine ⟨ρ / R, div_pos hρ hR, fun s hs hsb hsi => ?_⟩
  -- An affine basis in the closure of `s` relative to which the barycentric coordinates of the
  -- points of the closure lie in `[-1, 1]`.
  have hspan : affineSpan ℝ (closure s) = ⊤ :=
    top_unique <| (isOpen_interior.affineSpan_eq_top hsi).symm.le.trans
      (affineSpan_mono ℝ (interior_subset.trans subset_closure))
  obtain ⟨b, hbs, hb⟩ := hsb.isCompact_closure.exists_affineBasis_abs_coord_le_one hspan hι
  -- Move it onto the reference simplex, then recentre at `0` and rescale by `R⁻¹`.
  obtain ⟨T₀, hT₀⟩ := b.exists_affineEquiv_apply_eq b₁
  have hcoord : ∀ x i, b₁.coord i (T₀ x) = b.coord i x := fun x i =>
    b.coord_apply_of_forall_apply_eq b₁ (f := T₀.toAffineMap) hT₀ i x
  let T : E ≃ᵃ[ℝ] E := (T₀.trans (AffineEquiv.constVAdd ℝ E (-c))).trans
    (AffineEquiv.homothetyUnitsMulHom (0 : E) (Units.mk0 R⁻¹ (inv_ne_zero hR.ne')))
  have hT : ∀ x, T x = R⁻¹ • (T₀ x - c) := fun x => by
    simp [T, AffineEquiv.coe_homothetyUnitsMulHom_apply, AffineMap.homothety_apply,
      neg_add_eq_sub]
  refine ⟨T, fun y hy => ?_, ?_⟩
  · -- The preimage of a small ball lies in the interior of the simplex of `b`, inside `s`.
    have hy' : T₀.symm (c + R • y) ∈ s := by
      have hpos : ∀ i, 0 < b.coord i (T₀.symm (c + R • y)) := fun i => by
        rw [← hcoord, AffineEquiv.apply_symm_apply]
        refine hball ?_ i
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hR.le]
        rw [mem_ball_zero_iff, lt_div_iff₀ hR] at hy
        linarith
      have hhull : convexHull ℝ (range b) ⊆ closure s :=
        convexHull_min (range_subset_iff.2 hbs) hs.closure
      have hmem : T₀.symm (c + R • y) ∈ interior (convexHull ℝ (range b)) := by
        rw [b.interior_convexHull]
        exact hpos
      exact interior_subset (hs.interior_closure_eq_interior_of_nonempty_interior hsi ▸
        interior_mono hhull hmem)
    refine ⟨_, hy', ?_⟩
    rw [hT, AffineEquiv.apply_symm_apply, add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ hR.ne', one_smul]
  · -- The image of `s` lies within distance `R - 1` of `c` before rescaling.
    rintro - ⟨x, hx, rfl⟩
    have hle := hbound (T₀ x) fun i => by
      rw [hcoord]
      exact hb x (subset_closure hx) i
    rw [mem_ball_zero_iff, hT, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le),
      inv_mul_lt_iff₀ hR, mul_one]
    linarith [norm_sub_le (T₀ x) c]

end TauCeti
