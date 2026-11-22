/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Complex conjugation: invariant discs, symmetric norms and unit-norm quotients

Complex conjugation is an isometry fixing the real axis (Mathlib's `Complex.dist_conj_conj`), so
it maps every open or closed disc centred on the real axis to itself. Such discs are the natural
domains for reflection across the real axis, for instance the even reflection
`TauCeti.evenReflection`. A disc centred in the closed upper half-plane is not invariant, but
its mirror image meets the closed upper half-plane inside the disc itself, since a point of the
closed upper half-plane is at least as close to such a centre as to its mirror image
(`TauCeti.dist_le_dist_conj_of_im_nonneg`, `TauCeti.mem_ball_of_conj_mem_ball_of_im_nonneg`).
Any set becomes invariant under conjugation once its mirror image is added
(`TauCeti.conj_mem_union_preimage_conj`).
Conjugation maps the real axis into itself
(`TauCeti.mapsTo_conj_setOf_im_eq_zero`), whereas the rotation `z ↦ I z` does not
(`TauCeti.not_mapsTo_I_mul_setOf_im_eq_zero`).

Conjugation also preserves norms (Mathlib's `Complex.norm_conj`), so the norm of
`1 - conj w * z` is symmetric in `z` and `w` (`Complex.norm_one_sub_conj_mul_comm`). This
expression is the denominator of the Möbius automorphisms of the unit disc and of the
pseudo-hyperbolic expression. For `w` on the unit circle it has the norm of `z - w`
(`Complex.norm_one_sub_conj_mul`), and for `z` in the closed unit disc it lies in the closed right
half-plane (`Complex.re_one_sub_conj_mul_nonneg`; strictly inside it for `z` in the open disc,
`Complex.re_one_sub_conj_mul_pos`), by the bound `re (conj u * e) ≤ ‖u‖ ‖e‖`
(`Complex.re_conj_mul_le`).

As a continuous real-linear equivalence, conjugation is its own inverse (`Complex.conjCLE_symm`,
the counterpart of Mathlib's `Complex.conjLIE_symm`).

Inversion preserves both the open and closed right half-planes: `z⁻¹` has positive
(respectively nonnegative) real part exactly when `z` does (`Complex.inv_re_pos`,
`Complex.inv_re_nonneg`). Under a reflection symmetry `f (a - z) = c * conj (f (conj z))`, a
one-sided upper bound `Re ρ ≤ B` on all zeros of `f` confines every zero to the bounded vertical
strip `|Re ρ| ≤ max B |Re a - B|` (`TauCeti.abs_re_le_max_of_re_le_of_sub_conj`).

The map `y ↦ r² / y` (inversion in the circle of radius `r` followed by conjugation) satisfies
`‖conj x - r² / y‖ ≤ 3 ‖x - y‖` for `‖x‖ ≤ r ≤ ‖y‖` (`Complex.norm_conj_sub_sq_div_le`).

The scalar Cayley expression `1 + (z - conj z) / (r - z)` has unit norm for real `r`.
When `z ≠ r`, it is the quotient `(r - conj z) / (r - z)` of a complex number's conjugate
by itself; at `z = r`, Lean's totalized inverse gives value one.

Two integers whose images in `ℂ` are at distance less than `1` are equal.

A shift `s + μ` stays off the real axis when `|Im μ| < |Im s|`
(`Complex.add_im_ne_zero_of_abs_im_lt`).

The canonical embedding of an `RCLike` field into `ℂ` is bundled as
`TauCeti.toComplexStarAlgHom`, so real star-algebra constructions can be transported to `ℂ`.

Dividing by a natural number does not increase the norm, so `‖(a z + b) / M‖ ≤ ‖a‖ C + ‖b‖`
whenever `‖z‖ ≤ C` (`Complex.norm_mul_add_div_natCast_le`).

The real coordinates `equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ` do not increase distances, so they map the
disc of radius `r` about `equivRealProdCLM.symm z₀` into the square `B_r(z₀)` of `ℝ × ℝ`
(`Complex.dist_equivRealProdCLM_le`).

On the closed right half-plane `0 ≤ z.re`, `1 + z` has real part and norm at least `1`
(`Complex.one_le_re_one_add`, `Complex.one_le_norm_one_add`).

Any point `w` on the boundary of the square `[-ε, ε] × [-ε, ε]` satisfies `ε ≤ ‖w‖ ≤ 2 * ε`
(`Complex.norm_bounds_of_abs_re_le_of_abs_im_le`).
-/

public section

open scoped ComplexConjugate

/-- A complex number and its inverse lie in the open right half-plane together. -/
theorem Complex.inv_re_pos {z : ℂ} : 0 < z⁻¹.re ↔ 0 < z.re := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [inv_re, div_pos_iff_of_pos_right (normSq_pos.mpr hz)]

/-- A complex number and its inverse lie in the closed right half-plane together. -/
theorem Complex.inv_re_nonneg {z : ℂ} : 0 ≤ z⁻¹.re ↔ 0 ≤ z.re := by
  have hzero : z⁻¹.re = 0 ↔ z.re = 0 := by
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    · simp [inv_re, hz]
  simpa only [le_iff_eq_or_lt, eq_comm (a := (0 : ℝ))] using or_congr hzero Complex.inv_re_pos

/-- The scalar Cayley expression has unit norm at real `r`, including when `z = r`
under the totalized inverse convention. -/
theorem Complex.norm_one_add_sub_conj_mul_inv_ofReal_sub (z : ℂ) (r : ℝ) :
    ‖1 + (z - conj z) * ((r : ℂ) - z)⁻¹‖ = 1 := by
  by_cases hne : (r : ℂ) - z = 0
  · simp [hne]
  have heq : 1 + (z - conj z) * ((r : ℂ) - z)⁻¹ =
      ((r : ℂ) - conj z) / ((r : ℂ) - z) := by
    field_simp
    ring
  have hnorm : ‖(r : ℂ) - conj z‖ = ‖(r : ℂ) - z‖ := by
    simpa using Complex.norm_conj ((r : ℂ) - z)
  rw [heq, norm_div, hnorm, div_self (norm_ne_zero_iff.mpr hne)]

namespace TauCeti

/-- The canonical real star-algebra embedding of an `RCLike` field into `ℂ`. -/
noncomputable def toComplexStarAlgHom (𝕜 : Type*) [RCLike 𝕜] : 𝕜 →⋆ₐ[ℝ] ℂ where
  toFun x := (RCLike.re x : ℂ) + (RCLike.im x : ℂ) * Complex.I
  map_zero' := by simp
  map_one' := by simp
  map_add' := by intros; simp only [map_add, Complex.ofReal_add]; ring
  map_mul' := by
    intro x y
    simp only [RCLike.mul_re, RCLike.mul_im, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_add]
    ring_nf
    rw [Complex.I_sq]
    ring
  commutes' := by intro r; simp
  map_star' := by intro x; simp [RCLike.star_def, mul_comm]

/-- The canonical complex embedding sends a scalar to its real and imaginary components. -/
@[simp]
theorem toComplexStarAlgHom_apply {𝕜 : Type*} [RCLike 𝕜] (x : 𝕜) :
    toComplexStarAlgHom 𝕜 x = (RCLike.re x : ℂ) + (RCLike.im x : ℂ) * Complex.I :=
  (rfl)

/-- The canonical complex embedding is the identity on `ℂ`. -/
@[simp]
theorem toComplexStarAlgHom_complex : toComplexStarAlgHom ℂ = .id ℝ ℂ := by
  ext z
  simp

/-- The canonical complex embedding of `ℝ` is the real scalar inclusion. -/
@[simp]
theorem toComplexStarAlgHom_real : toComplexStarAlgHom ℝ = RCLike.ofRealStarAlgHom ℂ := by
  ext r
  simp

/-- The canonical complex embedding preserves the real scalar inclusion. -/
@[simp]
theorem toComplexStarAlgHom_comp_ofRealStarAlgHom (𝕜 : Type*) [RCLike 𝕜] :
    (toComplexStarAlgHom 𝕜).comp (RCLike.ofRealStarAlgHom 𝕜) =
      RCLike.ofRealStarAlgHom ℂ := by
  ext r
  simp

/-- The canonical complex embedding has the same underlying function as `RCLike.map`. -/
theorem coe_toComplexStarAlgHom_eq_map (𝕜 : Type*) [RCLike 𝕜] :
    (toComplexStarAlgHom 𝕜 : 𝕜 → ℂ) = RCLike.map 𝕜 ℂ :=
  (rfl)

/-- The canonical complex embedding preserves distances. -/
theorem isometry_toComplexStarAlgHom (𝕜 : Type*) [RCLike 𝕜] :
    Isometry (toComplexStarAlgHom 𝕜) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, ← map_sub, toComplexStarAlgHom_apply, RCLike.norm_to_complex,
    dist_eq_norm]

/-- The canonical complex embedding is continuous. -/
@[continuity, fun_prop]
theorem continuous_toComplexStarAlgHom (𝕜 : Type*) [RCLike 𝕜] :
    Continuous (toComplexStarAlgHom 𝕜) :=
  (isometry_toComplexStarAlgHom 𝕜).continuous

open ComplexConjugate Metric

variable {x₀ z : ℂ} {r : ℝ}

/-- Conjugation maps an open disc centred on the real axis to itself. -/
theorem conj_mem_ball_of_im_eq_zero (hx₀ : x₀.im = 0) (hz : z ∈ ball x₀ r) :
    conj z ∈ ball x₀ r := by
  rwa [mem_ball, ← Complex.conj_eq_iff_im.2 hx₀, Complex.dist_conj_conj]

/-- Conjugation maps a closed disc centred on the real axis to itself. -/
theorem conj_mem_closedBall_of_im_eq_zero (hx₀ : x₀.im = 0) (hz : z ∈ closedBall x₀ r) :
    conj z ∈ closedBall x₀ r := by
  rwa [mem_closedBall, ← Complex.conj_eq_iff_im.2 hx₀, Complex.dist_conj_conj]

/-- A point `w` of the closed upper half-plane is at least as close to a point `z` of the closed
upper half-plane as to its mirror image `conj z`. -/
theorem dist_le_dist_conj_of_im_nonneg {w : ℂ} (hw : 0 ≤ w.im) (hz : 0 ≤ z.im) :
    dist w z ≤ dist w (conj z) := by
  rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im]
  refine Real.sqrt_le_sqrt ?_
  simp only [Complex.conj_re, Complex.conj_im]
  nlinarith [mul_nonneg hw hz]

/-- If the mirror image of a point `z` of the closed upper half-plane lies in an open disc centred
in the closed upper half-plane, then so does `z`. -/
theorem mem_ball_of_conj_mem_ball_of_im_nonneg (hx₀ : 0 ≤ x₀.im) (hz : 0 ≤ z.im)
    (h : conj z ∈ ball x₀ r) : z ∈ ball x₀ r :=
  (dist_le_dist_conj_of_im_nonneg hz hx₀).trans_lt (by rwa [← Complex.dist_conj_comm])

/-- If the mirror image of a point `z` of the closed upper half-plane lies in a closed disc centred
in the closed upper half-plane, then so does `z`. -/
theorem mem_closedBall_of_conj_mem_closedBall_of_im_nonneg (hx₀ : 0 ≤ x₀.im) (hz : 0 ≤ z.im)
    (h : conj z ∈ closedBall x₀ r) : z ∈ closedBall x₀ r :=
  (dist_le_dist_conj_of_im_nonneg hz hx₀).trans (by rwa [← Complex.dist_conj_comm])

/-- The union of a set `s` with its preimage under conjugation is invariant under conjugation. -/
theorem conj_mem_union_preimage_conj {s : Set ℂ} (hz : z ∈ s ∪ conj ⁻¹' s) :
    conj z ∈ s ∪ conj ⁻¹' s := by
  simp only [Set.mem_union, Set.mem_preimage, Complex.conj_conj] at hz ⊢
  exact hz.symm

/-- A set `s` and its preimage under conjugation meet the closed upper half-plane in the same set,
provided every point of the closed upper half-plane whose mirror image lies in `s` lies in `s`,
as for discs centred in the closed upper half-plane
(`TauCeti.mem_ball_of_conj_mem_ball_of_im_nonneg`). -/
theorem setOfPred_le_im_inter_union_preimage_conj {s : Set ℂ}
    (hs : ∀ z, 0 ≤ z.im → conj z ∈ s → z ∈ s) :
    {z : ℂ | 0 ≤ z.im} ∩ (s ∪ conj ⁻¹' s) = {z : ℂ | 0 ≤ z.im} ∩ s :=
  subset_antisymm (fun z ⟨hz, hzs⟩ ↦ ⟨hz, hzs.elim id (hs z hz)⟩)
    (Set.inter_subset_inter_right _ Set.subset_union_left)

/-- Complex conjugation maps the real axis into itself. -/
theorem mapsTo_conj_setOf_im_eq_zero :
    Set.MapsTo (conj ·) {z : ℂ | z.im = 0} {z : ℂ | z.im = 0} := fun z hz => by
  simpa using hz

/-- The rotation `z ↦ I z` does not preserve the real axis, so it is not admissible on
half-discs. -/
theorem not_mapsTo_I_mul_setOf_im_eq_zero :
    ¬ Set.MapsTo (fun z : ℂ => Complex.I * z) {z | z.im = 0} {z | z.im = 0} := fun h => by
  simpa using h (show (1 : ℂ) ∈ {z : ℂ | z.im = 0} by simp)

/-- Under a reflection symmetry `f (a - z) = c * conj (f (conj z))`, a one-sided upper bound
`ρ.re ≤ B` on all zeros of `f` also gives `a.re - ρ.re ≤ B`, hence confines every zero to the
bounded vertical strip `|ρ.re| ≤ max B |a.re - B|`. -/
theorem abs_re_le_max_of_re_le_of_sub_conj {f : ℂ → ℂ} {B : ℝ}
    (hre : ∀ ρ : ℂ, f ρ = 0 → ρ.re ≤ B)
    {a c : ℂ} (hfe : ∀ z : ℂ, f (a - z) = c * conj (f (conj z)))
    {ρ : ℂ} (hρ : f ρ = 0) : |ρ.re| ≤ max B |a.re - B| := by
  have hsym : f (a - conj ρ) = 0 := by
    have := hfe (conj ρ)
    simpa [hρ] using this
  have h1 := hre (a - conj ρ) hsym
  simp only [Complex.sub_re, Complex.conj_re] at h1
  have hlow : -max B |a.re - B| ≤ a.re - B := by
    have := neg_abs_le (a.re - B)
    linarith [le_max_right B |a.re - B|]
  exact abs_le.mpr ⟨by linarith, (hre ρ hρ).trans (le_max_left _ _)⟩

variable {E : Type*} [TopologicalSpace E] {τ : E → E} {U : Set E} {ρ : ℝ}

/-- The parameter map `τ` composed with conjugation of the disc coordinate is continuous on the
product of `U` with a disc centred at zero, and maps this product and its punctured version to
themselves. -/
theorem continuousOn_mapsTo_prodMap_conj (hτ : ContinuousOn τ U) (hτU : Set.MapsTo τ U U) :
    ContinuousOn (fun b : E × ℂ ↦ (τ b.1, conj b.2)) (U ×ˢ ball 0 ρ) ∧
      Set.MapsTo (fun b : E × ℂ ↦ (τ b.1, conj b.2)) (U ×ˢ ball 0 ρ) (U ×ˢ ball 0 ρ) ∧
      Set.MapsTo (fun b : E × ℂ ↦ (τ b.1, conj b.2)) (U ×ˢ (ball 0 ρ \ {0}))
        (U ×ˢ (ball 0 ρ \ {0})) := by
  have hconjBall : Set.MapsTo conj (ball (0 : ℂ) ρ) (ball 0 ρ) := fun _ hz ↦
    conj_mem_ball_of_im_eq_zero (by simp) hz
  exact ⟨hτ.prodMap Complex.continuous_conj.continuousOn, hτU.prodMap hconjBall,
    hτU.prodMap fun z hz ↦ ⟨hconjBall hz.1, by simpa using hz.2⟩⟩

/-- **Two integers whose complex images are closer than `1` are equal.** -/
theorem eq_of_dist_intCast_lt_one {m n : ℤ} (h : dist (m : ℂ) (n : ℂ) < 1) : m = n := by
  by_contra hne
  have : (1 : ℝ) ≤ dist (m : ℂ) (n : ℂ) := by
    rw [Complex.isometry_intCast.dist_eq]; exact Int.pairwise_one_le_dist hne
  linarith

end TauCeti

namespace Complex

open ComplexConjugate

/-- Complex conjugation, as a continuous real-linear equivalence, is its own inverse. -/
@[simp]
theorem conjCLE_symm : conjCLE.symm = conjCLE := by
  rw [← conjLIE_toCLE, ← LinearIsometryEquiv.toContinuousLinearEquiv_symm, conjLIE_symm]

/-- The imaginary part of a conjugate product is bounded by the product of the norms. -/
theorem abs_im_conj_mul_le (u e : ℂ) : |(conj u * e).im| ≤ ‖u‖ * ‖e‖ := by
  simpa [norm_mul] using abs_im_le_norm (conj u * e)

/-- The real part of a conjugate product is bounded by the product of the norms. -/
theorem re_conj_mul_le (u e : ℂ) : (conj u * e).re ≤ ‖u‖ * ‖e‖ := by
  simpa [norm_mul] using re_le_norm (conj u * e)

/-- The norm of `1 - conj w * z` is symmetric in `z` and `w`: conjugation swaps the two
expressions and preserves norms. -/
theorem norm_one_sub_conj_mul_comm (z w : ℂ) : ‖1 - conj w * z‖ = ‖1 - conj z * w‖ := by
  rw [← norm_conj]
  simp [mul_comm]

/-- For `‖w‖ = 1`, `1 - conj w * z` has the norm of `z - w`. -/
theorem norm_one_sub_conj_mul {w z : ℂ} (hw : ‖w‖ = 1) : ‖1 - conj w * z‖ = ‖z - w‖ := by
  have h : w * (1 - conj w * z) = w - z := by
    rw [mul_sub, mul_one, ← mul_assoc, mul_conj, normSq_eq_norm_sq, hw]
    simp
  rw [norm_sub_rev z w, ← h, norm_mul, hw, one_mul]

/-- For `‖w‖ = 1` and `‖z‖ ≤ 1`, `1 - conj w * z` has nonnegative real part. -/
theorem re_one_sub_conj_mul_nonneg {w z : ℂ} (hw : ‖w‖ = 1) (hz : ‖z‖ ≤ 1) :
    0 ≤ (1 - conj w * z).re := by
  simpa [hw] using (re_conj_mul_le w z).trans (by simpa [hw] using hz)

/-- For `‖w‖ = 1` and `‖z‖ < 1`, `1 - conj w * z` has positive real part. -/
theorem re_one_sub_conj_mul_pos {w z : ℂ} (hw : ‖w‖ = 1) (hz : ‖z‖ < 1) :
    0 < (1 - conj w * z).re := by
  simpa [hw] using (re_conj_mul_le w z).trans_lt (by simpa [hw] using hz)

/-- For a point `x` of the closed disc of radius `r` and a point `y` outside the open disc, the
conjugate `conj x` is within `3 ‖x - y‖` of the point `r² / y`, the inversion of `y` in the circle
of radius `r` followed by conjugation. -/
theorem norm_conj_sub_sq_div_le {r : ℝ} (x y : ℂ)
    (hx : ‖x‖ ≤ r) (hy : r ≤ ‖y‖) :
    ‖conj x - (r : ℂ)^2/y‖ ≤ 3*‖x - y‖ := by
  have hr : 0 ≤ r := (norm_nonneg x).trans hx
  rcases eq_or_ne y 0 with rfl | hyne
  · have hr0 : r = 0 := le_antisymm (by simpa using hy) hr
    have hx0 : x = 0 := norm_le_zero_iff.mp (hr0 ▸ hx)
    simp [hr0, hx0]
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hyne
  have heq : conj y - (r : ℂ)^2/y = (((‖y‖^2 - r^2 : ℝ) : ℂ))/y := by
    apply (eq_div_iff hyne).mpr
    rw [sub_mul, div_mul_cancel₀ _ hyne, conj_mul', ofReal_sub, ofReal_pow, ofReal_pow]
  have hgap : ‖y‖-r ≤ ‖x - y‖ := by
    have h := norm_le_norm_add_norm_sub x y
    linarith
  have htail : ‖conj y - (r : ℂ)^2/y‖ ≤ 2 * (‖y‖-r) := by
    rw [heq, norm_div, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith : 0 ≤ ‖y‖^2 - r^2)]
    apply (div_le_iff₀ hy0).mpr
    nlinarith
  calc
    _ ≤ ‖conj x - conj y‖ + ‖conj y - (r : ℂ)^2/y‖ := by
      simpa only [dist_eq_norm] using dist_triangle (conj x) (conj y) ((r : ℂ)^2/y)
    _ ≤ ‖x - y‖ + 2 * (‖y‖-r) := by
      rw [← map_sub, norm_conj]
      exact add_le_add le_rfl htail
    _ ≤ _ := by linarith

/-- Dividing by a natural number does not increase the norm, so the point `(a z + b) / M` has
norm at most `‖a‖ C + ‖b‖` when `‖z‖ ≤ C`. For `M = 0` the quotient is `0` by Lean's convention
`x / 0 = 0`. -/
theorem norm_mul_add_div_natCast_le (M : ℕ) (a b : ℂ) {z : ℂ} {C : ℝ} (hz : ‖z‖ ≤ C) :
    ‖(a * z + b) / M‖ ≤ ‖a‖ * C + ‖b‖ := by
  rw [norm_div, Complex.norm_natCast]
  exact (div_nat_le_self_of_nonneg (norm_nonneg _) M).trans
    (norm_add_le_of_le (norm_mul_le_of_le le_rfl hz) le_rfl)

/-- The real coordinates `equivRealProdCLM` do not increase distances, so they map the disc of
radius `r` about `equivRealProdCLM.symm z₀` into the square `B_r(z₀)` of `ℝ × ℝ`. -/
theorem dist_equivRealProdCLM_le (y : ℂ) (z₀ : ℝ × ℝ) :
    dist (equivRealProdCLM y) z₀ ≤ dist y (equivRealProdCLM.symm z₀) := by
  conv_lhs => rw [← equivRealProdCLM.apply_symm_apply z₀]
  exact (lipschitz_equivRealProd.dist_le_mul y _).trans (by simp)

/-- For `z` in the closed right half-plane (`0 ≤ z.re`), `1 + z` has real part at least `1`. -/
theorem one_le_re_one_add {z : ℂ} (hz : 0 ≤ z.re) : 1 ≤ (1 + z).re := by
  simp [hz]

/-- For `z` in the closed right half-plane (`0 ≤ z.re`), `1 + z` has norm at least `1`. -/
theorem one_le_norm_one_add {z : ℂ} (hz : 0 ≤ z.re) : 1 ≤ ‖1 + z‖ :=
  (one_le_re_one_add hz).trans (re_le_norm _)

/-- A shift `s + μ` stays off the real axis when `|Im μ| < |Im s|`. -/
theorem add_im_ne_zero_of_abs_im_lt {s μ : ℂ} (h : |μ.im| < |s.im|) : (s + μ).im ≠ 0 :=
  fun h0 ↦ by
    rw [add_im, ← eq_neg_iff_add_eq_zero] at h0
    rw [h0, abs_neg] at h
    exact h.false

/-- Any point `w` on the boundary of the square `[-ε, ε] × [-ε, ε]` satisfies
`ε ≤ ‖w‖ ≤ 2 * ε`. -/
theorem norm_bounds_of_abs_re_le_of_abs_im_le (w : ℂ) (ε : ℝ) (hre : |w.re| ≤ ε)
    (him : |w.im| ≤ ε) (hside : |w.re| = ε ∨ |w.im| = ε) :
    ε ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * ε := by
  refine ⟨?_, (norm_le_abs_re_add_abs_im w).trans (by linarith)⟩
  rcases hside with h | h
  · exact h ▸ abs_re_le_norm w
  · exact h ▸ abs_im_le_norm w

end Complex
