/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import TauCeti.Analysis.CStarAlgebra.MatrixUnits.Conjugacy
public import TauCeti.Analysis.CStarAlgebra.Projection.Stability
import TauCeti.Topology.Algebra.Indicator

/-!
# Norm Stability of Matrix Units in C⋆-Algebras

Finite multi-block systems of matrix units are **norm-stable** across all C⋆-algebras (Blackadar,
*Operator Algebras*, Proposition II.8.3.23), preserving closed `ℂ`-⋆-subalgebras: diagonal entries
are perturbed jointly via `TauCeti.exists_delta_ortho_isStarProjection_mem`, column entries are
compressed and polar-perturbed via `TauCeti.exists_isPartialIsometry_mem_of_approx`, and
`TauCeti.IsMatrixUnitSystem.of_partialIsometry` reconstructs the full system.

## Main definitions

* `TauCeti.IsApproxMatrixUnitSystem`: matrix-unit relations holding up to norm `< δ`.

## Main results

* `TauCeti.exists_isPartialIsometry_mem_of_approx`.
* `TauCeti.exists_delta_isMatrixUnitSystem_mem`, `TauCeti.exists_delta_isMatrixUnitSystem`,
  `TauCeti.exists_delta_isUnitalMatrixUnitSystem_mem`,
  `TauCeti.exists_delta_isUnitalMatrixUnitSystem`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.8.3.23.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge Univ. Press (1998), 4.6.6.
-/

public section

open Function
open scoped NonUnitalContinuousFunctionalCalculus

namespace TauCeti

private def projCornerSubalgebra {A : Type*} [NonUnitalCStarAlgebra A]
    (s : NonUnitalStarSubalgebra ℂ A) (p : A) (hp : IsStarProjection p) :
    NonUnitalStarSubalgebra ℂ A where
  carrier := {a : A | a ∈ s ∧ p * a = a ∧ a * p = a}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, by rw [mul_add, ha.2.1, hb.2.1],
    by rw [add_mul, ha.2.2, hb.2.2]⟩
  zero_mem' := ⟨zero_mem s, mul_zero p, zero_mul p⟩
  mul_mem' ha hb := ⟨mul_mem ha.1 hb.1, by rw [← mul_assoc, ha.2.1], by rw [mul_assoc, hb.2.2]⟩
  smul_mem' c _ ha := ⟨SMulMemClass.smul_mem c ha.1, by rw [mul_smul_comm, ha.2.1],
    by rw [smul_mul_assoc, ha.2.2]⟩
  star_mem' ha := ⟨star_mem ha.1, by rw [← hp.isSelfAdjoint.star_eq, ← star_mul, ha.2.2],
    by rw [← hp.isSelfAdjoint.star_eq, ← star_mul, ha.2.1]⟩

private lemma isClosed_projCornerSubalgebra {A : Type*} [NonUnitalCStarAlgebra A]
    {s : NonUnitalStarSubalgebra ℂ A} (hs : IsClosed (s : Set A)) (p : A)
    (hp : IsStarProjection p) : IsClosed (projCornerSubalgebra s p hp : Set A) := by
  change IsClosed ({a : A | a ∈ s} ∩ ({a : A | p * a = a} ∩ {a : A | a * p = a}))
  exact hs.inter ((isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id))

/-- **Quantitative polar perturbation of an approximate partial isometry** between star projections
`p` and `q` when `η ≤ 1 / 32`. -/
theorem exists_isPartialIsometry_mem_of_approx {A S : Type*} [NonUnitalCStarAlgebra A]
    [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A] {s : S}
    [hs : IsClosed (s : Set A)] {η : ℝ} (hη : η ≤ 1 / 32) {p q z : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hzs : z ∈ s)
    (hqz : q * z = z) (hzp : z * p = z)
    (hinit : ‖star z * z - p‖ < η) (hfin : ‖z * star z - q‖ < η) :
    ∃ v ∈ s, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q ∧ ‖v - z‖ < 10 * η := by
  let corner := projCornerSubalgebra (NonUnitalStarSubalgebra.ofClass s) p hp
  have : IsClosed (corner : Set A) := isClosed_projCornerSubalgebra hs p hp
  set h : A := star z * z
  have hh_sa : IsSelfAdjoint h := IsSelfAdjoint.star_mul_self z
  have hph : p * h = h := by rw [← hp.isSelfAdjoint.star_eq, ← mul_assoc, ← star_mul, hzp]
  have hhp : h * p = h := by rw [mul_assoc, hzp]
  have hh_corner : h ∈ corner := ⟨mul_mem (star_mem hzs) hzs, hph, hhp⟩
  have hh_defect : ‖h * h - h‖ ≤ ‖h - p‖ ^ 2 + ‖h - p‖ := by
    rw [show h * h - h = (h - p) * (h - p) + (h - p) by
      simp only [sub_mul, mul_sub, hph, hhp, hp.isIdempotentElem.eq]; abel, sq]
    linarith [norm_mul_le (h - p) (h - p), norm_add_le ((h - p) * (h - p)) (h - p)]
  have hsq_lt : ‖h - p‖ ^ 2 ≤ (1 / 32) * ‖h - p‖ := by nlinarith [norm_nonneg (h - p)]
  have hh_lt_quarter : ‖h * h - h‖ < 1 / 4 := by linarith [norm_nonneg (h - p)]
  have hsp_corner : spectralProjection h ∈ corner := spectralProjection_mem hh_corner
  have hsp_dist_p : ‖spectralProjection h - p‖ < 1 := by
    have hsp_h := hh_sa.norm_spectralProjection_sub_le hh_lt_quarter
    linarith [show ‖spectralProjection h - p‖ ≤ ‖spectralProjection h - h‖ + ‖h - p‖ by
      simpa using norm_add_le (spectralProjection h - h) (h - p)]
  have hsp_eq_p : spectralProjection h = p :=
    (hh_sa.isStarProjection_spectralProjection hh_lt_quarter).eq_of_mul_eq_left_of_norm_sub_lt_one
      hp hsp_corner.2.2 hsp_dist_p
  set g : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator (fun t ↦ (√t)⁻¹)
  have hg_cont : ContinuousOn g (quasispectrum ℝ h) := by
    refine (Real.continuous_sqrt.continuousOn.inv₀ fun t ht ↦ ?_)
      |>.continuousOn_indicator_of_disjoint_frontier ?_
    · have ht_gt : (1 / 2 : ℝ) < t := interior_subset ht
      exact (Real.sqrt_pos.mpr (by linarith)).ne'
    · rw [frontier_Ioi, Set.disjoint_singleton_left]
      exact hh_sa.notMem_quasispectrum_half_of_norm_mul_self_sub_lt hh_lt_quarter
  have hg0 : g 0 = 0 := by simp [g]
  set w : A := cfcₙ g h
  have hw_corner : w ∈ corner := cfcₙ_mem (𝕜' := ℂ) g hh_corner
  have hw_sa : IsSelfAdjoint w := IsSelfAdjoint.cfcₙ
  set ind : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)
  have hwhw : w * h * w = p := by
    have hcfc_eq : w * h * w = cfcₙ ind h := by
      conv_lhs => lhs; rhs; rw [← cfcₙ_id' ℝ h]
      rw [← cfcₙ_mul g (fun t : ℝ ↦ t) h hg_cont hg0 continuousOn_id rfl,
        ← cfcₙ_mul (fun t : ℝ ↦ g t * t) g h (hg_cont.mul continuousOn_id) (by simp [hg0])
          hg_cont hg0]
      refine cfcₙ_congr fun t _ ↦ ?_
      by_cases ht : t ∈ Set.Ioi (1 / 2 : ℝ)
      · have ht_pos : 0 < t := by linarith [Set.mem_Ioi.mp ht]
        have hne : √t ≠ 0 := (Real.sqrt_pos.mpr ht_pos).ne'
        simp only [g, ind, Set.indicator_of_mem ht, Pi.one_apply]
        conv_lhs => lhs; rhs; rw [← Real.mul_self_sqrt ht_pos.le]
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul, mul_inv_cancel₀ hne]
      · simp only [g, ind, Set.indicator_of_notMem ht, zero_mul]
    rw [hcfc_eq, ← spectralProjection_def, hsp_eq_p]
  set v : A := z * w
  have hv_mem : v ∈ s := mul_mem hzs hw_corner.1
  have hv_init : star v * v = p := by
    dsimp [v]; rw [star_mul, hw_sa.star_eq, mul_assoc w, ← mul_assoc (star z), ← hwhw]
    simp [h, mul_assoc]
  have hv_pi : IsPartialIsometry v := by
    rw [isPartialIsometry_iff, mul_assoc, hv_init]; dsimp [v]; rw [mul_assoc, hw_corner.2.2]
  have hz_norm : ‖z‖ ≤ 2 := by
    have hnorm_h : ‖h‖ ≤ 2 := by
      linarith [hp.norm_le p, show ‖h‖ ≤ ‖p‖ + ‖h - p‖ by simpa using norm_add_le p (h - p)]
    rw [CStarRing.norm_star_mul_self] at hnorm_h; nlinarith [norm_nonneg z]
  have hw_sub_p : ‖w - p‖ ≤ 4 * ‖h * h - h‖ := by
    rw [← hsp_eq_p, spectralProjection_def, ← cfcₙ_sub g ind h hg_cont hg0
      (hh_sa.continuousOn_indicator_Ioi_half hh_lt_quarter) (by simp [ind])]
    refine norm_cfcₙ_le fun t ht ↦ ?_
    rw [Real.norm_eq_abs]
    have hqt := hh_sa.abs_mul_self_sub_le_norm ht
    by_cases hgt : t ∈ Set.Ioi (1 / 2 : ℝ)
    · simp only [g, ind, Set.indicator_of_mem hgt, Pi.one_apply]
      have ht_pos : 0 < t := by linarith [Set.mem_Ioi.mp hgt]
      have hsqrt_half : (1 / 2 : ℝ) < √t := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact Real.sqrt_lt_sqrt (by norm_num) (by linarith [Set.mem_Ioi.mp hgt])
      have hne : √t ≠ 0 := (Real.sqrt_pos.mpr ht_pos).ne'
      have h1t : 1 - t = ((√t)⁻¹ - 1) * (√t * (1 + √t)) := by
        calc 1 - t = 1 - √t * √t := by rw [Real.mul_self_sqrt ht_pos.le]
          _ = ((√t)⁻¹ * √t - √t) * (1 + √t) := by rw [inv_mul_cancel₀ hne]; ring
          _ = ((√t)⁻¹ - 1) * (√t * (1 + √t)) := by ring
      have hprod_sqrt : |1 - t| = |(√t)⁻¹ - 1| * (√t * (1 + √t)) := by
        rw [h1t, abs_mul, abs_of_pos (a := √t * (1 + √t)) (by positivity)]
      have hprod_t : |t * t - t| = t * |1 - t| := by
        rw [show t * t - t = t * (t - 1) by ring, abs_mul, abs_of_pos ht_pos, abs_sub_comm]
      have hD : 3 / 4 ≤ √t * (1 + √t) := by nlinarith
      have h1 : (3 / 4) * |(√t)⁻¹ - 1| ≤ |1 - t| := by nlinarith [abs_nonneg ((√t)⁻¹ - 1)]
      nlinarith [abs_nonneg (1 - t), Set.mem_Ioi.mp hgt]
    · simp only [g, ind, Set.indicator_of_notMem hgt, sub_zero, abs_zero]; positivity
  have hv_sub_z : ‖v - z‖ < 10 * η := by
    rw [show v - z = z * (w - p) by dsimp [v]; rw [mul_sub, hzp]]
    have hwp : ‖w - p‖ < 5 * η := by linarith [norm_nonneg (h - p)]
    exact (norm_mul_le z (w - p)).trans_lt
      (by linarith [mul_le_mul_of_nonneg_right hz_norm (norm_nonneg (w - p)), norm_nonneg (h - p)])
  have hv_fin_q : (v * star v) * q = v * star v := by
    have hqv : q * v = v := by dsimp [v]; rw [← mul_assoc, hqz]
    rw [← hq.isSelfAdjoint.star_eq, mul_assoc, ← star_mul, hqv]
  have hv_fin_dist : ‖v * star v - q‖ < 1 := by
    rw [show v * star v - q = (v - z) * star v + z * star (v - z) + (z * star z - q) by
      simp only [sub_mul, mul_sub, star_sub]; abel]
    have h1 : ‖(v - z) * star v‖ ≤ ‖v - z‖ := (norm_mul_le _ _).trans <| by
      rw [norm_star]; exact mul_le_of_le_one_right (norm_nonneg _) hv_pi.norm_le_one
    have h2 : ‖z * star (v - z)‖ ≤ 2 * ‖v - z‖ := (norm_mul_le _ _).trans <| by
      rw [norm_star]; exact mul_le_mul_of_nonneg_right hz_norm (norm_nonneg _)
    linarith [norm_add_le ((v - z) * star v + z * star (v - z)) (z * star z - q),
      norm_add_le ((v - z) * star v) (z * star (v - z))]
  exact ⟨v, hv_mem, hv_pi, hv_init,
    hv_pi.isStarProjection_mul_star_self.eq_of_mul_eq_left_of_norm_sub_lt_one hq hv_fin_q
      hv_fin_dist,
    hv_sub_z⟩

/-- A multi-block family `x` is a **`δ`-approximate system of matrix units** if the adjoint and
multiplication relations of `IsMatrixUnitSystem` hold up to norm `< δ`. -/
structure IsApproxMatrixUnitSystem {κ A : Type*} {n : κ → Type*} [SeminormedAddCommGroup A] [Mul A]
    [Star A] (δ : ℝ) (x : ∀ r : κ, n r → n r → A) : Prop where
  /-- Taking the star approximately transposes indices within each block. -/
  norm_star_sub_lt (r : κ) (i j : n r) : ‖star (x r i j) - x r j i‖ < δ
  /-- Composable entries within a block approximately contract the middle index. -/
  norm_mul_same_sub_lt (r : κ) (i j l : n r) : ‖x r i j * x r j l - x r i l‖ < δ
  /-- Non-composable entries within a block have product of norm `< δ`. -/
  norm_mul_ne_lt (r : κ) (i : n r) {j k : n r} (l : n r) : j ≠ k → ‖x r i j * x r k l‖ < δ
  /-- Entries from distinct blocks have product of norm `< δ`. -/
  norm_mul_block_ne_lt {r t : κ} : r ≠ t → ∀ (i j : n r) (k l : n t), ‖x r i j * x t k l‖ < δ

namespace IsMatrixUnitSystem

/-- Every exact system of matrix units is a `δ`-approximate system for every `δ > 0`. -/
theorem isApproxMatrixUnitSystem {κ A : Type*} {n : κ → Type*} [NonUnitalSeminormedRing A]
    [Star A] {e : ∀ r : κ, n r → n r → A} (he : IsMatrixUnitSystem e) {δ : ℝ} (hδ : 0 < δ) :
    IsApproxMatrixUnitSystem δ e where
  norm_star_sub_lt r i j := by simp [he.star_eq, hδ]
  norm_mul_same_sub_lt r i j l := by simp [he.mul_same, hδ]
  norm_mul_ne_lt r i {_ _} l hjk := by simp [he.mul_ne r i l hjk, hδ]
  norm_mul_block_ne_lt hrs i j k l := by simp [he.mul_block_ne hrs i j k l, hδ]

end IsMatrixUnitSystem

namespace IsApproxMatrixUnitSystem

/-- Monotonicity of `IsApproxMatrixUnitSystem` in the tolerance `δ`. -/
theorem mono {κ A : Type*} {n : κ → Type*} [SeminormedAddCommGroup A] [Mul A] [Star A] {δ₁ δ₂ : ℝ}
    {x : ∀ r : κ, n r → n r → A} (hx : IsApproxMatrixUnitSystem δ₁ x) (h : δ₁ ≤ δ₂) :
    IsApproxMatrixUnitSystem δ₂ x where
  norm_star_sub_lt r i j := (hx.norm_star_sub_lt r i j).trans_le h
  norm_mul_same_sub_lt r i j l := (hx.norm_mul_same_sub_lt r i j l).trans_le h
  norm_mul_ne_lt r i {_ _} l hjk := (hx.norm_mul_ne_lt r i l hjk).trans_le h
  norm_mul_block_ne_lt hrs i j k l := (hx.norm_mul_block_ne_lt hrs i j k l).trans_le h

/-- Every entry of a `δ`-approximate system of matrix units with `δ ≤ 1 / 2` has norm `< 3`. -/
theorem norm_lt_three {κ A : Type*} {n : κ → Type*} [NonUnitalCStarAlgebra A] {δ : ℝ}
    {x : ∀ r : κ, n r → n r → A} (hx : IsApproxMatrixUnitSystem δ x) (hδ : δ ≤ 1 / 2) (r : κ)
    (i j : n r) : ‖x r i j‖ < 3 := by
  have hdiag : ‖x r j j‖ < 3 := norm_lt_three_of_approx_projection
    (by rw [norm_sub_rev]; exact (hx.norm_star_sub_lt r j j).trans_le (by linarith))
    ((hx.norm_mul_same_sub_lt r j j j).trans_le (by linarith))
  have hsq : ‖x r i j‖ ^ 2 < 3 + (1 / 2) * ‖x r i j‖ + 1 / 2 := by
    rw [sq, ← CStarRing.norm_star_mul_self,
      show star (x r i j) * x r i j =
        x r j j + (star (x r i j) - x r j i) * x r i j + (x r j i * x r i j - x r j j) by
        simp only [sub_mul]; abel]
    have h1 : ‖(star (x r i j) - x r j i) * x r i j‖ ≤ (1 / 2) * ‖x r i j‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right ((hx.norm_star_sub_lt r i j).le.trans hδ) (norm_nonneg _))
    linarith [(hx.norm_mul_same_sub_lt r j i j).trans_le hδ,
      norm_add_le (x r j j + (star (x r i j) - x r j i) * x r i j) (x r j i * x r i j - x r j j),
      norm_add_le (x r j j) ((star (x r i j) - x r j i) * x r i j)]
  by_contra hge; nlinarith [not_lt.mp hge]

end IsApproxMatrixUnitSystem

private lemma norm_mul_le_of_le {A : Type*} [NonUnitalSeminormedRing A] {a b : A} {c d : ℝ}
    (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ d) : ‖a * b‖ ≤ c * d :=
  (norm_mul_le a b).trans (mul_le_mul ha hb (norm_nonneg b) ((norm_nonneg a).trans ha))

private lemma norm_mul₃_le_of_le {A : Type*} [NonUnitalSeminormedRing A] {a b c : A} {x y z : ℝ}
    (ha : ‖a‖ ≤ x) (hb : ‖b‖ ≤ y) (hc : ‖c‖ ≤ z) : ‖a * b * c‖ ≤ x * y * z :=
  norm_mul_le_of_le (norm_mul_le_of_le ha hb) hc

private lemma norm_add₄_le {E : Type*} [SeminormedAddCommGroup E] (a b c d : E) :
    ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  linarith [norm_add_le (a + b + c) d, norm_add_le (a + b) c, norm_add_le a b]

private lemma norm_add₅_le {E : Type*} [SeminormedAddCommGroup E] (a b c d e : E) :
    ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  linarith [norm_add_le (a + b + c + d) e, norm_add₄_le a b c d]

/-- **Uniform norm stability of finite multi-block systems of matrix units** (with subalgebra
preservation, Blackadar Proposition II.8.3.23). -/
theorem exists_delta_isMatrixUnitSystem_mem {κ : Type*} (n : κ → Type*) [Finite κ]
    [∀ r, Finite (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A S : Type*} [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A]
      [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)]
      {x : ∀ r : κ, n r → n r → A}, (∀ r i j, x r i j ∈ s) → IsApproxMatrixUnitSystem δ x →
      ∃ e : ∀ r : κ, n r → n r → A,
        (∀ r i j, e r i j ∈ s) ∧ IsMatrixUnitSystem e ∧ ∀ r i j, ‖e r i j - x r i j‖ < ε := by
  set ε₀ : ℝ := min ε 1
  set η : ℝ := min (1 / 32) (ε₀ / 60)
  obtain ⟨δ_diag, hδ_diag_pos, hδ_diag⟩ :=
    exists_delta_ortho_isStarProjection_mem (Σ r : κ, n r) (show 0 < η / 200 by positivity)
  set δ : ℝ := min (1 / 2) (min δ_diag (η / 200))
  refine ⟨δ, by positivity, fun {A S} _ _ _ _ _ {s} _ {x} hx_mem hx ↦ ?_⟩
  have hδ_half : δ ≤ 1 / 2 := min_le_left _ _
  have hδ_le_diag : δ ≤ δ_diag := (min_le_right _ _).trans (min_le_left _ _)
  have hδ_le_η : δ ≤ η / 200 := (min_le_right _ _).trans (min_le_right _ _)
  have hx_norm : ∀ r i j, ‖x r i j‖ < 3 := fun r i j ↦ hx.norm_lt_three hδ_half r i j
  obtain ⟨p_sig, hp_mem, hp_proj, hp_ortho, hp_dist⟩ :=
    hδ_diag (s := s) (d := fun u : Σ r : κ, n r ↦ x u.1 u.2 u.2) (fun u ↦ hx_mem u.1 u.2 u.2)
      (fun u ↦ by rw [norm_sub_rev]; exact (hx.norm_star_sub_lt u.1 u.2 u.2).trans_le hδ_le_diag)
      (fun u ↦ (hx.norm_mul_same_sub_lt u.1 u.2 u.2 u.2).trans_le hδ_le_diag)
      (fun u w huw ↦ by
        rcases u with ⟨r, i⟩; rcases w with ⟨t, j⟩
        by_cases hrt : r = t
        · subst hrt
          exact (hx.norm_mul_ne_lt r i j fun h ↦ huw (congrArg (Sigma.mk r) h)).trans_le hδ_le_diag
        · exact (hx.norm_mul_block_ne_lt hrt i i j j).trans_le hδ_le_diag)
  set p : ∀ r : κ, n r → A := fun r i ↦ p_sig ⟨r, i⟩
  have hv_exists (r : κ) (i : n r) :
      let i₀ : n r := Classical.choice ⟨i⟩
      ∃ v ∈ s, IsPartialIsometry v ∧ star v * v = p r i₀ ∧ v * star v = p r i ∧
        ‖v - x r i i₀‖ < 11 * η := by
    intro i₀
    set z : A := p r i * x r i i₀ * p r i₀
    have hz_mem : z ∈ s := mul_mem (mul_mem (hp_mem ⟨r, i⟩) (hx_mem r i i₀)) (hp_mem ⟨r, i₀⟩)
    have hqz : p r i * z = z := by
      dsimp [z]; rw [← mul_assoc, ← mul_assoc, (hp_proj ⟨r, i⟩).isIdempotentElem.eq]
    have hzp : z * p r i₀ = z := by dsimp [z]; rw [mul_assoc, (hp_proj ⟨r, i₀⟩).isIdempotentElem.eq]
    have hpri_norm : ‖p r i‖ ≤ 1 := (hp_proj ⟨r, i⟩).norm_le _
    have hpri₀_norm : ‖p r i₀‖ ≤ 1 := (hp_proj ⟨r, i₀⟩).norm_le _
    have hz_sub_x : ‖z - x r i i₀‖ < (16 / 200) * η := by
      rw [show z - x r i i₀ = (p r i - x r i i) * x r i i₀ * p r i₀ +
          x r i i * x r i i₀ * (p r i₀ - x r i₀ i₀) +
          (x r i i * x r i i₀ - x r i i₀) * x r i₀ i₀ + (x r i i₀ * x r i₀ i₀ - x r i i₀) by
        dsimp [z]; simp only [sub_mul, mul_sub]; abel]
      refine (norm_add₄_le _ _ _ _).trans_lt ?_
      linarith [norm_mul₃_le_of_le (hp_dist ⟨r, i⟩).le (hx_norm r i i₀).le hpri₀_norm,
        norm_mul₃_le_of_le (hx_norm r i i).le (hx_norm r i i₀).le (hp_dist ⟨r, i₀⟩).le,
        norm_mul_le_of_le (hx.norm_mul_same_sub_lt r i i i₀).le (hx_norm r i₀ i₀).le,
        hx.norm_mul_same_sub_lt r i i₀ i₀]
    have hz_norm : ‖z‖ ≤ 3 := by
      simpa using norm_mul₃_le_of_le hpri_norm (hx_norm r i i₀).le hpri₀_norm
    have hz_init : ‖star z * z - p r i₀‖ < η := by
      rw [show star z * z - p r i₀ = star (z - x r i i₀) * z + star (x r i i₀) * (z - x r i i₀) +
          (star (x r i i₀) - x r i₀ i) * x r i i₀ + (x r i₀ i * x r i i₀ - x r i₀ i₀) +
          (x r i₀ i₀ - p r i₀) by simp only [star_sub, sub_mul, mul_sub]; abel]
      refine (norm_add₅_le _ _ _ _ _).trans_lt ?_
      have hp' : ‖x r i₀ i₀ - p r i₀‖ < η / 200 := norm_sub_rev (p r i₀) _ ▸ hp_dist ⟨r, i₀⟩
      linarith [norm_nonneg (z - x r i i₀),
        norm_mul_le_of_le (norm_star (z - x r i i₀)).le hz_norm,
        norm_mul_le_of_le ((norm_star (x r i i₀)).le.trans (hx_norm r i i₀).le) hz_sub_x.le,
        norm_mul_le_of_le (hx.norm_star_sub_lt r i i₀).le (hx_norm r i i₀).le,
        hx.norm_mul_same_sub_lt r i₀ i i₀]
    have hz_fin : ‖z * star z - p r i‖ < η := by
      rw [show z * star z - p r i = (z - x r i i₀) * star z + x r i i₀ * star (z - x r i i₀) +
          x r i i₀ * (star (x r i i₀) - x r i₀ i) + (x r i i₀ * x r i₀ i - x r i i) +
          (x r i i - p r i) by simp only [star_sub, sub_mul, mul_sub]; abel]
      refine (norm_add₅_le _ _ _ _ _).trans_lt ?_
      have hp' : ‖x r i i - p r i‖ < η / 200 := norm_sub_rev (p r i) _ ▸ hp_dist ⟨r, i⟩
      linarith [norm_nonneg (z - x r i i₀),
        norm_mul_le_of_le hz_sub_x.le ((norm_star z).le.trans hz_norm),
        norm_mul_le_of_le (hx_norm r i i₀).le (norm_star (z - x r i i₀)).le,
        norm_mul_le_of_le (hx_norm r i i₀).le (hx.norm_star_sub_lt r i i₀).le,
        hx.norm_mul_same_sub_lt r i i₀ i]
    obtain ⟨v, hv_mem, hv_pi, hv_init, hv_fin, hv_dist_z⟩ :=
      exists_isPartialIsometry_mem_of_approx (s := s) (η := η) (min_le_left _ _)
        (hp_proj ⟨r, i₀⟩) (hp_proj ⟨r, i⟩) hz_mem hqz hzp hz_init hz_fin
    exact ⟨v, hv_mem, hv_pi, hv_init, hv_fin, by
      linarith [norm_nonneg (z - x r i i₀), show ‖v - x r i i₀‖ ≤ ‖v - z‖ + ‖z - x r i i₀‖ by
        simpa using norm_add_le (v - z) (z - x r i i₀)]⟩
  choose v hv_mem hv_pi hv_init hv_fin hv_dist using hv_exists
  refine ⟨fun r i j ↦ v r i * star (v r j),
    fun r i j ↦ mul_mem (hv_mem r i) (star_mem (hv_mem r j)),
    IsMatrixUnitSystem.of_partialIsometry hv_pi (fun r i j ↦ by rw [hv_init r i, hv_init r j])
      (fun u w huw ↦ by
        dsimp [onFun]; rw [hv_fin u.1 u.2, hv_fin w.1 w.2]
        exact (hp_ortho huw).mul_eq_zero' (hp_proj w).isSelfAdjoint),
    fun r i j ↦ ?_⟩
  let i₀ : n r := Classical.choice ⟨i⟩
  rw [show v r i * star (v r j) - x r i j =
      (v r i - x r i i₀) * star (v r j) + x r i i₀ * star (v r j - x r j i₀) +
        x r i i₀ * (star (x r j i₀) - x r i₀ j) + (x r i i₀ * x r i₀ j - x r i j) by
    simp only [star_sub, sub_mul, mul_sub]; abel]
  refine (norm_add₄_le _ _ _ _).trans_lt ?_
  have h1 :=
    norm_mul_le_of_le (hv_dist r i).le ((norm_star (v r j)).le.trans (hv_pi r j).norm_le_one)
  have h2 := norm_mul_le_of_le (hx_norm r i i₀).le
    ((norm_star (v r j - x r j i₀)).le.trans (hv_dist r j).le)
  linarith [norm_mul_le_of_le (hx_norm r i i₀).le (hx.norm_star_sub_lt r j i₀).le,
    hx.norm_mul_same_sub_lt r i i₀ j, norm_nonneg (v r i - x r i i₀),
    show η ≤ ε₀ / 60 from min_le_right _ _, show ε₀ ≤ ε from min_le_left _ _]

/-- **Uniform norm stability of finite multi-block systems of matrix units**. -/
theorem exists_delta_isMatrixUnitSystem {κ : Type*} (n : κ → Type*) [Finite κ]
    [∀ r, Finite (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {x : ∀ r : κ, n r → n r → A},
      IsApproxMatrixUnitSystem δ x →
      ∃ e : ∀ r : κ, n r → n r → A, IsMatrixUnitSystem e ∧ ∀ r i j, ‖e r i j - x r i j‖ < ε := by
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_delta_isMatrixUnitSystem_mem n hε
  refine ⟨δ, hδ_pos, fun {A} _ {_} hx ↦ ?_⟩
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨e, -, he, hdist⟩ := hδ (s := (⊤ : NonUnitalStarSubalgebra ℂ A)) (fun _ _ _ ↦ trivial) hx
  exact ⟨e, he, hdist⟩

/-- **Uniform norm stability of unital finite systems of matrix units** in a closed subalgebra. -/
theorem exists_delta_isUnitalMatrixUnitSystem_mem {κ : Type*} (n : κ → Type*) [Fintype κ]
    [∀ r, Fintype (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A S : Type*} [CStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A]
      [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)]
      {x : ∀ r : κ, n r → n r → A}, (∀ r i j, x r i j ∈ s) → IsApproxMatrixUnitSystem δ x →
      ‖matrixUnitSupport x - 1‖ < δ →
      ∃ e : ∀ r : κ, n r → n r → A,
        (∀ r i j, e r i j ∈ s) ∧ IsUnitalMatrixUnitSystem e ∧
        ∀ r i j, ‖e r i j - x r i j‖ < ε := by
  set M : ℕ := ∑ r : κ, Fintype.card (n r)
  set ε' : ℝ := min ε (1 / (2 * (M + 1 : ℝ)))
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := exists_delta_isMatrixUnitSystem_mem n (show 0 < ε' by positivity)
  set δ : ℝ := min δ₀ (1 / 2)
  refine ⟨δ, by positivity, fun {A S} _ _ _ _ _ {s} _ {x} hx_mem hx hsupp_x ↦ ?_⟩
  obtain ⟨e, he_mem, he, he_dist⟩ := hδ₀ hx_mem (hx.mono (min_le_left _ _))
  refine ⟨e, he_mem, ⟨he, ?_⟩, fun r i j ↦ (he_dist r i j).trans_le (min_le_left _ _)⟩
  apply he.isStarProjection_support.eq_one_of_norm_sub_one_lt_one
  have hsum_le : ‖matrixUnitSupport e - matrixUnitSupport x‖ ≤ (M : ℝ) * ε' := by
    simp only [matrixUnitSupport_def, ← Finset.sum_sub_distrib, M, Nat.cast_sum, Finset.sum_mul]
    exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun r _ ↦
      (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun i _ ↦ (he_dist r i i).le).trans (by simp)
  have hM_lt : (M : ℝ) * ε' < 1 / 2 :=
    calc (M : ℝ) * ε' ≤ (M : ℝ) * (1 / (2 * (M + 1 : ℝ))) := by gcongr; exact min_le_right _ _
      _ < ((M : ℝ) + 1) * (1 / (2 * (M + 1 : ℝ))) := by gcongr; linarith
      _ = 1 / 2 := by field_simp
  have htri : ‖matrixUnitSupport e - 1‖ ≤
      ‖matrixUnitSupport e - matrixUnitSupport x‖ + ‖matrixUnitSupport x - 1‖ := by
    simpa using norm_add_le (matrixUnitSupport e - matrixUnitSupport x) (matrixUnitSupport x - 1)
  linarith [min_le_right δ₀ (1 / 2)]

/-- **Uniform norm stability of unital finite multi-block systems of matrix units**. -/
theorem exists_delta_isUnitalMatrixUnitSystem {κ : Type*} (n : κ → Type*) [Fintype κ]
    [∀ r, Fintype (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [CStarAlgebra A] {x : ∀ r : κ, n r → n r → A},
      IsApproxMatrixUnitSystem δ x → ‖matrixUnitSupport x - 1‖ < δ →
      ∃ e : ∀ r : κ, n r → n r → A,
        IsUnitalMatrixUnitSystem e ∧ ∀ r i j, ‖e r i j - x r i j‖ < ε := by
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_delta_isUnitalMatrixUnitSystem_mem n hε
  refine ⟨δ, hδ_pos, fun {A} _ {_} hx hsupp ↦ ?_⟩
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨e, -, he, hdist⟩ :=
    hδ (s := (⊤ : NonUnitalStarSubalgebra ℂ A)) (fun _ _ _ ↦ trivial) hx hsupp
  exact ⟨e, he, hdist⟩

end TauCeti
