/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import TauCeti.Analysis.CStarAlgebra.MatrixUnits.Conjugacy
public import TauCeti.Analysis.CStarAlgebra.Projection.Stability

/-!
# Norm Stability of Matrix Units in C⋆-Algebras

This file proves Proposition II.8.3.23 of Blackadar's *Operator Algebras*: finite multi-block
systems of matrix units are **norm-stable** (semiprojective) across all C⋆-algebras, with a
perturbation threshold `δ > 0` depending only on `ε > 0` and the matrix dimensions `(κ, n)`, and
preserving every closed `ℂ`-⋆-subalgebra containing the approximate generators.

Combining norm stability of finite families of pairwise-orthogonal projections
(`TauCeti.exists_delta_ortho_isStarProjection_mem`) with two further ingredients yields the full
result:

1. **Polar perturbation of approximate partial isometries**
   (`TauCeti.exists_isPartialIsometry_mem_of_approx`): if `p, q` are star projections and
   `z ∈ s` satisfies `q * z = z`, `z * p = z`, `‖star z * z - p‖ < η`, and `‖z * star z - q‖ < η`
   with `η ≤ 1 / 32`, then `h = star z * z` lies in the corner `{a ∈ s | p * a = a ∧ a * p = a}`
   with `spectralProjection h = p`, and
   `v = z * cfcₙ ((Set.Ioi (1 / 2)).indicator (fun t ↦ (√t)⁻¹)) h` is a partial isometry in `s`
   with `star v * v = p`, `v * star v = q`, and `‖v - z‖ < 10 * η`.
2. **Assembly of full multi-block systems of matrix units**
   (`TauCeti.exists_delta_isMatrixUnitSystem_mem` and
   `TauCeti.exists_delta_isUnitalMatrixUnitSystem_mem`): diagonal entries are perturbed jointly to
   pairwise-orthogonal star projections, column entries from a basepoint in each block are
   compressed and perturbed to exact partial isometries via Step 1, and
   `TauCeti.IsMatrixUnitSystem.of_partialIsometry` reconstructs the full system. In the unital
   setting, `IsStarProjection.eq_one_of_norm_sub_one_lt_one` upgrades an approximate identity sum
   to `matrixUnitSupport e = 1`.

## Main definitions

* `TauCeti.IsApproxMatrixUnitSystem`: predicate expressing that a family
  `x : ∀ r : κ, n r → n r → A` satisfies the matrix-unit relations up to norm `< δ`.

## Main results

* `TauCeti.exists_isPartialIsometry_mem_of_approx`: quantitative polar perturbation of an
  approximate partial isometry between two star projections.
* `TauCeti.exists_delta_isMatrixUnitSystem_mem`, `TauCeti.exists_delta_isMatrixUnitSystem`,
  `TauCeti.exists_delta_isUnitalMatrixUnitSystem_mem`, and
  `TauCeti.exists_delta_isUnitalMatrixUnitSystem`: uniform norm stability of non-unital and unital
  finite multi-block systems of matrix units.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  Encyclopaedia of Mathematical Sciences **122**, Springer (2006), Proposition II.8.3.23.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications **5**,
  Cambridge University Press (1998), §4.6, Proposition 4.6.6.
-/

public section

open Function
open scoped NonUnitalContinuousFunctionalCalculus

namespace TauCeti

/-! ### Polar perturbation of approximate partial isometries -/

/-- The hereditary corner `{a ∈ s | p * a = a ∧ a * p = a}` inside a non-unital `ℂ`-⋆-subalgebra
`s` determined by a star projection `p`. -/
private def projCornerSubalgebra {A : Type*} [NonUnitalCStarAlgebra A]
    (s : NonUnitalStarSubalgebra ℂ A) (p : A) (hp : IsStarProjection p) :
    NonUnitalStarSubalgebra ℂ A where
  carrier := {a : A | a ∈ s ∧ p * a = a ∧ a * p = a}
  add_mem' {a b} ha hb :=
    ⟨add_mem ha.1 hb.1, by rw [mul_add, ha.2.1, hb.2.1], by rw [add_mul, ha.2.2, hb.2.2]⟩
  zero_mem' := ⟨zero_mem s, mul_zero p, zero_mul p⟩
  mul_mem' {a b} ha hb :=
    ⟨mul_mem ha.1 hb.1, by rw [← mul_assoc, ha.2.1], by rw [mul_assoc, hb.2.2]⟩
  smul_mem' c {a} ha :=
    ⟨SMulMemClass.smul_mem c ha.1, by rw [mul_smul_comm, ha.2.1],
      by rw [smul_mul_assoc, ha.2.2]⟩
  star_mem' {a} ha := by
    refine ⟨star_mem ha.1, ?_, ?_⟩
    · calc p * star a
          = star p * star a := by rw [hp.isSelfAdjoint.star_eq]
        _ = star (a * p) := (star_mul a p).symm
        _ = star a := by rw [ha.2.2]
    · calc star a * p
          = star a * star p := by rw [hp.isSelfAdjoint.star_eq]
        _ = star (p * a) := (star_mul p a).symm
        _ = star a := by rw [ha.2.1]

private lemma isClosed_projCornerSubalgebra {A : Type*} [NonUnitalCStarAlgebra A]
    {s : NonUnitalStarSubalgebra ℂ A} (hs : IsClosed (s : Set A)) (p : A)
    (hp : IsStarProjection p) :
    IsClosed (projCornerSubalgebra s p hp : Set A) := by
  change IsClosed ({a : A | a ∈ s} ∩ ({a : A | p * a = a} ∩ {a : A | a * p = a}))
  exact hs.inter
    ((isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
      (isClosed_eq (continuous_id.mul continuous_const) continuous_id))

/-- **Quantitative polar perturbation of an approximate partial isometry**: if `p` and `q` are star
projections in `A`, `s` is a closed non-unital `ℂ`-⋆-subalgebra of `A`, and `z ∈ s` satisfies
`q * z = z`, `z * p = z`, `‖star z * z - p‖ < η`, and `‖z * star z - q‖ < η` with `η ≤ 1 / 32`,
then there exists a partial isometry `v ∈ s` with initial projection `star v * v = p`, final
projection `v * star v = q`, and `‖v - z‖ < 10 * η`. -/
theorem exists_isPartialIsometry_mem_of_approx {A S : Type*} [NonUnitalCStarAlgebra A]
    [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A] {s : S}
    [hs : IsClosed (s : Set A)] {η : ℝ} (hη : η ≤ 1 / 32) {p q z : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hzs : z ∈ s)
    (hqz : q * z = z) (hzp : z * p = z)
    (hinit : ‖star z * z - p‖ < η) (hfin : ‖z * star z - q‖ < η) :
    ∃ v ∈ s, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q ∧ ‖v - z‖ < 10 * η := by
  have hη_pos : 0 < η := (norm_nonneg _).trans_lt hinit
  let s₀ : NonUnitalStarSubalgebra ℂ A := NonUnitalStarSubalgebra.ofClass s
  let corner := projCornerSubalgebra s₀ p hp
  have : IsClosed (corner : Set A) := isClosed_projCornerSubalgebra hs p hp
  set h : A := star z * z
  have hh_sa : IsSelfAdjoint h := IsSelfAdjoint.star_mul_self z
  have hph : p * h = h := by
    calc p * (star z * z)
        = (star p * star z) * z := by rw [hp.isSelfAdjoint.star_eq, mul_assoc]
      _ = star (z * p) * z := by rw [← star_mul]
      _ = star z * z := by rw [hzp]
  have hhp : h * p = h := by
    calc (star z * z) * p
        = star z * (z * p) := mul_assoc _ _ _
      _ = star z * z := by rw [hzp]
  have hh_corner : h ∈ corner := ⟨mul_mem (star_mem hzs) hzs, hph, hhp⟩
  have hh_defect_id : h * h - h = (h - p) * (h - p) + (h - p) := by
    simp only [sub_mul, mul_sub, hph, hhp, hp.isIdempotentElem.eq]
    abel
  have hh_defect : ‖h * h - h‖ ≤ ‖h - p‖ ^ 2 + ‖h - p‖ := by
    rw [hh_defect_id, sq]
    have hmul := norm_mul_le (h - p) (h - p)
    linarith [norm_add_le ((h - p) * (h - p)) (h - p)]
  have hsq_lt : ‖h - p‖ ^ 2 < η ^ 2 :=
    sq_lt_sq' (by linarith [norm_nonneg (h - p)]) hinit
  have hh_lt_quarter : ‖h * h - h‖ < 1 / 4 := by nlinarith
  have hsp_corner : spectralProjection h ∈ corner := spectralProjection_mem hh_corner
  have hsp_proj : IsStarProjection (spectralProjection h) :=
    hh_sa.isStarProjection_spectralProjection hh_lt_quarter
  have hsp_dist_h : ‖spectralProjection h - h‖ ≤ 2 * ‖h * h - h‖ :=
    hh_sa.norm_spectralProjection_sub_le hh_lt_quarter
  have hsp_dist_p : ‖spectralProjection h - p‖ < 1 := by
    have htri : ‖spectralProjection h - p‖ ≤ ‖spectralProjection h - h‖ + ‖h - p‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (spectralProjection h - h) (h - p)
    nlinarith
  have hsp_eq_p : spectralProjection h = p :=
    hsp_proj.eq_of_mul_eq_left_of_norm_sub_lt_one hp hsp_corner.2.2 hsp_dist_p
  set g : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator (fun t ↦ (√t)⁻¹)
  have hg_cont : ContinuousOn g (quasispectrum ℝ h) := by
    refine (Real.continuous_sqrt.continuousOn.inv₀ fun t ht ↦ ?_).indicator_Ioi_of_notMem
      (hh_sa.notMem_quasispectrum_half_of_norm_mul_self_sub_lt hh_lt_quarter)
    exact (Real.sqrt_pos.mpr (by linarith [Set.mem_Ioi.mp ht])).ne'
  have hg0 : g 0 = 0 := by simp [g]
  set w : A := cfcₙ g h
  have hw_corner : w ∈ corner := cfcₙ_mem (𝕜' := ℂ) g hh_corner
  have hw_sa : IsSelfAdjoint w := IsSelfAdjoint.cfcₙ
  have hwhw : w * h * w = p := by
    set ind : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)
    have hh_id : h = cfcₙ (fun t : ℝ ↦ t) h := (cfcₙ_id' ℝ h).symm
    have hcfc_eq : w * h * w = cfcₙ ind h := by
      calc w * h * w
          = cfcₙ g h * cfcₙ (fun t : ℝ ↦ t) h * cfcₙ g h := by
              dsimp only [w]
              exact congrArg (· * cfcₙ g h) (congrArg (cfcₙ g h * ·) hh_id)
        _ = cfcₙ (fun t : ℝ ↦ g t * t * g t) h := by
              rw [← cfcₙ_mul g (fun t : ℝ ↦ t) h hg_cont hg0 continuousOn_id rfl,
                ← cfcₙ_mul (fun t : ℝ ↦ g t * t) g h (hg_cont.mul continuousOn_id)
                  (by simp [hg0]) hg_cont hg0]
        _ = cfcₙ ind h := by
              refine cfcₙ_congr fun t _ ↦ ?_
              dsimp only [g, ind]
              by_cases ht : t ∈ Set.Ioi (1 / 2 : ℝ)
              · have ht_pos : 0 < t := by linarith [Set.mem_Ioi.mp ht]
                have hne : √t ≠ 0 := (Real.sqrt_pos.mpr ht_pos).ne'
                rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, Pi.one_apply]
                calc (√t)⁻¹ * t * (√t)⁻¹
                    = (√t)⁻¹ * (√t * √t) * (√t)⁻¹ := by rw [Real.mul_self_sqrt ht_pos.le]
                  _ = ((√t)⁻¹ * √t) * (√t * (√t)⁻¹) := by ring
                  _ = 1 := by rw [inv_mul_cancel₀ hne, mul_inv_cancel₀ hne, mul_one]
              · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul, zero_mul]
    rw [hcfc_eq, ← spectralProjection_def, hsp_eq_p]
  set v : A := z * w
  have hv_mem : v ∈ s := mul_mem hzs hw_corner.1
  have hv_init : star v * v = p := by
    dsimp [v]
    rw [star_mul, hw_sa.star_eq]
    calc w * star z * (z * w)
        = w * h * w := by simp only [h, mul_assoc]
      _ = p := hwhw
  have hv_pi : IsPartialIsometry v := by
    rw [isPartialIsometry_iff, mul_assoc, hv_init]
    dsimp [v]
    rw [mul_assoc, hw_corner.2.2]
  have hz_norm : ‖z‖ ≤ 2 := by
    have hnorm_h : ‖h‖ ≤ 2 := by
      have htri : ‖h‖ ≤ ‖p‖ + ‖h - p‖ := by
        simpa only [add_sub_cancel] using norm_add_le p (h - p)
      have hp_le : ‖p‖ ≤ 1 := hp.norm_le p
      linarith
    rw [CStarRing.norm_star_mul_self] at hnorm_h
    nlinarith [norm_nonneg z]
  have hw_sub_p : ‖w - p‖ ≤ 4 * ‖h * h - h‖ := by
    set ind : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)
    have hind_cont : ContinuousOn ind (quasispectrum ℝ h) :=
      hh_sa.continuousOn_indicator_Ioi_half hh_lt_quarter
    have hind0 : ind 0 = 0 := by simp [ind]
    rw [← hsp_eq_p, spectralProjection_def]
    dsimp [w]
    rw [← cfcₙ_sub g ind h hg_cont hg0 hind_cont hind0]
    refine norm_cfcₙ_le fun t ht ↦ ?_
    rw [Real.norm_eq_abs]
    have hqt : |t * t - t| ≤ ‖h * h - h‖ := hh_sa.abs_mul_self_sub_le_norm ht
    dsimp only [g, ind]
    by_cases hgt : t ∈ Set.Ioi (1 / 2 : ℝ)
    · rw [Set.indicator_of_mem hgt, Set.indicator_of_mem hgt, Pi.one_apply]
      have ht_half : (1 / 2 : ℝ) < t := Set.mem_Ioi.mp hgt
      have ht_pos : 0 < t := by linarith
      have hsqrt_half : (1 / 2 : ℝ) < √t := by
        rw [show (1 / 2 : ℝ) = √((1 / 2 : ℝ) ^ 2) by
          rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]]
        exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
      have hdenom_gt : (1 / 2 : ℝ) < √t * (1 + √t) := by nlinarith
      have hdenom_pos : 0 < √t * (1 + √t) := by linarith
      have hprod_sqrt : |1 - t| = |(√t)⁻¹ - 1| * (√t * (1 + √t)) := by
        have hne : √t ≠ 0 := (Real.sqrt_pos.mpr ht_pos).ne'
        have hid : 1 - t = ((√t)⁻¹ - 1) * (√t * (1 + √t)) := by
          calc 1 - t
              = 1 - √t * √t := by rw [Real.mul_self_sqrt ht_pos.le]
            _ = (1 - √t) * (1 + √t) := by ring
            _ = ((√t)⁻¹ * √t - 1 * √t) * (1 + √t) := by rw [inv_mul_cancel₀ hne, one_mul]
            _ = ((√t)⁻¹ - 1) * (√t * (1 + √t)) := by ring
        rw [hid, abs_mul, abs_of_pos hdenom_pos]
      have hprod_t : |t * t - t| = t * |1 - t| := by
        calc |t * t - t|
            = |t * (t - 1)| := by ring_nf
          _ = |t| * |t - 1| := abs_mul t (t - 1)
          _ = t * |1 - t| := by rw [abs_of_pos ht_pos, abs_sub_comm]
      nlinarith [abs_nonneg ((√t)⁻¹ - 1), abs_nonneg (1 - t)]
    · rw [Set.indicator_of_notMem hgt, Set.indicator_of_notMem hgt, sub_zero, abs_zero]
      positivity
  have hv_sub_z : ‖v - z‖ < 10 * η := by
    have hvz_eq : v - z = z * (w - p) := by
      calc v - z
          = z * w - z * p := by dsimp only [v]; rw [hzp]
        _ = z * (w - p) := (mul_sub z w p).symm
    rw [hvz_eq]
    have hmul_le : ‖z * (w - p)‖ ≤ ‖z‖ * ‖w - p‖ := norm_mul_le z (w - p)
    have : ‖w - p‖ < 5 * η := by nlinarith
    have hprod_lt : ‖z‖ * ‖w - p‖ < 2 * (5 * η) := by nlinarith [norm_nonneg z, norm_nonneg (w - p)]
    linarith
  have hv_fin_q : (v * star v) * q = v * star v := by
    have hqv : q * v = v := by
      dsimp [v]
      rw [← mul_assoc, hqz]
    calc (v * star v) * q
        = v * (star v * star q) := by rw [hq.isSelfAdjoint.star_eq, mul_assoc]
      _ = v * star (q * v) := by rw [← star_mul]
      _ = v * star v := by rw [hqv]
  have hv_fin_dist : ‖v * star v - q‖ < 1 := by
    have hsplit : v * star v - q = (v - z) * star v + z * star (v - z) + (z * star z - q) := by
      simp only [sub_mul, mul_sub, star_sub]
      abel
    rw [hsplit]
    have hv_norm_le : ‖v‖ ≤ 1 := hv_pi.norm_le_one
    have h1 : ‖(v - z) * star v‖ ≤ ‖v - z‖ := by
      calc ‖(v - z) * star v‖
          ≤ ‖v - z‖ * ‖star v‖ := norm_mul_le _ _
        _ ≤ ‖v - z‖ * 1 := by rw [norm_star]; gcongr
        _ = ‖v - z‖ := mul_one _
    have h2 : ‖z * star (v - z)‖ ≤ 2 * ‖v - z‖ := by
      calc ‖z * star (v - z)‖
          ≤ ‖z‖ * ‖star (v - z)‖ := norm_mul_le _ _
        _ = ‖z‖ * ‖v - z‖ := by rw [norm_star]
        _ ≤ 2 * ‖v - z‖ := by gcongr
    have hle1 := norm_add_le ((v - z) * star v + z * star (v - z)) (z * star z - q)
    have hle2 := norm_add_le ((v - z) * star v) (z * star (v - z))
    linarith
  have hv_fin : v * star v = q :=
    hv_pi.isStarProjection_mul_star_self.eq_of_mul_eq_left_of_norm_sub_lt_one hq hv_fin_q
      hv_fin_dist
  exact ⟨v, hv_mem, hv_pi, hv_init, hv_fin, hv_sub_z⟩

/-! ### Approximate matrix units and Blackadar Proposition II.8.3.23 -/

/-- A multi-block family `x : ∀ r : κ, n r → n r → A` is a **`δ`-approximate system of matrix
units** if each of the defining adjoint and multiplication relations of `IsMatrixUnitSystem` holds
up to norm strictly less than `δ`. -/
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

/-- Every entry of a `δ`-approximate system of matrix units in a non-unital C⋆-algebra with
`δ ≤ 1 / 2` has norm strictly less than `3`. -/
theorem norm_lt_three {κ A : Type*} {n : κ → Type*} [NonUnitalCStarAlgebra A] {δ : ℝ}
    {x : ∀ r : κ, n r → n r → A} (hx : IsApproxMatrixUnitSystem δ x) (hδ : δ ≤ 1 / 2) (r : κ)
    (i j : n r) : ‖x r i j‖ < 3 := by
  have hdiag : ‖x r j j‖ < 3 := by
    refine norm_lt_three_of_approx_projection ?_ ?_
    · rw [norm_sub_rev]
      exact (hx.norm_star_sub_lt r j j).trans_le (by linarith)
    · exact (hx.norm_mul_same_sub_lt r j j j).trans_le (by linarith)
  have hsplit :
      star (x r i j) * x r i j =
        x r j j + (star (x r i j) - x r j i) * x r i j + (x r j i * x r i j - x r j j) := by
    simp only [sub_mul]
    abel
  have hsq : ‖x r i j‖ ^ 2 < 3 + (1 / 2) * ‖x r i j‖ + 1 / 2 := by
    have hnorm_eq : ‖star (x r i j) * x r i j‖ = ‖x r i j‖ ^ 2 := by
      rw [CStarRing.norm_star_mul_self, sq]
    rw [← hnorm_eq, hsplit]
    have h1 : ‖(star (x r i j) - x r j i) * x r i j‖ ≤ (1 / 2) * ‖x r i j‖ := by
      calc ‖(star (x r i j) - x r j i) * x r i j‖
          ≤ ‖star (x r i j) - x r j i‖ * ‖x r i j‖ := norm_mul_le _ _
        _ ≤ (1 / 2) * ‖x r i j‖ :=
            mul_le_mul_of_nonneg_right ((hx.norm_star_sub_lt r i j).le.trans hδ) (norm_nonneg _)
    have h2 : ‖x r j i * x r i j - x r j j‖ < 1 / 2 :=
      (hx.norm_mul_same_sub_lt r j i j).trans_le hδ
    have hle1 := norm_add_le (x r j j + (star (x r i j) - x r j i) * x r i j)
      (x r j i * x r i j - x r j j)
    have hle2 := norm_add_le (x r j j) ((star (x r i j) - x r j i) * x r i j)
    linarith
  by_contra hge
  have := not_lt.mp hge
  nlinarith

end IsApproxMatrixUnitSystem

/-- **Uniform norm stability of finite multi-block systems of matrix units** (with subalgebra
preservation, Blackadar Proposition II.8.3.23): for every finite multi-block index `(κ, n)` and
every `ε > 0`, there exists `δ > 0` (depending only on `(κ, n)` and `ε`, independent of `A`) such
that in any non-unital C⋆-algebra `A` and closed non-unital `ℂ`-⋆-subalgebra `s`, every
`δ`-approximate system `x` in `s` is within `< ε` entrywise of an exact `IsMatrixUnitSystem e` in
`s`. -/
theorem exists_delta_isMatrixUnitSystem_mem {κ : Type*} (n : κ → Type*) [Finite κ]
    [∀ r, Finite (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A S : Type*} [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A]
      [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)]
      {x : ∀ r : κ, n r → n r → A},
      (∀ r i j, x r i j ∈ s) →
      IsApproxMatrixUnitSystem δ x →
      ∃ e : ∀ r : κ, n r → n r → A,
        (∀ r i j, e r i j ∈ s) ∧ IsMatrixUnitSystem e ∧ ∀ r i j, ‖e r i j - x r i j‖ < ε := by
  set ε₀ : ℝ := min ε 1
  set η : ℝ := min (1 / 32) (ε₀ / 60)
  have hη_pos : 0 < η := by positivity
  set γ : ℝ := η / 200
  have hγ_def : γ = η / 200 := rfl
  have hγ_pos : 0 < γ := by positivity
  obtain ⟨δ_diag, hδ_diag_pos, hδ_diag⟩ :=
    exists_delta_ortho_isStarProjection_mem (Σ r : κ, n r) hγ_pos
  set δ : ℝ := min (1 / 2) (min δ_diag (η / 200))
  have hδ_pos : 0 < δ := by positivity
  refine ⟨δ, hδ_pos, ?_⟩
  intro A S _ _ _ _ _ s hs x hx_mem hx
  have hδ_half : δ ≤ 1 / 2 := min_le_left _ _
  have hδ_le_diag : δ ≤ δ_diag := (min_le_right _ _).trans (min_le_left _ _)
  have hδ_le_η : δ ≤ η / 200 := (min_le_right _ _).trans (min_le_right _ _)
  have hx_norm : ∀ r i j, ‖x r i j‖ < 3 := fun r i j ↦ hx.norm_lt_three hδ_half r i j
  -- Perturb all diagonal entries simultaneously to pairwise-orthogonal star projections in `s`.
  obtain ⟨p_sig, hp_mem, hp_proj, hp_ortho, hp_dist⟩ :=
    hδ_diag (s := s) (d := fun u : Σ r : κ, n r ↦ x u.1 u.2 u.2)
      (fun u ↦ hx_mem u.1 u.2 u.2)
      (fun u ↦ by
        rw [norm_sub_rev]
        exact (hx.norm_star_sub_lt u.1 u.2 u.2).trans_le hδ_le_diag)
      (fun u ↦ (hx.norm_mul_same_sub_lt u.1 u.2 u.2 u.2).trans_le hδ_le_diag)
      (fun u w huw ↦ by
        by_cases hrt : u.1 = w.1
        · cases u with
          | mk r i =>
            cases w with
            | mk t j =>
              dsimp at hrt
              subst hrt
              have hij : i ≠ j := fun h ↦ huw (congrArg (Sigma.mk r) h)
              exact (hx.norm_mul_ne_lt r i j hij).trans_le hδ_le_diag
        · exact (hx.norm_mul_block_ne_lt hrt u.2 u.2 w.2 w.2).trans_le hδ_le_diag)
  set p : ∀ r : κ, n r → A := fun r i ↦ p_sig ⟨r, i⟩
  -- For each `(r, i)`, build the partial isometry `v r i ∈ s` from basepoint `i₀` to `i`.
  have hv_exists : ∀ (r : κ) (i : n r),
      let i₀ : n r := Classical.choice ⟨i⟩
      ∃ v ∈ s, IsPartialIsometry v ∧ star v * v = p r i₀ ∧ v * star v = p r i ∧
        ‖v - x r i i₀‖ < 11 * η := by
    intro r i
    let i₀ : n r := Classical.choice ⟨i⟩
    set z : A := p r i * x r i i₀ * p r i₀
    have hz_mem : z ∈ s := mul_mem (mul_mem (hp_mem ⟨r, i⟩) (hx_mem r i i₀)) (hp_mem ⟨r, i₀⟩)
    have hqz : p r i * z = z := by
      dsimp [z]
      rw [← mul_assoc, ← mul_assoc, (hp_proj ⟨r, i⟩).isIdempotentElem.eq]
    have hzp : z * p r i₀ = z := by
      dsimp [z]
      rw [mul_assoc, (hp_proj ⟨r, i₀⟩).isIdempotentElem.eq]
    have hpri_norm : ‖p r i‖ ≤ 1 := (hp_proj ⟨r, i⟩).norm_le _
    have hpri₀_norm : ‖p r i₀‖ ≤ 1 := (hp_proj ⟨r, i₀⟩).norm_le _
    have hz_sub_x : ‖z - x r i i₀‖ < (16 / 200) * η := by
      have hsplit :
          z - x r i i₀ =
            (p r i - x r i i) * x r i i₀ * p r i₀ +
              x r i i * x r i i₀ * (p r i₀ - x r i₀ i₀) +
              (x r i i * x r i i₀ - x r i i₀) * x r i₀ i₀ +
              (x r i i₀ * x r i₀ i₀ - x r i i₀) := by
        dsimp [z]
        simp only [sub_mul, mul_sub]
        abel
      rw [hsplit]
      have h1 : ‖(p r i - x r i i) * x r i i₀ * p r i₀‖ ≤ 3 * γ := by
        calc ‖(p r i - x r i i) * x r i i₀ * p r i₀‖
            ≤ ‖(p r i - x r i i) * x r i i₀‖ * ‖p r i₀‖ := norm_mul_le _ _
          _ ≤ (‖p r i - x r i i‖ * ‖x r i i₀‖) * ‖p r i₀‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
          _ ≤ (γ * 3) * 1 :=
              mul_le_mul (mul_le_mul (hp_dist ⟨r, i⟩).le (hx_norm r i i₀).le
                (norm_nonneg _) (by positivity)) hpri₀_norm (norm_nonneg _) (by positivity)
          _ = 3 * γ := by ring
      have h2 : ‖x r i i * x r i i₀ * (p r i₀ - x r i₀ i₀)‖ ≤ 9 * γ := by
        calc ‖x r i i * x r i i₀ * (p r i₀ - x r i₀ i₀)‖
            ≤ ‖x r i i * x r i i₀‖ * ‖p r i₀ - x r i₀ i₀‖ := norm_mul_le _ _
          _ ≤ (‖x r i i‖ * ‖x r i i₀‖) * ‖p r i₀ - x r i₀ i₀‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
          _ ≤ (3 * 3) * γ :=
              mul_le_mul (mul_le_mul (hx_norm r i i).le (hx_norm r i i₀).le
                (norm_nonneg _) (by positivity)) (hp_dist ⟨r, i₀⟩).le (norm_nonneg _)
                (by positivity)
          _ = 9 * γ := by ring
      have h3 : ‖(x r i i * x r i i₀ - x r i i₀) * x r i₀ i₀‖ ≤ 3 * δ := by
        calc ‖(x r i i * x r i i₀ - x r i i₀) * x r i₀ i₀‖
            ≤ ‖x r i i * x r i i₀ - x r i i₀‖ * ‖x r i₀ i₀‖ := norm_mul_le _ _
          _ ≤ δ * 3 :=
              mul_le_mul (hx.norm_mul_same_sub_lt r i i i₀).le (hx_norm r i₀ i₀).le
                (norm_nonneg _) (by positivity)
          _ = 3 * δ := by ring
      have h4 : ‖x r i i₀ * x r i₀ i₀ - x r i i₀‖ < δ := hx.norm_mul_same_sub_lt r i i₀ i₀
      have hle1 := norm_add_le
        ((p r i - x r i i) * x r i i₀ * p r i₀ +
          x r i i * x r i i₀ * (p r i₀ - x r i₀ i₀) +
          (x r i i * x r i i₀ - x r i i₀) * x r i₀ i₀)
        (x r i i₀ * x r i₀ i₀ - x r i i₀)
      have hle2 := norm_add_le
        ((p r i - x r i i) * x r i i₀ * p r i₀ +
          x r i i * x r i i₀ * (p r i₀ - x r i₀ i₀))
        ((x r i i * x r i i₀ - x r i i₀) * x r i₀ i₀)
      have hle3 := norm_add_le
        ((p r i - x r i i) * x r i i₀ * p r i₀)
        (x r i i * x r i i₀ * (p r i₀ - x r i₀ i₀))
      linarith
    have hz_norm : ‖z‖ ≤ 3 := by
      dsimp [z]
      calc ‖p r i * x r i i₀ * p r i₀‖
          ≤ ‖p r i * x r i i₀‖ * ‖p r i₀‖ := norm_mul_le _ _
        _ ≤ (‖p r i‖ * ‖x r i i₀‖) * ‖p r i₀‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ (1 * 3) * 1 :=
            mul_le_mul (mul_le_mul hpri_norm (hx_norm r i i₀).le (norm_nonneg _) (by positivity))
              hpri₀_norm (norm_nonneg _) (by positivity)
        _ = 3 := by ring
    have hz_init : ‖star z * z - p r i₀‖ < η := by
      have hsplit :
          star z * z - p r i₀ =
            star (z - x r i i₀) * z +
              star (x r i i₀) * (z - x r i i₀) +
              (star (x r i i₀) - x r i₀ i) * x r i i₀ +
              (x r i₀ i * x r i i₀ - x r i₀ i₀) +
              (x r i₀ i₀ - p r i₀) := by
        simp only [star_sub, sub_mul, mul_sub]
        abel
      rw [hsplit]
      have h1 : ‖star (z - x r i i₀) * z‖ ≤ 3 * ‖z - x r i i₀‖ := by
        calc ‖star (z - x r i i₀) * z‖
            ≤ ‖star (z - x r i i₀)‖ * ‖z‖ := norm_mul_le _ _
          _ ≤ ‖z - x r i i₀‖ * 3 := by
              rw [norm_star]
              exact mul_le_mul_of_nonneg_left hz_norm (norm_nonneg _)
          _ = 3 * ‖z - x r i i₀‖ := by ring
      have h2 : ‖star (x r i i₀) * (z - x r i i₀)‖ ≤ 3 * ‖z - x r i i₀‖ := by
        calc ‖star (x r i i₀) * (z - x r i i₀)‖
            ≤ ‖star (x r i i₀)‖ * ‖z - x r i i₀‖ := norm_mul_le _ _
          _ ≤ 3 * ‖z - x r i i₀‖ := by
              rw [norm_star]
              exact mul_le_mul_of_nonneg_right (hx_norm r i i₀).le (norm_nonneg _)
      have h3 : ‖(star (x r i i₀) - x r i₀ i) * x r i i₀‖ ≤ 3 * δ := by
        calc ‖(star (x r i i₀) - x r i₀ i) * x r i i₀‖
            ≤ ‖star (x r i i₀) - x r i₀ i‖ * ‖x r i i₀‖ := norm_mul_le _ _
          _ ≤ δ * 3 :=
              mul_le_mul (hx.norm_star_sub_lt r i i₀).le (hx_norm r i i₀).le
                (norm_nonneg _) (by positivity)
          _ = 3 * δ := by ring
      have h4 : ‖x r i₀ i * x r i i₀ - x r i₀ i₀‖ < δ := hx.norm_mul_same_sub_lt r i₀ i i₀
      have h5 : ‖x r i₀ i₀ - p r i₀‖ < γ := by
        rw [norm_sub_rev]
        exact hp_dist ⟨r, i₀⟩
      have hle1 := norm_add_le
        (star (z - x r i i₀) * z + star (x r i i₀) * (z - x r i i₀) +
          (star (x r i i₀) - x r i₀ i) * x r i i₀ + (x r i₀ i * x r i i₀ - x r i₀ i₀))
        (x r i₀ i₀ - p r i₀)
      have hle2 := norm_add_le
        (star (z - x r i i₀) * z + star (x r i i₀) * (z - x r i i₀) +
          (star (x r i i₀) - x r i₀ i) * x r i i₀)
        (x r i₀ i * x r i i₀ - x r i₀ i₀)
      have hle3 := norm_add_le
        (star (z - x r i i₀) * z + star (x r i i₀) * (z - x r i i₀))
        ((star (x r i i₀) - x r i₀ i) * x r i i₀)
      have hle4 := norm_add_le (star (z - x r i i₀) * z) (star (x r i i₀) * (z - x r i i₀))
      linarith
    have hz_fin : ‖z * star z - p r i‖ < η := by
      have hsplit :
          z * star z - p r i =
            (z - x r i i₀) * star z +
              x r i i₀ * star (z - x r i i₀) +
              x r i i₀ * (star (x r i i₀) - x r i₀ i) +
              (x r i i₀ * x r i₀ i - x r i i) +
              (x r i i - p r i) := by
        simp only [star_sub, sub_mul, mul_sub]
        abel
      rw [hsplit]
      have h1 : ‖(z - x r i i₀) * star z‖ ≤ 3 * ‖z - x r i i₀‖ := by
        calc ‖(z - x r i i₀) * star z‖
            ≤ ‖z - x r i i₀‖ * ‖star z‖ := norm_mul_le _ _
          _ ≤ ‖z - x r i i₀‖ * 3 := by
              rw [norm_star]
              exact mul_le_mul_of_nonneg_left hz_norm (norm_nonneg _)
          _ = 3 * ‖z - x r i i₀‖ := by ring
      have h2 : ‖x r i i₀ * star (z - x r i i₀)‖ ≤ 3 * ‖z - x r i i₀‖ := by
        calc ‖x r i i₀ * star (z - x r i i₀)‖
            ≤ ‖x r i i₀‖ * ‖star (z - x r i i₀)‖ := norm_mul_le _ _
          _ ≤ 3 * ‖z - x r i i₀‖ := by
              rw [norm_star]
              exact mul_le_mul_of_nonneg_right (hx_norm r i i₀).le (norm_nonneg _)
      have h3 : ‖x r i i₀ * (star (x r i i₀) - x r i₀ i)‖ ≤ 3 * δ := by
        calc ‖x r i i₀ * (star (x r i i₀) - x r i₀ i)‖
            ≤ ‖x r i i₀‖ * ‖star (x r i i₀) - x r i₀ i‖ := norm_mul_le _ _
          _ ≤ 3 * δ :=
              mul_le_mul (hx_norm r i i₀).le (hx.norm_star_sub_lt r i i₀).le
                (norm_nonneg _) (by positivity)
      have h4 : ‖x r i i₀ * x r i₀ i - x r i i‖ < δ := hx.norm_mul_same_sub_lt r i i₀ i
      have h5 : ‖x r i i - p r i‖ < γ := by
        rw [norm_sub_rev]
        exact hp_dist ⟨r, i⟩
      have hle1 := norm_add_le
        ((z - x r i i₀) * star z + x r i i₀ * star (z - x r i i₀) +
          x r i i₀ * (star (x r i i₀) - x r i₀ i) + (x r i i₀ * x r i₀ i - x r i i))
        (x r i i - p r i)
      have hle2 := norm_add_le
        ((z - x r i i₀) * star z + x r i i₀ * star (z - x r i i₀) +
          x r i i₀ * (star (x r i i₀) - x r i₀ i))
        (x r i i₀ * x r i₀ i - x r i i)
      have hle3 := norm_add_le
        ((z - x r i i₀) * star z + x r i i₀ * star (z - x r i i₀))
        (x r i i₀ * (star (x r i i₀) - x r i₀ i))
      have hle4 := norm_add_le ((z - x r i i₀) * star z) (x r i i₀ * star (z - x r i i₀))
      linarith
    obtain ⟨v, hv_mem, hv_pi, hv_init, hv_fin, hv_dist_z⟩ :=
      exists_isPartialIsometry_mem_of_approx (s := s) (min_le_left _ _)
        (hp_proj ⟨r, i₀⟩) (hp_proj ⟨r, i⟩) hz_mem hqz hzp hz_init hz_fin
    refine ⟨v, hv_mem, hv_pi, hv_init, hv_fin, ?_⟩
    have htri : ‖v - x r i i₀‖ ≤ ‖v - z‖ + ‖z - x r i i₀‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (v - z) (z - x r i i₀)
    linarith
  choose v hv_mem hv_pi hv_init hv_fin hv_dist using hv_exists
  refine ⟨fun r i j ↦ v r i * star (v r j), ?_, ?_, ?_⟩
  · intro r i j
    exact mul_mem (hv_mem r i) (star_mem (hv_mem r j))
  · refine IsMatrixUnitSystem.of_partialIsometry hv_pi (fun r i j ↦ ?_) ?_
    · rw [hv_init r i, hv_init r j]
    · intro u w huw
      dsimp [Function.onFun]
      rw [hv_fin u.1 u.2, hv_fin w.1 w.2]
      exact (hp_ortho huw).mul_eq_zero' (hp_proj w).isSelfAdjoint
  · intro r i j
    let i₀ : n r := Classical.choice ⟨i⟩
    have hvi : ‖v r i - x r i i₀‖ < 11 * η := hv_dist r i
    have hvj : ‖v r j - x r j i₀‖ < 11 * η := hv_dist r j
    have hsplit :
        v r i * star (v r j) - x r i j =
          (v r i - x r i i₀) * star (v r j) +
            x r i i₀ * star (v r j - x r j i₀) +
            x r i i₀ * (star (x r j i₀) - x r i₀ j) +
            (x r i i₀ * x r i₀ j - x r i j) := by
      simp only [star_sub, sub_mul, mul_sub]
      abel
    rw [hsplit]
    have h1 : ‖(v r i - x r i i₀) * star (v r j)‖ ≤ 11 * η := by
      calc ‖(v r i - x r i i₀) * star (v r j)‖
          ≤ ‖v r i - x r i i₀‖ * ‖star (v r j)‖ := norm_mul_le _ _
        _ ≤ (11 * η) * 1 := by
            rw [norm_star]
            exact mul_le_mul hvi.le (hv_pi r j).norm_le_one (norm_nonneg _) (by positivity)
        _ = 11 * η := mul_one _
    have h2 : ‖x r i i₀ * star (v r j - x r j i₀)‖ ≤ 33 * η := by
      calc ‖x r i i₀ * star (v r j - x r j i₀)‖
          ≤ ‖x r i i₀‖ * ‖star (v r j - x r j i₀)‖ := norm_mul_le _ _
        _ ≤ 3 * (11 * η) := by
            rw [norm_star]
            exact mul_le_mul (hx_norm r i i₀).le hvj.le (norm_nonneg _) (by positivity)
        _ = 33 * η := by ring
    have h3 : ‖x r i i₀ * (star (x r j i₀) - x r i₀ j)‖ ≤ 3 * δ := by
      calc ‖x r i i₀ * (star (x r j i₀) - x r i₀ j)‖
          ≤ ‖x r i i₀‖ * ‖star (x r j i₀) - x r i₀ j‖ := norm_mul_le _ _
        _ ≤ 3 * δ :=
            mul_le_mul (hx_norm r i i₀).le (hx.norm_star_sub_lt r j i₀).le
              (norm_nonneg _) (by positivity)
    have h4 : ‖x r i i₀ * x r i₀ j - x r i j‖ < δ := hx.norm_mul_same_sub_lt r i i₀ j
    have hη_le : η ≤ ε₀ / 60 := min_le_right _ _
    have hε₀_le : ε₀ ≤ ε := min_le_left _ _
    have hle1 := norm_add_le
      ((v r i - x r i i₀) * star (v r j) +
        x r i i₀ * star (v r j - x r j i₀) +
        x r i i₀ * (star (x r j i₀) - x r i₀ j))
      (x r i i₀ * x r i₀ j - x r i j)
    have hle2 := norm_add_le
      ((v r i - x r i i₀) * star (v r j) + x r i i₀ * star (v r j - x r j i₀))
      (x r i i₀ * (star (x r j i₀) - x r i₀ j))
    have hle3 := norm_add_le
      ((v r i - x r i i₀) * star (v r j))
      (x r i i₀ * star (v r j - x r j i₀))
    linarith

/-- **Uniform norm stability of finite multi-block systems of matrix units** in an ambient
non-unital C⋆-algebra (Blackadar Proposition II.8.3.23). -/
theorem exists_delta_isMatrixUnitSystem {κ : Type*} (n : κ → Type*) [Finite κ]
    [∀ r, Finite (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {x : ∀ r : κ, n r → n r → A},
      IsApproxMatrixUnitSystem δ x →
      ∃ e : ∀ r : κ, n r → n r → A,
        IsMatrixUnitSystem e ∧ ∀ r i j, ‖e r i j - x r i j‖ < ε := by
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_delta_isMatrixUnitSystem_mem n hε
  refine ⟨δ, hδ_pos, fun {A} _ {x} hx ↦ ?_⟩
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨e, -, he, hdist⟩ := hδ (s := (⊤ : NonUnitalStarSubalgebra ℂ A)) (fun _ _ _ ↦ trivial) hx
  exact ⟨e, he, hdist⟩

/-- **Uniform norm stability of unital finite multi-block systems of matrix units** (with subalgebra
preservation): in any unital C⋆-algebra `A` and closed `ℂ`-⋆-subalgebra `s`, if `x` is a
`δ`-approximate system of matrix units in `s` whose diagonal sum is within `< δ` of `1`, then `x`
is within `< ε` entrywise of an exact `IsUnitalMatrixUnitSystem e` in `s`. -/
theorem exists_delta_isUnitalMatrixUnitSystem_mem {κ : Type*} (n : κ → Type*) [Fintype κ]
    [∀ r, Fintype (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A S : Type*} [CStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A]
      [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)]
      {x : ∀ r : κ, n r → n r → A},
      (∀ r i j, x r i j ∈ s) →
      IsApproxMatrixUnitSystem δ x →
      ‖matrixUnitSupport x - 1‖ < δ →
      ∃ e : ∀ r : κ, n r → n r → A,
        (∀ r i j, e r i j ∈ s) ∧ IsUnitalMatrixUnitSystem e ∧
        ∀ r i j, ‖e r i j - x r i j‖ < ε := by
  set M : ℕ := ∑ r : κ, Fintype.card (n r)
  set ε' : ℝ := min ε (1 / (2 * (M + 1 : ℝ)))
  have hε'_pos : 0 < ε' := by positivity
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := exists_delta_isMatrixUnitSystem_mem n hε'_pos
  set δ : ℝ := min δ₀ (1 / 2)
  have hδ_pos : 0 < δ := by positivity
  refine ⟨δ, hδ_pos, ?_⟩
  intro A S _ _ _ _ _ s _ x hx_mem hx hsupp_x
  obtain ⟨e, he_mem, he, he_dist⟩ := hδ₀ hx_mem (hx.mono (min_le_left _ _))
  refine ⟨e, he_mem, ⟨he, ?_⟩, fun r i j ↦ (he_dist r i j).trans_le (min_le_left _ _)⟩
  apply he.isStarProjection_support.eq_one_of_norm_sub_one_lt_one
  have hsupp_diff :
      ‖matrixUnitSupport e - matrixUnitSupport x‖ < 1 / 2 := by
    have hdiff_eq :
        matrixUnitSupport e - matrixUnitSupport x =
          ∑ r : κ, ∑ i : n r, (e r i i - x r i i) := by
      simp only [matrixUnitSupport_def, ← Finset.sum_sub_distrib]
    rw [hdiff_eq]
    have hsum_le :
        ‖∑ r : κ, ∑ i : n r, (e r i i - x r i i)‖ ≤ (M : ℝ) * ε' := by
      calc ‖∑ r : κ, ∑ i : n r, (e r i i - x r i i)‖
          ≤ ∑ r : κ, ‖∑ i : n r, (e r i i - x r i i)‖ := norm_sum_le _ _
        _ ≤ ∑ r : κ, ∑ i : n r, ‖e r i i - x r i i‖ := by
            gcongr with r
            exact norm_sum_le _ _
        _ ≤ ∑ r : κ, ∑ _i : n r, ε' := by
            gcongr with r _ i
            exact (he_dist r i i).le
        _ = (M : ℝ) * ε' := by simp [M, Finset.sum_mul]
    have hε'_le : ε' ≤ 1 / (2 * (M + 1 : ℝ)) := min_le_right _ _
    have hM_lt : (M : ℝ) * ε' < 1 / 2 := by
      calc (M : ℝ) * ε'
          ≤ (M : ℝ) * (1 / (2 * (M + 1 : ℝ))) := by gcongr
        _ < ((M : ℝ) + 1) * (1 / (2 * (M + 1 : ℝ))) := by
            gcongr
            linarith
        _ = 1 / 2 := by field_simp
    linarith
  have htri :
      ‖matrixUnitSupport e - 1‖ ≤
        ‖matrixUnitSupport e - matrixUnitSupport x‖ + ‖matrixUnitSupport x - 1‖ := by
    simpa only [sub_add_sub_cancel] using
      norm_add_le (matrixUnitSupport e - matrixUnitSupport x) (matrixUnitSupport x - 1)
  have hδ_half : δ ≤ 1 / 2 := min_le_right _ _
  linarith

/-- **Uniform norm stability of unital finite multi-block systems of matrix units** in an ambient
unital C⋆-algebra. -/
theorem exists_delta_isUnitalMatrixUnitSystem {κ : Type*} (n : κ → Type*) [Fintype κ]
    [∀ r, Fintype (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [CStarAlgebra A] {x : ∀ r : κ, n r → n r → A},
      IsApproxMatrixUnitSystem δ x →
      ‖matrixUnitSupport x - 1‖ < δ →
      ∃ e : ∀ r : κ, n r → n r → A,
        IsUnitalMatrixUnitSystem e ∧ ∀ r i j, ‖e r i j - x r i j‖ < ε := by
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_delta_isUnitalMatrixUnitSystem_mem n hε
  refine ⟨δ, hδ_pos, fun {A} _ {x} hx hsupp ↦ ?_⟩
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨e, -, he, hdist⟩ :=
    hδ (s := (⊤ : NonUnitalStarSubalgebra ℂ A)) (fun _ _ _ ↦ trivial) hx hsupp
  exact ⟨e, he, hdist⟩

end TauCeti
