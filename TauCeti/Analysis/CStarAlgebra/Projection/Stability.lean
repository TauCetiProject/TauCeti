/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Algebra.Star.Orthogonal
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Topology.Algebra.Indicator
public import Mathlib.Topology.Order.DenselyOrdered
import TauCeti.Topology.Algebra.Indicator

/-!
# Norm Stability and Rigidity of Projections in C⋆-Algebras

This file proves norm rigidity of comparable star projections in C⋆-rings and norm stability of
single projections and finite families of pairwise-orthogonal projections in (not necessarily
unital) C⋆-algebras via spectral gap functional calculus (`TauCeti.spectralProjection`) and
inductive compression in orthogonal-complement corners.

## Main definitions

* `TauCeti.spectralProjection`: `cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator 1) a` cut at `1 / 2`.

## Main results

* `IsStarProjection.eq_zero_of_norm_lt_one`,
  `IsStarProjection.eq_of_mul_eq_left_of_norm_sub_lt_one`,
  `IsStarProjection.eq_of_le_of_norm_sub_lt_one`, `IsStarProjection.eq_one_of_norm_sub_one_lt_one`.
* `IsSelfAdjoint.isStarProjection_spectralProjection`,
  `IsSelfAdjoint.norm_spectralProjection_sub_le`.
* `TauCeti.exists_isStarProjection_mem_of_approx`, `TauCeti.exists_delta_isStarProjection_mem`,
  `TauCeti.exists_delta_ortho_isStarProjection_mem`, `TauCeti.exists_delta_ortho_isStarProjection`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.8.3.23.
* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C*-Algebras*,
  Cambridge Univ. Press (2000), Lemma 2.2.6.
-/

public section

open Function
open scoped NonUnitalContinuousFunctionalCalculus

namespace IsStarProjection

section CStarRing

variable {E : Type*} [NonUnitalNormedRing E] [StarRing E] [CStarRing E]

/-- A star projection of norm strictly less than `1` in a C⋆-ring must be `0`. -/
theorem eq_zero_of_norm_lt_one {e : E} (he : IsStarProjection e) (h : ‖e‖ < 1) : e = 0 := by
  by_contra hne
  have hpos : 0 < ‖e‖ := norm_pos_iff.mpr hne
  have hsq : ‖e‖ * ‖e‖ = ‖e‖ := by
    rw [← CStarRing.norm_star_mul_self, he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]
  nlinarith

/-- Every nonzero star projection in a C⋆-ring has norm `1`. -/
theorem norm_eq_one_of_ne_zero {e : E} (he : IsStarProjection e) (hne : e ≠ 0) : ‖e‖ = 1 :=
  le_antisymm (he.norm_le e) (not_lt.mp fun hlt ↦ hne (he.eq_zero_of_norm_lt_one hlt))

/-- Star projections `p, q` in a C⋆-ring with `p * q = p` and `‖p - q‖ < 1` satisfy `p = q`. -/
theorem eq_of_mul_eq_left_of_norm_sub_lt_one {p q : E} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : p * q = p) (h : ‖p - q‖ < 1) : p = q :=
  (sub_eq_zero.mp ((hp.sub_of_mul_eq_left hq hpq).eq_zero_of_norm_lt_one
    (norm_sub_rev p q ▸ h))).symm

/-- Star projections `p, q` in a C⋆-ring with `q * p = p` and `‖p - q‖ < 1` satisfy `p = q`. -/
theorem eq_of_mul_eq_right_of_norm_sub_lt_one {p q : E} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hqp : q * p = p) (h : ‖p - q‖ < 1) : p = q :=
  (sub_eq_zero.mp ((hp.sub_of_mul_eq_right hq hqp).eq_zero_of_norm_lt_one
    (norm_sub_rev p q ▸ h))).symm

end CStarRing

/-- Comparable star projections `p ≤ q` in a C⋆-algebra with `‖p - q‖ < 1` are equal. -/
theorem eq_of_le_of_norm_sub_lt_one {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hle : p ≤ q) (h : ‖p - q‖ < 1) : p = q :=
  hp.eq_of_mul_eq_left_of_norm_sub_lt_one hq ((hp.le_iff_mul_eq_left hq).mp hle) h

/-- A star projection at distance `< 1` from `1` in a unital C⋆-ring equals `1`. -/
theorem eq_one_of_norm_sub_one_lt_one {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]
    {p : E} (hp : IsStarProjection p) (h : ‖p - 1‖ < 1) : p = 1 :=
  hp.eq_of_mul_eq_left_of_norm_sub_lt_one (.one E) (mul_one p) h

end IsStarProjection

namespace TauCeti

/-- The spectral projection `cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator 1) a` cut at `1 / 2`. -/
noncomputable def spectralProjection {A : Type*} [NonUnitalCStarAlgebra A] (a : A) : A :=
  cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) a

/-- Unfold `TauCeti.spectralProjection`. -/
theorem spectralProjection_def {A : Type*} [NonUnitalCStarAlgebra A] (a : A) :
    spectralProjection a = cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) a := (rfl)

/-- `spectralProjection a` belongs to every closed non-unital `ℂ`-⋆-subalgebra containing `a`. -/
theorem spectralProjection_mem {A S : Type*} [NonUnitalCStarAlgebra A] [SetLike S A]
    [NonUnitalSubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A] {s : S}
    [IsClosed (s : Set A)] {a : A} (ha : a ∈ s) : spectralProjection a ∈ s := by
  rw [spectralProjection_def]; exact cfcₙ_mem (𝕜' := ℂ) _ ha

end TauCeti

namespace IsSelfAdjoint

open TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A] {a : A}

/-- Pointwise quasispectral estimate `|t * t - t| ≤ ‖a * a - a‖` for self-adjoint `a`. -/
theorem abs_mul_self_sub_le_norm (ha : IsSelfAdjoint a) {t : ℝ} (ht : t ∈ quasispectrum ℝ a) :
    |t * t - t| ≤ ‖a * a - a‖ := by
  have hcont_sq : ContinuousOn (fun x : ℝ ↦ x * x) (quasispectrum ℝ a) :=
    (continuous_id.mul continuous_id).continuousOn
  have hcfc : cfcₙ (fun x : ℝ ↦ x * x - x) a = a * a - a := by
    rw [cfcₙ_sub (fun x : ℝ ↦ x * x) (fun x : ℝ ↦ x) a hcont_sq (mul_zero 0) continuousOn_id rfl,
      cfcₙ_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ x) a continuousOn_id rfl continuousOn_id rfl,
      cfcₙ_id' ℝ a]
  simpa [Real.norm_eq_abs, hcfc] using
    norm_apply_le_norm_cfcₙ (fun x : ℝ ↦ x * x - x) a ht (hcont_sq.sub continuousOn_id)
      (by simp) ha

/-- When `IsSelfAdjoint a` and `‖a * a - a‖ < 1 / 4`, `1 / 2 ∉ quasispectrum ℝ a`. -/
theorem notMem_quasispectrum_half_of_norm_mul_self_sub_lt (ha : IsSelfAdjoint a)
    (h : ‖a * a - a‖ < 1 / 4) : (1 / 2 : ℝ) ∉ quasispectrum ℝ a := fun hmem ↦ by
  have hle := ha.abs_mul_self_sub_le_norm hmem; norm_num at hle; linarith

/-- Continuity of `indicator (Ioi (1 / 2)) 1` on `quasispectrum ℝ a` when `‖a * a - a‖ < 1 / 4`. -/
theorem continuousOn_indicator_Ioi_half (ha : IsSelfAdjoint a) (h : ‖a * a - a‖ < 1 / 4) :
    ContinuousOn ((Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) (quasispectrum ℝ a) :=
  continuousOn_const.continuousOn_indicator_of_disjoint_frontier <| by
    rw [frontier_Ioi, Set.disjoint_singleton_left]
    exact ha.notMem_quasispectrum_half_of_norm_mul_self_sub_lt h

/-- If `IsSelfAdjoint a` and `‖a * a - a‖ < 1 / 4`, `spectralProjection a` is a star projection. -/
theorem isStarProjection_spectralProjection (ha : IsSelfAdjoint a) (h : ‖a * a - a‖ < 1 / 4) :
    IsStarProjection (spectralProjection a) := by
  rw [spectralProjection_def]
  set f : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)
  have hf_cont := ha.continuousOn_indicator_Ioi_half h
  have hf0 : f 0 = 0 := by simp [f]
  refine ⟨?_, IsSelfAdjoint.cfcₙ⟩
  rw [IsIdempotentElem, ← cfcₙ_mul f f a hf_cont hf0 hf_cont hf0]
  refine cfcₙ_congr fun x _ ↦ ?_
  simp only [f, Set.indicator_apply, Pi.one_apply]; split_ifs <;> ring

/-- Sharp bound `‖spectralProjection a - a‖ ≤ 2 * ‖a * a - a‖` when `‖a * a - a‖ < 1 / 4`. -/
theorem norm_spectralProjection_sub_le (ha : IsSelfAdjoint a) (h : ‖a * a - a‖ < 1 / 4) :
    ‖spectralProjection a - a‖ ≤ 2 * ‖a * a - a‖ := by
  rw [spectralProjection_def]
  set f : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)
  rw [show cfcₙ f a - a = cfcₙ (fun t : ℝ ↦ f t - t) a by
    rw [cfcₙ_sub f (fun t : ℝ ↦ t) a (ha.continuousOn_indicator_Ioi_half h) (by simp [f])
      continuousOn_id rfl, cfcₙ_id' ℝ a]]
  refine norm_cfcₙ_le fun t ht ↦ ?_
  rw [Real.norm_eq_abs]; dsimp only [f]
  have hqt := ha.abs_mul_self_sub_le_norm ht
  have hprod : |t * t - t| = |t| * |1 - t| := by
    rw [show t * t - t = t * (t - 1) by ring, abs_mul, abs_sub_comm]
  by_cases hgt : t ∈ Set.Ioi (1 / 2 : ℝ)
  · rw [Set.indicator_of_mem hgt, Pi.one_apply]
    rw [abs_of_pos (a := t) (by linarith [Set.mem_Ioi.mp hgt])] at hprod
    nlinarith [abs_nonneg (1 - t), Set.mem_Ioi.mp hgt]
  · rw [Set.indicator_of_notMem hgt, zero_sub, abs_neg]
    rw [abs_of_pos (a := 1 - t) (by linarith [not_lt.mp hgt])] at hprod
    nlinarith [abs_nonneg t, not_lt.mp hgt]

end IsSelfAdjoint

namespace TauCeti

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A]

private lemma symmetrize_bounds (e : A) :
    let a : A := (2 : ℝ)⁻¹ • (e + star e)
    IsSelfAdjoint a ∧ ‖a - e‖ = (1 / 2) * ‖e - star e‖ ∧
      ‖a * a - a‖ ≤ ‖e * e - e‖ + (1 / 4) * ‖e - star e‖ ^ 2 := by
  set a : A := (2 : ℝ)⁻¹ • (e + star e)
  have ha_sa : IsSelfAdjoint a := by
    rw [IsSelfAdjoint, star_smul, star_trivial, star_add, star_star, add_comm]
  have h2 : ∀ x : A, (2 : ℝ)⁻¹ • (x + x) = x := fun x ↦ by
    rw [← two_smul ℝ x, inv_smul_smul₀ (by norm_num)]
  have ha_sub : ‖a - e‖ = (1 / 2) * ‖e - star e‖ := by
    have hsub : a - e = (2 : ℝ)⁻¹ • (star e - e) := by
      dsimp [a]; conv_lhs => rhs; rw [← h2 e]
      rw [← smul_sub]; congr 1; abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num), norm_sub_rev, one_div]
  have hid : a * a - a = (2 : ℝ)⁻¹ • ((e * e - e) + star (e * e - e)) -
      (4 : ℝ)⁻¹ • ((e - star e) * (e - star e)) := by
    have hmul : a * a = (4 : ℝ)⁻¹ • ((e + star e) * (e + star e)) := by
      dsimp [a]; rw [smul_mul_smul_comm]; norm_num
    have h4 : ∀ x : A, (2 : ℝ)⁻¹ • x = (4 : ℝ)⁻¹ • (x + x) := fun x ↦ by
      rw [← two_smul ℝ x, smul_smul]; norm_num
    rw [hmul]; dsimp [a]
    rw [h4 (e + star e), h4 ((e * e - e) + star (e * e - e)), ← smul_sub, ← smul_sub]
    congr 1; simp only [star_sub, star_mul, mul_add, add_mul, sub_mul, mul_sub]; abel
  refine ⟨ha_sa, ha_sub, ?_⟩
  rw [hid]
  have h1 : ‖(2 : ℝ)⁻¹ • ((e * e - e) + star (e * e - e))‖ ≤ ‖e * e - e‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    have hsum := norm_add_le (e * e - e) (star (e * e - e)); rw [norm_star] at hsum; linarith
  have h2' : ‖(4 : ℝ)⁻¹ • ((e - star e) * (e - star e))‖ ≤ (1 / 4) * ‖e - star e‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num), one_div, sq]
    gcongr; exact norm_mul_le _ _
  linarith [norm_sub_le ((2 : ℝ)⁻¹ • ((e * e - e) + star (e * e - e)))
    ((4 : ℝ)⁻¹ • ((e - star e) * (e - star e)))]

/-- Every approximate projection with `‖x - star x‖ < 1` and `‖x * x - x‖ < 1` has `‖x‖ < 3`. -/
theorem norm_lt_three_of_approx_projection {x : A} (hsa : ‖x - star x‖ < 1)
    (hidem : ‖x * x - x‖ < 1) : ‖x‖ < 3 := by
  obtain ⟨ha_sa, ha_sub, ha_def⟩ := symmetrize_bounds x
  set a : A := (2 : ℝ)⁻¹ • (x + star x)
  have hsq : ‖x - star x‖ ^ 2 < 1 := by nlinarith [norm_nonneg (x - star x)]
  have ha_norm : ‖a‖ * ‖a‖ - ‖a‖ ≤ ‖a * a - a‖ := by
    simpa [← CStarRing.norm_star_mul_self, ha_sa.star_eq] using norm_sub_norm_le (a * a) a
  have ha_le : ‖a‖ ≤ 2 := by nlinarith
  have htri : ‖x‖ ≤ ‖a‖ + ‖a - x‖ := by simpa [norm_sub_rev] using norm_sub_le a (a - x)
  linarith

/-- **Quantitative norm stability of projections** in a closed subalgebra for `δ ≤ 1 / 5`. -/
theorem exists_isStarProjection_mem_of_approx {S : Type*} [SetLike S A] [NonUnitalSubringClass S A]
    [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {e : A} (hes : e ∈ s)
    {δ : ℝ} (hδ : δ ≤ 1 / 5) (hsa : ‖e - star e‖ < δ) (hidem : ‖e * e - e‖ < δ) :
    ∃ p ∈ s, IsStarProjection p ∧ ‖p - e‖ < 3 * δ := by
  obtain ⟨ha_sa, ha_sub, ha_def⟩ := symmetrize_bounds e
  set a : A := (2 : ℝ)⁻¹ • (e + star e)
  have ha_mem : a ∈ s := by
    simpa only [Complex.coe_smul] using
      SMulMemClass.smul_mem (((2 : ℝ)⁻¹ : ℝ) : ℂ) (add_mem hes (star_mem hes))
  have hsq : ‖e - star e‖ ^ 2 ≤ ‖e - star e‖ := by nlinarith [norm_nonneg (e - star e)]
  have ha_lt : ‖a * a - a‖ < 1 / 4 := by linarith
  refine ⟨spectralProjection a, spectralProjection_mem ha_mem,
    ha_sa.isStarProjection_spectralProjection ha_lt, ?_⟩
  have hp_a := ha_sa.norm_spectralProjection_sub_le ha_lt
  have htri : ‖spectralProjection a - e‖ ≤ ‖spectralProjection a - a‖ + ‖a - e‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (spectralProjection a - a) (a - e)
  linarith

/-- **Quantitative norm stability of projections** for `δ ≤ 1 / 5`. -/
theorem exists_isStarProjection_of_approx {e : A} {δ : ℝ} (hδ : δ ≤ 1 / 5)
    (hsa : ‖e - star e‖ < δ) (hidem : ‖e * e - e‖ < δ) :
    ∃ p : A, IsStarProjection p ∧ ‖p - e‖ < 3 * δ := by
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨p, -, hp, hnorm⟩ :=
    exists_isStarProjection_mem_of_approx (s := (⊤ : NonUnitalStarSubalgebra ℂ A))
      trivial hδ hsa hidem
  exact ⟨p, hp, hnorm⟩

end NonUnital

/-- **Uniform norm stability of projections** (with subalgebra preservation). -/
theorem exists_delta_isStarProjection_mem {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A S : Type*} [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A]
      [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {e : A},
      e ∈ s → ‖e - star e‖ < δ → ‖e * e - e‖ < δ →
      ∃ p ∈ s, IsStarProjection p ∧ ‖p - e‖ < ε := by
  refine ⟨min (1 / 5) (ε / 3), by positivity, fun hes hsa hidem ↦ ?_⟩
  obtain ⟨p, hps, hp, hpe⟩ :=
    exists_isStarProjection_mem_of_approx hes (min_le_left _ _) hsa hidem
  exact ⟨p, hps, hp, hpe.trans_le (by linarith [min_le_right (1 / 5) (ε / 3)])⟩

/-- **Uniform norm stability of projections** in any non-unital C⋆-algebra. -/
theorem exists_delta_isStarProjection {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {e : A},
      ‖e - star e‖ < δ → ‖e * e - e‖ < δ → ∃ p : A, IsStarProjection p ∧ ‖p - e‖ < ε := by
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_delta_isStarProjection_mem hε
  refine ⟨δ, hδ_pos, fun {A} _ {_} hsa hidem ↦ ?_⟩
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨p, -, hp, hpe⟩ := hδ (s := (⊤ : NonUnitalStarSubalgebra ℂ A)) trivial hsa hidem
  exact ⟨p, hp, hpe⟩

private def orthoCornerSubalgebra {A : Type*} [NonUnitalCStarAlgebra A]
    (s : NonUnitalStarSubalgebra ℂ A) (P : A) (hP : IsStarProjection P) :
    NonUnitalStarSubalgebra ℂ A where
  carrier := {a : A | a ∈ s ∧ P * a = 0 ∧ a * P = 0}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, by rw [mul_add, ha.2.1, hb.2.1, add_zero],
    by rw [add_mul, ha.2.2, hb.2.2, add_zero]⟩
  zero_mem' := ⟨zero_mem s, mul_zero P, zero_mul P⟩
  mul_mem' ha hb := ⟨mul_mem ha.1 hb.1, by rw [← mul_assoc, ha.2.1, zero_mul],
    by rw [mul_assoc, hb.2.2, mul_zero]⟩
  smul_mem' c _ ha := ⟨SMulMemClass.smul_mem c ha.1, by rw [mul_smul_comm, ha.2.1, smul_zero],
    by rw [smul_mul_assoc, ha.2.2, smul_zero]⟩
  star_mem' ha := ⟨star_mem ha.1,
    by rw [← hP.isSelfAdjoint.star_eq, ← star_mul, ha.2.2, star_zero],
    by rw [← hP.isSelfAdjoint.star_eq, ← star_mul, ha.2.1, star_zero]⟩

private lemma isClosed_orthoCornerSubalgebra {A : Type*} [NonUnitalCStarAlgebra A]
    {s : NonUnitalStarSubalgebra ℂ A} (hs : IsClosed (s : Set A)) (P : A)
    (hP : IsStarProjection P) :
    IsClosed (orthoCornerSubalgebra s P hP : Set A) := by
  change IsClosed ({a : A | a ∈ s} ∩ ({a : A | P * a = 0} ∩ {a : A | a * P = 0}))
  exact hs.inter
    ((isClosed_eq (continuous_const.mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.mul continuous_const) continuous_const))

private lemma exists_delta_ortho_isStarProjection_fin :
    ∀ (m : ℕ) {ε : ℝ}, 0 < ε →
      ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A]
        {s : NonUnitalStarSubalgebra ℂ A}, IsClosed (s : Set A) →
        ∀ {d : Fin m → A}, (∀ i, d i ∈ s) → (∀ i, ‖d i - star (d i)‖ < δ) →
        (∀ i, ‖d i * d i - d i‖ < δ) → (∀ i j, i ≠ j → ‖d i * d j‖ < δ) →
        ∃ p : Fin m → A, (∀ i, p i ∈ s) ∧ (∀ i, IsStarProjection (p i)) ∧
          Pairwise (IsStarOrtho on p) ∧ ∀ i, ‖p i - d i‖ < ε
  | 0, _, _ => ⟨1, zero_lt_one, fun _ _ _ _ _ _ ↦
      ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩⟩
  | m + 1, ε, hε => by
      obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := exists_delta_isStarProjection_mem (half_pos hε)
      set μ : ℝ := min (1 / 2) (min (ε / 2) (δ₁ / 10))
      have hμ_pos : 0 < μ := by positivity
      set η : ℝ := min ε (μ / (12 * (m + 1 : ℝ)))
      obtain ⟨δ_ih, hδ_ih_pos, h_ih⟩ :=
        exists_delta_ortho_isStarProjection_fin m (show 0 < η by positivity)
      set δ : ℝ := min (1 / 2) (min δ_ih (min (δ₁ / 5) (μ / (12 * (m + 1 : ℝ)))))
      refine ⟨δ, by positivity, fun {A} _ {s} hs {d} hd_mem hd_sa hd_idem hd_ortho ↦ ?_⟩
      have hδ_le_ih : δ ≤ δ_ih := (min_le_right _ _).trans (min_le_left _ _)
      have hδ_le_half : δ ≤ 1 / 2 := min_le_left _ _
      have hδ_le_δ₁ : δ ≤ δ₁ / 5 :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
      have hδ_le_μ : δ ≤ μ / (12 * (m + 1 : ℝ)) :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
      obtain ⟨p₀, hp₀_mem, hp₀_proj, hp₀_ortho, hp₀_dist⟩ :=
        h_ih hs (d := fun j : Fin m ↦ d j.castSucc) (fun j ↦ hd_mem j.castSucc)
          (fun j ↦ (hd_sa j.castSucc).trans_le hδ_le_ih)
          (fun j ↦ (hd_idem j.castSucc).trans_le hδ_le_ih)
          (fun i j hij ↦
            (hd_ortho i.castSucc j.castSucc (Fin.castSucc_inj.not.mpr hij)).trans_le hδ_le_ih)
      set P : A := ∑ j : Fin m, p₀ j
      have hP_mem : P ∈ s := sum_mem fun j _ ↦ hp₀_mem j
      have hP_proj : IsStarProjection P :=
        IsStarProjection.sum (fun j _ ↦ hp₀_proj j) (hp₀_ortho.set_pairwise _)
      set x : A := d (Fin.last m)
      have hx_sa : ‖x - star x‖ < δ := hd_sa (Fin.last m)
      have hx_idem : ‖x * x - x‖ < δ := hd_idem (Fin.last m)
      have hx_norm : ‖x‖ < 3 :=
        norm_lt_three_of_approx_projection (hx_sa.trans_le (by linarith))
          (hx_idem.trans_le (by linarith))
      set y : A := x - P * x - x * P + P * x * P
      have hy_mem_corner : y ∈ orthoCornerSubalgebra s P hP_proj := by
        have hxm := hd_mem (Fin.last m)
        refine ⟨add_mem (sub_mem (sub_mem hxm (mul_mem hP_mem hxm)) (mul_mem hxm hP_mem))
          (mul_mem (mul_mem hP_mem hxm) hP_mem), ?_, ?_⟩
        · dsimp [y]; simp only [mul_add, mul_sub, ← mul_assoc, hP_proj.isIdempotentElem.eq]; abel
        · dsimp [y]; simp only [add_mul, sub_mul, mul_assoc, hP_proj.isIdempotentElem.eq]; abel
      have hPx_norm : ‖P * x‖ ≤ (m : ℝ) * (3 * η + δ) := by
        have hj (j : Fin m) : ‖p₀ j * x‖ ≤ 3 * η + δ := by
          rw [show p₀ j * x = (p₀ j - d j.castSucc) * x + d j.castSucc * x by
            rw [sub_mul, sub_add_cancel]]
          linarith [norm_add_le ((p₀ j - d j.castSucc) * x) (d j.castSucc * x),
            (norm_mul_le (p₀ j - d j.castSucc) x).trans
              (mul_le_mul (hp₀_dist j).le hx_norm.le (norm_nonneg _) (by positivity)),
            (hd_ortho j.castSucc (Fin.last m) (Fin.castSucc_lt_last j).ne).le]
        dsimp [P]; rw [Finset.sum_mul]
        exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ ↦ hj j).trans (by simp; linarith))
      have hxP_norm : ‖x * P‖ ≤ (m : ℝ) * (3 * η + δ) := by
        have hj (j : Fin m) : ‖x * p₀ j‖ ≤ 3 * η + δ := by
          rw [show x * p₀ j = x * (p₀ j - d j.castSucc) + x * d j.castSucc by
            rw [mul_sub, sub_add_cancel]]
          linarith [norm_add_le (x * (p₀ j - d j.castSucc)) (x * d j.castSucc),
            (norm_mul_le x (p₀ j - d j.castSucc)).trans
              (mul_le_mul hx_norm.le (hp₀_dist j).le (norm_nonneg _) (by positivity)),
            (hd_ortho (Fin.last m) j.castSucc (Fin.castSucc_lt_last j).ne').le]
        dsimp [P]; rw [Finset.mul_sum]
        exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ ↦ hj j).trans (by simp; linarith))
      have hy_sub_x : ‖y - x‖ < μ := by
        have hPxP : ‖P * x * P‖ ≤ ‖P * x‖ :=
          (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hP_proj.norm_le P))
        have htri : ‖y - x‖ ≤ 2 * ‖P * x‖ + ‖x * P‖ := by
          rw [show y - x = -(P * x) - x * P + P * x * P by dsimp [y]; abel]
          have hle2 := norm_sub_le (-(P * x)) (x * P); rw [norm_neg] at hle2
          linarith [norm_add_le (-(P * x) - x * P) (P * x * P)]
        have hsum_le : 3 * η + δ ≤ 4 * (μ / (12 * (m + 1 : ℝ))) := by
          linarith [min_le_right ε (μ / (12 * (m + 1 : ℝ)))]
        have hm_bound : 3 * (m : ℝ) * (3 * η + δ) < μ :=
          calc 3 * (m : ℝ) * (3 * η + δ)
              ≤ 3 * (m : ℝ) * (4 * (μ / (12 * (m + 1 : ℝ)))) := by gcongr
            _ = ((m : ℝ) / (m + 1 : ℝ)) * μ := by field_simp; ring
            _ < 1 * μ := by gcongr; rw [div_lt_one (by positivity)]; linarith
            _ = μ := one_mul μ
        linarith
      have hμ_half : μ ≤ 1 / 2 := min_le_left _ _
      have hμ_eps : μ ≤ ε / 2 := (min_le_right _ _).trans (min_le_left _ _)
      have hμ_δ₁ : μ ≤ δ₁ / 10 := (min_le_right _ _).trans (min_le_right _ _)
      have hy_norm : ‖y‖ < 4 := by
        linarith [show ‖y‖ ≤ ‖x‖ + ‖y - x‖ by simpa using norm_add_le x (y - x)]
      have hy_sa : ‖y - star y‖ < δ₁ := by
        rw [show y - star y = (y - x) + (x - star x) - star (y - x) by simp [star_sub]]
        have hle1 := norm_sub_le ((y - x) + (x - star x)) (star (y - x)); rw [norm_star] at hle1
        linarith [norm_add_le (y - x) (x - star x)]
      have hy_idem : ‖y * y - y‖ < δ₁ := by
        rw [show y * y - y = (y - x) * y + x * (y - x) + (x * x - x) - (y - x) by
          simp only [sub_mul, mul_sub]; abel]
        linarith [norm_sub_le ((y - x) * y + x * (y - x) + (x * x - x)) (y - x),
          norm_add_le ((y - x) * y + x * (y - x)) (x * x - x),
          norm_add_le ((y - x) * y) (x * (y - x)),
          (norm_mul_le (y - x) y).trans (mul_le_mul_of_nonneg_left hy_norm.le (norm_nonneg _)),
          (norm_mul_le x (y - x)).trans (mul_le_mul_of_nonneg_right hx_norm.le (norm_nonneg _))]
      have : IsClosed (orthoCornerSubalgebra s P hP_proj : Set A) :=
        isClosed_orthoCornerSubalgebra hs P hP_proj
      obtain ⟨q, hq_corner, hq_proj, hq_dist⟩ :=
        hδ₁ (s := orthoCornerSubalgebra s P hP_proj) hy_mem_corner hy_sa hy_idem
      have hq_sub_x : ‖q - x‖ < ε := by
        linarith [show ‖q - x‖ ≤ ‖q - y‖ + ‖y - x‖ by simpa using norm_add_le (q - y) (y - x)]
      have hortho_p₀_q : ∀ j : Fin m, IsStarOrtho (p₀ j) q := fun j ↦ by
        rw [(hp₀_proj j).isSelfAdjoint.isStarOrtho_iff_mul_eq_zero hq_proj.isSelfAdjoint]
        have hp₀P : p₀ j * P = p₀ j := by
          dsimp [P]; rw [Finset.mul_sum, Finset.sum_eq_single j
            (fun k _ hkj ↦ (hp₀_ortho hkj.symm).mul_eq_zero' (hp₀_proj k).isSelfAdjoint)
            (fun hj ↦ (hj (Finset.mem_univ j)).elim)]
          exact (hp₀_proj j).isIdempotentElem.eq
        rw [← hp₀P, mul_assoc, hq_corner.2.1, mul_zero]
      refine ⟨Fin.snoc p₀ q,
        Fin.lastCases (by simpa using hq_corner.1) (fun j ↦ by simpa using hp₀_mem j),
        Fin.lastCases (by simpa using hq_proj) (fun j ↦ by simpa using hp₀_proj j), ?_,
        Fin.lastCases (by simpa [x] using hq_sub_x)
          (fun j ↦ by simpa using (hp₀_dist j).trans_le (min_le_left _ _))⟩
      intro i k
      refine Fin.lastCases ?_ (fun i' ↦ ?_) i <;> refine Fin.lastCases ?_ (fun k' ↦ ?_) k <;>
        intro hik <;> simp only [onFun, Fin.snoc_last, Fin.snoc_castSucc]
      exacts [(hik rfl).elim, (hortho_p₀_q k').symm, hortho_p₀_q i',
        hp₀_ortho fun h ↦ hik (congrArg Fin.castSucc h)]

/-- **Uniform norm stability of finite families of pairwise-orthogonal projections** (with
subalgebra preservation). -/
theorem exists_delta_ortho_isStarProjection_mem (ι : Type*) [Finite ι] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A S : Type*} [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A]
      [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {d : ι → A},
      (∀ i, d i ∈ s) → (∀ i, ‖d i - star (d i)‖ < δ) → (∀ i, ‖d i * d i - d i‖ < δ) →
      (∀ i j, i ≠ j → ‖d i * d j‖ < δ) →
      ∃ p : ι → A, (∀ i, p i ∈ s) ∧ (∀ i, IsStarProjection (p i)) ∧
        Pairwise (IsStarOrtho on p) ∧ ∀ i, ‖p i - d i‖ < ε := by
  cases nonempty_fintype ι
  let σ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_delta_ortho_isStarProjection_fin (Fintype.card ι) hε
  refine ⟨δ, hδ_pos, fun {A S} _ _ _ _ _ {s} hs {d} hd_mem hd_sa hd_idem hd_ortho ↦ ?_⟩
  obtain ⟨p_fin, hp_mem, hp_proj, hp_ortho, hp_dist⟩ :=
    hδ (s := NonUnitalStarSubalgebra.ofClass s) hs (d := fun k ↦ d (σ.symm k))
      (fun k ↦ hd_mem (σ.symm k)) (fun k ↦ hd_sa (σ.symm k)) (fun k ↦ hd_idem (σ.symm k))
      (fun k l hkl ↦ hd_ortho (σ.symm k) (σ.symm l) (σ.symm.injective.ne hkl))
  exact ⟨fun i ↦ p_fin (σ i), fun i ↦ hp_mem (σ i), fun i ↦ hp_proj (σ i),
    fun _ _ hij ↦ hp_ortho (σ.injective.ne hij), fun i ↦ by simpa using hp_dist (σ i)⟩

/-- **Uniform norm stability of finite families of pairwise-orthogonal projections**. -/
theorem exists_delta_ortho_isStarProjection (ι : Type*) [Finite ι] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {d : ι → A},
      (∀ i, ‖d i - star (d i)‖ < δ) → (∀ i, ‖d i * d i - d i‖ < δ) →
      (∀ i j, i ≠ j → ‖d i * d j‖ < δ) →
      ∃ p : ι → A, (∀ i, IsStarProjection (p i)) ∧
        Pairwise (IsStarOrtho on p) ∧ ∀ i, ‖p i - d i‖ < ε := by
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_delta_ortho_isStarProjection_mem ι hε
  refine ⟨δ, hδ_pos, fun {A} _ {_} hd_sa hd_idem hd_ortho ↦ ?_⟩
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨p, -, hp_proj, hp_ortho, hp_dist⟩ :=
    hδ (s := (⊤ : NonUnitalStarSubalgebra ℂ A)) (fun _ ↦ trivial) hd_sa hd_idem hd_ortho
  exact ⟨p, hp_proj, hp_ortho, hp_dist⟩

end TauCeti
