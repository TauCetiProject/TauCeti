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

/-!
# Norm Stability and Rigidity of Projections in C⋆-Algebras

This file proves norm rigidity of comparable star projections in C⋆-rings and norm stability of
single projections and finite families of pairwise-orthogonal projections in (not necessarily
unital) C⋆-algebras via spectral gap functional calculus.

Given an approximate projection `e` in a non-unital C⋆-algebra `A` satisfying
`‖e - star e‖ < δ` and `‖e * e - e‖ < δ` with `δ ≤ 1 / 5`, its symmetrization
`a = (2 : ℝ)⁻¹ • (e + star e)` is self-adjoint with `‖a * a - a‖ < 1 / 4`, so `1 / 2` lies outside
`quasispectrum ℝ a`. Applying the non-unital continuous functional calculus to the indicator
`(Set.Ioi (1 / 2 : ℝ)).indicator 1` yields a genuine star projection `p` inside every closed
`ℂ`-⋆-subalgebra containing `e`, with explicit bound `‖p - e‖ < 3 * δ`. Consequently, the threshold
`δ = min (1 / 5) (ε / 3)` depends only on `ε`, uniformly across all C⋆-algebras.

For finite families of approximate pairwise-orthogonal projections, induction on the index
cardinality compresses each new generator `x` to `x - P * x - x * P + P * x * P` inside the closed
orthogonal-complement corner `{a ∈ s | P * a = 0 ∧ a * P = 0}` of the sum `P` of the previously
perturbed projections, producing genuine pairwise-orthogonal star projections in `s`.

## Main definitions

* `TauCeti.spectralProjection`: the spectral projection
  `cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator 1) a` cut at `1 / 2`.

## Main results

* `IsStarProjection.eq_zero_of_norm_lt_one`: a star projection of norm `< 1` in a C⋆-ring is `0`.
* `IsStarProjection.eq_of_mul_eq_left_of_norm_sub_lt_one`: if `p * q = p` and `‖p - q‖ < 1`, then
  `p = q`.
* `IsSelfAdjoint.isStarProjection_spectralProjection` and
  `IsSelfAdjoint.norm_spectralProjection_sub_le`: when `IsSelfAdjoint a` and `‖a * a - a‖ < 1 / 4`,
  `spectralProjection a` is a star projection at distance `≤ 2 * ‖a * a - a‖` from `a`.
* `TauCeti.exists_isStarProjection_mem_of_approx` and `TauCeti.exists_delta_isStarProjection`:
  quantitative and uniform `ε`-`δ` norm stability of projections, preserving closed ⋆-subalgebras.
* `TauCeti.exists_delta_ortho_isStarProjection_mem` and
  `TauCeti.exists_delta_ortho_isStarProjection`: uniform norm stability of finite families of
  pairwise-orthogonal projections.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  Encyclopaedia of Mathematical Sciences **122**, Springer (2006), Proposition II.8.3.23.
* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C*-Algebras*,
  London Mathematical Society Student Texts **49**, Cambridge University Press (2000), Lemma 2.2.6.
-/

public section

open Function
open scoped NonUnitalContinuousFunctionalCalculus

/-! ### Continuity of ray indicators away from the cut point -/

/-- If `g : ℝ → ℝ` is continuous on `(c, ∞)` and `c ∉ s`, then `(Set.Ioi c).indicator g` is
continuous on `s`. -/
theorem ContinuousOn.indicator_Ioi_of_notMem {g : ℝ → ℝ} {c : ℝ} {s : Set ℝ}
    (hg : ContinuousOn g (Set.Ioi c)) (hc : c ∉ s) :
    ContinuousOn ((Set.Ioi c).indicator g) s := by
  intro t ht
  refine ((hg.mono interior_subset).continuousAt_indicator ?_).continuousWithinAt
  rw [frontier_Ioi, Set.mem_singleton_iff]
  rintro rfl
  exact hc ht

/-! ### Norm rigidity of star projections in C⋆-rings -/

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

/-- If `p` and `q` are star projections in a C⋆-ring with `p * q = p` and `‖p - q‖ < 1`, then
`p = q`. -/
theorem eq_of_mul_eq_left_of_norm_sub_lt_one {p q : E} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : p * q = p) (h : ‖p - q‖ < 1) : p = q := by
  rw [norm_sub_rev] at h
  exact (sub_eq_zero.mp ((hp.sub_of_mul_eq_left hq hpq).eq_zero_of_norm_lt_one h)).symm

/-- If `p` and `q` are star projections in a C⋆-ring with `q * p = p` and `‖p - q‖ < 1`, then
`p = q`. -/
theorem eq_of_mul_eq_right_of_norm_sub_lt_one {p q : E} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hqp : q * p = p) (h : ‖p - q‖ < 1) : p = q := by
  rw [norm_sub_rev] at h
  exact (sub_eq_zero.mp ((hp.sub_of_mul_eq_right hq hqp).eq_zero_of_norm_lt_one h)).symm

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

/-! ### Spectral gap projection for self-adjoint approximate idempotents -/

namespace TauCeti

/-- The spectral projection `cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator 1) a` associated to an element
`a` of a non-unital C⋆-algebra by cutting its real quasispectrum at `1 / 2`. -/
noncomputable def spectralProjection {A : Type*} [NonUnitalCStarAlgebra A] (a : A) : A :=
  cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) a

/-- Unfold `TauCeti.spectralProjection`. -/
theorem spectralProjection_def {A : Type*} [NonUnitalCStarAlgebra A] (a : A) :
    spectralProjection a = cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) a :=
  (rfl)

/-- `spectralProjection a` belongs to every closed non-unital `ℂ`-⋆-subalgebra containing `a`. -/
theorem spectralProjection_mem {A S : Type*} [NonUnitalCStarAlgebra A] [SetLike S A]
    [NonUnitalSubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A] {s : S}
    [IsClosed (s : Set A)] {a : A} (ha : a ∈ s) :
    spectralProjection a ∈ s := by
  rw [spectralProjection_def]
  exact cfcₙ_mem (𝕜' := ℂ) _ ha

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

/-- When `IsSelfAdjoint a` and `‖a * a - a‖ < 1 / 4`, the cut point `1 / 2` does not belong to
`quasispectrum ℝ a`. -/
theorem notMem_quasispectrum_half_of_norm_mul_self_sub_lt (ha : IsSelfAdjoint a)
    (h : ‖a * a - a‖ < 1 / 4) : (1 / 2 : ℝ) ∉ quasispectrum ℝ a := by
  intro hmem
  have hle := ha.abs_mul_self_sub_le_norm hmem
  rw [show |(1 / 2 : ℝ) * (1 / 2) - 1 / 2| = 1 / 4 by norm_num] at hle
  linarith

/-- Continuity of `(Set.Ioi (1 / 2)).indicator 1` on `quasispectrum ℝ a` when
`‖a * a - a‖ < 1 / 4`. -/
theorem continuousOn_indicator_Ioi_half (ha : IsSelfAdjoint a) (h : ‖a * a - a‖ < 1 / 4) :
    ContinuousOn ((Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) (quasispectrum ℝ a) :=
  continuousOn_const.indicator_Ioi_of_notMem
    (ha.notMem_quasispectrum_half_of_norm_mul_self_sub_lt h)

/-- When `IsSelfAdjoint a` and `‖a * a - a‖ < 1 / 4`, `spectralProjection a` is a star
projection. -/
theorem isStarProjection_spectralProjection (ha : IsSelfAdjoint a) (h : ‖a * a - a‖ < 1 / 4) :
    IsStarProjection (spectralProjection a) := by
  rw [spectralProjection_def]
  set f : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)
  have hf_cont : ContinuousOn f (quasispectrum ℝ a) := ha.continuousOn_indicator_Ioi_half h
  have hf0 : f 0 = 0 := by simp [f]
  refine ⟨?_, IsSelfAdjoint.cfcₙ⟩
  rw [IsIdempotentElem, ← cfcₙ_mul f f a hf_cont hf0 hf_cont hf0]
  refine cfcₙ_congr fun x _ ↦ ?_
  dsimp only [f]
  by_cases hx : x ∈ Set.Ioi (1 / 2 : ℝ)
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem hx, mul_zero]

/-- Sharp linear error bound `‖spectralProjection a - a‖ ≤ 2 * ‖a * a - a‖` whenever `a` is
self-adjoint with `‖a * a - a‖ < 1 / 4`. -/
theorem norm_spectralProjection_sub_le (ha : IsSelfAdjoint a) (h : ‖a * a - a‖ < 1 / 4) :
    ‖spectralProjection a - a‖ ≤ 2 * ‖a * a - a‖ := by
  rw [spectralProjection_def]
  set f : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)
  have hf_cont : ContinuousOn f (quasispectrum ℝ a) := ha.continuousOn_indicator_Ioi_half h
  have hf0 : f 0 = 0 := by simp [f]
  have hsub : cfcₙ f a - a = cfcₙ (fun t : ℝ ↦ f t - t) a := by
    rw [cfcₙ_sub f (fun t : ℝ ↦ t) a hf_cont hf0 continuousOn_id rfl, cfcₙ_id' ℝ a]
  rw [hsub]
  refine norm_cfcₙ_le fun t ht ↦ ?_
  rw [Real.norm_eq_abs]
  have hqt : |t * t - t| ≤ ‖a * a - a‖ := ha.abs_mul_self_sub_le_norm ht
  have hpt : |f t - t| ≤ 2 * |t * t - t| := by
    by_cases hgt : t ∈ Set.Ioi (1 / 2 : ℝ)
    · have hf_val : f t = 1 := Set.indicator_of_mem hgt _
      have ht_pos : 0 < t := by linarith [Set.mem_Ioi.mp hgt]
      have hprod : |t * t - t| = t * |1 - t| := by
        calc |t * t - t|
            = |t * (t - 1)| := by ring_nf
          _ = |t| * |t - 1| := abs_mul t (t - 1)
          _ = t * |1 - t| := by rw [abs_of_pos ht_pos, abs_sub_comm]
      rw [hf_val, hprod]
      nlinarith [abs_nonneg (1 - t), Set.mem_Ioi.mp hgt]
    · have hf_val : f t = 0 := Set.indicator_of_notMem hgt _
      have hle : t ≤ 1 / 2 := not_lt.mp (Set.mem_Ioi.not.mp hgt)
      have h1mt_pos : 0 < 1 - t := by linarith [hle]
      have hprod : |t * t - t| = |t| * (1 - t) := by
        calc |t * t - t|
            = |t * (t - 1)| := by ring_nf
          _ = |t| * |t - 1| := abs_mul t (t - 1)
          _ = |t| * (1 - t) := by rw [abs_sub_comm, abs_of_pos h1mt_pos]
      rw [hf_val, zero_sub, abs_neg, hprod]
      nlinarith [abs_nonneg t, hle]
  linarith

end IsSelfAdjoint

/-! ### Quantitative and uniform norm stability of single approximate projections -/

namespace TauCeti

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Algebraic expansion of `a * a - a` for the symmetrization `a = (2 : ℝ)⁻¹ • (e + star e)` in
terms of the idempotence defect `e * e - e` and the self-adjointness defect `e - star e`. -/
private lemma symmetrize_mul_self_sub (e : A) :
    let a : A := (2 : ℝ)⁻¹ • (e + star e)
    a * a - a =
      (2 : ℝ)⁻¹ • ((e * e - e) + star (e * e - e)) -
        (4 : ℝ)⁻¹ • ((e - star e) * (e - star e)) := by
  dsimp only
  have hmul :
      ((2 : ℝ)⁻¹ • (e + star e)) * ((2 : ℝ)⁻¹ • (e + star e)) =
        (4 : ℝ)⁻¹ • ((e + star e) * (e + star e)) := by
    rw [smul_mul_smul_comm]
    norm_num
  have h2 : ∀ x : A, (2 : ℝ)⁻¹ • x = (4 : ℝ)⁻¹ • (x + x) := fun x ↦ by
    rw [← two_smul ℝ x, smul_smul]
    norm_num
  rw [hmul, h2 (e + star e), h2 ((e * e - e) + star (e * e - e)), ← smul_sub, ← smul_sub]
  congr 1
  simp only [star_sub, star_mul, mul_add, add_mul, sub_mul, mul_sub]
  abel

/-- Every approximate projection in a non-unital C⋆-algebra satisfying `‖x - star x‖ < 1` and
`‖x * x - x‖ < 1` has norm strictly less than `3`. -/
theorem norm_lt_three_of_approx_projection {x : A} (hsa : ‖x - star x‖ < 1)
    (hidem : ‖x * x - x‖ < 1) : ‖x‖ < 3 := by
  set a : A := (2 : ℝ)⁻¹ • (x + star x)
  have ha_sa : IsSelfAdjoint a := by
    rw [IsSelfAdjoint, star_smul, star_trivial, star_add, star_star, add_comm]
  have ha_def : ‖a * a - a‖ < 5 / 4 := by
    dsimp only [a]
    rw [symmetrize_mul_self_sub x]
    have h1 : ‖(2 : ℝ)⁻¹ • ((x * x - x) + star (x * x - x))‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      have hle := norm_add_le (x * x - x) (star (x * x - x))
      rw [norm_star] at hle
      linarith
    have h2 : ‖(4 : ℝ)⁻¹ • ((x - star x) * (x - star x))‖ < 1 / 4 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      have hmul_le := norm_mul_le (x - star x) (x - star x)
      nlinarith [norm_nonneg (x - star x)]
    linarith [norm_sub_le ((2 : ℝ)⁻¹ • ((x * x - x) + star (x * x - x)))
      ((4 : ℝ)⁻¹ • ((x - star x) * (x - star x)))]
  have ha_norm_sq : ‖a * a‖ = ‖a‖ * ‖a‖ := by
    calc ‖a * a‖
        = ‖star a * a‖ := by rw [ha_sa.star_eq]
      _ = ‖a‖ * ‖a‖ := CStarRing.norm_star_mul_self
  have ha_diff : ‖a * a‖ - ‖a‖ ≤ ‖a * a - a‖ := norm_sub_norm_le (a * a) a
  have ha_le : ‖a‖ ≤ 2 := by
    rw [ha_norm_sq] at ha_diff
    by_contra hgt
    have := not_le.mp hgt
    nlinarith
  have hx_sub_a : x - a = (2 : ℝ)⁻¹ • (x - star x) := by
    have htwo : (2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • x = x := by
      rw [← add_smul]
      norm_num
    dsimp only [a]
    calc x - (2 : ℝ)⁻¹ • (x + star x)
        = ((2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • x) - ((2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • star x) := by
            rw [htwo, smul_add]
      _ = (2 : ℝ)⁻¹ • (x - star x) := by rw [smul_sub]; abel
  have hnorm_x_sub_a : ‖x - a‖ < 1 / 2 := by
    rw [hx_sub_a, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    linarith
  have htri : ‖x‖ ≤ ‖a‖ + ‖x - a‖ := by
    simpa only [add_sub_cancel] using norm_add_le a (x - a)
  linarith

/-- **Quantitative norm stability of projections** (with subalgebra preservation): if `e` belongs
to a closed non-unital `ℂ`-⋆-subalgebra `s` of `A` and satisfies `‖e - star e‖ < δ` and
`‖e * e - e‖ < δ` with `δ ≤ 1 / 5`, then `p = spectralProjection ((2 : ℝ)⁻¹ • (e + star e))` lies
in `s`, is a star projection, and satisfies `‖p - e‖ < 3 * δ`. -/
theorem exists_isStarProjection_mem_of_approx {S : Type*} [SetLike S A] [NonUnitalSubringClass S A]
    [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {e : A} (hes : e ∈ s)
    {δ : ℝ} (hδ : δ ≤ 1 / 5) (hsa : ‖e - star e‖ < δ) (hidem : ‖e * e - e‖ < δ) :
    ∃ p ∈ s, IsStarProjection p ∧ ‖p - e‖ < 3 * δ := by
  have hδ_pos : 0 < δ := (norm_nonneg _).trans_lt hsa
  set a : A := (2 : ℝ)⁻¹ • (e + star e)
  have ha_sa : IsSelfAdjoint a := by
    rw [IsSelfAdjoint, star_smul, star_trivial, star_add, star_star, add_comm]
  have ha_mem : a ∈ s := by
    have hsmul : a = (((2 : ℝ)⁻¹ : ℝ) : ℂ) • (e + star e) := (Complex.coe_smul _ _).symm
    rw [hsmul]
    exact SMulMemClass.smul_mem _ (add_mem hes (star_mem hes))
  have ha_sub_e : a - e = (2 : ℝ)⁻¹ • (star e - e) := by
    have htwo : (2 : ℝ)⁻¹ • e + (2 : ℝ)⁻¹ • e = e := by
      rw [← add_smul]
      norm_num
    calc a - e
        = (2 : ℝ)⁻¹ • e + (2 : ℝ)⁻¹ • star e - ((2 : ℝ)⁻¹ • e + (2 : ℝ)⁻¹ • e) := by
            rw [← smul_add, htwo]
      _ = (2 : ℝ)⁻¹ • (star e - e) := by rw [smul_sub]; abel
  have hnorm_a_sub_e : ‖a - e‖ = (1 / 2) * ‖e - star e‖ := by
    rw [ha_sub_e, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num), norm_sub_rev]
    ring
  have hnorm_a_defect : ‖a * a - a‖ ≤ ‖e * e - e‖ + (1 / 4) * ‖e - star e‖ ^ 2 := by
    rw [symmetrize_mul_self_sub e]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖(2 : ℝ)⁻¹ • ((e * e - e) + star (e * e - e))‖ ≤ ‖e * e - e‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      have hsum := norm_add_le (e * e - e) (star (e * e - e))
      rw [norm_star] at hsum
      linarith
    have h2 : ‖(4 : ℝ)⁻¹ • ((e - star e) * (e - star e))‖ ≤ (1 / 4) * ‖e - star e‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num), one_div, sq]
      gcongr
      exact norm_mul_le _ _
    linarith
  have hsq_lt : ‖e - star e‖ ^ 2 < δ ^ 2 :=
    sq_lt_sq' (by linarith [norm_nonneg (e - star e)]) hsa
  have ha_lt : ‖a * a - a‖ < 1 / 4 := by
    nlinarith
  refine ⟨spectralProjection a, spectralProjection_mem ha_mem,
    ha_sa.isStarProjection_spectralProjection ha_lt, ?_⟩
  have hp_sub_a : ‖spectralProjection a - a‖ ≤ 2 * ‖a * a - a‖ :=
    ha_sa.norm_spectralProjection_sub_le ha_lt
  have hp_sub_e : ‖spectralProjection a - e‖ ≤ ‖spectralProjection a - a‖ + ‖a - e‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (spectralProjection a - a) (a - e)
  nlinarith

/-- **Quantitative norm stability of projections**: if `‖e - star e‖ < δ` and `‖e * e - e‖ < δ`
with `δ ≤ 1 / 5`, there exists a star projection `p : A` with `‖p - e‖ < 3 * δ`. -/
theorem exists_isStarProjection_of_approx {e : A} {δ : ℝ} (hδ : δ ≤ 1 / 5)
    (hsa : ‖e - star e‖ < δ) (hidem : ‖e * e - e‖ < δ) :
    ∃ p : A, IsStarProjection p ∧ ‖p - e‖ < 3 * δ := by
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨p, -, hp, hnorm⟩ :=
    exists_isStarProjection_mem_of_approx (s := (⊤ : NonUnitalStarSubalgebra ℂ A))
      trivial hδ hsa hidem
  exact ⟨p, hp, hnorm⟩

end NonUnital

/-- **Uniform norm stability of projections** (with subalgebra preservation): for every `ε > 0`
there exists `δ > 0` (independent of `A`) such that every approximate projection `e` in a closed
non-unital `ℂ`-⋆-subalgebra `s` of any C⋆-algebra `A` with `‖e - star e‖ < δ` and
`‖e * e - e‖ < δ` is within `ε` of a star projection in `s`. -/
theorem exists_delta_isStarProjection_mem {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A S : Type*} [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A]
      [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {e : A},
      e ∈ s → ‖e - star e‖ < δ → ‖e * e - e‖ < δ →
      ∃ p ∈ s, IsStarProjection p ∧ ‖p - e‖ < ε := by
  refine ⟨min (1 / 5) (ε / 3), by positivity, ?_⟩
  intro A S _ _ _ _ _ s _ e hes hsa hidem
  obtain ⟨p, hps, hp, hpe⟩ :=
    exists_isStarProjection_mem_of_approx hes (min_le_left _ _) hsa hidem
  refine ⟨p, hps, hp, hpe.trans_le ?_⟩
  have hle : min (1 / 5) (ε / 3) ≤ ε / 3 := min_le_right _ _
  linarith

/-- **Uniform norm stability of projections**: for every `ε > 0` there exists `δ > 0` (independent
of `A`) such that in any non-unital C⋆-algebra `A`, every `e : A` with `‖e - star e‖ < δ` and
`‖e * e - e‖ < δ` is within `ε` of a star projection `p : A`. -/
theorem exists_delta_isStarProjection {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {e : A},
      ‖e - star e‖ < δ → ‖e * e - e‖ < δ →
      ∃ p : A, IsStarProjection p ∧ ‖p - e‖ < ε := by
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_delta_isStarProjection_mem hε
  refine ⟨δ, hδ_pos, fun {A} _ {e} hsa hidem ↦ ?_⟩
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨p, -, hp, hpe⟩ := hδ (s := (⊤ : NonUnitalStarSubalgebra ℂ A)) trivial hsa hidem
  exact ⟨p, hp, hpe⟩

/-! ### Norm stability of finite families of pairwise-orthogonal projections -/

/-- The orthogonal-complement corner `{a ∈ s | P * a = 0 ∧ a * P = 0}` inside a non-unital
`ℂ`-⋆-subalgebra `s` determined by a star projection `P`. -/
private def orthoCornerSubalgebra {A : Type*} [NonUnitalCStarAlgebra A]
    (s : NonUnitalStarSubalgebra ℂ A) (P : A) (hP : IsStarProjection P) :
    NonUnitalStarSubalgebra ℂ A where
  carrier := {a : A | a ∈ s ∧ P * a = 0 ∧ a * P = 0}
  add_mem' {a b} ha hb :=
    ⟨add_mem ha.1 hb.1, by rw [mul_add, ha.2.1, hb.2.1, add_zero],
      by rw [add_mul, ha.2.2, hb.2.2, add_zero]⟩
  zero_mem' := ⟨zero_mem s, mul_zero P, zero_mul P⟩
  mul_mem' {a b} ha hb :=
    ⟨mul_mem ha.1 hb.1, by rw [← mul_assoc, ha.2.1, zero_mul],
      by rw [mul_assoc, hb.2.2, mul_zero]⟩
  smul_mem' c {a} ha :=
    ⟨SMulMemClass.smul_mem c ha.1, by rw [mul_smul_comm, ha.2.1, smul_zero],
      by rw [smul_mul_assoc, ha.2.2, smul_zero]⟩
  star_mem' {a} ha := by
    refine ⟨star_mem ha.1, ?_, ?_⟩
    · calc P * star a
          = star P * star a := by rw [hP.isSelfAdjoint.star_eq]
        _ = star (a * P) := (star_mul a P).symm
        _ = 0 := by rw [ha.2.2, star_zero]
    · calc star a * P
          = star a * star P := by rw [hP.isSelfAdjoint.star_eq]
        _ = star (P * a) := (star_mul P a).symm
        _ = 0 := by rw [ha.2.1, star_zero]

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
        ∀ {d : Fin m → A}, (∀ i, d i ∈ s) →
        (∀ i, ‖d i - star (d i)‖ < δ) →
        (∀ i, ‖d i * d i - d i‖ < δ) →
        (∀ i j, i ≠ j → ‖d i * d j‖ < δ) →
        ∃ p : Fin m → A, (∀ i, p i ∈ s) ∧ (∀ i, IsStarProjection (p i)) ∧
          Pairwise (IsStarOrtho on p) ∧ ∀ i, ‖p i - d i‖ < ε
  | 0, _, _ =>
      ⟨1, zero_lt_one, fun _ _ _ _ _ _ ↦
        ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩⟩
  | m + 1, ε, hε => by
      obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := exists_delta_isStarProjection_mem (half_pos hε)
      set μ : ℝ := min (1 / 2) (min (ε / 2) (δ₁ / 10))
      have hμ_pos : 0 < μ := by positivity
      set η : ℝ := min ε (μ / (12 * (m + 1 : ℝ)))
      have hη_pos : 0 < η := by positivity
      obtain ⟨δ_ih, hδ_ih_pos, h_ih⟩ := exists_delta_ortho_isStarProjection_fin m hη_pos
      set δ : ℝ := min (1 / 2) (min δ_ih (min (δ₁ / 5) (μ / (12 * (m + 1 : ℝ)))))
      have hδ_pos : 0 < δ := by positivity
      refine ⟨δ, hδ_pos, ?_⟩
      intro A _ s hs d hd_mem hd_sa hd_idem hd_ortho
      have hδ_le_ih : δ ≤ δ_ih := (min_le_right _ _).trans (min_le_left _ _)
      have hδ_le_half : δ ≤ 1 / 2 := min_le_left _ _
      have hδ_le_δ₁ : δ ≤ δ₁ / 5 :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
      have hδ_le_μ : δ ≤ μ / (12 * (m + 1 : ℝ)) :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
      obtain ⟨p₀, hp₀_mem, hp₀_proj, hp₀_ortho, hp₀_dist⟩ :=
        h_ih hs (d := fun j : Fin m ↦ d j.castSucc)
          (fun j ↦ hd_mem j.castSucc)
          (fun j ↦ (hd_sa j.castSucc).trans_le hδ_le_ih)
          (fun j ↦ (hd_idem j.castSucc).trans_le hδ_le_ih)
          (fun i j hij ↦
            (hd_ortho i.castSucc j.castSucc (Fin.castSucc_inj.not.mpr hij)).trans_le hδ_le_ih)
      set P : A := ∑ j : Fin m, p₀ j
      have hP_mem : P ∈ s := sum_mem fun j _ ↦ hp₀_mem j
      have hP_proj : IsStarProjection P :=
        IsStarProjection.sum (fun j _ ↦ hp₀_proj j) (hp₀_ortho.set_pairwise _)
      set x : A := d (Fin.last m)
      have hx_mem : x ∈ s := hd_mem (Fin.last m)
      have hx_sa : ‖x - star x‖ < δ := hd_sa (Fin.last m)
      have hx_idem : ‖x * x - x‖ < δ := hd_idem (Fin.last m)
      have hx_norm : ‖x‖ < 3 :=
        norm_lt_three_of_approx_projection (hx_sa.trans_le (by linarith))
          (hx_idem.trans_le (by linarith))
      set y : A := x - P * x - x * P + P * x * P
      have hy_mem_corner : y ∈ orthoCornerSubalgebra s P hP_proj := by
        refine ⟨add_mem (sub_mem (sub_mem hx_mem (mul_mem hP_mem hx_mem))
          (mul_mem hx_mem hP_mem)) (mul_mem (mul_mem hP_mem hx_mem) hP_mem), ?_, ?_⟩
        · dsimp [y]
          simp only [mul_add, mul_sub, ← mul_assoc, hP_proj.isIdempotentElem.eq]
          abel
        · dsimp [y]
          simp only [add_mul, sub_mul, mul_assoc, hP_proj.isIdempotentElem.eq]
          abel
      have hPx_norm : ‖P * x‖ ≤ (m : ℝ) * (3 * η + δ) := by
        dsimp [P]
        rw [Finset.sum_mul]
        calc ‖∑ j : Fin m, p₀ j * x‖
            ≤ ∑ j : Fin m, ‖p₀ j * x‖ := norm_sum_le _ _
          _ ≤ ∑ _j : Fin m, (3 * η + δ) := by
              refine Finset.sum_le_sum fun j _ ↦ ?_
              have hsplit : p₀ j * x = (p₀ j - d j.castSucc) * x + d j.castSucc * x := by
                rw [sub_mul, sub_add_cancel]
              rw [hsplit]
              have h1 : ‖(p₀ j - d j.castSucc) * x‖ ≤ 3 * η := by
                calc ‖(p₀ j - d j.castSucc) * x‖
                    ≤ ‖p₀ j - d j.castSucc‖ * ‖x‖ := norm_mul_le _ _
                  _ ≤ η * 3 :=
                      mul_le_mul (hp₀_dist j).le hx_norm.le (norm_nonneg _) (by positivity)
                  _ = 3 * η := by ring
              have h2 : ‖d j.castSucc * x‖ ≤ δ :=
                (hd_ortho j.castSucc (Fin.last m) (Fin.castSucc_lt_last j).ne).le
              linarith [norm_add_le ((p₀ j - d j.castSucc) * x) (d j.castSucc * x)]
          _ = (m : ℝ) * (3 * η + δ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hxP_norm : ‖x * P‖ ≤ (m : ℝ) * (3 * η + δ) := by
        dsimp [P]
        rw [Finset.mul_sum]
        calc ‖∑ j : Fin m, x * p₀ j‖
            ≤ ∑ j : Fin m, ‖x * p₀ j‖ := norm_sum_le _ _
          _ ≤ ∑ _j : Fin m, (3 * η + δ) := by
              refine Finset.sum_le_sum fun j _ ↦ ?_
              have hsplit : x * p₀ j = x * (p₀ j - d j.castSucc) + x * d j.castSucc := by
                rw [mul_sub, sub_add_cancel]
              rw [hsplit]
              have h1 : ‖x * (p₀ j - d j.castSucc)‖ ≤ 3 * η := by
                calc ‖x * (p₀ j - d j.castSucc)‖
                    ≤ ‖x‖ * ‖p₀ j - d j.castSucc‖ := norm_mul_le _ _
                  _ ≤ 3 * η :=
                      mul_le_mul hx_norm.le (hp₀_dist j).le (norm_nonneg _) (by positivity)
              have h2 : ‖x * d j.castSucc‖ ≤ δ :=
                (hd_ortho (Fin.last m) j.castSucc (Fin.castSucc_lt_last j).ne').le
              linarith [norm_add_le (x * (p₀ j - d j.castSucc)) (x * d j.castSucc)]
          _ = (m : ℝ) * (3 * η + δ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hy_sub_x : ‖y - x‖ < μ := by
        have hdiff : y - x = -(P * x) - x * P + P * x * P := by
          dsimp [y]
          abel
        have hPxP : ‖P * x * P‖ ≤ ‖P * x‖ := by
          calc ‖P * x * P‖
              ≤ ‖P * x‖ * ‖P‖ := norm_mul_le _ _
            _ ≤ ‖P * x‖ * 1 := mul_le_mul_of_nonneg_left (hP_proj.norm_le P) (norm_nonneg _)
            _ = ‖P * x‖ := mul_one _
        have htri : ‖y - x‖ ≤ 2 * ‖P * x‖ + ‖x * P‖ := by
          rw [hdiff]
          have hle1 := norm_add_le (-(P * x) - x * P) (P * x * P)
          have hle2 := norm_sub_le (-(P * x)) (x * P)
          rw [norm_neg] at hle2
          linarith
        have hη_le_μ : η ≤ μ / (12 * (m + 1 : ℝ)) := min_le_right _ _
        have hm_bound : 3 * (m : ℝ) * (3 * η + δ) < μ := by
          have hsum_le : 3 * η + δ ≤ 4 * (μ / (12 * (m + 1 : ℝ))) := by linarith
          have hm_pos : (0 : ℝ) < m + 1 := by positivity
          calc 3 * (m : ℝ) * (3 * η + δ)
              ≤ 3 * (m : ℝ) * (4 * (μ / (12 * (m + 1 : ℝ)))) := by gcongr
            _ = ((m : ℝ) / (m + 1 : ℝ)) * μ := by field_simp; ring
            _ < 1 * μ := by
                gcongr
                rw [div_lt_one hm_pos]
                linarith
            _ = μ := one_mul μ
        linarith
      have hμ_half : μ ≤ 1 / 2 := min_le_left _ _
      have hμ_eps : μ ≤ ε / 2 := (min_le_right _ _).trans (min_le_left _ _)
      have hμ_δ₁ : μ ≤ δ₁ / 10 := (min_le_right _ _).trans (min_le_right _ _)
      have hy_norm : ‖y‖ < 4 := by
        have htri : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
          simpa only [add_sub_cancel] using norm_add_le x (y - x)
        linarith
      have hy_sa : ‖y - star y‖ < δ₁ := by
        have hsplit : y - star y = (y - x) + (x - star x) - star (y - x) := by
          simp only [star_sub]
          abel
        rw [hsplit]
        have hle1 := norm_sub_le ((y - x) + (x - star x)) (star (y - x))
        have hle2 := norm_add_le (y - x) (x - star x)
        rw [norm_star] at hle1
        linarith
      have hy_idem : ‖y * y - y‖ < δ₁ := by
        have hsplit : y * y - y = (y - x) * y + x * (y - x) + (x * x - x) - (y - x) := by
          simp only [sub_mul, mul_sub]
          abel
        rw [hsplit]
        have h1 : ‖(y - x) * y‖ ≤ 4 * ‖y - x‖ := by
          calc ‖(y - x) * y‖
              ≤ ‖y - x‖ * ‖y‖ := norm_mul_le _ _
            _ ≤ ‖y - x‖ * 4 := mul_le_mul_of_nonneg_left hy_norm.le (norm_nonneg _)
            _ = 4 * ‖y - x‖ := by ring
        have h2 : ‖x * (y - x)‖ ≤ 3 * ‖y - x‖ := by
          calc ‖x * (y - x)‖
              ≤ ‖x‖ * ‖y - x‖ := norm_mul_le _ _
            _ ≤ 3 * ‖y - x‖ := mul_le_mul_of_nonneg_right hx_norm.le (norm_nonneg _)
        have hle1 := norm_sub_le ((y - x) * y + x * (y - x) + (x * x - x)) (y - x)
        have hle2 := norm_add_le ((y - x) * y + x * (y - x)) (x * x - x)
        have hle3 := norm_add_le ((y - x) * y) (x * (y - x))
        linarith
      have : IsClosed (orthoCornerSubalgebra s P hP_proj : Set A) :=
        isClosed_orthoCornerSubalgebra hs P hP_proj
      obtain ⟨q, hq_corner, hq_proj, hq_dist⟩ :=
        hδ₁ (s := orthoCornerSubalgebra s P hP_proj) hy_mem_corner hy_sa hy_idem
      have hq_mem : q ∈ s := hq_corner.1
      have hPq : P * q = 0 := hq_corner.2.1
      have hq_sub_x : ‖q - x‖ < ε := by
        have htri : ‖q - x‖ ≤ ‖q - y‖ + ‖y - x‖ := by
          simpa only [sub_add_sub_cancel] using norm_add_le (q - y) (y - x)
        linarith
      have hp₀_mul_P : ∀ j : Fin m, p₀ j * P = p₀ j := fun j ↦ by
        dsimp [P]
        rw [Finset.mul_sum, Finset.sum_eq_single j]
        · exact (hp₀_proj j).isIdempotentElem.eq
        · intro k _ hkj
          exact (hp₀_ortho hkj.symm).mul_eq_zero' (hp₀_proj k).isSelfAdjoint
        · intro hj
          exact (hj (Finset.mem_univ j)).elim
      have hortho_p₀_q : ∀ j : Fin m, IsStarOrtho (p₀ j) q := fun j ↦ by
        rw [(hp₀_proj j).isSelfAdjoint.isStarOrtho_iff_mul_eq_zero hq_proj.isSelfAdjoint]
        calc p₀ j * q
            = (p₀ j * P) * q := by rw [hp₀_mul_P j]
          _ = p₀ j * (P * q) := mul_assoc _ _ _
          _ = 0 := by rw [hPq, mul_zero]
      refine ⟨Fin.snoc p₀ q, ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa using hq_mem
        · simpa using hp₀_mem j
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa using hq_proj
        · simpa using hp₀_proj j
      · intro i k
        refine Fin.lastCases ?_ (fun i' ↦ ?_) i <;> refine Fin.lastCases ?_ (fun k' ↦ ?_) k <;>
          intro hik
        · exact (hik rfl).elim
        · dsimp [Function.onFun]
          rw [Fin.snoc_last, Fin.snoc_castSucc]
          exact (hortho_p₀_q k').symm
        · dsimp [Function.onFun]
          rw [Fin.snoc_castSucc, Fin.snoc_last]
          exact hortho_p₀_q i'
        · dsimp [Function.onFun]
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hp₀_ortho fun h ↦ hik (congrArg Fin.castSucc h)
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa [x] using hq_sub_x
        · simpa using (hp₀_dist j).trans_le (min_le_left _ _)

/-- **Uniform norm stability of finite families of pairwise-orthogonal projections** (with
subalgebra preservation): for every finite index type `ι` and `ε > 0`, there exists `δ > 0`
(depending only on `ι` and `ε`, independent of `A`) such that in any C⋆-algebra `A` and closed
non-unital `ℂ`-⋆-subalgebra `s`, approximate pairwise-orthogonal projections `d : ι → A` in `s`
within `< δ` can be perturbed within `< ε` to genuine pairwise-orthogonal star projections
`p : ι → A` in `s`. -/
theorem exists_delta_ortho_isStarProjection_mem (ι : Type*) [Finite ι] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A S : Type*} [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A]
      [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {d : ι → A},
      (∀ i, d i ∈ s) →
      (∀ i, ‖d i - star (d i)‖ < δ) →
      (∀ i, ‖d i * d i - d i‖ < δ) →
      (∀ i j, i ≠ j → ‖d i * d j‖ < δ) →
      ∃ p : ι → A, (∀ i, p i ∈ s) ∧ (∀ i, IsStarProjection (p i)) ∧
        Pairwise (IsStarOrtho on p) ∧ ∀ i, ‖p i - d i‖ < ε := by
  cases nonempty_fintype ι
  let σ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_delta_ortho_isStarProjection_fin (Fintype.card ι) hε
  refine ⟨δ, hδ_pos, ?_⟩
  intro A S _ _ _ _ _ s hs d hd_mem hd_sa hd_idem hd_ortho
  let s₀ : NonUnitalStarSubalgebra ℂ A := NonUnitalStarSubalgebra.ofClass s
  have hs₀ : IsClosed (s₀ : Set A) := hs
  obtain ⟨p_fin, hp_mem, hp_proj, hp_ortho, hp_dist⟩ :=
    hδ hs₀ (d := fun k ↦ d (σ.symm k))
      (fun k ↦ hd_mem (σ.symm k))
      (fun k ↦ hd_sa (σ.symm k))
      (fun k ↦ hd_idem (σ.symm k))
      (fun k l hkl ↦ hd_ortho (σ.symm k) (σ.symm l) (σ.symm.injective.ne hkl))
  refine ⟨fun i ↦ p_fin (σ i), fun i ↦ hp_mem (σ i), fun i ↦ hp_proj (σ i), ?_, fun i ↦ ?_⟩
  · intro i j hij
    exact hp_ortho (σ.injective.ne hij)
  · simpa [σ.symm_apply_apply] using hp_dist (σ i)

/-- **Uniform norm stability of finite families of pairwise-orthogonal projections** in an ambient
non-unital C⋆-algebra. -/
theorem exists_delta_ortho_isStarProjection (ι : Type*) [Finite ι] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {d : ι → A},
      (∀ i, ‖d i - star (d i)‖ < δ) →
      (∀ i, ‖d i * d i - d i‖ < δ) →
      (∀ i j, i ≠ j → ‖d i * d j‖ < δ) →
      ∃ p : ι → A, (∀ i, IsStarProjection (p i)) ∧
        Pairwise (IsStarOrtho on p) ∧ ∀ i, ‖p i - d i‖ < ε := by
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_delta_ortho_isStarProjection_mem ι hε
  refine ⟨δ, hδ_pos, fun {A} _ {d} hd_sa hd_idem hd_ortho ↦ ?_⟩
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨p, -, hp_proj, hp_ortho, hp_dist⟩ :=
    hδ (s := (⊤ : NonUnitalStarSubalgebra ℂ A)) (fun _ ↦ trivial) hd_sa hd_idem hd_ortho
  exact ⟨p, hp_proj, hp_ortho, hp_dist⟩

end TauCeti
