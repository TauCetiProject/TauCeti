/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RoundProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TauCeti.Algebra.Algebra.Unitization
import TauCeti.Analysis.CStarAlgebra.Projection.Perturbation
import TauCeti.Topology.Algebra.Indicator

/-!
# Projections from approximate data

Two facts let one replace approximate projections and approximate equivalences in a C⋆-algebra by
exact ones.

* **Rounding.** A self-adjoint element `x` of a C⋆-algebra, possibly without unit, with
  `‖x - x * x‖ ≤ δ < 1/4` is within `2δ` of a star projection
  (`TauCeti.exists_isStarProjection_norm_sub_le`): the spectral projection `χ_{[1/2, ∞)}(x)`,
  computed in the unitization and lying in the algebra since the indicator vanishes at `0`.
* **Approximate equivalence.** Let `p` and `q` be orthogonal star projections and `w = q w p`
  with `‖w⋆w - p‖ + ‖ww⋆ - q‖ < 1`. Then `p` and `q` are Murray–von Neumann equivalent
  (`IsStarProjection.exists_star_mul_self_eq_of_norm_sub_add_norm_sub_lt_one`). For
  `c = cos t`, `s = sin t`, the self-adjoint elements
  `X t = c² p + s² q + c s (w + w⋆)` satisfy `X t - (X t)² = -c² s² ((w⋆w - p) + (ww⋆ - q))`,
  so `‖X t - (X t)²‖ < 1/4` uniformly in `t`. Their roundings form a norm-continuous path of
  projections from `p` (at `t = 0`) to `q` (at `t = π/2`), and the values of such a path are
  equivalent (`Continuous.exists_star_mul_self_eq`).

For matrices over a C⋆-algebra the norm of `CStarMatrix m n A` is at most the sum of the norms of
the entries (`CStarMatrix.norm_le_sum_norm_entry`), so entrywise estimates give norm estimates
with a constant depending only on the sizes.

These are the perturbation steps of the continuity of `K₀` along C⋆-inductive limits.

## Main statements

* `TauCeti.exists_isStarProjection_norm_sub_le`: rounding an almost-projection.
* `IsStarProjection.exists_star_mul_self_eq_of_norm_sub_add_norm_sub_lt_one`: orthogonal
  projections joined by an approximate partial isometry are Murray–von Neumann equivalent.
* `CStarMatrix.norm_le_sum_norm_entry`: `‖M‖ ≤ Σ i, Σ j, ‖M i j‖`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  5.2.4.
-/

public section

open scoped CStarAlgebra

namespace TauCeti

section Rounding

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- **Rounding an almost-projection, without unit.** A self-adjoint element `x` of a C⋆-algebra,
possibly without unit, with `‖x - x * x‖ ≤ δ < 1/4` is within `2δ` of a star projection. -/
theorem exists_isStarProjection_norm_sub_le {x : A} (hx : IsSelfAdjoint x) {δ : ℝ}
    (hδ : ‖x - x * x‖ ≤ δ) (hδ4 : δ < 1 / 4) :
    ∃ p : A, IsStarProjection p ∧ ‖x - p‖ ≤ 2 * δ := by
  set g : ℝ → ℝ := (Set.Ici (1 / 2 : ℝ)).indicator 1 with hg
  have hg0 : g 0 = 0 := Set.indicator_of_notMem (by norm_num) _
  have hinr : ((cfcₙ g x : A) : Unitization ℂ A) = roundProjection (x : Unitization ℂ A) := by
    rw [roundProjection_def, ← hg, Unitization.real_cfcₙ_eq_cfc_inr x g hg0]
  refine ⟨cfcₙ g x, ?_, ?_⟩
  · rw [← Unitization.isStarProjection_inr_iff (R := ℂ), hinr]
    exact isStarProjection_roundProjection _
  · have hδ' : ‖(x : Unitization ℂ A) - (x : Unitization ℂ A) ^ 2‖ ≤ δ := by
      rwa [sq, ← Unitization.inr_mul, ← Unitization.inr_sub, Unitization.norm_inr]
    have := norm_sub_roundProjection_le (hx.inr ℂ) hδ' hδ4
    rwa [← hinr, ← Unitization.inr_sub, Unitization.norm_inr] at this

end Rounding

end TauCeti

open TauCeti Real

namespace IsStarProjection

section Unital

variable {A : Type*} [CStarAlgebra A] {p q w : A}

/-- The path `t ↦ cos² t • p + sin² t • q + (cos t sin t) • (w + w⋆)` joining `p` to `q`. -/
private noncomputable def rotationPath (p q w : A) (t : ℝ) : A :=
  (Real.cos t ^ 2) • p + (Real.sin t ^ 2) • q + (Real.cos t * Real.sin t) • (w + star w)

private theorem isSelfAdjoint_rotationPath (hp : IsStarProjection p) (hq : IsStarProjection q)
    (t : ℝ) : IsSelfAdjoint (rotationPath p q w t) := by
  unfold rotationPath
  refine ((IsSelfAdjoint.all _).smul hp.isSelfAdjoint |>.add
    ((IsSelfAdjoint.all _).smul hq.isSelfAdjoint)).add ((IsSelfAdjoint.all _).smul ?_)
  simp

private theorem continuous_rotationPath : Continuous (rotationPath p q w) := by
  unfold rotationPath
  fun_prop

/-- The defect of the rotation path from being a projection. -/
private theorem rotationPath_sub_sq (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : p * q = 0) (hw : q * w * p = w) (t : ℝ) :
    rotationPath p q w t - rotationPath p q w t ^ 2 =
      -(Real.cos t ^ 2 * Real.sin t ^ 2) • ((star w * w - p) + (w * star w - q)) := by
  have hpp : p * p = p := hp.isIdempotentElem.eq
  have hqq : q * q = q := hq.isIdempotentElem.eq
  have hqp : q * p = 0 := by
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congrArg star hpq
  have hwp : w * p = w := by rw [← hw, mul_assoc, hpp]
  have hqw : q * w = w := by rw [← hw, ← mul_assoc, ← mul_assoc, hqq]
  have hpw : p * w = 0 := by rw [← hw, ← mul_assoc, ← mul_assoc, hpq, zero_mul, zero_mul]
  have hwq : w * q = 0 := by rw [← hw, mul_assoc, hpq, mul_zero]
  have hww : w * w = 0 := by
    calc w * w = w * (q * w) := by rw [hqw]
      _ = 0 := by rw [← mul_assoc, hwq, zero_mul]
  have hsp : star w * p = 0 := by
    simpa [hp.isSelfAdjoint.star_eq] using congrArg star hpw
  have hps : p * star w = star w := by
    simpa [hp.isSelfAdjoint.star_eq] using congrArg star hwp
  have hqs : q * star w = 0 := by
    simpa [hq.isSelfAdjoint.star_eq] using congrArg star hwq
  have hsq : star w * q = star w := by
    simpa [hq.isSelfAdjoint.star_eq] using congrArg star hqw
  have hss : star w * star w = 0 := by simpa using congrArg star hww
  have hcs : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
  unfold rotationPath
  set c := Real.cos t
  set s := Real.sin t
  simp only [sq, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    hpp, hqq, hpq, hqp, hwp, hqw, hpw, hwq, hww, hsp, hps, hqs, hsq, hss, smul_zero]
  linear_combination (norm := module) hcs • (-(c ^ 2) • p - s ^ 2 • q - (c * s) • (w + star w))

/-- The defect of the rotation path is at most a quarter of `‖w⋆w - p‖ + ‖ww⋆ - q‖`. -/
private theorem norm_rotationPath_sub_sq_le (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : p * q = 0) (hw : q * w * p = w) (t : ℝ) :
    ‖rotationPath p q w t - rotationPath p q w t ^ 2‖ ≤
      (‖star w * w - p‖ + ‖w * star w - q‖) / 4 := by
  rw [rotationPath_sub_sq hp hq hpq hw, norm_smul, Real.norm_eq_abs]
  have hcs : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
  have h4 : |-(Real.cos t ^ 2 * Real.sin t ^ 2)| ≤ 1 / 4 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (Real.cos t ^ 2 - Real.sin t ^ 2)]
  calc |-(Real.cos t ^ 2 * Real.sin t ^ 2)| * ‖star w * w - p + (w * star w - q)‖
      ≤ 1 / 4 * (‖star w * w - p‖ + ‖w * star w - q‖) :=
        mul_le_mul h4 (norm_add_le _ _) (norm_nonneg _) (by norm_num)
    _ = _ := by ring

/-- If `‖w⋆w - p‖ + ‖ww⋆ - q‖ < 1`, the spectra of the elements of the rotation path avoid a
common neighbourhood of `1/2`, so their roundings form a continuous path of projections. -/
private theorem continuous_roundProjection_rotationPath (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : p * q = 0) (hw : q * w * p = w)
    (h : ‖star w * w - p‖ + ‖w * star w - q‖ < 1) :
    Continuous fun t ↦ roundProjection (rotationPath p q w t) := by
  set η := ‖star w * w - p‖ + ‖w * star w - q‖
  set r := (1 - η) / 4 with hr
  set S : Set ℝ := Set.Iio (1 / 2 - r) ∪ Set.Ioi (1 / 2 + r) with hS
  have hspec (t : ℝ) : spectrum ℝ (rotationPath p q w t) ⊆ S := by
    intro μ hμ
    rcases lt_and_abs_le_or_le_and_abs_one_sub_le_of_mem_spectrum
      (norm_rotationPath_sub_sq_le hp hq hpq hw t) hμ with ⟨-, h2⟩ | ⟨-, h2⟩
    · left
      rw [Set.mem_Iio]
      linarith [le_abs_self μ]
    · right
      rw [Set.mem_Ioi]
      linarith [le_abs_self (1 - μ)]
  have hcont : ContinuousOn ((Set.Ici (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) S := by
    refine continuousOn_const.continuousOn_indicator_of_disjoint_frontier ?_
    rw [frontier_Ici, Set.disjoint_singleton_left, hS]
    rintro (h | h)
    · rw [Set.mem_Iio] at h
      linarith
    · rw [Set.mem_Ioi] at h
      linarith
  simp_rw [roundProjection_def]
  exact continuous_rotationPath.cfc_of_mem_nhdsSet _
    ((isOpen_Iio.union isOpen_Ioi).mem_nhdsSet.2 (Set.iUnion_subset hspec))
    (fun t ↦ isSelfAdjoint_rotationPath hp hq t) hcont

/-- The rounding of a star projection is itself. -/
private theorem roundProjection_eq_self {e : A} (he : IsStarProjection e) :
    roundProjection e = e := by
  have := norm_sub_roundProjection_le he.isSelfAdjoint (δ := 0)
    (by rw [sq, he.isIdempotentElem.eq, sub_self, norm_zero]) (by norm_num)
  rw [mul_zero, norm_le_zero_iff, sub_eq_zero] at this
  exact this.symm

/-- **Approximately equivalent orthogonal projections are equivalent.** Let `p` and `q` be
orthogonal star projections of a unital C⋆-algebra and `w = q w p` with
`‖w⋆w - p‖ + ‖ww⋆ - q‖ < 1`. Then `star v * v = p` and `v * star v = q` for some `v`. -/
private theorem exists_star_mul_self_eq_of_norm_sub_add_norm_sub_lt_one_of_unital
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) (hw : q * w * p = w)
    (h : ‖star w * w - p‖ + ‖w * star w - q‖ < 1) : ∃ v : A, star v * v = p ∧ v * star v = q := by
  obtain ⟨v, hv₁, hv₂⟩ := Continuous.exists_star_mul_self_eq
    (continuous_roundProjection_rotationPath hp hq hpq hw h)
    (fun t ↦ isStarProjection_roundProjection _) 0 (π / 2)
  have h0 : rotationPath p q w 0 = p := by simp [rotationPath]
  have h1 : rotationPath p q w (π / 2) = q := by simp [rotationPath]
  refine ⟨v, ?_, ?_⟩
  · rw [hv₁, h0, roundProjection_eq_self hp]
  · rw [hv₂, h1, roundProjection_eq_self hq]

end Unital

variable {A : Type*} [NonUnitalCStarAlgebra A] {p q w : A}

/-- **Approximately equivalent orthogonal projections are equivalent.** Let `p` and `q` be
orthogonal star projections of a C⋆-algebra, possibly without unit, and `w = q w p` with
`‖w⋆w - p‖ + ‖ww⋆ - q‖ < 1`. Then `star v * v = p` and `v * star v = q` for some `v`. -/
theorem exists_star_mul_self_eq_of_norm_sub_add_norm_sub_lt_one (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : p * q = 0) (hw : q * w * p = w)
    (h : ‖star w * w - p‖ + ‖w * star w - q‖ < 1) : ∃ v : A, star v * v = p ∧ v * star v = q := by
  have hp' : IsStarProjection (p : Unitization ℂ A) := hp.inr
  have hq' : IsStarProjection (q : Unitization ℂ A) := hq.inr
  obtain ⟨u, hu₁, hu₂⟩ := exists_star_mul_self_eq_of_norm_sub_add_norm_sub_lt_one_of_unital hp' hq'
    (w := (w : Unitization ℂ A)) (by rw [← Unitization.inr_mul, hpq, Unitization.inr_zero])
    (by rw [← Unitization.inr_mul, ← Unitization.inr_mul, hw])
    (by simpa only [← Unitization.inr_star, ← Unitization.inr_mul, ← Unitization.inr_sub,
      Unitization.norm_inr] using h)
  -- `u * p` lies in `A`
  have hv := (Unitization.mul_inr u p).symm
  have hpp : p * p = p := hp.isIdempotentElem.eq
  refine ⟨u.fst • p + u.snd * p, Unitization.inr_injective (R := ℂ) ?_,
    Unitization.inr_injective (R := ℂ) ?_⟩
  · rw [Unitization.inr_mul, Unitization.inr_star, hv, star_mul, mul_assoc,
      ← mul_assoc (star u), hu₁, ← Unitization.inr_star, ← Unitization.inr_mul,
      ← Unitization.inr_mul, hp.isSelfAdjoint.star_eq, hpp, hpp]
  · rw [Unitization.inr_mul, Unitization.inr_star, hv, star_mul, mul_assoc,
      ← mul_assoc _ (star _), ← Unitization.inr_star, ← Unitization.inr_mul,
      hp.isSelfAdjoint.star_eq, hpp, ← hu₁, ← mul_assoc, ← mul_assoc, hu₂,
      mul_assoc, hu₂, hq'.isIdempotentElem.eq]

end IsStarProjection

namespace CStarMatrix

variable {m n A : Type*} [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A] [PartialOrder A]
  [StarOrderedRing A]

open WithCStarModule in
/-- The norm of a matrix over a C⋆-algebra is at most the sum of the norms of its entries. -/
theorem norm_le_sum_norm_entry (M : CStarMatrix m n A) : ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  rw [norm_def]
  refine (toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  simp only [toCLM_apply_eq_sum, Finset.sum_mul]
  refine (pi_norm_le_sum_norm _).trans ?_
  gcongr with j _
  refine (norm_sum_le _ _).trans ?_
  gcongr with i _
  refine (norm_mul_le _ _).trans ?_
  rw [mul_comm]
  gcongr
  exact norm_apply_le_norm v i

/-- If every entry of a matrix has norm less than `ε`, its norm is at most
`card m * card n * ε`. -/
theorem norm_le_card_mul_of_forall_norm_entry_le (M : CStarMatrix m n A) {ε : ℝ}
    (h : ∀ i j, ‖M i j‖ ≤ ε) : ‖M‖ ≤ Fintype.card m * Fintype.card n * ε := by
  refine (norm_le_sum_norm_entry M).trans ?_
  calc ∑ j, ∑ i, ‖M i j‖ ≤ ∑ _j : n, ∑ _i : m, ε := by gcongr with j _ i _; exact h i j
    _ = _ := by simp [Finset.card_univ]; ring

end CStarMatrix
