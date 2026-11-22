/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AutomorphyFactor
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Units
import TauCeti.Analysis.Normed.Group.Ultra

/-!
# Möbius transformations of the closed unit polydisc

Let `R` be a complete ultrametric normed commutative ring with `‖1‖ = 1`. A matrix
`g = !![a, b; c, d]` over `R` with `‖a‖, ‖b‖ ≤ 1`, `‖c‖ < 1` and `d` a multiplicative unit of
norm one (`TauCeti.IsNormMulUnit`) acts on the closed unit disc by the Möbius transformation
`z ↦ (a z + b) / (c z + d)`: since `‖c‖ < 1 = ‖d‖`, the denominator `c z + d` is a unit of the
Tate algebra `R⟨z⟩`, given by a Neumann series, and the quotient is a restricted series of Gauss
norm at most one. Such matrices form a monoid (`TauCeti.MvPowerSeries.mobiusSubmonoid`). Over
`ℚ_p`, or over a Banach algebra over a finite extension of `ℚ_p` along an embedding, it contains
the monoids `Σ₀(pᵗ)` of integral matrices with `c ≡ 0 mod pᵗ` and unit `d` that act on the
coefficient modules of overconvergent automorphic forms.

For a `k`-tuple of such matrices, one for each variable, the series
`TauCeti.MvPowerSeries.mobius i g = (a Xᵢ + b) (c Xᵢ + d)⁻¹` are formed in the unit Tate algebra
`R⟨X₁, …, X_k⟩`, and the denominators `c Xᵢ + d` are `TauCeti.MvPowerSeries.mobiusDenom i g`. The
main identity is the composition law `w_g(w_δ) = w_{g δ}`
(`TauCeti.MvPowerSeries.restrictedAnalyticSubst_mobius`), proved by analytic substitution in the
Tate algebra, together with the cocycle law of the denominators
`(c w_δ + d) (c' X + d') = c'' X + d''` for `g δ = !![a'', b''; c'', d'']`
(`TauCeti.MvPowerSeries.restrictedAnalyticSubst_mobiusDenom_mul`). Neither uses evaluation at
points, so both hold over nonreduced and integral coefficient rings.

Together they make `γ ↦ (w_γ, ∏ᵢ (cᵢ Xᵢ + dᵢ) ^ nᵢ)` a restricted automorphy factor
(`TauCeti.MvPowerSeries.mobiusAutomorphyFactor`), whose slash action
`f ↦ ∏ᵢ (cᵢ Xᵢ + dᵢ) ^ nᵢ · f((a X + b) / (c X + d))` is the weight-`n` action of the monoid by
norm-nonincreasing operators on `R⟨X⟩`.

## Main definitions

* `TauCeti.MvPowerSeries.mobiusSubmonoid`: the monoid of matrices `!![a, b; c, d]` with
  `‖a‖, ‖b‖ ≤ 1`, `‖c‖ < 1` and `d` a multiplicative unit of norm one.
* `TauCeti.MvPowerSeries.mobiusDenom`: the denominator `c Xᵢ + d`.
* `TauCeti.MvPowerSeries.mobius`: the Möbius series `(a Xᵢ + b) (c Xᵢ + d)⁻¹`.
* `TauCeti.MvPowerSeries.mobiusAutomorphyFactor`: the automorphy factor of weight `n`.

## Main results

* `TauCeti.MvPowerSeries.isNormMulUnit_mobiusDenom`, `TauCeti.MvPowerSeries.norm_mobiusDenom`:
  the denominator is a multiplicative unit of norm one.
* `TauCeti.MvPowerSeries.mobius_mul_mobiusDenom`, `TauCeti.MvPowerSeries.norm_mobius_le`: the
  Möbius series is the quotient `(a Xᵢ + b) / (c Xᵢ + d)` and lies in the closed unit ball.
* `TauCeti.MvPowerSeries.restrictedAnalyticSubst_mobiusDenom_mul`: the cocycle law of the
  denominators.
* `TauCeti.MvPowerSeries.restrictedAnalyticSubst_mobius`: the composition law of Möbius series.
* `TauCeti.MvPowerSeries.norm_factor_mobiusAutomorphyFactor`: the weight-`n` factor has norm one,
  so its slash operators do not increase norms.

## References

* K. Buzzard, *Eigenvarieties*, in *L-functions and Galois representations*, LMS Lecture Note
  Ser. 320 (2007), 59–120, §§9–10.
* D. Jacobs, *Slopes of compact Hecke operators*, PhD thesis, Imperial College London (2003),
  §1.5.
-/

public section

open MvPowerSeries

namespace TauCeti.MvPowerSeries

section Submonoid

variable (R : Type*) [NormedRing R] [NormOneClass R] [IsUltrametricDist R]
  [HasSummableGeomSeries R]

/-- The monoid of `2 × 2` matrices `!![a, b; c, d]` over `R` with `‖a‖ ≤ 1`, `‖b‖ ≤ 1`,
`‖c‖ < 1` and `d` a multiplicative unit of norm one. These are the matrices whose Möbius
transformation `z ↦ (a z + b) / (c z + d)` is an analytic self-map of the closed unit disc with
unit denominator `c z + d`. -/
def mobiusSubmonoid : Submonoid (Matrix (Fin 2) (Fin 2) R) where
  carrier := {g | ‖g 0 0‖ ≤ 1 ∧ ‖g 0 1‖ ≤ 1 ∧ ‖g 1 0‖ < 1 ∧ IsNormMulUnit (g 1 1) ∧ ‖g 1 1‖ = 1}
  one_mem' := by simp [isNormMulUnit_one]
  mul_mem' {g h} hg hh := by
    obtain ⟨ha, hb, hc, hd, hd1⟩ := hg
    obtain ⟨ha', hb', hc', hd', hd1'⟩ := hh
    have hle {x y : R} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 :=
      (norm_mul_le x y).trans ((mul_le_of_le_one_left (norm_nonneg y) hx).trans hy)
    have hlt {x y : R} (hx : ‖x‖ < 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ < 1 :=
      (norm_mul_le x y).trans_lt ((mul_le_of_le_one_right (norm_nonneg x) hy).trans_lt hx)
    have hu : ‖g 1 1 * h 1 1‖ = 1 := by rw [hd.norm_mul, hd1, hd1', one_mul]
    have hsub : ‖g 1 0 * h 0 1 + g 1 1 * h 1 1 - g 1 1 * h 1 1‖ < ‖g 1 1 * h 1 1‖ := by
      rw [add_sub_cancel_right, hu]
      exact hlt hc hb'
    simp only [Set.mem_ofPred_eq, Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hle ha ha') (hle hb hc'.le)),
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hle ha hb') (hle hb hd1'.le)),
      (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hlt hc ha') ?_),
      (hd.mul hd').of_norm_sub_lt hsub, ?_⟩
    · rw [hd.norm_mul, hd1, one_mul]
      exact hc'
    · rw [← IsUltrametricDist.norm_eq_of_norm_sub_lt_left (by rwa [norm_sub_rev]), hu]

variable {R}

/-- Membership in `mobiusSubmonoid R`: `‖a‖ ≤ 1`, `‖b‖ ≤ 1`, `‖c‖ < 1`, and `d` a multiplicative
unit of norm one. -/
theorem mem_mobiusSubmonoid_iff {g : Matrix (Fin 2) (Fin 2) R} :
    g ∈ mobiusSubmonoid R ↔
      ‖g 0 0‖ ≤ 1 ∧ ‖g 0 1‖ ≤ 1 ∧ ‖g 1 0‖ < 1 ∧ IsNormMulUnit (g 1 1) ∧ ‖g 1 1‖ = 1 :=
  Iff.rfl

/-- A matrix with lower right entry one lies in `mobiusSubmonoid R` exactly when its other
entries satisfy `‖a‖ ≤ 1`, `‖b‖ ≤ 1` and `‖c‖ < 1`. This covers the diagonal matrices
`diag(a, 1)` and the translations `!![1, b; 0, 1]`. -/
theorem mem_mobiusSubmonoid_iff_of_eq_one {g : Matrix (Fin 2) (Fin 2) R} (hg : g 1 1 = 1) :
    g ∈ mobiusSubmonoid R ↔ ‖g 0 0‖ ≤ 1 ∧ ‖g 0 1‖ ≤ 1 ∧ ‖g 1 0‖ < 1 := by
  simp [mem_mobiusSubmonoid_iff, hg, isNormMulUnit_one]

/-- A norm-preserving ring homomorphism maps `mobiusSubmonoid S` into `mobiusSubmonoid R`. For
instance, the algebra map of a normed algebra with `‖1‖ = 1` over a normed field carries the
integral matrices with small lower left and unit lower right entry into `mobiusSubmonoid R`. -/
theorem map_mem_mobiusSubmonoid {S : Type*} [NormedRing S] [NormOneClass S] [IsUltrametricDist S]
    [HasSummableGeomSeries S] {g : Matrix (Fin 2) (Fin 2) S} (hg : g ∈ mobiusSubmonoid S)
    (φ : S →+* R) (hφ : ∀ x, ‖φ x‖ = ‖x‖) : g.map φ ∈ mobiusSubmonoid R := by
  obtain ⟨ha, hb, hc, hd, hd1⟩ := hg
  simp only [mem_mobiusSubmonoid_iff, Matrix.map_apply, hφ]
  exact ⟨ha, hb, hc, hd.map φ.toMonoidHom hφ, hd1⟩

end Submonoid

section Mobius

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {k : ℕ}

/-- The **denominator** `c Xᵢ + d` of the Möbius transformation of `g = !![a, b; c, d]` in the
variable `Xᵢ` of the unit Tate algebra. It is a unit when `g ∈ mobiusSubmonoid R`
(`TauCeti.MvPowerSeries.isNormMulUnit_mobiusDenom`). -/
noncomputable def mobiusDenom (i : Fin k) (g : Matrix (Fin 2) (Fin 2) R) :
    IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ) :=
  g 1 0 • ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ + algebraMap R _ (g 1 1)

/-- The **Möbius series** `(a Xᵢ + b) (c Xᵢ + d)⁻¹` of `g = !![a, b; c, d]` in the variable `Xᵢ`
of the unit Tate algebra. For `g ∈ mobiusSubmonoid R` it is the quotient
`(a Xᵢ + b) / (c Xᵢ + d)` (`TauCeti.MvPowerSeries.mobius_mul_mobiusDenom`) and has Gauss norm at
most one (`TauCeti.MvPowerSeries.norm_mobius_le`). Outside that monoid the inverse is
`Ring.inverse`, which is `0` on nonunits. -/
noncomputable def mobius (i : Fin k) (g : Matrix (Fin 2) (Fin 2) R) :
    IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ) :=
  (g 0 0 • ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ + algebraMap R _ (g 0 1)) *
    Ring.inverse (mobiusDenom i g)

theorem mobiusDenom_def (i : Fin k) (g : Matrix (Fin 2) (Fin 2) R) :
    mobiusDenom i g =
      g 1 0 • ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ + algebraMap R _ (g 1 1) :=
  (rfl)

theorem mobius_def (i : Fin k) (g : Matrix (Fin 2) (Fin 2) R) :
    mobius i g =
      (g 0 0 • ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ + algebraMap R _ (g 0 1)) *
        Ring.inverse (mobiusDenom i g) :=
  (rfl)

@[simp]
theorem mobiusDenom_one (i : Fin k) : mobiusDenom i (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  simp [mobiusDenom_def]

@[simp]
theorem mobius_one (i : Fin k) :
    mobius i (1 : Matrix (Fin 2) (Fin 2) R) =
      ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ := by
  simp [mobius_def]

/-- **The affine case.** When `c = 0` and `d = 1`, the Möbius series is `a Xᵢ + b`. -/
theorem mobius_of_eq_zero_of_eq_one (i : Fin k) {g : Matrix (Fin 2) (Fin 2) R} (hc : g 1 0 = 0)
    (hd : g 1 1 = 1) :
    mobius i g =
      g 0 0 • ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ + algebraMap R _ (g 0 1) := by
  rw [mobius_def, mobiusDenom_def, hc, hd, zero_smul, zero_add, map_one, Ring.inverse_one,
    mul_one]

variable [CompleteSpace R] [NormOneClass R] {i : Fin k} {g : Matrix (Fin 2) (Fin 2) R}

omit [CompleteSpace R] in
/-- The scalar multiple `a Xᵢ` has Gauss norm at most `‖a‖`. -/
private theorem norm_smul_X_le (a : R) :
    ‖a • (⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ :
      IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ))‖ ≤ ‖a‖ := by
  have h := norm_smul_le a (⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ :
    IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ))
  rwa [norm_X, mul_one] at h

/-- The denominator differs from its constant term `d` by `c Xᵢ`, of norm less than one. -/
private theorem norm_mobiusDenom_sub_lt (hg : g ∈ mobiusSubmonoid R) :
    ‖mobiusDenom i g -
        algebraMap R (IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) (g 1 1)‖ <
      ‖algebraMap R (IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) (g 1 1)‖ := by
  rw [mobiusDenom_def, add_sub_cancel_right, norm_algebraMap_isRestrictedSubring, hg.2.2.2.2]
  exact norm_smul_X_le _ |>.trans_lt hg.2.2.1

private theorem isNormMulUnit_algebraMap_lowerRight (hg : g ∈ mobiusSubmonoid R) :
    IsNormMulUnit
      (algebraMap R (IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) (g 1 1)) :=
  hg.2.2.2.1.map (algebraMap R _).toMonoidHom norm_algebraMap_isRestrictedSubring

/-- For `g ∈ mobiusSubmonoid R` the denominator `c Xᵢ + d` is a multiplicative unit of the
Tate algebra: its inverse is the Neumann series of `d⁻¹ c Xᵢ`. -/
theorem isNormMulUnit_mobiusDenom (hg : g ∈ mobiusSubmonoid R) :
    IsNormMulUnit (mobiusDenom i g) :=
  (isNormMulUnit_algebraMap_lowerRight hg).of_norm_sub_lt (norm_mobiusDenom_sub_lt hg)

theorem isUnit_mobiusDenom (hg : g ∈ mobiusSubmonoid R) : IsUnit (mobiusDenom i g) :=
  (isNormMulUnit_mobiusDenom hg).isUnit

/-- For `g ∈ mobiusSubmonoid R` the denominator `c Xᵢ + d` has Gauss norm one. -/
theorem norm_mobiusDenom (hg : g ∈ mobiusSubmonoid R) : ‖mobiusDenom i g‖ = 1 := by
  rw [← IsUltrametricDist.norm_eq_of_norm_sub_lt_left
    (by rw [norm_sub_rev]; exact norm_mobiusDenom_sub_lt hg),
    norm_algebraMap_isRestrictedSubring, hg.2.2.2.2]

/-- For `g ∈ mobiusSubmonoid R` the inverse of the denominator has Gauss norm one. -/
theorem norm_ringInverse_mobiusDenom (hg : g ∈ mobiusSubmonoid R) :
    ‖Ring.inverse (mobiusDenom i g)‖ = 1 := by
  rw [(isNormMulUnit_algebraMap_lowerRight hg).norm_inverse_of_norm_sub_lt
    (norm_mobiusDenom_sub_lt hg), norm_algebraMap_isRestrictedSubring, hg.2.2.2.2, inv_one]

/-- For `g ∈ mobiusSubmonoid R` the Möbius series is the quotient `(a Xᵢ + b) / (c Xᵢ + d)`. -/
theorem mobius_mul_mobiusDenom (hg : g ∈ mobiusSubmonoid R) :
    mobius i g * mobiusDenom i g =
      g 0 0 • ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ + algebraMap R _ (g 0 1) := by
  rw [mobius_def, Ring.inverse_mul_cancel_right _ _ (isUnit_mobiusDenom hg)]

/-- For `g ∈ mobiusSubmonoid R` the Möbius series lies in the closed unit ball, so it can be
substituted into series restricted at radius one. -/
theorem norm_mobius_le (hg : g ∈ mobiusSubmonoid R) : ‖mobius i g‖ ≤ 1 := by
  rw [mobius_def]
  refine (norm_mul_le _ _).trans ?_
  rw [norm_ringInverse_mobiusDenom hg, mul_one]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact norm_smul_X_le _ |>.trans hg.1
  · rw [norm_algebraMap_isRestrictedSubring]
    exact hg.2.1

variable {h : Fin k → IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)} {hh : ∀ j, ‖h j‖ ≤ 1}

omit [NormOneClass R] in
/-- Substituting `h` into the denominator `c Xᵢ + d` gives `c hᵢ + d`. -/
@[simp]
theorem restrictedAnalyticSubst_mobiusDenom :
    restrictedAnalyticSubst h hh (mobiusDenom i g) = g 1 0 • h i + algebraMap R _ (g 1 1) := by
  rw [mobiusDenom_def, map_add, map_smul, AlgHom.commutes, restrictedAnalyticSubst_X]

variable {δ : Fin k → Matrix (Fin 2) (Fin 2) R}

/-- **The cocycle law of the denominators.** Writing `w_δ` for the Möbius series of the matrices
`δⱼ ∈ mobiusSubmonoid R`, substituting `w_δ` into the denominator of `g` and multiplying by the
denominator of `δᵢ` gives the denominator of `g δᵢ`: `(c w_δ + d) (c' Xᵢ + d') = c'' Xᵢ + d''`. -/
theorem restrictedAnalyticSubst_mobiusDenom_mul (hδ : ∀ j, δ j ∈ mobiusSubmonoid R) :
    restrictedAnalyticSubst (fun j ↦ mobius j (δ j)) (fun j ↦ norm_mobius_le (hδ j))
        (mobiusDenom i g) * mobiusDenom i (δ i) = mobiusDenom i (g * δ i) := by
  rw [restrictedAnalyticSubst_mobiusDenom, add_mul, smul_mul_assoc,
    mobius_mul_mobiusDenom (hδ i)]
  simp only [mobiusDenom_def, Matrix.mul_apply, Fin.sum_univ_two, mul_add,
    Algebra.smul_def, map_add, map_mul]
  ring

/-- The numerator analogue of `TauCeti.MvPowerSeries.restrictedAnalyticSubst_mobiusDenom_mul`:
`(a w_δ + b) (c' Xᵢ + d') = a'' Xᵢ + b''`. -/
private theorem restrictedAnalyticSubst_mobiusNum_mul (hδ : ∀ j, δ j ∈ mobiusSubmonoid R) :
    restrictedAnalyticSubst (fun j ↦ mobius j (δ j)) (fun j ↦ norm_mobius_le (hδ j))
        (g 0 0 • ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ +
          algebraMap R _ (g 0 1)) * mobiusDenom i (δ i) =
      (g * δ i) 0 0 • ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ +
        algebraMap R _ ((g * δ i) 0 1) := by
  rw [map_add, map_smul, AlgHom.commutes, restrictedAnalyticSubst_X, add_mul, smul_mul_assoc,
    mobius_mul_mobiusDenom (hδ i)]
  simp only [mobiusDenom_def, Matrix.mul_apply, Fin.sum_univ_two, mul_add,
    Algebra.smul_def, map_add, map_mul]
  ring

/-- **The composition law of Möbius series.** For `g` and `δⱼ` in `mobiusSubmonoid R`,
substituting the Möbius series `w_δ` of the `δⱼ` into the Möbius series of `g` in `Xᵢ` gives the
Möbius series of `g δᵢ`: `w_g(w_δ) = w_{g δ}`. -/
theorem restrictedAnalyticSubst_mobius (hg : g ∈ mobiusSubmonoid R)
    (hδ : ∀ j, δ j ∈ mobiusSubmonoid R) :
    restrictedAnalyticSubst (fun j ↦ mobius j (δ j)) (fun j ↦ norm_mobius_le (hδ j))
      (mobius i g) = mobius i (g * δ i) := by
  rw [mobius_def (g := g * δ i), Ring.eq_mul_inverse_iff_mul_eq _ _ _
    (isUnit_mobiusDenom (mul_mem hg (hδ i))), ← restrictedAnalyticSubst_mobiusDenom_mul hδ,
    ← mul_assoc, ← map_mul, mobius_mul_mobiusDenom hg, restrictedAnalyticSubst_mobiusNum_mul hδ]

end Mobius

section AutomorphyFactor

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R]
  {k : ℕ}

variable (R) in
/-- The **automorphy factor of weight `n`** for `k`-tuples of matrices in `mobiusSubmonoid R`,
one for each variable: the substitution is the Möbius series `w_γ = ((aᵢ Xᵢ + bᵢ)/(cᵢ Xᵢ + dᵢ))ᵢ`
and the factor is `∏ᵢ (cᵢ Xᵢ + dᵢ) ^ nᵢ`. Its slash action is
`f ↦ ∏ᵢ (cᵢ Xᵢ + dᵢ) ^ nᵢ · f(w_γ)`. -/
noncomputable def mobiusAutomorphyFactor (n : Fin k → ℕ) :
    RestrictedAutomorphyFactor (Fin k → mobiusSubmonoid R) R k where
  subst γ i := mobius i (γ i : Matrix (Fin 2) (Fin 2) R)
  norm_subst_le γ i := norm_mobius_le (γ i).property
  factor γ := ∏ i, mobiusDenom i (γ i : Matrix (Fin 2) (Fin 2) R) ^ n i
  subst_one i := mobius_one i
  subst_mul γ δ i := (restrictedAnalyticSubst_mobius (γ i).property fun j ↦ (δ j).property).symm
  factor_one := by simp
  factor_mul γ δ := by
    simp only [Pi.mul_apply, Submonoid.coe_mul, map_prod, map_pow, ← Finset.prod_mul_distrib,
      ← mul_pow, restrictedAnalyticSubst_mobiusDenom_mul fun j ↦ (δ j).property]

variable (n : Fin k → ℕ)

@[simp]
theorem mobiusAutomorphyFactor_subst (γ : Fin k → mobiusSubmonoid R) (i : Fin k) :
    (mobiusAutomorphyFactor R n).subst γ i = mobius i (γ i : Matrix (Fin 2) (Fin 2) R) :=
  (rfl)

@[simp]
theorem mobiusAutomorphyFactor_factor (γ : Fin k → mobiusSubmonoid R) :
    (mobiusAutomorphyFactor R n).factor γ =
      ∏ i, mobiusDenom i (γ i : Matrix (Fin 2) (Fin 2) R) ^ n i :=
  (rfl)

/-- The weight-`n` factor has Gauss norm one, so the weight-`n` slash operators do not increase
the Gauss norm (`TauCeti.MvPowerSeries.RestrictedAutomorphyFactor.norm_slash_apply_le`). -/
theorem norm_factor_mobiusAutomorphyFactor (γ : Fin k → mobiusSubmonoid R) :
    ‖(mobiusAutomorphyFactor R n).factor γ‖ = 1 := by
  rw [mobiusAutomorphyFactor_factor,
    IsNormMulUnit.norm_prod fun i _ ↦ (isNormMulUnit_mobiusDenom (γ i).property).pow _]
  exact Finset.prod_eq_one fun i _ ↦ by
    rw [(isNormMulUnit_mobiusDenom (γ i).property).norm_pow, norm_mobiusDenom (γ i).property,
      one_pow]

end AutomorphyFactor

end TauCeti.MvPowerSeries
