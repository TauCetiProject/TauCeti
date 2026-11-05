/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Compact
public import TauCeti.Analysis.Fourier.Winding
public import TauCeti.Analysis.Fredholm.CompactPerturbation

import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Units
import TauCeti.Analysis.Fredholm.Adjoint
import TauCeti.Analysis.Fredholm.Pow

/-!
# The shift algebra and the Gohberg–Krein Fredholm index theorem

This file develops the Fredholm theory of Toeplitz operators `T_a` with continuous symbols
`a : C(UnitAddCircle, ℂ)` on the boundary Hardy space `HardySpace`.

## Mathematical overview

1. **The shift algebra and Laurent monomial models.** The forward shift
   `S = toeplitz (fourierLp ∞ 1)` raises the Hardy basis (`S eₙ = eₙ₊₁`), while its adjoint
   `S† = toeplitz (fourierLp ∞ (-1))` is the backward shift (`S† e₀ = 0`, `S† eₙ₊₁ = eₙ`). They
   satisfy `S† ∘L S = id` and the defect identity `S ∘L S† = id - P_{e₀}`, where
   `P_{e₀} = (ℂ ∙ hardyBasis 0).starProjection` is the rank-one orthogonal projection onto the
   constant mode. In particular `S†` is surjective with one-dimensional kernel `ℂ ∙ hardyBasis 0`,
   so `S†` is Fredholm of index `1`, `S` is Fredholm of index `-1`, and for every `k : ℤ` the
   monomial Toeplitz operator `toeplitz (fourierLp ∞ k)` is Fredholm of index `-k`.

2. **Sufficiency and homotopy invariance.** When `a : C(UnitAddCircle, ℂ)` is nowhere zero, `a⁻¹`
   is also continuous, and the semicommutators `T_(a⁻¹) T_a - I` and `T_a T_(a⁻¹) - I` are compact
   by `TauCeti.isCompactOperator_toeplitz_comp_sub_toeplitz_toLp`. Thus `T_(a⁻¹)` is a two-sided
   Fredholm quasi-inverse modulo compact operators, making `T_a` Fredholm. Any continuous homotopy
   through nowhere-zero symbols gives a continuous family of Fredholm operators over `[0, 1]`,
   along which `Continuous.index_eq_of_preconnectedSpace` holds the index constant; deforming `a`
   to `fourier (a.windingNumber ha)` via `ContinuousMap.exists_homotopy_fourier` yields the index
   formula `index T_a = -a.windingNumber ha`.

3. **Necessity (Gohberg–Krein).** Conversely, if `a x₀ = 0` at some point of the circle,
   `ContinuousMap.exists_norm_sub_lt_windingNumber_ne` approximates `a` uniformly within any
   `ε > 0` by nowhere-zero continuous symbols of distinct winding numbers, hence Toeplitz operators
   of distinct Fredholm indices arbitrarily close in operator norm to `T_a`. Since the Fredholm
   locus is open and the index is locally constant on it, `T_a` cannot be Fredholm.

4. **Compact perturbations.** Adding or subtracting a compact operator `K` preserves both the
   Fredholm characterization `∀ x, a x ≠ 0` and the index `-a.windingNumber ha`. As an explicit
   witness that Fredholm of index zero is strictly weaker than invertibility on `T_C + K(H²)`, the
   rank-one perturbation `T_1 - (ℂ ∙ hardyBasis 0).starProjection` (= `S ∘L S†`) is Fredholm of
   index `0`, annihilates `hardyBasis 0`, and is therefore not invertible.

## Main results

* `TauCeti.toeplitz_fourierLp_neg_one_comp_one`, `TauCeti.toeplitz_fourierLp_one_comp_neg_one`:
  `S† ∘L S = id` and `S ∘L S† = id - (ℂ ∙ hardyBasis 0).starProjection`.
* `TauCeti.isFredholm_toeplitz_fourierLp`, `TauCeti.index_toeplitz_fourierLp`: for every `k : ℤ`,
  `toeplitz (fourierLp ∞ k)` is Fredholm of index `-k`.
* `TauCeti.isFredholm_toeplitz_toLp_iff`: **Gohberg–Krein Fredholm criterion** — for continuous
  `a`, `T_a` is Fredholm if and only if `∀ x, a x ≠ 0`.
* `TauCeti.index_toeplitz_toLp`: **Gohberg–Krein index theorem** —
  `ContinuousLinearMap.index T_a = -a.windingNumber ha`.
* `TauCeti.isFredholm_toeplitz_toLp_add_iff`, `TauCeti.index_toeplitz_toLp_add`: Fredholm
  characterization and index formula for compact perturbations `T_a + K`.
* `TauCeti.not_isUnit_toeplitz_toLp_one_sub_span_hardyBasis_zero_starProjection`: `T_1 - P_{e₀}`
  is a compact perturbation of `T_1` that is Fredholm of index `0` yet not a unit.

## References

* I. C. Gohberg and M. G. Krein, *Systems of integral equations on a half line with kernels
  depending on the difference of arguments*, Amer. Math. Soc. Transl. (2) 14 (1960), 217–287.
* R. G. Douglas, *Banach Algebra Techniques in Operator Theory*, second edition, Theorem 7.26.
* J. B. Conway, *A Course in Functional Analysis*, second edition, Chapter XI.
* E. Park, *Toeplitz operators*.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace unitInterval

namespace TauCeti

section ShiftAlgebra

/-- The `Lp` star (pointwise complex conjugate) of the Fourier monomial `fourierLp p k` is
`fourierLp p (-k)`. -/
@[simp]
theorem star_fourierLp {T : ℝ} [Fact (0 < T)] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℤ) :
    star (fourierLp (T := T) p k) = fourierLp (T := T) p (-k) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (fourierLp (T := T) p k),
    coeFn_fourierLp (T := T) p k, coeFn_fourierLp (T := T) p (-k)] with x hstar hk hneg
  rw [hstar, Pi.star_apply, hk, hneg, fourier_neg, RCLike.star_def]

private theorem fourierLp_infty_mul (m n : ℤ) :
    (fourierLp (T := 1) ∞ m • fourierLp (T := 1) ∞ n :
        Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) =
      fourierLp (T := 1) ∞ (m + n) := by
  apply Lp.ext
  filter_upwards [coeFn_fourierLp_smul m (fourierLp (T := 1) ∞ n),
    coeFn_fourierLp (T := 1) ∞ n, coeFn_fourierLp (T := 1) ∞ (m + n)] with x hsmul hn hmn
  rw [hsmul, hn, hmn, fourier_add]

/-- The adjoint of the monomial Toeplitz operator `T_(e_k)` is `T_(e_{-k})`. -/
theorem adjoint_toeplitz_fourierLp (k : ℤ) :
    ContinuousLinearMap.adjoint (toeplitz (fourierLp (T := 1) ∞ k)) =
      toeplitz (fourierLp (T := 1) ∞ (-k)) := by
  rw [adjoint_toeplitz, star_fourierLp]

/-- The Toeplitz operator of the constant mode `e_0` is the identity on `HardySpace`. -/
@[simp]
theorem toeplitz_fourierLp_zero :
    toeplitz (fourierLp (T := 1) ∞ 0) = ContinuousLinearMap.id ℂ HardySpace := by
  have h0 : fourierLp (T := 1) ∞ 0 = Lp.const ∞ (AddCircle.haarAddCircle (T := 1)) (1 : ℂ) := by
    apply Lp.ext
    filter_upwards [coeFn_fourierLp (T := 1) ∞ 0,
      Lp.coeFn_const ∞ (AddCircle.haarAddCircle (T := 1)) (1 : ℂ)] with x hx hc
    rw [hx, hc, Function.const_apply, fourier_zero]
  rw [h0, toeplitz_const, one_smul]

/-- The backward shift `T_(e_{-1})` annihilates the constant Hardy mode `hardyBasis 0`. -/
@[simp]
theorem toeplitz_fourierLp_neg_one_hardyBasis_zero :
    toeplitz (fourierLp (T := 1) ∞ (-1)) (hardyBasis 0) = 0 := by
  apply hardyBasis.repr.injective
  rw [hardyBasis.repr.map_zero]
  apply lp.ext
  funext i
  rw [lp.coeFn_zero, Pi.zero_apply, hardyBasis_repr_toeplitz_apply, coe_hardyBasis,
    fourierLp_smul_fourierBasis, Nat.cast_zero, add_zero, coe_fourierBasis,
    fourierCoeff_fourierLp, ite_eq_right (by omega)]

/-- The backward shift `T_(e_{-1})` lowers every positive Hardy basis mode by `1`. -/
@[simp]
theorem toeplitz_fourierLp_neg_one_hardyBasis_succ (n : ℕ) :
    toeplitz (fourierLp (T := 1) ∞ (-1)) (hardyBasis (n + 1)) = hardyBasis n := by
  apply hardyBasis.repr.injective
  apply lp.ext
  funext i
  have hidx : (-1 : ℤ) + ((n + 1 : ℕ) : ℤ) = (n : ℤ) := by omega
  rw [hardyBasis_repr_toeplitz_apply, coe_hardyBasis, fourierLp_smul_fourierBasis, hidx,
    ← coe_hardyBasis, ← hardyBasis_repr]

/-- The backward shift is a left inverse to the forward shift: `S† ∘L S = id`. -/
@[simp]
theorem toeplitz_fourierLp_neg_one_comp_one :
    toeplitz (fourierLp (T := 1) ∞ (-1)) ∘L toeplitz (fourierLp (T := 1) ∞ 1) =
      ContinuousLinearMap.id ℂ HardySpace := by
  rw [toeplitz_comp_of_analytic]
  · rw [fourierLp_infty_mul, neg_add_cancel, toeplitz_fourierLp_zero]
  · intro n hn
    rw [fourierCoeff_fourierLp, ite_eq_right (by omega)]

/-- **Shift defect identity.** Composing the forward shift after the backward shift differs from
the identity by the rank-one orthogonal projection onto `ℂ ∙ hardyBasis 0`. -/
theorem toeplitz_fourierLp_one_comp_neg_one :
    toeplitz (fourierLp (T := 1) ∞ 1) ∘L toeplitz (fourierLp (T := 1) ∞ (-1)) =
      ContinuousLinearMap.id ℂ HardySpace - (ℂ ∙ hardyBasis 0).starProjection := by
  have hnorm0 : ‖hardyBasis 0‖ = 1 := hardyBasis.orthonormal.1 0
  apply ContinuousLinearMap.ext_on (s := Set.range hardyBasis) (by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, hardyBasis.dense_span]
    rfl)
  rintro _ ⟨k, rfl⟩
  cases k with
  | zero =>
    rw [ContinuousLinearMap.comp_apply, toeplitz_fourierLp_neg_one_hardyBasis_zero, map_zero,
      sub_apply, ContinuousLinearMap.id_apply,
      Submodule.starProjection_unit_singleton ℂ hnorm0,
      orthonormal_iff_ite.mp hardyBasis.orthonormal 0 0, ite_eq_left rfl, one_smul, sub_self]
  | succ n =>
    rw [ContinuousLinearMap.comp_apply, toeplitz_fourierLp_neg_one_hardyBasis_succ,
      toeplitz_fourierLp_one_hardyBasis, sub_apply,
      ContinuousLinearMap.id_apply, Submodule.starProjection_unit_singleton ℂ hnorm0,
      orthonormal_iff_ite.mp hardyBasis.orthonormal 0 (n + 1), ite_eq_right (Nat.zero_ne_add_one n),
      zero_smul, sub_zero]

/-- The forward shift `S = T_(e_1)` is injective: its kernel is trivial. -/
theorem ker_toeplitz_fourierLp_one :
    LinearMap.ker (toeplitz (fourierLp (T := 1) ∞ 1) : HardySpace →ₗ[ℂ] HardySpace) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hf
  have h := congrArg (fun T => T f) toeplitz_fourierLp_neg_one_comp_one
  rw [ContinuousLinearMap.comp_apply, hf, map_zero, ContinuousLinearMap.id_apply] at h
  exact h.symm

/-- The backward shift `S† = T_(e_{-1})` is surjective. -/
theorem surjective_toeplitz_fourierLp_neg_one :
    Function.Surjective (toeplitz (fourierLp (T := 1) ∞ (-1))) := fun g =>
  ⟨toeplitz (fourierLp (T := 1) ∞ 1) g,
    congrArg (fun T => T g) toeplitz_fourierLp_neg_one_comp_one⟩

/-- The kernel of the backward shift `S† = T_(e_{-1})` is the one-dimensional subspace spanned by
`hardyBasis 0`. -/
theorem ker_toeplitz_fourierLp_neg_one :
    LinearMap.ker (toeplitz (fourierLp (T := 1) ∞ (-1)) : HardySpace →ₗ[ℂ] HardySpace) =
      ℂ ∙ hardyBasis 0 := by
  refine le_antisymm (fun f hf => ?_) ?_
  · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hf
    have h := congrArg (fun T => T f) toeplitz_fourierLp_one_comp_neg_one
    rw [ContinuousLinearMap.comp_apply, hf, map_zero, sub_apply, ContinuousLinearMap.id_apply,
      eq_comm, sub_eq_zero] at h
    rw [h, Submodule.starProjection_apply]
    exact Submodule.coe_mem _
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe]
    exact toeplitz_fourierLp_neg_one_hardyBasis_zero

/-- The backward shift `T_(e_{-1})` is a Fredholm operator on `HardySpace`. -/
theorem isFredholm_toeplitz_fourierLp_neg_one :
    ContinuousLinearMap.IsFredholm (toeplitz (fourierLp (T := 1) ∞ (-1))) := by
  refine ContinuousLinearMap.IsFredholm.of_finite_ker_coker _ ?_ ?_
  · rw [ker_toeplitz_fourierLp_neg_one]
    infer_instance
  · rw [LinearMap.range_eq_top.mpr surjective_toeplitz_fourierLp_neg_one]
    infer_instance

/-- The backward shift `T_(e_{-1})` has Fredholm index `1`. -/
theorem index_toeplitz_fourierLp_neg_one :
    ContinuousLinearMap.index (toeplitz (fourierLp (T := 1) ∞ (-1))) = 1 := by
  have hne : hardyBasis 0 ≠ 0 := norm_ne_zero_iff.mp (by simp [hardyBasis.orthonormal.1 0])
  rw [ContinuousLinearMap.index_of_surjective _ surjective_toeplitz_fourierLp_neg_one,
    ker_toeplitz_fourierLp_neg_one, finrank_span_singleton hne, Nat.cast_one]

/-- The forward shift `T_(e_1)` is a Fredholm operator on `HardySpace`. -/
theorem isFredholm_toeplitz_fourierLp_one :
    ContinuousLinearMap.IsFredholm (toeplitz (fourierLp (T := 1) ∞ 1)) := by
  have h := isFredholm_toeplitz_fourierLp_neg_one.adjoint
  rwa [adjoint_toeplitz_fourierLp, neg_neg] at h

/-- The forward shift `T_(e_1)` has Fredholm index `-1`. -/
theorem index_toeplitz_fourierLp_one :
    ContinuousLinearMap.index (toeplitz (fourierLp (T := 1) ∞ 1)) = -1 := by
  have h := ContinuousLinearMap.index_adjoint (toeplitz (fourierLp (T := 1) ∞ (-1)))
    isFredholm_toeplitz_fourierLp_neg_one
  rw [adjoint_toeplitz_fourierLp, neg_neg, index_toeplitz_fourierLp_neg_one] at h
  exact h

/-- For `m : ℕ`, the analytic monomial Toeplitz operator `T_(e_m)` is the `m`-th power of the
forward shift `T_(e_1)`. -/
theorem toeplitz_fourierLp_natCast_eq_pow (m : ℕ) :
    toeplitz (fourierLp (T := 1) ∞ (m : ℤ)) = (toeplitz (fourierLp (T := 1) ∞ 1)) ^ m := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, pow_zero, ContinuousLinearMap.one_def, toeplitz_fourierLp_zero]
  | succ m ih =>
    rw [pow_succ, ContinuousLinearMap.mul_def, ← ih, toeplitz_comp_of_analytic]
    · rw [fourierLp_infty_mul, Nat.cast_add, Nat.cast_one]
    · intro n hn
      rw [fourierCoeff_fourierLp, ite_eq_right (by omega)]

/-- Every Fourier monomial `e_k` (`k : ℤ`) defines a Fredholm Toeplitz operator on `HardySpace`. -/
theorem isFredholm_toeplitz_fourierLp (k : ℤ) :
    ContinuousLinearMap.IsFredholm (toeplitz (fourierLp (T := 1) ∞ k)) := by
  cases k with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, toeplitz_fourierLp_natCast_eq_pow]
    exact isFredholm_toeplitz_fourierLp_one.pow m
  | negSucc m =>
    have h : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := rfl
    rw [h, ← adjoint_toeplitz_fourierLp, toeplitz_fourierLp_natCast_eq_pow]
    exact (isFredholm_toeplitz_fourierLp_one.pow (m + 1)).adjoint

/-- **Index of Laurent monomial Toeplitz operators.** For every `k : ℤ`, `T_(e_k)` has Fredholm
index `-k`. -/
@[simp]
theorem index_toeplitz_fourierLp (k : ℤ) :
    ContinuousLinearMap.index (toeplitz (fourierLp (T := 1) ∞ k)) = -k := by
  cases k with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, toeplitz_fourierLp_natCast_eq_pow,
      ContinuousLinearMap.index_pow _ isFredholm_toeplitz_fourierLp_one,
      index_toeplitz_fourierLp_one]
    ring
  | negSucc m =>
    have h : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := rfl
    have hpow := isFredholm_toeplitz_fourierLp_one.pow (m + 1)
    rw [h, ← adjoint_toeplitz_fourierLp, toeplitz_fourierLp_natCast_eq_pow,
      ContinuousLinearMap.index_adjoint _ hpow,
      ContinuousLinearMap.index_pow _ isFredholm_toeplitz_fourierLp_one,
      index_toeplitz_fourierLp_one]
    ring

end ShiftAlgebra

section GohbergKrein

private theorem toLp_infty_smul (a b : C(UnitAddCircle, ℂ)) :
    (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a •
        ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ b :
          Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) =
      ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ (a * b) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := ∞)
      (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a)
      (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ b),
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (AddCircle.haarAddCircle (T := 1)) a,
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (AddCircle.haarAddCircle (T := 1)) b,
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (AddCircle.haarAddCircle (T := 1)) (a * b)] with x
    hsmul ha hb hab
  rw [hsmul, Pi.smul_apply', ha, hb, hab, ContinuousMap.mul_apply, smul_eq_mul]

/-- The continuous symbol `1` induces the identity Toeplitz operator on `HardySpace`. -/
@[simp]
theorem toeplitz_toLp_one :
    toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ (1 : C(UnitAddCircle, ℂ))) =
      ContinuousLinearMap.id ℂ HardySpace := by
  have h1 : ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ (1 : C(UnitAddCircle, ℂ)) =
      Lp.const ∞ (AddCircle.haarAddCircle (T := 1)) (1 : ℂ) := by
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (AddCircle.haarAddCircle (T := 1))
        (1 : C(UnitAddCircle, ℂ)),
      Lp.coeFn_const ∞ (AddCircle.haarAddCircle (T := 1)) (1 : ℂ)] with x h1 hc
    rw [h1, hc, ContinuousMap.one_apply, Function.const_apply]
  rw [h1, toeplitz_const, one_smul]

/-- A nowhere-zero continuous symbol `a : C(UnitAddCircle, ℂ)` induces a Fredholm Toeplitz
operator: `T_(a⁻¹)` is a two-sided quasi-inverse modulo compact operators. -/
theorem isFredholm_toeplitz_toLp_of_forall_ne_zero {a : C(UnitAddCircle, ℂ)}
    (ha : ∀ x, a x ≠ 0) :
    ContinuousLinearMap.IsFredholm
      (toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a)) := by
  obtain ⟨u, rfl⟩ := (ContinuousMap.isUnit_iff_forall_ne_zero a).mpr ha
  let a₀ : C(UnitAddCircle, ℂ) := u
  let b₀ : C(UnitAddCircle, ℂ) := ↑u⁻¹
  let Ta := toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a₀)
  let Tb := toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ b₀)
  have hba : b₀ * a₀ = 1 := Units.inv_mul u
  have hab : a₀ * b₀ = 1 := Units.mul_inv u
  have hK₁ : IsCompactOperator ((Tb ∘L Ta - 1 : HardySpace →L[ℂ] HardySpace)) := by
    have h := isCompactOperator_toeplitz_comp_sub_toeplitz_toLp
      (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ b₀) a₀
    rwa [toLp_infty_smul, hba, toeplitz_toLp_one, ← ContinuousLinearMap.one_def] at h
  have hK₂ : IsCompactOperator ((Ta ∘L Tb - 1 : HardySpace →L[ℂ] HardySpace)) := by
    have h := isCompactOperator_toeplitz_comp_sub_toeplitz_toLp
      (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a₀) b₀
    rwa [toLp_infty_smul, hab, toeplitz_toLp_one, ← ContinuousLinearMap.one_def] at h
  have hFred₁ : ContinuousLinearMap.IsFredholm (Tb ∘L Ta) := by
    have heq : Tb ∘L Ta = 1 + (Tb ∘L Ta - 1) := by abel
    rw [heq]
    exact isFredholm_one_add hK₁
  have hFred₂ : ContinuousLinearMap.IsFredholm (Ta ∘L Tb) := by
    have heq : Ta ∘L Tb = 1 + (Ta ∘L Tb - 1) := by abel
    rw [heq]
    exact isFredholm_one_add hK₂
  refine ContinuousLinearMap.IsFredholm.of_finite_ker_coker Ta ?_ ?_
  · have hker : LinearMap.ker (Ta : HardySpace →ₗ[ℂ] HardySpace) ≤
        LinearMap.ker ((Tb ∘L Ta) : HardySpace →ₗ[ℂ] HardySpace) := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      simpa only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, map_zero] using
        congrArg Tb hx
    have := ((isFredholm_iff_finite_ker_coker _).mp hFred₁).1
    exact Submodule.finiteDimensional_of_le hker
  · have hrange : LinearMap.range ((Ta ∘L Tb) : HardySpace →ₗ[ℂ] HardySpace) ≤
        LinearMap.range (Ta : HardySpace →ₗ[ℂ] HardySpace) := by
      rintro y ⟨z, rfl⟩
      exact ⟨Tb z, rfl⟩
    have := ((isFredholm_iff_finite_ker_coker _).mp hFred₂).2
    exact FiniteDimensional.of_surjective (Submodule.factor hrange)
      (Submodule.factor_surjective hrange)

/-- **Homotopy invariance of the Toeplitz Fredholm index.** Two nowhere-zero continuous symbols
joined by a continuous homotopy through nowhere-zero symbols induce Toeplitz operators of equal
Fredholm index. -/
theorem index_toeplitz_toLp_eq_of_homotopy {a b : C(UnitAddCircle, ℂ)}
    (H : C(I × UnitAddCircle, ℂ)) (hH : ∀ p, H p ≠ 0)
    (h0 : ∀ x, H (0, x) = a x) (h1 : ∀ x, H (1, x) = b x) :
    ContinuousLinearMap.index
        (toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a)) =
      ContinuousLinearMap.index
        (toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ b)) := by
  let Φ := toeplitz ∘L ContinuousMap.toLp (E := ℂ) ∞ (AddCircle.haarAddCircle (T := 1)) ℂ
  have hcont : Continuous (fun t : I => Φ (H.curry t)) := Φ.continuous.comp H.curry.continuous
  have hfred (t : I) : ContinuousLinearMap.IsFredholm (Φ (H.curry t)) :=
    isFredholm_toeplitz_toLp_of_forall_ne_zero fun x => hH (t, x)
  have heq := Continuous.index_eq_of_preconnectedSpace hcont hfred 0 1
  have hcurry0 : H.curry 0 = a := ContinuousMap.ext h0
  have hcurry1 : H.curry 1 = b := ContinuousMap.ext h1
  simpa only [Φ, ContinuousLinearMap.comp_apply, hcurry0, hcurry1] using heq

/-- **Gohberg–Krein index theorem.** The Toeplitz operator of a nowhere-zero continuous symbol
`a : C(UnitAddCircle, ℂ)` has Fredholm index equal to minus the winding number of `a` about `0`. -/
theorem index_toeplitz_toLp (a : C(UnitAddCircle, ℂ)) (ha : ∀ x, a x ≠ 0) :
    ContinuousLinearMap.index
      (toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a)) =
        -a.windingNumber ha := by
  obtain ⟨H, hH, h0, h1⟩ := a.exists_homotopy_fourier ha
  rw [index_toeplitz_toLp_eq_of_homotopy H hH h0 h1]
  exact index_toeplitz_fourierLp (a.windingNumber ha)

/-- **Gohberg–Krein Fredholm theorem.** For a continuous symbol `a : C(UnitAddCircle, ℂ)`, the
Toeplitz operator `T_a` on `HardySpace` is Fredholm if and only if `a` vanishes nowhere on the unit
circle. -/
theorem isFredholm_toeplitz_toLp_iff (a : C(UnitAddCircle, ℂ)) :
    ContinuousLinearMap.IsFredholm
      (toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a)) ↔
        ∀ x, a x ≠ 0 := by
  refine ⟨fun hFred => ?_, isFredholm_toeplitz_toLp_of_forall_ne_zero⟩
  by_contra hnot
  push Not at hnot
  obtain ⟨x₀, hx₀⟩ := hnot
  let Φ := toeplitz ∘L ContinuousMap.toLp (E := ℂ) ∞ (AddCircle.haarAddCircle (T := 1)) ℂ
  have hnhds : ∀ᶠ g : C(UnitAddCircle, ℂ) in nhds a,
      ContinuousLinearMap.IsFredholm (Φ g) ∧
        ContinuousLinearMap.index (Φ g) = ContinuousLinearMap.index (Φ a) :=
    Φ.continuous.continuousAt hFred.eventually_isFredholm_and_index_eq
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  obtain ⟨g₁, g₂, hg₁, hg₂, hdist₁, hdist₂, hwind_ne⟩ :=
    a.exists_norm_sub_lt_windingNumber_ne hx₀ hε
  have hind₁ : ContinuousLinearMap.index (Φ g₁) = ContinuousLinearMap.index (Φ a) :=
    (hball (by simpa [Metric.mem_ball, dist_eq_norm] using hdist₁)).2
  have hind₂ : ContinuousLinearMap.index (Φ g₂) = ContinuousLinearMap.index (Φ a) :=
    (hball (by simpa [Metric.mem_ball, dist_eq_norm] using hdist₂)).2
  have heq : -g₁.windingNumber hg₁ = -g₂.windingNumber hg₂ := by
    rw [← index_toeplitz_toLp g₁ hg₁, ← index_toeplitz_toLp g₂ hg₂]
    exact hind₁.trans hind₂.symm
  exact hwind_ne (neg_inj.mp heq)

end GohbergKrein

section CompactPerturbation

/-- A compact perturbation `T_a + K` of a continuous-symbol Toeplitz operator is Fredholm if and
only if the symbol `a` is nowhere zero. -/
theorem isFredholm_toeplitz_toLp_add_iff (a : C(UnitAddCircle, ℂ))
    {K : HardySpace →L[ℂ] HardySpace} (hK : IsCompactOperator K) :
    ContinuousLinearMap.IsFredholm
      (toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a) + K) ↔
        ∀ x, a x ≠ 0 := by
  constructor
  · intro hFred
    have hKneg : IsCompactOperator (-K : HardySpace →L[ℂ] HardySpace) := by
      simpa only [FunLike.coe_neg] using hK.neg
    have hTa : ContinuousLinearMap.IsFredholm
        (toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a)) := by
      have h := hFred.add_of_isCompactOperator hKneg
      rwa [add_neg_cancel_right] at h
    exact (isFredholm_toeplitz_toLp_iff a).mp hTa
  · intro ha
    exact (isFredholm_toeplitz_toLp_of_forall_ne_zero ha).add_of_isCompactOperator hK

/-- A compact perturbation `T_a + K` of a nowhere-zero continuous-symbol Toeplitz operator has
Fredholm index `-a.windingNumber ha`. -/
theorem index_toeplitz_toLp_add (a : C(UnitAddCircle, ℂ)) (ha : ∀ x, a x ≠ 0)
    {K : HardySpace →L[ℂ] HardySpace} (hK : IsCompactOperator K) :
    ContinuousLinearMap.index
      (toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a) + K) =
        -a.windingNumber ha := by
  rw [ContinuousLinearMap.index_add_of_isCompactOperator
    (isFredholm_toeplitz_toLp_of_forall_ne_zero ha) hK, index_toeplitz_toLp a ha]

/-- Subtracting a compact operator `K` from a continuous-symbol Toeplitz operator `T_a` yields a
Fredholm operator if and only if `a` is nowhere zero. -/
theorem isFredholm_toeplitz_toLp_sub_iff (a : C(UnitAddCircle, ℂ))
    {K : HardySpace →L[ℂ] HardySpace} (hK : IsCompactOperator K) :
    ContinuousLinearMap.IsFredholm
      (toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a) - K) ↔
        ∀ x, a x ≠ 0 := by
  have hKneg : IsCompactOperator (-K : HardySpace →L[ℂ] HardySpace) := by
    simpa only [FunLike.coe_neg] using hK.neg
  have hrw : toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a) - K =
      toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a) + (-K) := by abel
  rw [hrw]
  exact isFredholm_toeplitz_toLp_add_iff a hKneg

/-- Subtracting a compact operator `K` from a nowhere-zero continuous-symbol Toeplitz operator
`T_a` leaves its Fredholm index equal to `-a.windingNumber ha`. -/
theorem index_toeplitz_toLp_sub (a : C(UnitAddCircle, ℂ)) (ha : ∀ x, a x ≠ 0)
    {K : HardySpace →L[ℂ] HardySpace} (hK : IsCompactOperator K) :
    ContinuousLinearMap.index
      (toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a) - K) =
        -a.windingNumber ha := by
  have hKneg : IsCompactOperator (-K : HardySpace →L[ℂ] HardySpace) := by
    simpa only [FunLike.coe_neg] using hK.neg
  have hrw : toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a) - K =
      toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ a) + (-K) := by abel
  rw [hrw, index_toeplitz_toLp_add a ha hKneg]

/-- Orthogonal projection onto the constant Hardy mode `ℂ ∙ hardyBasis 0` has finite rank. -/
theorem hasFiniteRange_span_hardyBasis_zero_starProjection :
    (((ℂ ∙ hardyBasis 0).starProjection : HardySpace →L[ℂ] HardySpace) :
      HardySpace →ₗ[ℂ] HardySpace).HasFiniteRange := by
  have hnorm0 : ‖hardyBasis 0‖ = 1 := hardyBasis.orthonormal.1 0
  refine hardyBasis.hasFiniteRange_of_apply_eq_zero _ {0} fun k hk => ?_
  rw [Finset.mem_singleton] at hk
  rw [Submodule.starProjection_unit_singleton ℂ hnorm0,
    orthonormal_iff_ite.mp hardyBasis.orthonormal 0 k, ite_eq_right (Ne.symm hk), zero_smul]

/-- Orthogonal projection onto `ℂ ∙ hardyBasis 0` is a compact operator on `HardySpace`. -/
theorem isCompactOperator_span_hardyBasis_zero_starProjection :
    IsCompactOperator ((ℂ ∙ hardyBasis 0).starProjection : HardySpace →L[ℂ] HardySpace) :=
  hasFiniteRange_span_hardyBasis_zero_starProjection.isCompactOperator

/-- The compact perturbation `T_1 - (ℂ ∙ hardyBasis 0).starProjection` (= `S ∘L S†`) is Fredholm. -/
theorem isFredholm_toeplitz_toLp_one_sub_span_hardyBasis_zero_starProjection :
    ContinuousLinearMap.IsFredholm
      (toeplitz
        (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ (1 : C(UnitAddCircle, ℂ))) -
          (ℂ ∙ hardyBasis 0).starProjection) :=
  (isFredholm_toeplitz_toLp_sub_iff 1 isCompactOperator_span_hardyBasis_zero_starProjection).mpr
    fun _ => one_ne_zero

/-- The compact perturbation `T_1 - (ℂ ∙ hardyBasis 0).starProjection` has Fredholm index `0`. -/
theorem index_toeplitz_toLp_one_sub_span_hardyBasis_zero_starProjection :
    ContinuousLinearMap.index
      (toeplitz
        (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ (1 : C(UnitAddCircle, ℂ))) -
          (ℂ ∙ hardyBasis 0).starProjection) = 0 := by
  rw [index_toeplitz_toLp_sub 1 (fun _ => one_ne_zero)
    isCompactOperator_span_hardyBasis_zero_starProjection, ContinuousMap.windingNumber_one,
    neg_zero]

/-- Although `T_1 - (ℂ ∙ hardyBasis 0).starProjection` is a compact perturbation of `T_1` that is
Fredholm of index `0`, it annihilates `hardyBasis 0` and is therefore not invertible. -/
theorem not_isUnit_toeplitz_toLp_one_sub_span_hardyBasis_zero_starProjection :
    ¬ IsUnit
      (toeplitz
        (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ (1 : C(UnitAddCircle, ℂ))) -
          (ℂ ∙ hardyBasis 0).starProjection) := by
  rintro ⟨u, hu⟩
  set A := toeplitz
    (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ (1 : C(UnitAddCircle, ℂ))) -
      (ℂ ∙ hardyBasis 0).starProjection
  have hA0 : A (hardyBasis 0) = 0 := by
    simp only [A, sub_apply, toeplitz_toLp_one, ContinuousLinearMap.id_apply,
      Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self _), sub_self]
  have heq : hardyBasis 0 = 0 := by
    calc
      hardyBasis 0 = (↑u⁻¹ * (u : HardySpace →L[ℂ] HardySpace)) (hardyBasis 0) := by
        rw [Units.inv_mul, one_apply_eq_self]
      _ = (↑u⁻¹ : HardySpace →L[ℂ] HardySpace) (A (hardyBasis 0)) := by
        rw [mul_apply_eq_comp, hu]
      _ = 0 := by rw [hA0, map_zero]
  have hnorm : ‖hardyBasis 0‖ = 1 := hardyBasis.orthonormal.1 0
  simp [heq] at hnorm

end CompactPerturbation

end TauCeti

end
