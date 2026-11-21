/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Analysis.Normed.Field.TransferInstance
public import Mathlib.Analysis.Normed.Field.WithAbs
public import TauCeti.Analysis.AbsoluteValue.Nonarchimedean

import Mathlib.Algebra.CharP.Algebra
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Analysis.Normed.Module.Bases.CountableType

/-!
# The Frobenius-root normed algebra of an ultrametric field

For an ultrametric normed field `K` of exponential characteristic `p` and `e : ℕ`, adjoining
`p ^ e`-th roots of all scalars in `K` produces a field isomorphic to `K` itself via the `e`-fold
Frobenius `a ↦ a ^ p ^ e`. Equipping that copy of `K` with the norm `‖x‖ ^ (p ^ e)⁻¹` makes the
`e`-fold Frobenius an isometric `K`-algebra structure: every `a : K` has `p ^ e`-th root `root a`
of norm `‖a‖ ^ (p ^ e)⁻¹`, while `‖algebraMap K (FrobeniusRoot K p e) a‖ = ‖a‖`.

Wrapping `WithAbs` in a dedicated one-field structure avoids an `Algebra K` diamond with the
untwisted `K`-algebra structure that `WithAbs` inherits from `Algebra.id K`.

## Main definitions and results

* `TauCeti.FrobeniusRoot K p e`: a copy of `K` carrying the norm `‖x‖ ^ (p ^ e)⁻¹` and the
  `K`-algebra structure given by `iterateFrobenius K p e`.
* `TauCeti.FrobeniusRoot.ringEquiv`: the underlying ring isomorphism `FrobeniusRoot K p e ≃+* K`.
* `TauCeti.FrobeniusRoot.root`: the inverse ring homomorphism `K →+* FrobeniusRoot K p e` sending
  each scalar `a` to its `p ^ e`-th root over `K`.
* `TauCeti.FrobeniusRoot.exists_dual_norm_le_and_ne_zero_span_of_countable`: over a complete
  ultrametric normed field `K` (nontrivially or trivially normed), norm-bounded `K`-linear
  functionals separate nonzero elements on the `K`-span of any countable subset of
  `FrobeniusRoot K p e`.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §3.5.3.
-/

public section

namespace TauCeti

/-- The real absolute value `x ↦ ‖x‖ ^ (p ^ e)⁻¹` on an ultrametric normed field `K`. -/
noncomputable def frobeniusRootAbs (K : Type*) [NormedField K] [IsUltrametricDist K]
    (p : ℕ) [ExpChar K p] (e : ℕ) : AbsoluteValue K ℝ :=
  (IsAbsoluteValue.toAbsoluteValue (norm : K → ℝ)).nonarchRpow
    (by
      rw [funext (IsAbsoluteValue.toAbsoluteValue_apply (norm : K → ℝ))]
      exact IsUltrametricDist.isNonarchimedean_norm)
    (inv_pos.mpr (Nat.cast_pos.mpr (pow_pos (expChar_pos K p) e)))

@[simp] theorem frobeniusRootAbs_apply {K : Type*} [NormedField K] [IsUltrametricDist K]
    (p : ℕ) [ExpChar K p] (e : ℕ) (x : K) :
    frobeniusRootAbs K p e x = ‖x‖ ^ ((p ^ e : ℕ) : ℝ)⁻¹ := by
  rw [frobeniusRootAbs, AbsoluteValue.nonarchRpow_apply, IsAbsoluteValue.toAbsoluteValue_apply]

theorem isNonarchimedean_frobeniusRootAbs (K : Type*) [NormedField K] [IsUltrametricDist K]
    (p : ℕ) [ExpChar K p] (e : ℕ) : IsNonarchimedean (frobeniusRootAbs K p e) := by
  unfold frobeniusRootAbs
  exact AbsoluteValue.isNonarchimedean_nonarchRpow _ _ _

/-- A copy of an ultrametric normed field `K` of exponential characteristic `p`, equipped with
the norm `‖x‖ ^ (p ^ e)⁻¹` and the `K`-algebra structure induced by `iterateFrobenius K p e`. -/
structure FrobeniusRoot (K : Type*) [NormedField K] [IsUltrametricDist K]
    (p : ℕ) [ExpChar K p] (e : ℕ) where
  /-- Wraps an element of `WithAbs (frobeniusRootAbs K p e)` into `FrobeniusRoot K p e`. -/
  ofWithAbs ::
  /-- Unwraps `FrobeniusRoot K p e` into `WithAbs (frobeniusRootAbs K p e)`. -/
  toWithAbs : WithAbs (frobeniusRootAbs K p e)

namespace FrobeniusRoot

section NormedField

variable (K : Type*) [NormedField K] [IsUltrametricDist K] (p : ℕ) [ExpChar K p] (e : ℕ)

/-- The canonical bijection between `FrobeniusRoot K p e` and
`WithAbs (frobeniusRootAbs K p e)`. -/
noncomputable def equivWithAbs : FrobeniusRoot K p e ≃ WithAbs (frobeniusRootAbs K p e) :=
  ⟨toWithAbs, ofWithAbs, fun _ ↦ rfl, fun _ ↦ rfl⟩

noncomputable instance instNormedField : NormedField (FrobeniusRoot K p e) :=
  fast_instance% (equivWithAbs K p e).normedField

/-- The underlying ring isomorphism `FrobeniusRoot K p e ≃+* K` forgetting the twisted
`K`-algebra structure and rescaled norm. -/
noncomputable def ringEquiv : FrobeniusRoot K p e ≃+* K :=
  (equivWithAbs K p e).ringEquiv.trans (WithAbs.equiv (frobeniusRootAbs K p e))

/-- The ring homomorphism `K →+* FrobeniusRoot K p e` sending `a` to its `p ^ e`-th root over
`K`. -/
noncomputable def root : K →+* FrobeniusRoot K p e := (ringEquiv K p e).symm.toRingHom

/-- The underlying element of `K`, as a ring homomorphism `FrobeniusRoot K p e →+* K`. -/
noncomputable def val : FrobeniusRoot K p e →+* K := (ringEquiv K p e).toRingHom

variable {K p e}

@[simp] theorem ringEquiv_apply (x : FrobeniusRoot K p e) : ringEquiv K p e x = val K p e x := (rfl)

@[simp] theorem ringEquiv_symm_apply (a : K) : (ringEquiv K p e).symm a = root K p e a := (rfl)

@[simp] theorem val_root (a : K) : val K p e (root K p e a) = a :=
  (ringEquiv K p e).apply_symm_apply a

@[simp] theorem root_val (x : FrobeniusRoot K p e) : root K p e (val K p e x) = x :=
  (ringEquiv K p e).symm_apply_apply x

theorem root_injective : Function.Injective (root K p e) := (ringEquiv K p e).symm.injective

theorem val_injective : Function.Injective (val K p e) := (ringEquiv K p e).injective

@[simp] theorem norm_toWithAbs (x : FrobeniusRoot K p e) : ‖x.toWithAbs‖ = ‖x‖ := (rfl)

@[simp] theorem ofAbs_toWithAbs (x : FrobeniusRoot K p e) : x.toWithAbs.ofAbs = val K p e x := (rfl)

theorem norm_def (x : FrobeniusRoot K p e) : ‖x‖ = ‖val K p e x‖ ^ ((p ^ e : ℕ) : ℝ)⁻¹ := by
  rw [← norm_toWithAbs, WithAbs.norm_eq_apply_ofAbs, ofAbs_toWithAbs, frobeniusRootAbs_apply]

@[simp] theorem norm_root (a : K) : ‖root K p e a‖ = ‖a‖ ^ ((p ^ e : ℕ) : ℝ)⁻¹ := by
  rw [norm_def, val_root]

instance : IsUltrametricDist (FrobeniusRoot K p e) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    simpa only [norm_def, map_add, ← frobeniusRootAbs_apply (K := K) p e] using
      isNonarchimedean_frobeniusRootAbs K p e (val K p e x) (val K p e y)

noncomputable instance : Algebra K (FrobeniusRoot K p e) :=
  RingHom.toAlgebra ((root K p e).comp (iterateFrobenius K p e))

instance : ExpChar (FrobeniusRoot K p e) p :=
  expChar_of_injective_algebraMap (algebraMap K (FrobeniusRoot K p e)).injective p

theorem algebraMap_apply (a : K) : algebraMap K (FrobeniusRoot K p e) a = root K p e (a ^ p ^ e) :=
  (rfl)

/-- `root K p e a` is a `p ^ e`-th root of `algebraMap K (FrobeniusRoot K p e) a`. -/
@[simp] theorem root_pow_expChar_pow (a : K) :
    root K p e a ^ p ^ e = algebraMap K (FrobeniusRoot K p e) a := by
  rw [algebraMap_apply, ← map_pow]

/-- The `e`-fold Frobenius `K`-algebra map `K → FrobeniusRoot K p e` is norm-preserving. -/
theorem norm_algebraMap (a : K) :
    ‖algebraMap K (FrobeniusRoot K p e) a‖ = ‖a‖ := by
  have hq : ((p ^ e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (pow_pos (expChar_pos K p) e).ne'
  rw [algebraMap_apply, norm_root, norm_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (norm_nonneg a), mul_inv_cancel₀ hq, Real.rpow_one]

noncomputable instance : NormedAlgebra K (FrobeniusRoot K p e) where
  norm_smul_le a x := by rw [Algebra.smul_def, norm_mul, norm_algebraMap]

/-- `root K p e` is a uniform inducing map from `K` to `FrobeniusRoot K p e`, since distances are
raised to the positive exponent `(p ^ e)⁻¹`. -/
theorem isUniformInducing_root : IsUniformInducing (root K p e) := by
  have hq : (0 : ℝ) < (p ^ e : ℕ) := Nat.cast_pos.mpr (pow_pos (expChar_pos K p) e)
  have hq_inv : (0 : ℝ) < ((p ^ e : ℕ) : ℝ)⁻¹ := inv_pos.mpr hq
  rw [Metric.isUniformInducing_iff, Metric.uniformContinuous_iff]
  refine ⟨fun ε hε ↦ ⟨ε ^ ((p ^ e : ℕ) : ℝ), Real.rpow_pos_of_pos hε _, fun {a b} hab ↦ ?_⟩,
    fun δ hδ ↦ ⟨δ ^ ((p ^ e : ℕ) : ℝ)⁻¹, Real.rpow_pos_of_pos hδ _, fun {a b} hab ↦ ?_⟩⟩
  · rw [dist_eq_norm, ← map_sub, norm_root, ← dist_eq_norm]
    calc dist a b ^ ((p ^ e : ℕ) : ℝ)⁻¹
        < (ε ^ ((p ^ e : ℕ) : ℝ)) ^ ((p ^ e : ℕ) : ℝ)⁻¹ :=
          Real.rpow_lt_rpow dist_nonneg hab hq_inv
      _ = ε := by rw [← Real.rpow_mul hε.le, mul_inv_cancel₀ hq.ne', Real.rpow_one]
  · rw [dist_eq_norm, ← map_sub, norm_root, ← dist_eq_norm] at hab
    exact (Real.rpow_lt_rpow_iff dist_nonneg hδ.le hq_inv).mp hab

instance [CompleteSpace K] : CompleteSpace (FrobeniusRoot K p e) :=
  ((isUniformInducing_root (K := K) (p := p) (e := e)).completeSpace_congr
    (ringEquiv K p e).symm.surjective).mp inferInstance

/-- Over a complete ultrametric normed field `K` (nontrivially or trivially normed), norm-bounded
`K`-linear functionals separate nonzero elements on the `K`-span of any countable subset of
`FrobeniusRoot K p e` (Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §3.5.3). -/
theorem exists_dual_norm_le_and_ne_zero_span_of_countable [CompleteSpace K]
    {S : Set (FrobeniusRoot K p e)} (hS : S.Countable)
    {x : Submodule.span K S} (hx : x ≠ 0) :
    ∃ (f : Submodule.span K S →ₗ[K] K) (C : ℝ),
      0 ≤ C ∧ (∀ v, ‖f v‖ ≤ C * ‖v‖) ∧ f x ≠ 0 := by
  by_cases hnt : ∃ a : K, 1 < ‖a‖
  · let _ : NontriviallyNormedField K :=
      { __ := (inferInstance : NormedField K), non_trivial := hnt }
    have : SeparatingDual K (Submodule.span K S) := Submodule.separatingDual_span_of_countable hS
    obtain ⟨f, hfx⟩ := SeparatingDual.exists_ne_zero (R := K) hx
    exact ⟨f.toLinearMap, ‖f‖, norm_nonneg f, f.le_opNorm, hfx⟩
  · push Not at hnt
    have ha_norm {a : K} (ha : a ≠ 0) : ‖a‖ = 1 := by
      refine le_antisymm (hnt a) ?_
      have h1 : (1 : ℝ) = ‖a‖ * ‖a⁻¹‖ := by rw [← norm_mul, mul_inv_cancel₀ ha, norm_one]
      nlinarith [hnt a⁻¹, norm_nonneg a]
    have hv_norm {v : Submodule.span K S} (hv : v ≠ 0) : ‖v‖ = 1 := by
      have hval : val K p e v.val ≠ 0 :=
        (map_ne_zero_iff _ val_injective).mpr (Subtype.coe_ne_coe.mpr hv)
      rw [← Submodule.norm_coe, norm_def, ha_norm hval, Real.one_rpow]
    obtain ⟨f, hfx⟩ := Module.Projective.exists_dual_ne_zero K hx
    refine ⟨f, 1, zero_le_one, fun v ↦ ?_, hfx⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · rw [hv_norm hv, mul_one]
      exact hnt (f v)

end NormedField

noncomputable instance {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    (p : ℕ) [ExpChar K p] (e : ℕ) :
    NontriviallyNormedField (FrobeniusRoot K p e) where
  toNormedField := instNormedField K p e
  non_trivial :=
    let ⟨a, ha⟩ := NontriviallyNormedField.non_trivial (α := K)
    ⟨algebraMap K (FrobeniusRoot K p e) a, ha.trans_eq (norm_algebraMap a).symm⟩

end FrobeniusRoot

end TauCeti
