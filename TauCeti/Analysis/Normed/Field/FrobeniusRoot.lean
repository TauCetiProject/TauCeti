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

/-!
# The Frobenius-root normed algebra of an ultrametric field

For an ultrametric normed field `K` of exponential characteristic `p` and `e : ℕ`, adjoining
`p ^ e`-th roots of all scalars in `K` produces a field isomorphic to `K` itself via the `e`-fold
Frobenius `a ↦ a ^ p ^ e`. Equipping that copy of `K` with the norm `‖x‖ ^ (p ^ e)⁻¹` makes the
`e`-fold Frobenius an isometric `K`-algebra structure: every `a : K` has `p ^ e`-th root `root a`
of norm `‖a‖ ^ (p ^ e)⁻¹`, while `‖algebraMap K (FrobeniusRoot K p e) a‖ = ‖a‖`.

Wrapping `WithAbs` in a dedicated one-field structure avoids an `Algebra K` diamond with the
untwisted `K`-algebra structure that `WithAbs` inherits from `Algebra.id K`.

## Main definitions

* `TauCeti.FrobeniusRoot K p e`: a copy of `K` carrying the norm `‖x‖ ^ (p ^ e)⁻¹` and the
  `K`-algebra structure given by `iterateFrobenius K p e`.
* `TauCeti.FrobeniusRoot.ringEquiv`: the underlying ring isomorphism `FrobeniusRoot K p e ≃+* K`.
* `TauCeti.FrobeniusRoot.root`: the inverse ring homomorphism `K →+* FrobeniusRoot K p e` sending
  each scalar `a` to its `p ^ e`-th root over `K`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §3.5.3.
-/

public section

namespace TauCeti

/-- The real absolute value `x ↦ ‖x‖ ^ (p ^ e)⁻¹` on an ultrametric normed field `K`. -/
noncomputable def frobeniusRootAbs (K : Type*) [NormedField K] [IsUltrametricDist K]
    (p : ℕ) [ExpChar K p] (e : ℕ) : AbsoluteValue K ℝ :=
  (IsAbsoluteValue.toAbsoluteValue (norm : K → ℝ)).nonarchRpow
    (by
      rw [show ⇑(IsAbsoluteValue.toAbsoluteValue (norm : K → ℝ)) = norm from rfl]
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
