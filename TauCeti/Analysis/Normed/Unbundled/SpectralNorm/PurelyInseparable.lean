/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic

import Mathlib.Algebra.Polynomial.Eval.Subring
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Trace

/-!
# Spectral norms on purely inseparable extensions

Let `K` be an ultrametric normed field, not assumed complete or nontrivially normed, and let
`M / K` be a purely inseparable algebraic extension. Every element `x ∈ M` has a positive
characteristic-power `x ^ p ^ n` in `K`, so power-multiplicativity of `spectralNorm K M` forces
`(spectralNorm K M x) ^ p ^ n = ‖a‖` where `algebraMap K M a = x ^ p ^ n`. Consequently:

* `spectralNorm K M` is multiplicative on `M`, defining a nonarchimedean real absolute value
  `TauCeti.spectralAbsoluteValue K M` and an ultrametric normed-algebra structure on
  `WithAbs (spectralAbsoluteValue K M)`.
* In any algebraic tower `K → M → N` with `M / K` purely inseparable, the spectral norm of `N`
  over `WithAbs (spectralAbsoluteValue K M)` equals its spectral norm over `K`
  (`TauCeti.spectralNorm_withAbs_spectralAbsoluteValue`).
* In any tower `K → M → N` with `M / K` purely inseparable and `N / M` finite separable, spectral
  boundedness of every `K`-linear functional transfers from `M` to `N`
  (`Module.Dual.exists_bound_spectralNorm_of_isPurelyInseparable_of_isSeparable`).

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§3.2.2 and 3.5.2.
-/

public section

namespace TauCeti

open Polynomial

section NormedField

variable {K M : Type*} [NormedField K] [IsUltrametricDist K] [Field M] [Algebra K M]

/-- On a purely inseparable extension of an ultrametric normed field, the spectral norm is
multiplicative, without completeness or nontriviality of the norm on `K`. -/
theorem spectralNorm_mul_of_isPurelyInseparable [IsPurelyInseparable K M] (x y : M) :
    spectralNorm K M (x * y) = spectralNorm K M x * spectralNorm K M y := by
  let p := ringExpChar K
  obtain ⟨m, a, ha⟩ := IsPurelyInseparable.pow_mem K p x
  obtain ⟨n, b, hb⟩ := IsPurelyInseparable.pow_mem K p y
  set q := p ^ (m + n)
  have hq : q ≠ 0 := (pow_pos (expChar_pos K p) (m + n)).ne'
  have hxq : x ^ q = algebraMap K M (a ^ p ^ n) := by
    rw [map_pow, ha, ← pow_mul, ← pow_add]
  have hyq : y ^ q = algebraMap K M (b ^ p ^ m) := by
    rw [map_pow, hb, ← pow_mul, ← pow_add, add_comm]
  have hxyq : (x * y) ^ q = algebraMap K M (a ^ p ^ n * b ^ p ^ m) := by
    rw [mul_pow, hxq, hyq, map_mul]
  refine (pow_left_inj₀ (spectralNorm_nonneg _)
    (mul_nonneg (spectralNorm_nonneg _) (spectralNorm_nonneg _)) hq).mp ?_
  rw [mul_pow, spectralNorm_pow_eq_norm_of_pow_eq_algebraMap hq hxyq,
    spectralNorm_pow_eq_norm_of_pow_eq_algebraMap hq hxq,
    spectralNorm_pow_eq_norm_of_pow_eq_algebraMap hq hyq, norm_mul]

/-- The spectral norm on a purely inseparable extension `M / K` as a real absolute value on `M`. -/
noncomputable def spectralAbsoluteValue (K M : Type*) [NormedField K] [IsUltrametricDist K]
    [Field M] [Algebra K M] [IsPurelyInseparable K M] : AbsoluteValue M ℝ where
  toFun := spectralNorm K M
  map_mul' := spectralNorm_mul_of_isPurelyInseparable
  nonneg' := spectralNorm_nonneg
  eq_zero' x := ⟨fun hx ↦ eq_zero_of_map_spectralNorm_eq_zero hx
    (Algebra.IsAlgebraic.isAlgebraic x), fun hx ↦ hx ▸ spectralNorm_zero⟩
  add_le' _ _ := isNonarchimedean_spectralNorm.add_le spectralNorm_nonneg

@[simp]
theorem spectralAbsoluteValue_apply [IsPurelyInseparable K M] (x : M) :
    spectralAbsoluteValue K M x = spectralNorm K M x :=
  (rfl)

theorem isNonarchimedean_spectralAbsoluteValue (K M : Type*) [NormedField K]
    [IsUltrametricDist K] [Field M] [Algebra K M] [IsPurelyInseparable K M] :
    IsNonarchimedean (spectralAbsoluteValue K M) :=
  isNonarchimedean_spectralNorm

instance [IsPurelyInseparable K M] : IsUltrametricDist (WithAbs (spectralAbsoluteValue K M)) :=
  (isNonarchimedean_spectralAbsoluteValue K M).isUltrametricDist_withAbs

private theorem norm_algebraMap_withAbs_spectralAbsoluteValue [IsPurelyInseparable K M] (a : K) :
    ‖algebraMap K (WithAbs (spectralAbsoluteValue K M)) a‖ = ‖a‖ := by
  rw [WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq, spectralAbsoluteValue_apply,
    spectralNorm_extends]

noncomputable instance [IsPurelyInseparable K M] :
    NormedAlgebra K (WithAbs (spectralAbsoluteValue K M)) where
  norm_smul_le a x := by
    rw [Algebra.smul_def, norm_mul, norm_algebraMap_withAbs_spectralAbsoluteValue]

end NormedField

/-- **Tower invariance of the spectral norm across a purely inseparable subextension.**
Let `K → M → N` be a tower of fields with `M / K` purely inseparable and `N / M` algebraic.
Equipping `M` with `spectralAbsoluteValue K M` through `WithAbs`, the spectral norm of `N` over
`M` coincides with its spectral norm over `K`. -/
theorem spectralNorm_withAbs_spectralAbsoluteValue {K M N : Type*} [NormedField K]
    [IsUltrametricDist K] [Field M] [Algebra K M] [IsPurelyInseparable K M]
    [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N] [Algebra.IsAlgebraic M N]
    (y : N) :
    spectralNorm (WithAbs (spectralAbsoluteValue K M)) N y = spectralNorm K N y := by
  let M' := WithAbs (spectralAbsoluteValue K M)
  have : Algebra.IsAlgebraic K N := Algebra.IsAlgebraic.trans K M N
  have : Algebra.IsAlgebraic M' N :=
    Algebra.IsAlgebraic.ringHom_of_comp_eq (R := M) (A := N)
      (WithAbs.equiv (spectralAbsoluteValue K M)).symm.toRingHom (RingHom.id N)
      (WithAbs.equiv _).symm.injective Function.surjective_id
      (by
        ext
        simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
          Function.comp_apply, WithAbs.equiv_symm_apply, RingHom.coe_id, id_eq]
        rw [WithAbs.algebraMap_left_apply, WithAbs.ofAbs_toAbs])
  refine le_antisymm ?_ ?_
  · -- `minpoly K y`, mapped to `M'[X]`, is monic, annihilates `y`, and keeps its `spectralValue`.
    set P := minpoly K y
    have hP : P.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral y)
    have hroot : aeval y (P.map (algebraMap K M')) = 0 := by
      rw [aeval_map_algebraMap, minpoly.aeval]
    calc spectralNorm M' N y = spectralAlgNorm M' N y := (spectralAlgNorm_def y).symm
      _ ≤ spectralValue (P.map (algebraMap K M')) :=
          norm_root_le_spectralValue spectralAlgNorm_isPowMul isNonarchimedean_spectralNorm
            (hP.map _) hroot
      _ = spectralValue P :=
          (algebraMap K M').spectralValue_map_of_norm_eq
            norm_algebraMap_withAbs_spectralAbsoluteValue P
      _ = spectralNorm K N y := by rw [spectralNorm]
  · -- Raise `Q = minpoly M' y` to a `p ^ n`-th power whose coefficients descend to `K`.
    classical
    set Q := minpoly M' y
    have hQ : Q.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral y)
    let p := ringExpChar K
    have : ExpChar M' p := expChar_of_injective_algebraMap (algebraMap K M').injective p
    have hex (i : ℕ) : ∃ m : ℕ, (Q.coeff i) ^ p ^ m ∈ (algebraMap K M').range := by
      obtain ⟨m, a, ha⟩ := IsPurelyInseparable.pow_mem K p (Q.coeff i).ofAbs
      refine ⟨m, a, ?_⟩
      apply WithAbs.ofAbs_injective
      rw [WithAbs.algebraMap_right_apply, WithAbs.ofAbs_toAbs, WithAbs.ofAbs_pow]
      exact ha
    let m_fn (i : ℕ) : ℕ := (hex i).choose
    set n : ℕ := Q.support.sup m_fn
    set q : ℕ := p ^ n
    have hq : 0 < q := pow_pos (expChar_pos K p) n
    have hmem (i : ℕ) : Q.coeff i ^ q ∈ (algebraMap K M').range := by
      by_cases hi : i ∈ Q.support
      · obtain ⟨a, ha⟩ := (hex i).choose_spec
        have hle : m_fn i ≤ n := Finset.le_sup hi
        refine ⟨a ^ p ^ (n - m_fn i), ?_⟩
        rw [map_pow, ha, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hle]
      · rw [notMem_support_iff.mp hi, zero_pow hq.ne']
        exact ⟨0, map_zero _⟩
    obtain ⟨Q₀, hQ₀⟩ : Q.map (iterateFrobenius M' p n) ∈ (mapRingHom (algebraMap K M')).range :=
      (mem_map_range (algebraMap K M')).mpr fun i ↦ by
        rw [coeff_map, iterateFrobenius_def]
        exact hmem i
    rw [coe_mapRingHom] at hQ₀
    set R : K[X] := Polynomial.expand K q Q₀
    have hR_map : R.map (algebraMap K M') = Q ^ q := by
      calc R.map (algebraMap K M')
          = Polynomial.expand M' q (Q₀.map (algebraMap K M')) := map_expand
        _ = Polynomial.expand M' q (Q.map (iterateFrobenius M' p n)) := by rw [hQ₀]
        _ = (Polynomial.expand M' q Q).map (iterateFrobenius M' p n) := map_expand.symm
        _ = Q ^ q := map_iterateFrobenius_expand p Q n
    have hR_monic : R.Monic := by
      refine monic_of_injective (algebraMap K M').injective ?_
      rw [hR_map]
      exact hQ.pow q
    have hR_root : aeval y R = 0 := by
      rw [← aeval_map_algebraMap M' y R, hR_map, map_pow, minpoly.aeval, zero_pow hq.ne']
    calc spectralNorm K N y = spectralAlgNorm K N y := (spectralAlgNorm_def y).symm
      _ ≤ spectralValue R :=
          norm_root_le_spectralValue spectralAlgNorm_isPowMul isNonarchimedean_spectralNorm
            hR_monic hR_root
      _ = spectralValue (Q.map (iterateFrobenius M' p n)) ^ (1 / (q : ℝ)) := by
          rw [Q₀.spectralValue_expand hq.ne', ← hQ₀,
            (algebraMap K M').spectralValue_map_of_norm_eq
              norm_algebraMap_withAbs_spectralAbsoluteValue]
      _ ≤ (spectralValue Q ^ q) ^ (1 / (q : ℝ)) :=
          Real.rpow_le_rpow (spectralValue_nonneg _)
            (Q.spectralValue_map_iterateFrobenius_le p n) (by positivity)
      _ = spectralValue Q := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (spectralValue_nonneg Q),
            mul_one_div_cancel (Nat.cast_ne_zero.mpr hq.ne'), Real.rpow_one]
      _ = spectralNorm M' N y := by rw [spectralNorm]

end TauCeti

namespace Module.Dual

/-- In a tower `K → M → N` over an ultrametric normed field `K` with `M / K` purely inseparable
and `N / M` finite separable, if every `K`-linear functional on `M` is bounded by
`spectralNorm K M`, then every `K`-linear functional on `N` is bounded by `spectralNorm K N`. -/
theorem exists_bound_spectralNorm_of_isPurelyInseparable_of_isSeparable {K M N : Type*}
    [NormedField K] [IsUltrametricDist K]
    [Field M] [Algebra K M] [IsPurelyInseparable K M]
    [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]
    [FiniteDimensional M N] [Algebra.IsSeparable M N]
    (hM : ∀ ψ : Module.Dual K M, ∃ C : ℝ, ∀ x, ‖ψ x‖ ≤ C * spectralNorm K M x)
    (φ : Module.Dual K N) :
    ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * spectralNorm K N y := by
  let M' := WithAbs (TauCeti.spectralAbsoluteValue K M)
  let b := Module.finBasis M' N
  choose C₁ hC₁ using fun i ↦ Module.Dual.exists_bound_spectralNorm_of_isSeparable (b.coord i)
  let ψ (i : Fin (Module.finrank M' N)) : Module.Dual K M :=
    { toFun := fun x ↦ φ (x • b i)
      map_add' := fun x y ↦ by rw [add_smul, map_add]
      map_smul' := fun c x ↦ by rw [smul_assoc, map_smul, RingHom.id_apply] }
  choose C₂ hC₂ using fun i ↦ hM (ψ i)
  let D₂ (i : Fin (Module.finrank M' N)) : ℝ := max (C₂ i) 0
  refine ⟨∑ i, D₂ i * C₁ i, fun y ↦ ?_⟩
  have hy : φ y = ∑ i, ψ i (b.repr y i).ofAbs := by
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [WithAbs.smul_left_def]
  calc ‖φ y‖ = ‖∑ i, ψ i (b.repr y i).ofAbs‖ := by rw [hy]
    _ ≤ ∑ i, ‖ψ i (b.repr y i).ofAbs‖ := norm_sum_le _ _
    _ ≤ ∑ i, D₂ i * spectralNorm K M (b.repr y i).ofAbs :=
        Finset.sum_le_sum fun i _ ↦ (hC₂ i _).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (spectralNorm_nonneg _))
    _ = ∑ i, D₂ i * ‖b.coord i y‖ := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Module.Basis.coord_apply, WithAbs.norm_eq_apply_ofAbs,
          TauCeti.spectralAbsoluteValue_apply]
    _ ≤ ∑ i, D₂ i * (C₁ i * spectralNorm M' N y) :=
        Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_left (hC₁ i y) (le_max_right _ _)
    _ = (∑ i, D₂ i * C₁ i) * spectralNorm K N y := by
        rw [TauCeti.spectralNorm_withAbs_spectralAbsoluteValue (K := K) (M := M) y,
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ (mul_assoc _ _ _).symm

end Module.Dual
