/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NormResidueSymbol.Basic
public import TauCeti.NumberTheory.LocalField.Units.Decomposition
import TauCeti.Algebra.CharP.LocalRing
import TauCeti.FieldTheory.Kummer.Degree
import TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified
import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
import TauCeti.NumberTheory.LocalField.RootsOfUnity.Torsion

/-!
# The tame formula for the norm-residue symbol with a unit radical

Let `K` be a nonarchimedean local field containing the `n`-th roots of unity, where `n` is prime
to the residue characteristic `p`, and let `q` be the cardinality of the residue field. Then
`n ∣ q - 1`. This file computes the norm-residue symbol `(a, b) = Art_K(a)(ⁿ√b) / ⁿ√b` of
`TauCeti.normResidueSymbol` whenever the radical argument `b` is a unit of `𝒪[K]`:

`(a, b) = ω(b) ^ (v(a) · (q - 1) / n)`,

where `v` is the normalized valuation and `ω(b)` is the Teichmüller representative of `b`, the
`(q - 1)`-st root of unity with the same residue as `b`. Equivalently, `(a, b)` is the unique
`n`-th root of unity congruent to `b ^ (v(a) · (q - 1) / n)` modulo the maximal ideal. In
particular two units pair trivially, and a uniformizer `π` pairs with a unit `b` to the root of
unity whose residue is `r ^ ((q - 1) / n)`, the `n`-th power residue of the residue `r` of `b`.

The reason is that every `n`-th root of a unit lies in the maximal unramified extension. There the
Artin symbol of a unit acts trivially, because it lies in inertia, while the Artin symbol of a
uniformizer acts as arithmetic Frobenius, which raises roots of unity of order prime to `p` to the
`q`-th power. Writing `b = ω(b) · w ^ n` with `w` a principal unit reduces the computation to an
`n`-th root `z` of `ω(b)`, a root of unity of order prime to `p`, for which
`Frob(z) / z = z ^ (q - 1) = ω(b) ^ ((q - 1) / n)`.

These are the values of the symbol that identify it with the `n`-th power residue symbol and the
tame symbol at a place prime to `n`. The remaining values, with both arguments non-units, follow
from these and the Steinberg relation.

## Main results

* `TauCeti.normResidueSymbol_eq_one_of_mem_unitFiltration_zero`: `(u, b) = 1` for units `u, b`.
* `TauCeti.coe_normResidueSymbol_uniformizer`: `(π, b) = ω(b) ^ ((q - 1) / n)` for a
  uniformizer `π` and a unit `b`.
* `TauCeti.coe_normResidueSymbol_of_mem_unitFiltration_zero`:
  `(a, b) = ω(b) ^ (v(a) · (q - 1) / n)` for every `a` and every unit `b`.
* `TauCeti.normResidueSymbol_mul_inv_zpow_mem_unitFiltration_one`: the tame congruence
  `(a, b) ≡ b ^ (v(a) · (q - 1) / n)` modulo the maximal ideal, read in `U(K,1)`.
* `TauCeti.normResidueSymbol_eq_iff_mul_inv_zpow_mem_unitFiltration_one`: this congruence
  characterizes `(a, b)` among the `n`-th roots of unity.

## References

* J.-P. Serre, *Local Fields*, Chapter XIV, §3, Proposition 8.
* J. S. Milne, *Class Field Theory*, Chapter III, §4, Theorem 4.4 and Remark 4.5.

Both sources state the formula for arbitrary arguments, each in its own orientation of the symbol;
`TauCeti.normResidueSymbol` lets the first argument act through the Artin map.
-/

public section

noncomputable section

open IsLocalRing ValuativeRel

namespace TauCeti

open ClassFieldTheory

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

/-- **Units pair trivially at a tame exponent.** If `n` is prime to the residue characteristic and
`u, b` are units of `𝒪[K]`, then `(u, b) = 1`. -/
theorem normResidueSymbol_eq_one_of_mem_unitFiltration_zero (hp : ¬ ringChar 𝓀[K] ∣ n)
    {u b : Kˣ} (hu : u ∈ unitFiltration K 0) (hb : b ∈ unitFiltration K 0) :
    normResidueSymbol K n u b = 1 := by
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (α := Field.absoluteGaloisGroup K) (artinMap K u)
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (b : K))
    (Nat.pos_of_neZero n)
  -- `σ` lies in inertia, which is the kernel of restriction to `K^{ur}`, and `β ∈ K^{ur}`.
  have hσ1 := mem_inertiaSubgroup_of_mk_eq_artinMap K u ((mem_unitFiltration_zero u).1 hu) σ hσ
  rw [← ker_restrictMaximalUnramifiedHom, MonoidHom.mem_ker] at hσ1
  have hfix := congrArg Subtype.val (DFunLike.congr_fun hσ1
    ⟨β, mem_maximalUnramifiedExtension_of_pow_eq hp hb hβ⟩)
  rw [restrictMaximalUnramifiedHom_coe_apply, normResidueSymbol_spec u b σ hσ hβ] at hfix
  apply Subtype.ext
  apply Units.ext
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [OneMemClass.coe_one, Units.val_one, map_one]
  exact mul_eq_right₀ (ne_zero_of_pow_eq_algebraMap hβ) |>.1 hfix

/-- **The tame formula at a uniformizer.** If `n` is prime to the residue characteristic, `π` is a
uniformizer and `b` is a unit of `𝒪[K]`, then `(π, b) = ω(b) ^ ((q - 1) / n)`, where `ω(b)` is the
Teichmüller representative of `b` and `q` is the cardinality of the residue field. -/
theorem coe_normResidueSymbol_uniformizer (hp : ¬ ringChar 𝓀[K] ∣ n) {π b : Kˣ}
    (hπ : IsUniformizer K π) (hb : b ∈ unitFiltration K 0) :
    (normResidueSymbol K n π b : Kˣ) =
      ((unitFiltrationZeroEquivProd K ⟨b, hb⟩).1 : Kˣ) ^ ((Nat.card 𝓀[K] - 1) / n) := by
  set q := Nat.card 𝓀[K]
  set y := unitFiltrationZeroEquivProd K ⟨b, hb⟩
  set ω : Kˣ := (y.1 : Kˣ)
  have hn : IsUnit (n : 𝒪[K]) := isUnit_natCast_iff_not_dvd.2 hp
  -- The principal-unit component of `b` is an `n`-th power, so `(π, b) = (π, ω)`.
  obtain ⟨w, hw⟩ := unitFiltration_one_le_range_powMonoidHom_of_isUnit hn y.2.property
  have hbω : b = ω * w ^ n := by
    rw [← powMonoidHom_apply, hw, coe_unitFiltrationZeroEquivProd_apply_snd, mul_comm b,
      mul_inv_cancel_left]
  rw [hbω, normResidueSymbol_mul_right, normResidueSymbol_pow_right_eq_one, mul_one]
  -- An `n`-th root `z` of `ω` is a root of unity of order `n (q - 1)`, prime to `p`.
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (α := Field.absoluteGaloisGroup K) (artinMap K π)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (ω : K))
    (Nat.pos_of_neZero n)
  have hωq : (ω : K) ^ (q - 1) = 1 := by
    simpa using congrArg Units.val ((mem_rootsOfUnity _ _).1 y.1.property)
  have hzm : z ^ (n * (q - 1)) = 1 := by rw [pow_mul, hz, ← map_pow, hωq, map_one]
  have hcop : (n * (q - 1)).Coprime (ringChar 𝓀[K]) := by
    have hq := isUnit_natCast_natCard_pow_sub_one K one_ne_zero
    rw [pow_one, isUnit_natCast_iff_not_dvd] at hq
    have hpr := CharP.prime_ringChar 𝓀[K]
    exact Nat.Coprime.mul_left (hpr.coprime_iff_not_dvd.2 hp).symm
      (hpr.coprime_iff_not_dvd.2 hq).symm
  -- The Artin symbol of `π` acts on `z` as arithmetic Frobenius, `z ↦ z ^ q`.
  have hσz := (isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer K hπ σ hσ).apply_of_pow_eq_one
    hcop hzm
  rw [normResidueSymbol_spec π ω σ hσ hz] at hσz
  obtain ⟨d, hd⟩ := dvd_natCard_residueField_sub_one hn
  apply Units.ext
  apply (algebraMap K (AlgebraicClosure K)).injective
  calc algebraMap K (AlgebraicClosure K) ((normResidueSymbol K n π ω : Kˣ) : K) = z ^ (q - 1) := by
        refine mul_right_cancel₀ (ne_zero_of_pow_eq_algebraMap hz) ?_
        rw [hσz, ← pow_succ, Nat.sub_add_cancel (Nat.card_pos (α := 𝓀[K]))]
    _ = algebraMap K (AlgebraicClosure K) ((ω ^ ((q - 1) / n) : Kˣ) : K) := by
        rw [hd, Nat.mul_div_cancel_left _ (Nat.pos_of_neZero n), pow_mul, hz,
          Units.val_pow_eq_pow_val, map_pow]

/-- **The tame formula with a unit radical.** If `n` is prime to the residue characteristic and
`b` is a unit of `𝒪[K]`, then `(a, b) = ω(b) ^ (v(a) · (q - 1) / n)` for every `a ∈ Kˣ`, where
`v` is the normalized valuation, `ω(b)` is the Teichmüller representative of `b` and `q` is the
cardinality of the residue field. -/
theorem coe_normResidueSymbol_of_mem_unitFiltration_zero (hp : ¬ ringChar 𝓀[K] ∣ n)
    (a : Kˣ) {b : Kˣ} (hb : b ∈ unitFiltration K 0) :
    (normResidueSymbol K n a b : Kˣ) =
      ((unitFiltrationZeroEquivProd K ⟨b, hb⟩).1 : Kˣ) ^
        ((normalizedValuation K a).toAdd * (((Nat.card 𝓀[K] - 1) / n : ℕ) : ℤ)) := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer (K := K)
  set k := (normalizedValuation K a).toAdd
  -- Write `a = π ^ k u` with `u` a unit; the symbol is multiplicative in its Artin argument.
  have hu : a * π ^ (-k) ∈ unitFiltration K 0 :=
    mul_zpow_neg_mem_unitFiltration_zero ((isUniformizer_def π).1 hπ) a
  let f : Kˣ →* rootsOfUnity n K :=
    MonoidHom.mk' (fun x ↦ normResidueSymbol K n x b) fun x y ↦ normResidueSymbol_mul_left x y b
  have ha : f a = f π ^ k * f (a * π ^ (-k)) := by
    rw [← map_zpow, ← map_mul, mul_left_comm, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  have hfa : normResidueSymbol K n a b = normResidueSymbol K n π b ^ k := by
    simpa only [f, MonoidHom.mk'_apply,
      normResidueSymbol_eq_one_of_mem_unitFiltration_zero hp hu hb, mul_one] using ha
  rw [hfa, SubgroupClass.coe_zpow, coe_normResidueSymbol_uniformizer hp hπ hb, ← zpow_natCast,
    ← zpow_mul, mul_comm]

/-- **The tame congruence with a unit radical.** If `n` is prime to the residue characteristic and
`b` is a unit of `𝒪[K]`, then `(a, b) ≡ b ^ (v(a) · (q - 1) / n)` modulo the maximal ideal: their
quotient is a principal unit. -/
theorem normResidueSymbol_mul_inv_zpow_mem_unitFiltration_one (hp : ¬ ringChar 𝓀[K] ∣ n)
    (a : Kˣ) {b : Kˣ} (hb : b ∈ unitFiltration K 0) :
    (normResidueSymbol K n a b : Kˣ) *
        (b ^ ((normalizedValuation K a).toAdd * (((Nat.card 𝓀[K] - 1) / n : ℕ) : ℤ)))⁻¹ ∈
      unitFiltration K 1 := by
  set y := unitFiltrationZeroEquivProd K ⟨b, hb⟩
  -- `ω(b) b⁻¹` is the inverse of the principal-unit component of `b`.
  have hωb : (y.1 : Kˣ) * b⁻¹ = (y.2 : Kˣ)⁻¹ := by
    rw [coe_unitFiltrationZeroEquivProd_apply_snd, mul_inv_rev, inv_inv, mul_comm]
  rw [coe_normResidueSymbol_of_mem_unitFiltration_zero hp a hb, ← inv_zpow, ← mul_zpow, hωb]
  exact zpow_mem (inv_mem y.2.property) _

/-- **The tame congruence characterizes the symbol.** If `n` is prime to the residue
characteristic and `b` is a unit of `𝒪[K]`, then `(a, b)` is the unique `n`-th root of unity
congruent to `b ^ (v(a) · (q - 1) / n)` modulo the maximal ideal. -/
theorem normResidueSymbol_eq_iff_mul_inv_zpow_mem_unitFiltration_one (hp : ¬ ringChar 𝓀[K] ∣ n)
    (a : Kˣ) {b : Kˣ} (hb : b ∈ unitFiltration K 0) (ζ : rootsOfUnity n K) :
    normResidueSymbol K n a b = ζ ↔
      (ζ : Kˣ) * (b ^ ((normalizedValuation K a).toAdd * (((Nat.card 𝓀[K] - 1) / n : ℕ) : ℤ)))⁻¹ ∈
        unitFiltration K 1 := by
  refine ⟨fun h ↦ h ▸ normResidueSymbol_mul_inv_zpow_mem_unitFiltration_one hp a hb, fun h ↦ ?_⟩
  -- Two `n`-th roots of unity with the same residue agree, since `μ_n(K) ∩ U(K,1) = 1`.
  have hmem := div_mem (normResidueSymbol_mul_inv_zpow_mem_unitFiltration_one hp a hb) h
  rw [mul_div_mul_right_eq_div] at hmem
  have h1 := Subgroup.disjoint_def.mp
    (disjoint_rootsOfUnity_unitFiltration_one_of_isUnit (isUnit_natCast_iff_not_dvd.2 hp))
    (div_mem (normResidueSymbol K n a b).property ζ.property) hmem
  exact Subtype.ext (div_eq_one.1 h1)

end TauCeti
