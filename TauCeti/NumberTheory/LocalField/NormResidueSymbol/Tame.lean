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
import TauCeti.NumberTheory.LocalField.NormResidueSymbol.Steinberg
import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
import TauCeti.NumberTheory.LocalField.RootsOfUnity.Torsion

/-!
# The tame formula for the norm-residue symbol

Let `K` be a nonarchimedean local field containing the `n`-th roots of unity, where `n` is prime
to the residue characteristic `p`, and let `q` be the cardinality of the residue field. Then
`n ∣ q - 1`. This file computes the norm-residue symbol `(a, b) = Art_K(a)(ⁿ√b) / ⁿ√b` of
`TauCeti.normResidueSymbol` for all `a, b ∈ Kˣ`. Writing `v` for the normalized valuation, the
element `c = (-1) ^ (v(a) v(b)) · b ^ v(a) · a ^ (-v(b))` is a unit of `𝒪[K]`, and

`(a, b) = ω(c) ^ ((q - 1) / n)`,

where `ω(c)` is the Teichmüller representative of `c`, the `(q - 1)`-st root of unity with the
same residue as `c`. Equivalently, `(a, b)` is the unique `n`-th root of unity congruent to
`c ^ ((q - 1) / n)` modulo the maximal ideal, and `(a, b) = 1` exactly when `c` is an `n`-th power.
This is the tame formula. For a `ℤᵐ⁰`-valued valuation whose order is `v`, the unit `c` is the tame
unit `Valuation.tameUnit` of `b` and `a`, so the residue of `c` is the tame symbol `∂{b, a}`.

The file first treats a unit radical `b`, where `c = b ^ v(a)`: then
`(a, b) = ω(b) ^ (v(a) · (q - 1) / n)`. In particular two units pair trivially, and a uniformizer
`π` pairs with a unit `b` to the root of unity whose residue is `r ^ ((q - 1) / n)`, the `n`-th
power residue of the residue `r` of `b`.

The reason is that every `n`-th root of a unit lies in the maximal unramified extension. There the
Artin symbol of a unit acts trivially, because it lies in inertia, while the Artin symbol of a
uniformizer acts as arithmetic Frobenius, which raises roots of unity of order prime to `p` to the
`q`-th power. Writing `b = ω(b) · w ^ n` with `w` a principal unit reduces the computation to an
`n`-th root `z` of `ω(b)`, a root of unity of order prime to `p`, for which
`Frob(z) / z = z ^ (q - 1) = ω(b) ^ ((q - 1) / n)`.

For arbitrary arguments, write `a = π ^ v(a) u` and `b = π ^ v(b) w` with `u, w` units. By
bimultiplicativity, skew symmetry, `(u, w) = 1` and the diagonal value `(π, π) = (π, -1)` of the
Steinberg relation, `(a, b) = (π, c)`, whose radical is a unit.

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
* `TauCeti.normResidueSymbol_eq_normResidueSymbol_uniformizer`: `(a, b) = (π, c)` for every
  uniformizer `π`.
* `TauCeti.coe_normResidueSymbol_eq_fst_unitFiltrationZeroEquivProd_pow`: the tame formula
  `(a, b) = ω(c) ^ ((q - 1) / n)` for all `a, b`.
* `TauCeti.normResidueSymbol_mul_inv_pow_mem_unitFiltration_one`,
  `TauCeti.normResidueSymbol_eq_iff_mul_inv_pow_mem_unitFiltration_one`: the tame congruence
  `(a, b) ≡ c ^ ((q - 1) / n)` for all `a, b`, and its characterization of `(a, b)`.
* `TauCeti.normResidueSymbol_eq_one_iff_mem_range_powMonoidHom`: `(a, b) = 1` exactly when `c` is
  an `n`-th power in `K`.

## References

* J.-P. Serre, *Local Fields*, Chapter XIV, §3, Proposition 8.
* J. S. Milne, *Class Field Theory*, Chapter III, §4, Theorem 4.4 and Remark 4.5.

Both sources state the formula for arbitrary arguments, each in its own orientation of the symbol;
`TauCeti.normResidueSymbol` lets the first argument act through the Artin map, which places
`b ^ v(a)` rather than `a ^ v(b)` in the numerator of `c`.
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
    rw [← map_zpow, ← map_mul, zpow_neg, mul_mul_inv_cancel'_right]
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

/-! ### The tame formula for arbitrary arguments -/

/-- **Reduction of the tame formula to a uniformizer.** If `n` is prime to the residue
characteristic and `π` is a uniformizer, then for all `a, b ∈ Kˣ`
`(a, b) = (π, (-1) ^ (v(a) v(b)) · b ^ v(a) · a ^ (-v(b)))`, whose radical argument is a unit of
`𝒪[K]` (`TauCeti.neg_one_zpow_mul_zpow_mul_zpow_mem_unitFiltration_zero`). -/
theorem normResidueSymbol_eq_normResidueSymbol_uniformizer (hp : ¬ ringChar 𝓀[K] ∣ n) {π : Kˣ}
    (hπ : IsUniformizer K π) (a b : Kˣ) :
    normResidueSymbol K n a b = normResidueSymbol K n π
      ((-1) ^ ((normalizedValuation K a).toAdd * (normalizedValuation K b).toAdd) *
        b ^ (normalizedValuation K a).toAdd * a ^ (-(normalizedValuation K b).toAdd)) := by
  set α := (normalizedValuation K a).toAdd
  set β := (normalizedValuation K b).toAdd
  -- Write `a = π ^ α u` and `b = π ^ β w` with `u, w` units of `𝒪[K]`.
  have hπ1 := (isUniformizer_def π).1 hπ
  obtain ⟨u, hu, ha⟩ : ∃ u ∈ unitFiltration K 0, a = π ^ α * u :=
    ⟨a * π ^ (-α), mul_zpow_neg_mem_unitFiltration_zero hπ1 a,
      by rw [zpow_neg, mul_mul_inv_cancel'_right]⟩
  obtain ⟨w, hw, hb⟩ : ∃ w ∈ unitFiltration K 0, b = π ^ β * w :=
    ⟨b * π ^ (-β), mul_zpow_neg_mem_unitFiltration_zero hπ1 b,
      by rw [zpow_neg, mul_mul_inv_cancel'_right]⟩
  -- The values `(π, b)`, `(π, u)` and `(π, -1)` determine both sides.
  have hub : normResidueSymbol K n u b = (normResidueSymbol K n π u)⁻¹ ^ β := by
    conv_lhs => rw [hb]
    rw [normResidueSymbol_mul_right, normResidueSymbol_zpow_right,
      normResidueSymbol_eq_one_of_mem_unitFiltration_zero hp hu hw, mul_one,
      normResidueSymbol_swap]
  have hab : normResidueSymbol K n a b =
      normResidueSymbol K n π b ^ α * (normResidueSymbol K n π u)⁻¹ ^ β := by
    conv_lhs => rw [ha]
    rw [normResidueSymbol_mul_left, normResidueSymbol_zpow_left, hub]
  have hπa : normResidueSymbol K n π a =
      normResidueSymbol K n π (-1) ^ α * normResidueSymbol K n π u := by
    conv_lhs => rw [ha]
    rw [normResidueSymbol_mul_right, normResidueSymbol_zpow_right,
      normResidueSymbol_self_eq_normResidueSymbol_neg_one_right]
  rw [hab, normResidueSymbol_mul_right, normResidueSymbol_mul_right, normResidueSymbol_zpow_right,
    normResidueSymbol_zpow_right, normResidueSymbol_zpow_right, hπa]
  -- The factors `(π, -1) ^ (α β)` and `(π, -1) ^ (-α β)` cancel, leaving
  -- `(π, b) ^ α (π, u) ^ (-β)` on both sides.
  rw [mul_zpow, ← zpow_mul, mul_neg, zpow_neg _ (α * β), inv_zpow',
    mul_mul_mul_comm, mul_inv_cancel, one_mul]

/-- **The tame formula.** If `n` is prime to the residue characteristic, then for all
`a, b ∈ Kˣ` the norm-residue symbol is `(a, b) = ω(c) ^ ((q - 1) / n)`, where
`c = (-1) ^ (v(a) v(b)) · b ^ v(a) · a ^ (-v(b))` is a unit of `𝒪[K]`, `ω(c)` is its Teichmüller
representative and `q` is the cardinality of the residue field. -/
theorem coe_normResidueSymbol_eq_fst_unitFiltrationZeroEquivProd_pow (hp : ¬ ringChar 𝓀[K] ∣ n)
    (a b : Kˣ) :
    (normResidueSymbol K n a b : Kˣ) =
      ((unitFiltrationZeroEquivProd K
        ⟨_, neg_one_zpow_mul_zpow_mul_zpow_mem_unitFiltration_zero a b⟩).1 : Kˣ) ^
        ((Nat.card 𝓀[K] - 1) / n) := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer (K := K)
  rw [normResidueSymbol_eq_normResidueSymbol_uniformizer hp hπ a b]
  exact coe_normResidueSymbol_uniformizer hp hπ _

/-- **The tame congruence.** If `n` is prime to the residue characteristic, then for all
`a, b ∈ Kˣ` the norm-residue symbol satisfies
`(a, b) ≡ ((-1) ^ (v(a) v(b)) · b ^ v(a) · a ^ (-v(b))) ^ ((q - 1) / n)` modulo the maximal ideal:
their quotient is a principal unit. -/
theorem normResidueSymbol_mul_inv_pow_mem_unitFiltration_one (hp : ¬ ringChar 𝓀[K] ∣ n)
    (a b : Kˣ) :
    (normResidueSymbol K n a b : Kˣ) *
        (((-1) ^ ((normalizedValuation K a).toAdd * (normalizedValuation K b).toAdd) *
          b ^ (normalizedValuation K a).toAdd * a ^ (-(normalizedValuation K b).toAdd)) ^
            ((Nat.card 𝓀[K] - 1) / n))⁻¹ ∈
      unitFiltration K 1 := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer (K := K)
  have h := normResidueSymbol_mul_inv_zpow_mem_unitFiltration_one hp π
    (neg_one_zpow_mul_zpow_mul_zpow_mem_unitFiltration_zero a b)
  rwa [(isUniformizer_def π).1 hπ, toAdd_ofAdd, one_mul, zpow_natCast,
    ← normResidueSymbol_eq_normResidueSymbol_uniformizer hp hπ a b] at h

/-- **The tame congruence characterizes the symbol.** If `n` is prime to the residue
characteristic, then for all `a, b ∈ Kˣ` the norm-residue symbol `(a, b)` is the unique `n`-th root
of unity congruent to `((-1) ^ (v(a) v(b)) · b ^ v(a) · a ^ (-v(b))) ^ ((q - 1) / n)` modulo the
maximal ideal. -/
theorem normResidueSymbol_eq_iff_mul_inv_pow_mem_unitFiltration_one (hp : ¬ ringChar 𝓀[K] ∣ n)
    (a b : Kˣ) (ζ : rootsOfUnity n K) :
    normResidueSymbol K n a b = ζ ↔
      (ζ : Kˣ) *
          (((-1) ^ ((normalizedValuation K a).toAdd * (normalizedValuation K b).toAdd) *
            b ^ (normalizedValuation K a).toAdd * a ^ (-(normalizedValuation K b).toAdd)) ^
              ((Nat.card 𝓀[K] - 1) / n))⁻¹ ∈
        unitFiltration K 1 := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer (K := K)
  rw [normResidueSymbol_eq_normResidueSymbol_uniformizer hp hπ a b,
    normResidueSymbol_eq_iff_mul_inv_zpow_mem_unitFiltration_one hp π
      (neg_one_zpow_mul_zpow_mul_zpow_mem_unitFiltration_zero a b),
    (isUniformizer_def π).1 hπ, toAdd_ofAdd, one_mul, zpow_natCast]

/-- **The tame criterion for triviality.** If `n` is prime to the residue characteristic, then for
all `a, b ∈ Kˣ` the norm-residue symbol `(a, b)` is trivial exactly when the unit
`(-1) ^ (v(a) v(b)) · b ^ v(a) · a ^ (-v(b))` of `𝒪[K]` is an `n`-th power in `K`. -/
theorem normResidueSymbol_eq_one_iff_mem_range_powMonoidHom (hp : ¬ ringChar 𝓀[K] ∣ n)
    (a b : Kˣ) :
    normResidueSymbol K n a b = 1 ↔
      (-1) ^ ((normalizedValuation K a).toAdd * (normalizedValuation K b).toAdd) *
          b ^ (normalizedValuation K a).toAdd * a ^ (-(normalizedValuation K b).toAdd) ∈
        (powMonoidHom n : Kˣ →* Kˣ).range := by
  rw [normResidueSymbol_eq_iff_mul_inv_pow_mem_unitFiltration_one hp a b, OneMemClass.coe_one,
    one_mul, inv_mem_iff, pow_natCard_sub_one_div_mem_unitFiltration_one_iff
      (dvd_natCard_residueField_sub_one (isUnit_natCast_iff_not_dvd.2 hp))
      (neg_one_zpow_mul_zpow_mul_zpow_mem_unitFiltration_zero a b)]

end TauCeti
