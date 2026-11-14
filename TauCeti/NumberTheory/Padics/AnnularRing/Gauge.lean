/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer
public import TauCeti.NumberTheory.Padics.AnnularRing.Basic
public import TauCeti.RingTheory.Huber.TateGauge.Basic

/-!
# The Tate gauge and Banach–Tate structure on `ℤ_p⟦T, p/T⟧[1/T]`

For the annular coefficient ring `H = AnnularRing p`, inverting the non-zero-divisor `T` yields the
Laurent ring `Localization.Away (T : AnnularRing p)`, in which `T` becomes a unit while `U = p / T`
remains non-invertible. Each element `z` of `Localization.Away (T : AnnularRing p)` has a unique
shifted two-sided coefficient sequence `awayCoeff z : ℤ → ℤ_[p]` obtained from `z * T ^ k = x` by
`awayCoeff z m = x.coeff (m + k)`.

Fixing a real parameter `α ∈ (0, 1)`, the type synonym `TauCeti.AnnularLaurent p hα` equips
`Localization.Away (T : AnnularRing p)` with the Tate gauge (`TauCeti.Huber.tateGauge`) of the
image `A₀` of `AnnularRing p`, the pseudo-uniformiser `T`, and the base `α⁻¹ > 1`. Because the
`T`-adic filtration on `AnnularRing p` is separated and degreewise `p`-adically complete, this
gauge is a complete ultrametric `NormedCommRing` norm with closed unit ball `A₀`, multiplicative
pseudo-uniformiser `T` of norm `α`, `‖p‖ = α`, and `‖U ^ k‖ = 1` for all `k : ℕ`. Changing `α`
raises the norm to a positive real power (`norm_ofRadius`), so all `α ∈ (0, 1)` induce the same
Banach–Tate topology on `H[1/T]`.

Because `‖U ^ k‖ = 1` for every `k`, the geometric series `∑_{k ≥ 0} U ^ k` fails to converge in
`AnnularLaurent p hα` (`not_summable_algebraMap_U_pow`), even though `1 - U` is already a unit in
`AnnularRing p` whose inverse has the formal series `∑_{k ≥ 0} U ^ k` in the boundary variables.

## Main definitions

* `TauCeti.AnnularRing.awayCoeff`: the `ℤ_p`-linear two-sided coefficient map
  `Localization.Away (T : AnnularRing p) →ₗ[ℤ_[p]] (ℤ → ℤ_[p])`.
* `TauCeti.AnnularLaurent p hα`: `Localization.Away (T : AnnularRing p)` equipped with the
  complete ultrametric Tate gauge norm of radius `‖T‖ = α`.
* `TauCeti.AnnularLaurent.unitT` and `TauCeti.AnnularLaurent.pseudoUniformizer`: `T` as a unit and
  multiplicative pseudo-uniformiser of `AnnularLaurent p hα`.

## Main results

* `TauCeti.AnnularRing.awayCoeff_injective` and
  `TauCeti.AnnularRing.mem_range_algebraMap_iff_norm_awayCoeff_le`: elements of `H[1/T]` are
  determined by `awayCoeff`, and `H` is cut out inside `H[1/T]` by `‖awayCoeff z m‖ ≤ p ^ min 0 m`.
* `TauCeti.AnnularLaurent.instNormedCommRing`, `TauCeti.AnnularLaurent.instIsTate`, and
  `TauCeti.AnnularLaurent.instCompleteSpace`: `AnnularLaurent p hα` is a complete ultrametric
  Banach–Tate ring (hence also `TauCeti.Huber.IsTateRing`).
* `TauCeti.AnnularLaurent.unitClosedBall_eq_range_algebraMap`: its closed unit ball is the image of
  `AnnularRing p`.
* `TauCeti.AnnularLaurent.norm_algebraMap_T`, `TauCeti.AnnularLaurent.norm_natCast_p`, and
  `TauCeti.AnnularLaurent.norm_algebraMap_U_pow`: `‖T‖ = α`, `‖p‖ = α`, and `‖U ^ k‖ = 1`.
* `TauCeti.AnnularLaurent.not_summable_algebraMap_U_pow` and
  `TauCeti.AnnularLaurent.isUnit_one_sub_algebraMap_U`: `∑ U ^ k` diverges in the Tate topology
  even though `1 - U` is invertible via its integral series in `AnnularRing p`.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4.
-/

public noncomputable section

open Filter Topology

namespace TauCeti

namespace AnnularRing

variable {p : ℕ} [Fact p.Prime]

private theorem one_lt_p : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt

/-- Multiplication by `T ^ k` shifts coefficients up by `k` degrees. -/
@[simp]
theorem coeff_T_pow_mul (x : AnnularRing p) (k : ℕ) (m : ℤ) :
    ((T : AnnularRing p) ^ k * x).coeff m = x.coeff (m - k) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, coeff_T_mul, ih]
    congr 1
    omega

/-- The localization map `AnnularRing p →+* Localization.Away T` is injective because `T` is a
non-zero-divisor. -/
theorem algebraMap_localizationAway_injective :
    Function.Injective (algebraMap (AnnularRing p) (Localization.Away (T : AnnularRing p))) :=
  IsLocalization.injective _ (Submonoid.powers_le.2 T_mem_nonZeroDivisors)

private def awayCoeffAux (z : Localization.Away (T : AnnularRing p)) (m : ℤ) : ℤ_[p] :=
  (IsLocalization.Away.sec (T : AnnularRing p) z).1.coeff
    (m + (IsLocalization.Away.sec (T : AnnularRing p) z).2)

private theorem awayCoeffAux_eq_of_mul_pow_eq {z : Localization.Away (T : AnnularRing p)}
    {k : ℕ} {x : AnnularRing p}
    (hz : z * algebraMap (AnnularRing p) _ T ^ k = algebraMap (AnnularRing p) _ x) (m : ℤ) :
    awayCoeffAux z m = x.coeff (m + k) := by
  set s := IsLocalization.Away.sec (T : AnnularRing p) z
  have hs : z * algebraMap (AnnularRing p) _ T ^ s.2 = algebraMap (AnnularRing p) _ s.1 := by
    simpa [s, map_pow] using IsLocalization.Away.sec_spec (T : AnnularRing p) z
  have heq : (T : AnnularRing p) ^ k * s.1 = T ^ s.2 * x := by
    apply algebraMap_localizationAway_injective
    calc algebraMap (AnnularRing p) _ (T ^ k * s.1)
        = z * algebraMap (AnnularRing p) _ T ^ s.2 * algebraMap (AnnularRing p) _ T ^ k := by
          rw [map_mul, map_pow, ← hs, mul_comm]
      _ = z * algebraMap (AnnularRing p) _ T ^ k * algebraMap (AnnularRing p) _ T ^ s.2 := by ring
      _ = algebraMap (AnnularRing p) _ (T ^ s.2 * x) := by rw [hz, map_mul, map_pow, mul_comm]
  have hm := congr_arg (coeff · (m + s.2 + k)) heq
  rw [awayCoeffAux]
  simpa [s, coeff_T_pow_mul, add_sub_cancel_right,
    show m + (s.2 : ℤ) + k - s.2 = m + k by omega] using hm

/-- The two-sided coefficient sequence of an element of `Localization.Away (T : AnnularRing p)`,
sending `x / T ^ k` to `m ↦ x.coeff (m + k)`. -/
def awayCoeff : Localization.Away (T : AnnularRing p) →ₗ[ℤ_[p]] (ℤ → ℤ_[p]) where
  toFun := awayCoeffAux
  map_add' z₁ z₂ := by
    obtain ⟨k₁, x₁, hx₁⟩ := IsLocalization.Away.surj (T : AnnularRing p) z₁
    obtain ⟨k₂, x₂, hx₂⟩ := IsLocalization.Away.surj (T : AnnularRing p) z₂
    have h₁₂ : (z₁ + z₂) * algebraMap (AnnularRing p) _ T ^ (k₁ + k₂) =
        algebraMap (AnnularRing p) _ (T ^ k₂ * x₁ + T ^ k₁ * x₂) := by
      rw [pow_add, add_mul, ← mul_assoc, hx₁, ← mul_assoc, mul_right_comm z₂, hx₂,
        map_add, map_mul, map_mul, map_pow, map_pow]
      ring
    ext m : 1
    rw [Pi.add_apply, awayCoeffAux_eq_of_mul_pow_eq h₁₂, awayCoeffAux_eq_of_mul_pow_eq hx₁,
      awayCoeffAux_eq_of_mul_pow_eq hx₂, coeff_add, coeff_T_pow_mul, coeff_T_pow_mul]
    congr 2 <;> omega
  map_smul' c z := by
    obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (T : AnnularRing p) z
    have hcz : (c • z) * algebraMap (AnnularRing p) _ T ^ k =
        algebraMap (AnnularRing p) _ (c • x) := by
      rw [Algebra.smul_def, mul_assoc, hx, Algebra.smul_def, map_mul,
        IsScalarTower.algebraMap_apply ℤ_[p] (AnnularRing p)]
    ext m : 1
    rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, awayCoeffAux_eq_of_mul_pow_eq hcz,
      awayCoeffAux_eq_of_mul_pow_eq hx, coeff_smul]

/-- Characterisation of `awayCoeff` from a clearing denominator identity `z * T ^ k = x`. -/
theorem awayCoeff_eq_of_mul_pow_eq {z : Localization.Away (T : AnnularRing p)}
    {k : ℕ} {x : AnnularRing p}
    (hz : z * algebraMap (AnnularRing p) _ T ^ k = algebraMap (AnnularRing p) _ x) (m : ℤ) :
    awayCoeff z m = x.coeff (m + k) :=
  awayCoeffAux_eq_of_mul_pow_eq hz m

@[simp]
theorem awayCoeff_algebraMap (x : AnnularRing p) (m : ℤ) :
    awayCoeff (algebraMap (AnnularRing p) (Localization.Away (T : AnnularRing p)) x) m =
      x.coeff m := by
  simpa using awayCoeff_eq_of_mul_pow_eq (k := 0) (x := x) (by simp) m

@[simp]
theorem awayCoeff_one (m : ℤ) :
    awayCoeff (1 : Localization.Away (T : AnnularRing p)) m = if m = 0 then 1 else 0 := by
  rw [← map_one (algebraMap (AnnularRing p) _), awayCoeff_algebraMap, coeff_one]

@[simp]
theorem awayCoeff_mul_algebraMap_T (z : Localization.Away (T : AnnularRing p)) (m : ℤ) :
    awayCoeff (algebraMap (AnnularRing p) _ T * z) m = awayCoeff z (m - 1) := by
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (T : AnnularRing p) z
  have hTz : (algebraMap (AnnularRing p) _ T * z) * algebraMap (AnnularRing p) _ T ^ k =
      algebraMap (AnnularRing p) _ (T * x) := by
    rw [mul_assoc, hx, map_mul]
  rw [awayCoeff_eq_of_mul_pow_eq hTz, coeff_T_mul, awayCoeff_eq_of_mul_pow_eq hx]
  congr 1
  omega

/-- Elements of `Localization.Away (T : AnnularRing p)` are determined by their two-sided
coefficients. -/
theorem awayCoeff_injective :
    Function.Injective (awayCoeff (p := p)) := by
  refine LinearMap.ker_eq_bot.1 ((Submodule.eq_bot_iff _).2 fun z hz ↦ ?_)
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (T : AnnularRing p) z
  have hx0 : x = 0 := by
    ext n : 2
    have hm := congr_fun hz (n - k)
    simpa [awayCoeff_eq_of_mul_pow_eq hx, sub_add_cancel] using hm
  rw [hx0, map_zero] at hx
  exact (IsLocalization.Away.algebraMap_pow_isUnit (T : AnnularRing p) k).mul_left_eq_zero.1 hx

/-- An element of `Localization.Away T` lies in the image of `AnnularRing p` if and only if its
two-sided coefficients satisfy the annular norm bound `‖awayCoeff z m‖ ≤ p ^ min 0 m`. -/
theorem mem_range_algebraMap_iff_norm_awayCoeff_le (z : Localization.Away (T : AnnularRing p)) :
    z ∈ (algebraMap (AnnularRing p) (Localization.Away (T : AnnularRing p))).range ↔
      ∀ m : ℤ, ‖awayCoeff z m‖ ≤ (p : ℝ) ^ min 0 m := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨x, rfl⟩ m
    rw [awayCoeff_algebraMap]
    exact x.norm_coeff_le m
  · refine ⟨⟨awayCoeff z, h⟩, awayCoeff_injective ?_⟩
    ext m : 1
    exact awayCoeff_algebraMap ⟨awayCoeff z, h⟩ m

/-- A two-sided sequence `d : ℤ → ℤ_p` arises from `Localization.Away (T : AnnularRing p)` if and
only if some shift `m ↦ d (m - k)` satisfies the annular norm bound. -/
theorem mem_range_awayCoeff_iff (d : ℤ → ℤ_[p]) :
    d ∈ Set.range (awayCoeff (p := p)) ↔
      ∃ k : ℕ, ∀ m : ℤ, ‖d m‖ ≤ (p : ℝ) ^ min 0 (m + k) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (T : AnnularRing p) z
    refine ⟨k, fun m ↦ ?_⟩
    rw [awayCoeff_eq_of_mul_pow_eq hx]
    exact x.norm_coeff_le (m + k)
  · rintro ⟨k, hk⟩
    let x : AnnularRing p := ⟨fun n ↦ d (n - k), fun n ↦ by simpa using hk (n - k)⟩
    let s : Submonoid.powers (T : AnnularRing p) := ⟨T ^ k, k, rfl⟩
    let z : Localization.Away (T : AnnularRing p) := IsLocalization.mk' _ x s
    have hz : z * algebraMap (AnnularRing p) _ T ^ k = algebraMap (AnnularRing p) _ x := by
      simpa [z, s, map_pow] using
        IsLocalization.mk'_spec (Localization.Away (T : AnnularRing p)) x s
    refine ⟨z, funext fun m ↦ ?_⟩
    simp [awayCoeff_eq_of_mul_pow_eq hz, x]

end AnnularRing

/-! ### The Banach–Tate Laurent ring `AnnularLaurent p hα` -/

/-- `Localization.Away (T : AnnularRing p)` equipped with the Tate gauge norm of radius
`‖T‖ = α ∈ (0, 1)`. -/
-- Exposed so the underlying ring and localization instances transfer from `Localization.Away`.
@[expose]
def AnnularLaurent (p : ℕ) [Fact p.Prime] {α : ℝ} (_hα : α ∈ Set.Ioo 0 1) : Type :=
  Localization.Away (AnnularRing.T (p := p))

namespace AnnularLaurent

open AnnularRing

section Instances

variable {p : ℕ} [Fact p.Prime] {α : ℝ}

private theorem one_lt_p : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt

private theorem one_lt_inv_of_mem_Ioo {β : ℝ} (hβ : β ∈ Set.Ioo 0 1) : 1 < β⁻¹ :=
  (one_lt_inv₀ hβ.1).2 hβ.2

instance (hα : α ∈ Set.Ioo 0 1) : CommRing (AnnularLaurent p hα) :=
  inferInstanceAs (CommRing (Localization.Away (T : AnnularRing p)))

instance (hα : α ∈ Set.Ioo 0 1) : Algebra (AnnularRing p) (AnnularLaurent p hα) :=
  inferInstanceAs (Algebra (AnnularRing p) (Localization.Away (T : AnnularRing p)))

instance (hα : α ∈ Set.Ioo 0 1) : Algebra ℤ_[p] (AnnularLaurent p hα) :=
  inferInstanceAs (Algebra ℤ_[p] (Localization.Away (T : AnnularRing p)))

instance (hα : α ∈ Set.Ioo 0 1) : IsScalarTower ℤ_[p] (AnnularRing p) (AnnularLaurent p hα) :=
  inferInstanceAs (IsScalarTower ℤ_[p] (AnnularRing p) (Localization.Away (T : AnnularRing p)))

instance (hα : α ∈ Set.Ioo 0 1) : IsLocalization.Away (T : AnnularRing p) (AnnularLaurent p hα) :=
  inferInstanceAs (IsLocalization.Away (T : AnnularRing p) (Localization.Away (T : AnnularRing p)))

/-- The two-sided coefficient map on `AnnularLaurent p hα`. -/
def coeff {hα : α ∈ Set.Ioo 0 1} : AnnularLaurent p hα →ₗ[ℤ_[p]] (ℤ → ℤ_[p]) :=
  awayCoeff (p := p)

@[simp]
theorem coeff_algebraMap {hα : α ∈ Set.Ioo 0 1} (x : AnnularRing p) (m : ℤ) :
    coeff (algebraMap (AnnularRing p) (AnnularLaurent p hα) x) m = x.coeff m :=
  awayCoeff_algebraMap x m

@[simp]
theorem coeff_one {hα : α ∈ Set.Ioo 0 1} (m : ℤ) :
    coeff (1 : AnnularLaurent p hα) m = if m = 0 then 1 else 0 :=
  awayCoeff_one m

@[simp]
theorem coeff_mul_algebraMap_T {hα : α ∈ Set.Ioo 0 1} (z : AnnularLaurent p hα) (m : ℤ) :
    coeff (algebraMap (AnnularRing p) (AnnularLaurent p hα) T * z) m = coeff z (m - 1) :=
  awayCoeff_mul_algebraMap_T z m

theorem coeff_injective {hα : α ∈ Set.Ioo 0 1} :
    Function.Injective (coeff (p := p) (hα := hα)) :=
  awayCoeff_injective

/-- Identity `AnnularRing p`-algebra equivalence changing the gauge parameter from `α` to `β`. -/
def ofRadius {β : ℝ} (hα : α ∈ Set.Ioo 0 1) (hβ : β ∈ Set.Ioo 0 1) :
    AnnularLaurent p hα ≃ₐ[AnnularRing p] AnnularLaurent p hβ :=
  AlgEquiv.refl

@[simp]
theorem coeff_ofRadius {β : ℝ} (hα : α ∈ Set.Ioo 0 1) (hβ : β ∈ Set.Ioo 0 1)
    (z : AnnularLaurent p hα) :
    coeff (ofRadius hα hβ z) = coeff z := (rfl)

/-- `T` as a unit of `AnnularLaurent p hα`. -/
def unitT (p : ℕ) [Fact p.Prime] (hα : α ∈ Set.Ioo 0 1) : (AnnularLaurent p hα)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := AnnularLaurent p hα) (T : AnnularRing p)).unit

@[simp]
theorem val_unitT (hα : α ∈ Set.Ioo 0 1) :
    ((unitT p hα : (AnnularLaurent p hα)ˣ) : AnnularLaurent p hα) =
      algebraMap (AnnularRing p) (AnnularLaurent p hα) T := (rfl)

/-- The canonical ring of definition of `AnnularLaurent p hα`: the image of `AnnularRing p`. -/
def ringOfDefinition (p : ℕ) [Fact p.Prime] (hα : α ∈ Set.Ioo 0 1) :
    Subring (AnnularLaurent p hα) :=
  (algebraMap (AnnularRing p) (AnnularLaurent p hα)).range

theorem mem_ringOfDefinition_iff {hα : α ∈ Set.Ioo 0 1} (z : AnnularLaurent p hα) :
    z ∈ ringOfDefinition p hα ↔
      z ∈ (algebraMap (AnnularRing p) (AnnularLaurent p hα)).range := Iff.rfl

theorem mem_ringOfDefinition_iff_norm_coeff_le {hα : α ∈ Set.Ioo 0 1} (z : AnnularLaurent p hα) :
    z ∈ ringOfDefinition p hα ↔ ∀ m : ℤ, ‖coeff z m‖ ≤ (p : ℝ) ^ min 0 m :=
  mem_range_algebraMap_iff_norm_awayCoeff_le z

theorem unitT_mem_ringOfDefinition (hα : α ∈ Set.Ioo 0 1) :
    ((unitT p hα : (AnnularLaurent p hα)ˣ) : AnnularLaurent p hα) ∈ ringOfDefinition p hα :=
  ⟨T, rfl⟩

theorem exists_zpow_unitT_mul_mem (hα : α ∈ Set.Ioo 0 1) (z : AnnularLaurent p hα) :
    ∃ n : ℤ, (((unitT p hα ^ n : (AnnularLaurent p hα)ˣ) : AnnularLaurent p hα) * z) ∈
      ringOfDefinition p hα := by
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (T : AnnularRing p) z
  refine ⟨k, x, ?_⟩
  rw [zpow_natCast, Units.val_pow_eq_pow_val, val_unitT, mul_comm, hx]

@[simp]
theorem coeff_zpow_unitT_mul (hα : α ∈ Set.Ioo 0 1) (k : ℤ) (z : AnnularLaurent p hα) (m : ℤ) :
    coeff ((((unitT p hα ^ k : (AnnularLaurent p hα)ˣ) : AnnularLaurent p hα) * z)) m =
      coeff z (m - k) := by
  have hnat : ∀ n : ℕ, ∀ w : AnnularLaurent p hα, ∀ q : ℤ,
      coeff ((((unitT p hα ^ (n : ℤ) : (AnnularLaurent p hα)ˣ) : AnnularLaurent p hα) * w)) q =
        coeff w (q - n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro w q
      rw [Nat.cast_succ, zpow_add, zpow_one, Units.val_mul, mul_assoc, val_unitT,
        ih, coeff_mul_algebraMap_T]
      exact congr_arg (coeff w) (by omega)
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    exact hnat k z m
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -n := ⟨(-k).toNat, by omega⟩
    let w : AnnularLaurent p hα :=
      (((unitT p hα ^ (-(n : ℤ)) : (AnnularLaurent p hα)ˣ) : AnnularLaurent p hα) * z)
    have hcancel :
        (((unitT p hα ^ (n : ℤ) : (AnnularLaurent p hα)ˣ) : AnnularLaurent p hα) * w) = z := by
      simp only [w, ← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
        Units.val_one, one_mul]
    have := hnat n w (m + n)
    rw [hcancel, add_sub_cancel_right] at this
    simpa [w, sub_neg_eq_add] using this.symm

private theorem zpow_unitT_neg_mul_mem_iff (hα : α ∈ Set.Ioo 0 1) (z : AnnularLaurent p hα)
    (r : ℤ) :
    (((unitT p hα ^ (-r) : (AnnularLaurent p hα)ˣ) : AnnularLaurent p hα) * z) ∈
      ringOfDefinition p hα ↔ ∀ m : ℤ, ‖coeff z m‖ ≤ (p : ℝ) ^ min 0 (m - r) := by
  rw [mem_ringOfDefinition_iff_norm_coeff_le]
  refine ⟨fun h m ↦ ?_, fun h n ↦ ?_⟩
  · have hm := h (m - r)
    rwa [coeff_zpow_unitT_mul, sub_neg_eq_add, sub_add_cancel] at hm
  · rw [coeff_zpow_unitT_mul, sub_neg_eq_add]
    simpa using h (n + r)

private theorem tateGauge_le_zpow_iff_coeff (hα : α ∈ Set.Ioo 0 1) (z : AnnularLaurent p hα)
    (r : ℤ) :
    Huber.tateGauge (ringOfDefinition p hα) (unitT p hα) α⁻¹ z ≤ α ^ r ↔
      ∀ m : ℤ, ‖coeff z m‖ ≤ (p : ℝ) ^ min 0 (m - r) := by
  have hpow : (α⁻¹) ^ (-r) = α ^ r := by rw [inv_zpow, zpow_neg, inv_inv]
  rw [← hpow, Huber.tateGauge_le_zpow_iff (unitT_mem_ringOfDefinition hα)
    (exists_zpow_unitT_mul_mem hα z) (one_lt_inv_of_mem_Ioo hα), zpow_unitT_neg_mul_mem_iff]

/-- The Tate gauge of `(ringOfDefinition p hα, unitT p hα, α⁻¹)` as a `RingNorm` on
`AnnularLaurent p hα`. -/
def ringNorm (p : ℕ) [Fact p.Prime] (hα : α ∈ Set.Ioo 0 1) : RingNorm (AnnularLaurent p hα) :=
  { Huber.tateSeminorm (unitT_mem_ringOfDefinition (p := p) hα) (exists_zpow_unitT_mul_mem hα)
      (one_lt_inv_of_mem_Ioo hα) with
    eq_zero_of_map_eq_zero' := fun z hz ↦ by
      have hz' : Huber.tateGauge (ringOfDefinition p hα) (unitT p hα) α⁻¹ z = 0 := by
        change (Huber.tateSeminorm (unitT_mem_ringOfDefinition (p := p) hα)
          (exists_zpow_unitT_mul_mem hα) (one_lt_inv_of_mem_Ioo hα)) z = 0 at hz
        rwa [Huber.coe_tateSeminorm] at hz
      apply coeff_injective
      ext m : 1
      rw [LinearMap.map_zero, Pi.zero_apply, ← norm_eq_zero]
      refine le_antisymm ?_ (norm_nonneg _)
      by_contra! hpos
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ (one_lt_p (p := p)))
      have hle : Huber.tateGauge (ringOfDefinition p hα) (unitT p hα) α⁻¹ z ≤ α ^ (m + k) := by
        rw [hz']
        exact zpow_nonneg hα.1.le _
      have hm := (tateGauge_le_zpow_iff_coeff hα z (m + k)).1 hle m
      rw [show min (0 : ℤ) (m - (m + k)) = -(k : ℤ) by omega, zpow_neg, zpow_natCast,
        ← inv_pow] at hm
      linarith }

instance instNormedCommRing (hα : α ∈ Set.Ioo 0 1) : NormedCommRing (AnnularLaurent p hα) where
  __ := (ringNorm p hα).toNormedRing
  mul_comm := mul_comm

theorem norm_def (hα : α ∈ Set.Ioo 0 1) (z : AnnularLaurent p hα) :
    ‖z‖ = Huber.tateGauge (ringOfDefinition p hα) (unitT p hα) α⁻¹ z := by
  change (Huber.tateSeminorm (unitT_mem_ringOfDefinition (p := p) hα)
    (exists_zpow_unitT_mul_mem hα) (one_lt_inv_of_mem_Ioo hα)) z = _
  rw [Huber.coe_tateSeminorm]

instance (hα : α ∈ Set.Ioo 0 1) : IsUltrametricDist (AnnularLaurent p hα) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    simpa only [norm_def] using
      Huber.isNonarchimedean_tateGauge (unitT_mem_ringOfDefinition hα)
        (exists_zpow_unitT_mul_mem hα) (inv_nonneg.2 hα.1.le) x y

variable (hα : α ∈ Set.Ioo 0 1)

/-- Membership in the closed ball of radius `α ^ r` is membership in `T ^ r A₀`. -/
theorem norm_le_zpow_iff (z : AnnularLaurent p hα) (r : ℤ) :
    ‖z‖ ≤ α ^ r ↔
      (((unitT p hα ^ (-r) : (AnnularLaurent p hα)ˣ) : AnnularLaurent p hα) * z) ∈
        ringOfDefinition p hα := by
  rw [norm_def]
  have hpow : (α⁻¹) ^ (-r) = α ^ r := by rw [inv_zpow, zpow_neg, inv_inv]
  rw [← hpow]
  exact Huber.tateGauge_le_zpow_iff (unitT_mem_ringOfDefinition hα)
    (exists_zpow_unitT_mul_mem hα z) (one_lt_inv_of_mem_Ioo hα)

/-- Coefficientwise characterisation of the closed ball `‖z‖ ≤ α ^ r`. -/
theorem norm_le_zpow_iff_norm_coeff_le (z : AnnularLaurent p hα) (r : ℤ) :
    ‖z‖ ≤ α ^ r ↔ ∀ m : ℤ, ‖coeff z m‖ ≤ (p : ℝ) ^ min 0 (m - r) := by
  rw [norm_def]
  exact tateGauge_le_zpow_iff_coeff hα z r

private theorem norm_eq_one_of_mem_of_not_le {z : AnnularLaurent p hα}
    (hz : z ∈ ringOfDefinition p hα) (hnot : ¬ ‖z‖ ≤ α) : ‖z‖ = 1 := by
  rw [norm_def] at hnot ⊢
  refine le_antisymm (Huber.tateGauge_le_one hz) ?_
  by_contra! hlt
  obtain ⟨n, hn, hnr⟩ := (Huber.tateGauge_lt_iff (inv_nonneg.2 hα.1.le)
    (exists_zpow_unitT_mul_mem hα z)).1 hlt
  have hn1 : (1 : ℤ) ≤ n := by
    have hpow : (α⁻¹) ^ (-n) < (α⁻¹) ^ (0 : ℤ) := by simpa using hnr
    have := (zpow_lt_zpow_iff_right₀ (one_lt_inv_of_mem_Ioo hα)).1 hpow
    omega
  exact hnot <| by
    simpa using Huber.tateGauge_le_zpow (inv_nonneg.2 hα.1.le)
      (Huber.zpow_neg_mul_mem_of_le (unitT_mem_ringOfDefinition hα) hn1 hn)

private theorem norm_one_eq : ‖(1 : AnnularLaurent p hα)‖ = 1 := by
  refine norm_eq_one_of_mem_of_not_le hα (Subring.one_mem _) fun h ↦ ?_
  have h0 := (norm_le_zpow_iff_norm_coeff_le hα 1 1).1 (by simpa using h) 0
  simp only [coeff_one, ite_true, norm_one, zero_sub,
    show min (0 : ℤ) (-1) = -1 by omega] at h0
  linarith [zpow_lt_one_of_neg₀ (one_lt_p (p := p)) (by omega : (-1 : ℤ) < 0)]

@[simp]
theorem norm_algebraMap_T :
    ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) T‖ = α := by
  have h := Huber.tateGauge_zpow_mul (A₀ := ringOfDefinition p hα) (ϖ := unitT p hα)
    (inv_pos.2 hα.1) 1 1
  have h1 : Huber.tateGauge (ringOfDefinition p hα) (unitT p hα) α⁻¹ 1 = 1 := by
    rw [← norm_def, norm_one_eq]
  simpa [norm_def, h1] using h

/-- `T` as a multiplicative pseudo-uniformiser of `AnnularLaurent p hα`, with `‖T‖ = α`. -/
def pseudoUniformizer (p : ℕ) [Fact p.Prime] :
    NormedRing.PseudoUniformizer (AnnularLaurent p hα) where
  unit := unitT p hα
  norm_mul x := by
    have h := Huber.tateGauge_zpow_mul (A₀ := ringOfDefinition p hα) (ϖ := unitT p hα)
      (inv_pos.2 hα.1) 1 x
    have hT : ‖((unitT p hα : (AnnularLaurent p hα)ˣ) : AnnularLaurent p hα)‖ = α := by
      rw [val_unitT, norm_algebraMap_T]
    rw [hT, norm_def, norm_def]
    simpa using h
  norm_pos := by rw [val_unitT, norm_algebraMap_T]; exact hα.1
  norm_lt_one := by rw [val_unitT, norm_algebraMap_T]; exact hα.2

@[simp]
theorem pseudoUniformizer_unit : (pseudoUniformizer hα p).unit = unitT p hα := (rfl)

/-- `AnnularLaurent p hα` is a normed Tate ring (`NormOneClass` and `Huber.IsTateRing` follow
automatically). -/
instance instIsTate : NormedRing.IsTate (AnnularLaurent p hα) := ⟨⟨pseudoUniformizer hα p⟩⟩

/-- The closed unit ball of `AnnularLaurent p hα` is the image of `AnnularRing p`. -/
theorem unitClosedBall_eq_range_algebraMap :
    Subring.unitClosedBall (AnnularLaurent p hα) =
      (algebraMap (AnnularRing p) (AnnularLaurent p hα)).range := by
  ext z
  simpa [mem_ringOfDefinition_iff] using norm_le_zpow_iff hα z 0

theorem norm_algebraMap_le_one (x : AnnularRing p) :
    ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) x‖ ≤ 1 := by
  rw [← Subring.mem_unitClosedBall, unitClosedBall_eq_range_algebraMap]
  exact ⟨x, rfl⟩

/-- Changing the gauge parameter from `α` to `β ∈ (0, 1)` raises the norm to the positive power
`log β / log α`. -/
theorem norm_ofRadius {β : ℝ} (hβ : β ∈ Set.Ioo 0 1) (z : AnnularLaurent p hα) :
    ‖ofRadius hα hβ z‖ = ‖z‖ ^ (Real.log β / Real.log α) := by
  have hexp : Real.log β⁻¹ / Real.log α⁻¹ = Real.log β / Real.log α := by
    rw [Real.log_inv, Real.log_inv, neg_div_neg_eq]
  rw [norm_def hβ, norm_def hα, ← hexp]
  exact Huber.tateGauge_rpow (one_lt_inv_of_mem_Ioo hα) (one_lt_inv_of_mem_Ioo hβ) z

@[simp]
theorem norm_algebraMap_U_pow (k : ℕ) :
    ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) U ^ k‖ = 1 := by
  rw [← map_pow]
  refine norm_eq_one_of_mem_of_not_le hα ⟨U ^ k, rfl⟩ fun h ↦ ?_
  have hk := (norm_le_zpow_iff_norm_coeff_le hα
    (algebraMap (AnnularRing p) (AnnularLaurent p hα) (U ^ k)) 1).1 (by simpa using h) (-(k : ℤ))
  rw [coeff_algebraMap, coeff_U_pow, ite_eq_left rfl, PadicInt.norm_p_pow,
    show min (0 : ℤ) (-(k : ℤ) - 1) = -((k : ℤ) + 1) by omega] at hk
  linarith [zpow_lt_zpow_right₀ (one_lt_p (p := p)) (by omega : -((k : ℤ) + 1) < -(k : ℤ))]

@[simp]
theorem norm_algebraMap_U :
    ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) U‖ = 1 := by
  simpa using norm_algebraMap_U_pow hα 1

@[simp]
theorem norm_natCast_p : ‖(p : AnnularLaurent p hα)‖ = α := by
  have hp : (p : AnnularLaurent p hα) =
      (((pseudoUniformizer hα p).unit : (AnnularLaurent p hα)ˣ) : AnnularLaurent p hα) *
        algebraMap (AnnularRing p) (AnnularLaurent p hα) U := by
    rw [pseudoUniformizer_unit, val_unitT, ← map_mul, T_mul_U, map_natCast]
  rw [hp, (pseudoUniformizer hα p).norm_mul, pseudoUniformizer_unit, val_unitT,
    norm_algebraMap_T, norm_algebraMap_U, mul_one]

/-- `AnnularLaurent p hα` is complete in its Tate gauge metric. -/
instance instCompleteSpace : CompleteSpace (AnnularLaurent p hα) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  have hcauchy (m : ℤ) : CauchySeq fun n ↦ coeff (u n) m := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (p : ℝ) ^ (-(k : ℤ)) < ε := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ (one_lt_p (p := p)))
      exact ⟨k, by simpa [zpow_neg, zpow_natCast, inv_pow] using hk⟩
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu (α ^ (m + k)) (zpow_pos hα.1 _)
    refine ⟨N, fun i hi j hj ↦ ?_⟩
    have hij : ‖u i - u j‖ ≤ α ^ (m + k) := by
      simpa [dist_eq_norm] using (hN i hi j hj).le
    have hm := (norm_le_zpow_iff_norm_coeff_le hα (u i - u j) (m + k)).1 hij m
    rw [dist_eq_norm, ← Pi.sub_apply, ← LinearMap.map_sub]
    exact (hm.trans_eq (by rw [show min (0 : ℤ) (m - (m + k)) = -(k : ℤ) by omega])).trans_lt hk
  choose d hd using fun m ↦ cauchySeq_tendsto_of_complete (hcauchy m)
  obtain ⟨N₀, hN₀⟩ := Metric.cauchySeq_iff.1 hu 1 zero_lt_one
  have hy_bound (m : ℤ) : ‖coeff (u N₀) m - d m‖ ≤ (p : ℝ) ^ min 0 m := by
    have hlim : Tendsto (fun j ↦ ‖coeff (u N₀) m - coeff (u j) m‖) atTop
        (𝓝 ‖coeff (u N₀) m - d m‖) :=
      (tendsto_const_nhds.sub (hd m)).norm
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨N₀, fun j hj ↦ ?_⟩)
    have hle : ‖u N₀ - u j‖ ≤ α ^ (0 : ℤ) := by
      simpa [dist_eq_norm] using (hN₀ N₀ le_rfl j hj).le
    have hm := (norm_le_zpow_iff_norm_coeff_le hα (u N₀ - u j) 0).1 hle m
    simpa [LinearMap.map_sub] using hm
  let y : AnnularRing p := ⟨fun m ↦ coeff (u N₀) m - d m, hy_bound⟩
  let z : AnnularLaurent p hα := u N₀ - algebraMap (AnnularRing p) (AnnularLaurent p hα) y
  have hz_coeff (m : ℤ) : coeff z m = d m := by
    simp [z, y]
  refine ⟨z, Metric.tendsto_atTop.2 fun ε hε ↦ ?_⟩
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε hα.2
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu (α ^ (r : ℤ)) (zpow_pos hα.1 _)
  refine ⟨N, fun i hi ↦ ?_⟩
  rw [dist_eq_norm]
  have hle : ‖u i - z‖ ≤ α ^ (r : ℤ) :=
    (norm_le_zpow_iff_norm_coeff_le hα (u i - z) r).2 fun m ↦ by
      rw [LinearMap.map_sub, Pi.sub_apply, hz_coeff]
      have hlim : Tendsto (fun j ↦ ‖coeff (u i) m - coeff (u j) m‖) atTop
          (𝓝 ‖coeff (u i) m - d m‖) :=
        (tendsto_const_nhds.sub (hd m)).norm
      refine le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun j hj ↦ ?_⟩)
      have hij : ‖u i - u j‖ ≤ α ^ (r : ℤ) := by
        simpa [dist_eq_norm] using (hN i hi j hj).le
      simpa [LinearMap.map_sub] using
        (norm_le_zpow_iff_norm_coeff_le hα (u i - u j) r).1 hij m
  exact hle.trans_lt (by simpa [zpow_natCast] using hr)

/-- The scalar map `ℤ_p →+* AnnularLaurent p hα` is continuous (`p ^ k` maps to `(T U) ^ k`, of
norm `α ^ k`). -/
theorem continuous_algebraMap_padicInt :
    Continuous (algebraMap ℤ_[p] (AnnularLaurent p hα)) := by
  refine continuous_of_continuousAt_zero (algebraMap ℤ_[p] (AnnularLaurent p hα)).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hα.2
  rw [Metric.eventually_nhds_iff]
  refine ⟨(p : ℝ) ^ (-(k : ℤ)), zpow_pos (zero_lt_one.trans (one_lt_p (p := p))) _, fun c hc ↦ ?_⟩
  rw [dist_zero_right] at hc ⊢
  have hmem : c ∈ Ideal.span {(p : ℤ_[p]) ^ k} :=
    (PadicInt.norm_le_pow_iff_mem_span_pow c k).1 hc.le
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hmem
  change ‖algebraMap ℤ_[p] (AnnularLaurent p hα) (q * (p : ℤ_[p]) ^ k)‖ < ε
  rw [map_mul, map_pow, map_natCast]
  have hq : ‖algebraMap ℤ_[p] (AnnularLaurent p hα) q‖ ≤ 1 := by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] (AnnularRing p) (AnnularLaurent p hα)]
    exact norm_algebraMap_le_one hα _
  refine (norm_mul_le _ _).trans_lt ?_
  refine (mul_le_of_le_one_left (norm_nonneg _) hq).trans_lt ?_
  exact (norm_pow_le (p : AnnularLaurent p hα) k).trans_lt (by simpa [norm_natCast_p hα] using hk)

instance : ContinuousSMul ℤ_[p] (AnnularLaurent p hα) :=
  ⟨by
    simp_rw [Algebra.smul_def]
    exact (continuous_algebraMap_padicInt hα |>.comp continuous_fst).mul continuous_snd⟩

/-- The powers `U ^ k` are not summable in `AnnularLaurent p hα`, because every term has gauge norm
`1`. -/
theorem not_summable_algebraMap_U_pow :
    ¬ Summable fun k : ℕ ↦ algebraMap (AnnularRing p) (AnnularLaurent p hα) U ^ k := by
  intro hs
  have h0 : Tendsto (fun k : ℕ ↦ ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) U ^ k‖)
      atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    exact tendsto_norm_zero.comp hs.tendsto_cofinite_zero
  simp only [norm_algebraMap_U_pow] at h0
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h0)

/-- Although `∑_{k ≥ 0} U ^ k` diverges in the Tate gauge topology, `1 - U` is a unit in
`AnnularLaurent p hα` with explicit inverse `ofPowerSeriesU (PowerSeries.mk 1)`. -/
theorem one_sub_algebraMap_U_mul_inv :
    (1 - algebraMap (AnnularRing p) (AnnularLaurent p hα) U) *
      algebraMap (AnnularRing p) (AnnularLaurent p hα) (ofPowerSeriesU (PowerSeries.mk 1)) = 1 := by
  rw [← map_one (algebraMap (AnnularRing p) _), ← map_sub, ← map_mul,
    one_sub_U_mul_ofPowerSeriesU_mk_one, map_one]

theorem isUnit_one_sub_algebraMap_U :
    IsUnit (1 - algebraMap (AnnularRing p) (AnnularLaurent p hα) U) :=
  .of_mul_eq_one _ (one_sub_algebraMap_U_mul_inv hα)

end Instances

end AnnularLaurent

end TauCeti
