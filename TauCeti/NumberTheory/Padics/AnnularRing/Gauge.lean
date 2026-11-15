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

Inverting the non-zero-divisor `T` in `H = AnnularRing p` gives `Localization.Away T` with unique
two-sided coefficients `awayCoeff z : ℤ → ℤ_[p]`. For `α ∈ (0, 1)`, `TauCeti.AnnularLaurent p hα`
equips `Localization.Away T` with the complete ultrametric Tate gauge norm (`‖T‖ = α`, `‖p‖ = α`,
`‖U ^ k‖ = 1`, closed unit ball `H`), making it a Banach–Tate ring (`NormedRing.IsTate`) in which
`∑ U ^ k` is not summable yet `1 - U` is a unit.

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

@[simp] theorem coeff_T_pow_mul (x : AnnularRing p) (k : ℕ) (m : ℤ) :
    ((T : AnnularRing p) ^ k * x).coeff m = x.coeff (m - k) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, coeff_T_mul, ih]; exact congr_arg x.coeff (by omega)

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
  have heq : (T : AnnularRing p) ^ k * s.1 = T ^ s.2 * x :=
    algebraMap_localizationAway_injective <| by
      rw [map_mul, map_mul, map_pow, map_pow, mul_comm _ (algebraMap _ _ s.1), ← hs,
        mul_right_comm, hz, mul_comm]
  have hm := congr_arg (coeff · (m + s.2 + k)) heq
  have hidx : m + (s.2 : ℤ) + k - s.2 = m + k := by omega
  simpa [awayCoeffAux, s, coeff_T_pow_mul, add_sub_cancel_right, hidx] using hm

/-- Two-sided coefficient map on `Localization.Away (T : AnnularRing p)`, sending `x / T ^ k` to
`m ↦ x.coeff (m + k)`. -/
def awayCoeff : Localization.Away (T : AnnularRing p) →ₗ[ℤ_[p]] (ℤ → ℤ_[p]) where
  toFun := awayCoeffAux
  map_add' z₁ z₂ := by
    obtain ⟨k₁, x₁, hx₁⟩ := IsLocalization.Away.surj (T : AnnularRing p) z₁
    obtain ⟨k₂, x₂, hx₂⟩ := IsLocalization.Away.surj (T : AnnularRing p) z₂
    have h₁₂ : (z₁ + z₂) * algebraMap (AnnularRing p) _ T ^ (k₁ + k₂) =
        algebraMap (AnnularRing p) _ (T ^ k₂ * x₁ + T ^ k₁ * x₂) := by
      rw [pow_add, add_mul, ← mul_assoc, hx₁, ← mul_assoc, mul_right_comm z₂, hx₂,
        map_add, map_mul, map_mul, map_pow, map_pow]; ring
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

theorem awayCoeff_eq_of_mul_pow_eq {z : Localization.Away (T : AnnularRing p)}
    {k : ℕ} {x : AnnularRing p}
    (hz : z * algebraMap (AnnularRing p) _ T ^ k = algebraMap (AnnularRing p) _ x) (m : ℤ) :
    awayCoeff z m = x.coeff (m + k) := awayCoeffAux_eq_of_mul_pow_eq hz m

@[simp] theorem awayCoeff_algebraMap (x : AnnularRing p) (m : ℤ) :
    awayCoeff (algebraMap (AnnularRing p) (Localization.Away (T : AnnularRing p)) x) m =
      x.coeff m := by
  simpa using awayCoeff_eq_of_mul_pow_eq (k := 0) (x := x) (by simp) m

@[simp] theorem awayCoeff_one (m : ℤ) :
    awayCoeff (1 : Localization.Away (T : AnnularRing p)) m = if m = 0 then 1 else 0 := by
  rw [← map_one (algebraMap (AnnularRing p) _), awayCoeff_algebraMap, coeff_one]

@[simp] theorem awayCoeff_mul_algebraMap_T (z : Localization.Away (T : AnnularRing p)) (m : ℤ) :
    awayCoeff (algebraMap (AnnularRing p) _ T * z) m = awayCoeff z (m - 1) := by
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (T : AnnularRing p) z
  have hTz : (algebraMap (AnnularRing p) _ T * z) * algebraMap (AnnularRing p) _ T ^ k =
      algebraMap (AnnularRing p) _ (T * x) := by rw [mul_assoc, hx, map_mul]
  rw [awayCoeff_eq_of_mul_pow_eq hTz, coeff_T_mul, awayCoeff_eq_of_mul_pow_eq hx]
  exact congr_arg _ (by omega)

theorem awayCoeff_injective : Function.Injective (awayCoeff (p := p)) := by
  refine LinearMap.ker_eq_bot.1 ((Submodule.eq_bot_iff _).2 fun z hz ↦ ?_)
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (T : AnnularRing p) z
  have hx0 : x = 0 := AnnularRing.ext <| funext fun n ↦ by
    simpa [awayCoeff_eq_of_mul_pow_eq hx, sub_add_cancel] using congr_fun hz (n - k)
  rw [hx0, map_zero] at hx
  exact (IsLocalization.Away.algebraMap_pow_isUnit (T : AnnularRing p) k).mul_left_eq_zero.1 hx

theorem mem_range_algebraMap_iff_norm_awayCoeff_le (z : Localization.Away (T : AnnularRing p)) :
    z ∈ (algebraMap (AnnularRing p) (Localization.Away (T : AnnularRing p))).range ↔
      ∀ m : ℤ, ‖awayCoeff z m‖ ≤ (p : ℝ) ^ min 0 m :=
  ⟨by rintro ⟨x, rfl⟩ m; simpa using x.norm_coeff_le m,
    fun h ↦ ⟨⟨awayCoeff z, h⟩, awayCoeff_injective <| funext fun m ↦ awayCoeff_algebraMap _ m⟩⟩

theorem mem_range_awayCoeff_iff (d : ℤ → ℤ_[p]) :
    d ∈ Set.range (awayCoeff (p := p)) ↔
      ∃ k : ℕ, ∀ m : ℤ, ‖d m‖ ≤ (p : ℝ) ^ min 0 (m + k) := by
  refine ⟨?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (T : AnnularRing p) z
    exact ⟨k, fun m ↦ (awayCoeff_eq_of_mul_pow_eq hx m) ▸ x.norm_coeff_le (m + k)⟩
  · let x : AnnularRing p := ⟨fun n ↦ d (n - k), fun n ↦ by simpa using hk (n - k)⟩
    let s : Submonoid.powers (T : AnnularRing p) := ⟨T ^ k, k, rfl⟩
    have hz : IsLocalization.mk' (Localization.Away (T : AnnularRing p)) x s *
        algebraMap (AnnularRing p) _ T ^ k = algebraMap (AnnularRing p) _ x := by
      simpa [s, map_pow] using IsLocalization.mk'_spec (Localization.Away (T : AnnularRing p)) x s
    exact ⟨_, funext fun m ↦ (awayCoeff_eq_of_mul_pow_eq hz m).trans
      (congr_arg d (add_sub_cancel_right m k))⟩

end AnnularRing

/-! ### The Banach–Tate Laurent ring `AnnularLaurent p hα` -/

/-- `Localization.Away (T : AnnularRing p)` equipped with the Tate gauge norm `‖T‖ = α ∈ (0, 1)`.
-/
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
def coeff {hα : α ∈ Set.Ioo 0 1} : AnnularLaurent p hα →ₗ[ℤ_[p]] (ℤ → ℤ_[p]) := awayCoeff (p := p)

@[simp] theorem coeff_algebraMap {hα : α ∈ Set.Ioo 0 1} (x : AnnularRing p) (m : ℤ) :
    coeff (algebraMap (AnnularRing p) (AnnularLaurent p hα) x) m = x.coeff m :=
  awayCoeff_algebraMap x m
@[simp] theorem coeff_one {hα : α ∈ Set.Ioo 0 1} (m : ℤ) :
    coeff (1 : AnnularLaurent p hα) m = if m = 0 then 1 else 0 := awayCoeff_one m
@[simp] theorem coeff_mul_algebraMap_T {hα : α ∈ Set.Ioo 0 1} (z : AnnularLaurent p hα) (m : ℤ) :
    coeff (algebraMap (AnnularRing p) (AnnularLaurent p hα) T * z) m = coeff z (m - 1) :=
  awayCoeff_mul_algebraMap_T z m

theorem coeff_injective {hα : α ∈ Set.Ioo 0 1} :
    Function.Injective (coeff (p := p) (hα := hα)) := awayCoeff_injective

/-- Identity `AnnularRing p`-algebra equivalence changing the gauge parameter from `α` to `β`. -/
def ofRadius {β : ℝ} (hα : α ∈ Set.Ioo 0 1) (hβ : β ∈ Set.Ioo 0 1) :
    AnnularLaurent p hα ≃ₐ[AnnularRing p] AnnularLaurent p hβ := AlgEquiv.refl

@[simp] theorem coeff_ofRadius {β : ℝ} (hα : α ∈ Set.Ioo 0 1) (hβ : β ∈ Set.Ioo 0 1)
    (z : AnnularLaurent p hα) : coeff (ofRadius hα hβ z) = coeff z := (rfl)

/-- `T` as a unit of `AnnularLaurent p hα`. -/
def unitT (p : ℕ) [Fact p.Prime] (hα : α ∈ Set.Ioo 0 1) : (AnnularLaurent p hα)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := AnnularLaurent p hα) (T : AnnularRing p)).unit

@[simp] theorem val_unitT (hα : α ∈ Set.Ioo 0 1) :
    (unitT p hα : AnnularLaurent p hα) = algebraMap (AnnularRing p) (AnnularLaurent p hα) T := (rfl)

/-- The canonical ring of definition of `AnnularLaurent p hα`: the image of `AnnularRing p`. -/
def ringOfDefinition (p : ℕ) [Fact p.Prime] (hα : α ∈ Set.Ioo 0 1) :
    Subring (AnnularLaurent p hα) := (algebraMap (AnnularRing p) (AnnularLaurent p hα)).range

theorem mem_ringOfDefinition_iff {hα : α ∈ Set.Ioo 0 1} (z : AnnularLaurent p hα) :
    z ∈ ringOfDefinition p hα ↔
      z ∈ (algebraMap (AnnularRing p) (AnnularLaurent p hα)).range := Iff.rfl
theorem mem_ringOfDefinition_iff_norm_coeff_le {hα : α ∈ Set.Ioo 0 1} (z : AnnularLaurent p hα) :
    z ∈ ringOfDefinition p hα ↔ ∀ m : ℤ, ‖coeff z m‖ ≤ (p : ℝ) ^ min 0 m :=
  mem_range_algebraMap_iff_norm_awayCoeff_le z
theorem unitT_mem_ringOfDefinition (hα : α ∈ Set.Ioo 0 1) :
    (unitT p hα : AnnularLaurent p hα) ∈ ringOfDefinition p hα := ⟨T, rfl⟩

theorem exists_zpow_unitT_mul_mem (hα : α ∈ Set.Ioo 0 1) (z : AnnularLaurent p hα) :
    ∃ n : ℤ, (unitT p hα ^ n).val * z ∈ ringOfDefinition p hα := by
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (T : AnnularRing p) z
  exact ⟨k, x, by rw [zpow_natCast, Units.val_pow_eq_pow_val, val_unitT, mul_comm, hx]⟩

@[simp] theorem coeff_zpow_unitT_mul (hα : α ∈ Set.Ioo 0 1) (k : ℤ) (z : AnnularLaurent p hα)
    (m : ℤ) : coeff ((unitT p hα ^ k).val * z) m = coeff z (m - k) := by
  have hnat (n : ℕ) (w : AnnularLaurent p hα) (q : ℤ) :
      coeff ((unitT p hα ^ (n : ℤ)).val * w) q = coeff w (q - n) := by
    induction n generalizing w q with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, zpow_add, zpow_one, Units.val_mul, mul_assoc, val_unitT, ih,
        coeff_mul_algebraMap_T]
      exact congr_arg (coeff w) (by omega)
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk; exact hnat k z m
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -n := ⟨(-k).toNat, by omega⟩
    let w : AnnularLaurent p hα := (unitT p hα ^ (-(n : ℤ))).val * z
    have hcancel : (unitT p hα ^ (n : ℤ)).val * w = z := by
      simp only [w, ← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
        Units.val_one, one_mul]
    have := hnat n w (m + n)
    rw [hcancel, add_sub_cancel_right] at this
    simpa [w, sub_neg_eq_add] using this.symm

private theorem zpow_unitT_neg_mul_mem_iff (hα : α ∈ Set.Ioo 0 1) (z : AnnularLaurent p hα)
    (r : ℤ) : (unitT p hα ^ (-r)).val * z ∈ ringOfDefinition p hα ↔
      ∀ m : ℤ, ‖coeff z m‖ ≤ (p : ℝ) ^ min 0 (m - r) := by
  rw [mem_ringOfDefinition_iff_norm_coeff_le]
  refine ⟨fun h m ↦ ?_, fun h n ↦ ?_⟩
  · have hm := h (m - r); rwa [coeff_zpow_unitT_mul, sub_neg_eq_add, sub_add_cancel] at hm
  · rw [coeff_zpow_unitT_mul, sub_neg_eq_add]; simpa using h (n + r)

private theorem tateGauge_le_zpow_iff_coeff (hα : α ∈ Set.Ioo 0 1) (z : AnnularLaurent p hα)
    (r : ℤ) : Huber.tateGauge (ringOfDefinition p hα) (unitT p hα) α⁻¹ z ≤ α ^ r ↔
      ∀ m : ℤ, ‖coeff z m‖ ≤ (p : ℝ) ^ min 0 (m - r) := by
  have hpow : (α⁻¹) ^ (-r) = α ^ r := by rw [inv_zpow, zpow_neg, inv_inv]
  rw [← hpow, Huber.tateGauge_le_zpow_iff (unitT_mem_ringOfDefinition hα)
    (exists_zpow_unitT_mul_mem hα z) (one_lt_inv_of_mem_Ioo hα), zpow_unitT_neg_mul_mem_iff]

/-- The Tate gauge of `(ringOfDefinition p hα, unitT p hα, α⁻¹)` as a `RingNorm` on
`AnnularLaurent p hα`. -/
def ringNorm (p : ℕ) [Fact p.Prime] (hα : α ∈ Set.Ioo 0 1) : RingNorm (AnnularLaurent p hα) :=
  let s := Huber.tateSeminorm (unitT_mem_ringOfDefinition (p := p) hα)
    (exists_zpow_unitT_mul_mem hα) (one_lt_inv_of_mem_Ioo hα)
  have hs : ⇑s = Huber.tateGauge (ringOfDefinition p hα) (unitT p hα) α⁻¹ :=
    Huber.coe_tateSeminorm (unitT_mem_ringOfDefinition (p := p) hα)
      (exists_zpow_unitT_mul_mem hα) (one_lt_inv_of_mem_Ioo hα)
  { toFun := Huber.tateGauge (ringOfDefinition p hα) (unitT p hα) α⁻¹
    map_zero' := hs ▸ map_zero s
    add_le' := hs ▸ map_add_le_add s
    neg' := hs ▸ map_neg_eq_map s
    mul_le' := hs ▸ map_mul_le_mul s
    eq_zero_of_map_eq_zero' z hz := coeff_injective <| funext fun m ↦ by
      rw [LinearMap.map_zero, Pi.zero_apply, ← norm_eq_zero]
      refine le_antisymm ?_ (norm_nonneg _)
      by_contra! hpos
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ (one_lt_p (p := p)))
      have hle : Huber.tateGauge (ringOfDefinition p hα) (unitT p hα) α⁻¹ z ≤ α ^ (m + k) :=
        hz ▸ zpow_nonneg hα.1.le _
      have hm := (tateGauge_le_zpow_iff_coeff hα z (m + k)).1 hle m
      have hmin : min (0 : ℤ) (m - (m + k)) = -(k : ℤ) := by omega
      rw [hmin, zpow_neg, zpow_natCast, ← inv_pow] at hm
      linarith }

instance instNormedCommRing (hα : α ∈ Set.Ioo 0 1) : NormedCommRing (AnnularLaurent p hα) where
  __ := (ringNorm p hα).toNormedRing
  mul_comm := mul_comm

theorem norm_def (hα : α ∈ Set.Ioo 0 1) (z : AnnularLaurent p hα) :
    ‖z‖ = Huber.tateGauge (ringOfDefinition p hα) (unitT p hα) α⁻¹ z := (rfl)

instance (hα : α ∈ Set.Ioo 0 1) : IsUltrametricDist (AnnularLaurent p hα) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦
    Huber.isNonarchimedean_tateGauge (unitT_mem_ringOfDefinition hα)
      (exists_zpow_unitT_mul_mem hα) (inv_nonneg.2 hα.1.le) x y

variable (hα : α ∈ Set.Ioo 0 1)

theorem norm_le_zpow_iff (z : AnnularLaurent p hα) (r : ℤ) :
    ‖z‖ ≤ α ^ r ↔ ↑(unitT p hα ^ (-r)) * z ∈ ringOfDefinition p hα := by
  have hpow : (α⁻¹) ^ (-r) = α ^ r := by rw [inv_zpow, zpow_neg, inv_inv]
  rw [norm_def, ← hpow]
  exact Huber.tateGauge_le_zpow_iff (unitT_mem_ringOfDefinition hα)
    (exists_zpow_unitT_mul_mem hα z) (one_lt_inv_of_mem_Ioo hα)

theorem norm_le_zpow_iff_norm_coeff_le (z : AnnularLaurent p hα) (r : ℤ) :
    ‖z‖ ≤ α ^ r ↔ ∀ m : ℤ, ‖coeff z m‖ ≤ (p : ℝ) ^ min 0 (m - r) :=
  tateGauge_le_zpow_iff_coeff hα z r

private theorem norm_eq_one_of_mem_of_not_le {z : AnnularLaurent p hα}
    (hz : z ∈ ringOfDefinition p hα) (hnot : ¬ ‖z‖ ≤ α) : ‖z‖ = 1 := by
  rw [norm_def] at hnot ⊢
  refine le_antisymm (Huber.tateGauge_le_one hz) ?_
  by_contra! hlt
  obtain ⟨n, hn, hnr⟩ := (Huber.tateGauge_lt_iff (inv_nonneg.2 hα.1.le)
    (exists_zpow_unitT_mul_mem hα z)).1 hlt
  have hpow : (α⁻¹) ^ (-n) < (α⁻¹) ^ (0 : ℤ) := by simpa using hnr
  have hn1 : (1 : ℤ) ≤ n := by
    have := (zpow_lt_zpow_iff_right₀ (one_lt_inv_of_mem_Ioo hα)).1 hpow; omega
  exact hnot <| by
    simpa using Huber.tateGauge_le_zpow (inv_nonneg.2 hα.1.le)
      (Huber.zpow_neg_mul_mem_of_le (unitT_mem_ringOfDefinition hα) hn1 hn)

private theorem norm_one_eq : ‖(1 : AnnularLaurent p hα)‖ = 1 := by
  refine norm_eq_one_of_mem_of_not_le hα (Subring.one_mem _) fun h ↦ ?_
  have h0 := (norm_le_zpow_iff_norm_coeff_le hα 1 1).1 (by simpa using h) 0
  have hmin : min (0 : ℤ) (-1) = -1 := by omega
  simp only [coeff_one, ite_true, norm_one, zero_sub, hmin] at h0
  linarith [zpow_lt_one_of_neg₀ (one_lt_p (p := p)) (by omega : (-1 : ℤ) < 0)]

@[simp] theorem norm_algebraMap_T : ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) T‖ = α := by
  have h := Huber.tateGauge_zpow_mul (A₀ := ringOfDefinition p hα) (ϖ := unitT p hα)
    (inv_pos.2 hα.1) 1 1
  simpa [← norm_def hα, norm_one_eq hα] using h

/-- `T` as a multiplicative pseudo-uniformiser of `AnnularLaurent p hα`, with `‖T‖ = α`. -/
def pseudoUniformizer (p : ℕ) [Fact p.Prime] :
    NormedRing.PseudoUniformizer (AnnularLaurent p hα) where
  unit := unitT p hα
  norm_mul x := by
    rw [val_unitT, norm_algebraMap_T, norm_def, norm_def]
    simpa using Huber.tateGauge_zpow_mul (A₀ := ringOfDefinition p hα) (ϖ := unitT p hα)
      (inv_pos.2 hα.1) 1 x
  norm_pos := by rw [val_unitT, norm_algebraMap_T]; exact hα.1
  norm_lt_one := by rw [val_unitT, norm_algebraMap_T]; exact hα.2

@[simp] theorem pseudoUniformizer_unit : (pseudoUniformizer hα p).unit = unitT p hα := (rfl)

instance instIsTate : NormedRing.IsTate (AnnularLaurent p hα) := ⟨⟨pseudoUniformizer hα p⟩⟩

/-- The closed unit ball of `AnnularLaurent p hα` is the image of `AnnularRing p`. -/
theorem unitClosedBall_eq_range_algebraMap :
    Subring.unitClosedBall (AnnularLaurent p hα) =
      (algebraMap (AnnularRing p) (AnnularLaurent p hα)).range := by
  ext z; simpa [mem_ringOfDefinition_iff] using norm_le_zpow_iff hα z 0

theorem norm_algebraMap_le_one (x : AnnularRing p) :
    ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) x‖ ≤ 1 := by
  rw [← Subring.mem_unitClosedBall, unitClosedBall_eq_range_algebraMap]; exact ⟨x, rfl⟩

/-- Changing the gauge parameter from `α` to `β` raises the norm to `log β / log α`. -/
theorem norm_ofRadius {β : ℝ} (hβ : β ∈ Set.Ioo 0 1) (z : AnnularLaurent p hα) :
    ‖ofRadius hα hβ z‖ = ‖z‖ ^ (Real.log β / Real.log α) := by
  have hexp : Real.log β⁻¹ / Real.log α⁻¹ = Real.log β / Real.log α := by
    rw [Real.log_inv, Real.log_inv, neg_div_neg_eq]
  rw [norm_def hβ, norm_def hα, ← hexp]
  exact Huber.tateGauge_rpow (one_lt_inv_of_mem_Ioo hα) (one_lt_inv_of_mem_Ioo hβ) z

@[simp] theorem norm_algebraMap_U_pow (k : ℕ) :
    ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) U ^ k‖ = 1 := by
  rw [← map_pow]
  refine norm_eq_one_of_mem_of_not_le hα ⟨U ^ k, rfl⟩ fun h ↦ ?_
  have hk := (norm_le_zpow_iff_norm_coeff_le hα
    (algebraMap (AnnularRing p) (AnnularLaurent p hα) (U ^ k)) 1).1 (by simpa using h) (-(k : ℤ))
  have hmin : min (0 : ℤ) (-(k : ℤ) - 1) = -((k : ℤ) + 1) := by omega
  rw [coeff_algebraMap, coeff_U_pow, ite_eq_left rfl, PadicInt.norm_p_pow, hmin] at hk
  linarith [zpow_lt_zpow_right₀ (one_lt_p (p := p)) (by omega : -((k : ℤ) + 1) < -(k : ℤ))]

@[simp] theorem norm_algebraMap_U : ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) U‖ = 1 := by
  simpa using norm_algebraMap_U_pow hα 1

@[simp] theorem norm_natCast_p : ‖(p : AnnularLaurent p hα)‖ = α := by
  have hp : (p : AnnularLaurent p hα) = ((pseudoUniformizer hα p).unit : AnnularLaurent p hα) *
      algebraMap (AnnularRing p) (AnnularLaurent p hα) U := by
    rw [pseudoUniformizer_unit, val_unitT, ← map_mul, T_mul_U, map_natCast]
  rw [hp, (pseudoUniformizer hα p).norm_mul, pseudoUniformizer_unit, val_unitT,
    norm_algebraMap_T, norm_algebraMap_U, mul_one]

private theorem norm_coeff_sub_lim_le {u : ℕ → AnnularLaurent p hα} {d : ℤ → ℤ_[p]}
    (hd : ∀ m, Tendsto (fun j ↦ coeff (u j) m) atTop (𝓝 (d m))) {r : ℤ} {N i : ℕ}
    (hN : ∀ j ≥ N, ‖u i - u j‖ ≤ α ^ r) (m : ℤ) :
    ‖coeff (u i) m - d m‖ ≤ (p : ℝ) ^ min 0 (m - r) :=
  le_of_tendsto ((tendsto_const_nhds.sub (hd m)).norm) <| eventually_atTop.2 ⟨N, fun j hj ↦ by
    simpa [LinearMap.map_sub] using (norm_le_zpow_iff_norm_coeff_le hα (u i - u j) r).1 (hN j hj) m⟩

instance instCompleteSpace : CompleteSpace (AnnularLaurent p hα) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  have hcauchy (m : ℤ) : CauchySeq fun n ↦ coeff (u n) m := by
    refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ (one_lt_p (p := p)))
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu (α ^ (m + k)) (zpow_pos hα.1 _)
    refine ⟨N, fun i hi j hj ↦ ?_⟩
    have hm := (norm_le_zpow_iff_norm_coeff_le hα (u i - u j) (m + k)).1
      (by simpa [dist_eq_norm] using (hN i hi j hj).le) m
    have hmin : min (0 : ℤ) (m - (m + k)) = -(k : ℤ) := by omega
    rw [dist_eq_norm, ← Pi.sub_apply, ← LinearMap.map_sub]
    exact (hm.trans_eq (by rw [hmin, zpow_neg, zpow_natCast, inv_pow])).trans_lt hk
  choose d hd using fun m ↦ cauchySeq_tendsto_of_complete (hcauchy m)
  obtain ⟨N₀, hN₀⟩ := Metric.cauchySeq_iff.1 hu 1 zero_lt_one
  let y : AnnularRing p := ⟨fun m ↦ coeff (u N₀) m - d m, fun m ↦ by
    simpa using norm_coeff_sub_lim_le hα hd (r := 0) (N := N₀)
      (fun j hj ↦ by simpa [dist_eq_norm] using (hN₀ N₀ le_rfl j hj).le) m⟩
  let z : AnnularLaurent p hα := u N₀ - algebraMap (AnnularRing p) (AnnularLaurent p hα) y
  refine ⟨z, Metric.tendsto_atTop.2 fun ε hε ↦ ?_⟩
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε hα.2
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu (α ^ (r : ℤ)) (zpow_pos hα.1 _)
  refine ⟨N, fun i hi ↦ ?_⟩
  have hle : ‖u i - z‖ ≤ α ^ (r : ℤ) := (norm_le_zpow_iff_norm_coeff_le hα _ r).2 fun m ↦ by
    simpa [z, y] using norm_coeff_sub_lim_le hα hd (r := r) (N := N)
      (fun j hj ↦ by simpa [dist_eq_norm] using (hN i hi j hj).le) m
  exact (dist_eq_norm (u i) z).trans_lt (hle.trans_lt (by simpa [zpow_natCast] using hr))

theorem continuous_algebraMap_padicInt :
    Continuous (algebraMap ℤ_[p] (AnnularLaurent p hα)) := by
  refine continuous_of_continuousAt_zero (algebraMap ℤ_[p] (AnnularLaurent p hα)).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hα.2
  refine Metric.eventually_nhds_iff.2
    ⟨(p : ℝ) ^ (-(k : ℤ)), zpow_pos (zero_lt_one.trans (one_lt_p (p := p))) _, fun c hc ↦ ?_⟩
  rw [dist_zero_right] at hc ⊢
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1
    ((PadicInt.norm_le_pow_iff_mem_span_pow c k).1 hc.le)
  rw [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, map_mul, map_pow, map_natCast]
  have hq : ‖algebraMap ℤ_[p] (AnnularLaurent p hα) q‖ ≤ 1 := by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] (AnnularRing p) (AnnularLaurent p hα)]
    exact norm_algebraMap_le_one hα _
  exact (norm_mul_le _ _).trans_lt <| (mul_le_of_le_one_left (norm_nonneg _) hq).trans_lt <|
    (norm_pow_le (p : AnnularLaurent p hα) k).trans_lt (by simpa [norm_natCast_p hα] using hk)

instance : ContinuousSMul ℤ_[p] (AnnularLaurent p hα) :=
  ⟨by simp_rw [Algebra.smul_def]
      exact (continuous_algebraMap_padicInt hα |>.comp continuous_fst).mul continuous_snd⟩

theorem not_summable_algebraMap_U_pow :
    ¬ Summable fun k : ℕ ↦ algebraMap (AnnularRing p) (AnnularLaurent p hα) U ^ k := fun hs ↦ by
  have h0 : Tendsto (fun k : ℕ ↦ ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) U ^ k‖)
      atTop (𝓝 0) := Nat.cofinite_eq_atTop ▸ tendsto_norm_zero.comp hs.tendsto_cofinite_zero
  simp only [norm_algebraMap_U_pow] at h0
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h0)

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
