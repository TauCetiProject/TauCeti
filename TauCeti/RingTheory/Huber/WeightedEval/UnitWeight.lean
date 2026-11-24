/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Monoid.MulUnit
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Huber.WeightedEval.Finite

import Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful
import TauCeti.Analysis.Normed.Ring.MulUnit

/-!
# Evaluation bounds for singleton and unit weights in normed rings

For singleton weights `Tᵢ = {tᵢ}`,
`TauCeti.Huber.isWeightBounded_singleton_iff_forall_isPowerBounded` reduces
`TauCeti.Huber.IsWeightBounded` along a ring homomorphism `φ : R →+* S` to coordinatewise
power-boundedness of `φ (t i) * a i`. Over seminormed commutative rings, this file converts between
that topological boundedness condition and coordinatewise norm bounds `‖aᵢ‖ ≤ cᵢ`.

In the forward direction, norm bounds `‖tᵢ‖ * cᵢ ≤ 1` and `‖aᵢ‖ ≤ cᵢ` always imply
`IsWeightBounded` along any bounded ring homomorphism `φ`, without requiring `tᵢ` to be a unit,
`‖1‖ = 1`, or multiplicativity of the norms. In the converse direction, whenever `tᵢ` is a
multiplicative unit (`TauCeti.IsNormMulUnit`) and the target seminorm is power-multiplicative and
bounds power-bounded elements by `1`, `IsWeightBounded` yields `‖aᵢ‖ ≤ ‖tᵢ‖⁻¹` (and hence
`‖aᵢ‖ ≤ c` whenever `1 ≤ ‖tᵢ‖ * c`). Specialising to targets with a pseudouniformiser or to normed
fields identifies unit-weight boundedness with polydisc bounds `∀ i, ‖aᵢ‖ ≤ cᵢ`.

## Main results

* `TauCeti.Huber.isWeightBounded_singleton_of_norm_le`: norm bounds `‖tᵢ‖ * cᵢ ≤ 1` and
  `‖aᵢ‖ ≤ cᵢ` imply `IsWeightBounded` for singleton weights `{tᵢ}`.
* `TauCeti.Huber.norm_le_inv_norm_of_isWeightBounded_singleton` and
  `TauCeti.Huber.norm_le_of_isWeightBounded_singleton`: general elimination from singleton
  weight-boundedness to `‖aᵢ‖ ≤ ‖tᵢ‖⁻¹` and `‖aᵢ‖ ≤ c` at any multiplicative-unit coordinate.
* `TauCeti.Huber.IsPseudoUniformizer.isWeightBounded_units_iff_norm_le` and
  `TauCeti.Huber.isWeightBounded_units_iff_norm_le`: equivalence between `IsWeightBounded` for
  multiplicative-unit weights and coordinatewise polydisc bounds `‖aᵢ‖ ≤ cᵢ`.
* `TauCeti.Huber.radii_comp_eq_of_singleton_subset`: reindexing compatibility of reciprocal
  polyradii under inclusion of singleton weights.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], §5.6, Proposition 5.50.
-/

public section

namespace TauCeti.Huber

variable {k : ℕ}

/-- Norm bounds `‖tᵢ‖ * cᵢ ≤ 1` and `‖aᵢ‖ ≤ cᵢ` imply `IsWeightBounded` for singleton weights
`Tᵢ = {tᵢ}` along any bounded ring homomorphism `‖φ r‖ ≤ C * ‖r‖`, without assuming contractivity,
multiplicativity of norms, or `‖1‖ = 1`. -/
theorem isWeightBounded_singleton_of_norm_le {R S : Type*} [SeminormedCommRing R]
    [SeminormedCommRing S] {φ : R →+* S} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    {t : Fin k → R} {c : Fin k → ℝ} (htc : ∀ i, ‖t i‖ * c i ≤ 1)
    {a : Fin k → S} (ha : ∀ i, ‖a i‖ ≤ c i) :
    IsWeightBounded φ (fun i ↦ ({t i} : Set R)) a := by
  rw [isWeightBounded_singleton_iff_forall_isPowerBounded]
  exact fun i ↦ isPowerBounded_map_mul_of_norm_le hφ (htc i) (ha i)

/-- If `a` is weight-bounded for singleton weights `Tᵢ = {tᵢ}` along a bounded ring homomorphism
into a seminormed commutative ring whose norm is power-multiplicative and bounds power-bounded
elements by `1`, then `‖aᵢ‖ ≤ ‖tᵢ‖⁻¹` at every coordinate where `tᵢ` is a multiplicative unit. -/
theorem norm_le_inv_norm_of_isWeightBounded_singleton {R S : Type*} [SeminormedCommRing R]
    [SeminormedCommRing S] {φ : R →+* S} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    {t : Fin k → R} {a : Fin k → S} (hb : IsWeightBounded φ (fun i ↦ ({t i} : Set R)) a)
    (hS : IsPowMul (‖·‖ : S → ℝ)) (hpb : ∀ x : S, IsPowerBounded x → ‖x‖ ≤ 1)
    {i : Fin k} (ht : IsNormMulUnit (t i)) :
    ‖a i‖ ≤ ‖t i‖⁻¹ := by
  obtain ⟨u, hu⟩ := ht.isUnit
  have hle1 : ‖φ (t i) * a i‖ ≤ 1 :=
    hpb _ ((isWeightBounded_singleton_iff_forall_isPowerBounded φ _ a).mp hb i)
  have hinv : ‖((u⁻¹ : Rˣ) : R)‖ = ‖t i‖⁻¹ :=
    hu ▸ (Units.isNormMulUnit_iff_norm_inv u).mp (hu ▸ ht)
  have hφ_bdd : φ.IsBounded :=
    ⟨max C 1, by positivity, fun r ↦
      (hφ r).trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (norm_nonneg r))⟩
  have hcancel : a i = φ ((u⁻¹ : Rˣ) : R) * (φ (t i) * a i) := by
    rw [← mul_assoc, ← map_mul, ← hu, Units.inv_mul, map_one, one_mul]
  calc ‖a i‖ = ‖φ ((u⁻¹ : Rˣ) : R) * (φ (t i) * a i)‖ := congrArg norm hcancel
    _ ≤ ‖φ ((u⁻¹ : Rˣ) : R)‖ * ‖φ (t i) * a i‖ := norm_mul_le _ _
    _ ≤ ‖t i‖⁻¹ * 1 := mul_le_mul ((contraction_of_isPowMul hS hφ_bdd _).trans_eq hinv) hle1
        (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _))
    _ = ‖t i‖⁻¹ := mul_one _

/-- If `a` is weight-bounded for singleton weights `Tᵢ = {tᵢ}` along a bounded ring homomorphism
into a seminormed commutative ring whose norm is power-multiplicative and bounds power-bounded
elements by `1`, then `‖aᵢ‖ ≤ c` whenever `tᵢ` is a multiplicative unit with `1 ≤ ‖tᵢ‖ * c`. -/
theorem norm_le_of_isWeightBounded_singleton {R S : Type*} [SeminormedCommRing R]
    [SeminormedCommRing S] {φ : R →+* S} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    {t : Fin k → R} {a : Fin k → S} (hb : IsWeightBounded φ (fun i ↦ ({t i} : Set R)) a)
    (hS : IsPowMul (‖·‖ : S → ℝ)) (hpb : ∀ x : S, IsPowerBounded x → ‖x‖ ≤ 1)
    {i : Fin k} (ht : IsNormMulUnit (t i)) {c : ℝ} (htc : 1 ≤ ‖t i‖ * c) :
    ‖a i‖ ≤ c := by
  have hpos : 0 < ‖t i‖ := lt_of_le_of_ne (norm_nonneg _) fun h0 ↦
    not_le_of_gt zero_lt_one (by simpa [← h0] using htc)
  exact (norm_le_inv_norm_of_isWeightBounded_singleton hφ hb hS hpb ht).trans
    ((inv_le_iff_one_le_mul₀' hpos).mpr htc)

/-- **Weight bounds equal polydisc bounds under a pseudouniformiser and a power-multiplicative
norm.** Along any bounded ring homomorphism `φ : R →+* S` into a seminormed commutative ring with a
pseudouniformiser and power-multiplicative norm, a tuple `a` is weight-bounded for multiplicative
units `Tᵢ = {uᵢ}` (`‖uᵢ‖ * cᵢ = 1`) precisely when `‖aᵢ‖ ≤ cᵢ` for every `i`. -/
theorem IsPseudoUniformizer.isWeightBounded_units_iff_norm_le {R S : Type*}
    [SeminormedCommRing R] [SeminormedCommRing S] {ϖ : S} (hϖ : IsPseudoUniformizer ϖ)
    (hS : IsPowMul (‖·‖ : S → ℝ)) {φ : R →+* S} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    (u : Fin k → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R)) {c : Fin k → ℝ}
    (hc : ∀ i, ‖(u i : R)‖ * c i = 1) {a : Fin k → S} :
    IsWeightBounded φ (fun i ↦ ({(u i : R)} : Set R)) a ↔ ∀ i, ‖a i‖ ≤ c i :=
  ⟨fun hb i ↦ norm_le_of_isWeightBounded_singleton hφ hb hS
      (fun _ hx ↦ (hϖ.isPowerBounded_iff_norm_le_one hS).mp hx) (hu i) (hc i).ge,
    isWeightBounded_singleton_of_norm_le hφ fun i ↦ (hc i).le⟩

/-- **Weight bounds equal polydisc bounds over a normed field.** Along any bounded homomorphism
into a normed field `K`, a tuple `a` is weight-bounded for multiplicative units `Tᵢ = {uᵢ}`
(`‖uᵢ‖ * cᵢ = 1`) precisely when `‖aᵢ‖ ≤ cᵢ` for every `i`. -/
theorem isWeightBounded_units_iff_norm_le {R K : Type*} [SeminormedCommRing R] [NormedField K]
    {φ : R →+* K} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (u : Fin k → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) {c : Fin k → ℝ} (hc : ∀ i, ‖(u i : R)‖ * c i = 1)
    {a : Fin k → K} :
    IsWeightBounded φ (fun i ↦ ({(u i : R)} : Set R)) a ↔ ∀ i, ‖a i‖ ≤ c i :=
  ⟨fun hb i ↦ norm_le_of_isWeightBounded_singleton hφ hb (fun x n _ ↦ norm_pow x n)
      (fun _ ↦ isPowerBounded_iff_norm_le_one.mp) (hu i) (hc i).ge,
    isWeightBounded_singleton_of_norm_le hφ fun i ↦ (hc i).le⟩

/-- When singleton weights `{tᵢ}` map into `{s_{e i}}` and satisfy `‖tᵢ‖ * cᵢ = 1` and
`‖sⱼ‖ * dⱼ = 1`, the target polyradii reindex to `c`. -/
theorem radii_comp_eq_of_singleton_subset {m : ℕ} {R : Type*} [Norm R]
    {t : Fin k → R} {c : Fin k → ℝ} (hc : ∀ i, ‖t i‖ * c i = 1)
    {s : Fin m → R} {d : Fin m → ℝ} (hd : ∀ j, ‖s j‖ * d j = 1)
    (e : Fin k → Fin m) (hts : ∀ i, ({t i} : Set R) ⊆ {s (e i)}) :
    d ∘ e = c := by
  funext i
  have hi : t i = s (e i) := Set.singleton_subset_singleton.mp (hts i)
  have hne : ‖t i‖ ≠ 0 := fun h0 ↦ by simpa [h0] using hc i
  exact mul_left_cancel₀ hne (by rw [Function.comp_apply, hc i, ← hd (e i), hi])

end TauCeti.Huber
