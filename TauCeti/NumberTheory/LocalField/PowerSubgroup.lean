/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.RingTheory.Henselian

/-!
# The `n`-th power subgroup of a local field away from the residue characteristic

Let `K` be a nonarchimedean local field and let `n` be a natural number that is invertible in
`𝒪[K]`, that is, prime to the residue characteristic. This file shows that the subgroup
`(Kˣ)ⁿ`, the range of `powMonoidHom n : Kˣ →* Kˣ`, is open, and hence closed, in `Kˣ`.

The proof exhibits an explicit open subgroup inside the range: every principal unit is an
`n`-th power. More precisely, the `n`-th power map carries each positive-depth step `U(K,i+1)` of
the unit filtration onto itself, by Hensel's lemma applied to `X ^ n - u` at the approximate root
`1`, whose derivative `n` is a unit there. Openness does not follow from any finiteness of the
quotient `Kˣ ⧸ (Kˣ)ⁿ`: a subgroup of finite index in a topological group need not be open.

As a consequence, a subgroup of `Kˣ` is open as soon as the exponent (for instance, the index) of
the quotient by it is invertible in `𝒪[K]`, since it then contains the power subgroup attached to
that exponent.

## Main results

* `TauCeti.map_powMonoidHom_unitFiltration_succ_of_isUnit`: the `n`-th power map carries
  `U(K,i+1)` onto itself.
* `TauCeti.unitFiltration_one_le_range_powMonoidHom_of_isUnit`: every principal unit is an
  `n`-th power, `U(K,1) ≤ (Kˣ)ⁿ`.
* `TauCeti.isOpen_range_powMonoidHom_of_isUnit` and
  `TauCeti.isClosed_range_powMonoidHom_of_isUnit`: the power subgroup is open and closed.
* `TauCeti.isOpen_of_isUnit_exponent` and `TauCeti.isOpen_of_isUnit_index`: a subgroup of `Kˣ`
  is open when the exponent, or the index, of the quotient by it is invertible in `𝒪[K]`.

## Implementation notes

The hypothesis `IsUnit (n : 𝒪[K])` already forces `n ≠ 0`, so no separate nonvanishing
assumption is taken. In mixed characteristic the same openness holds for every `n ≠ 0`, but
there the `p`-primary part needs the logarithm on deep units instead of Hensel's lemma at `1`,
and in equal characteristic `p` the range of `powMonoidHom p` is not open.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- For `n` invertible in `𝒪[K]`, the `n`-th power map carries each positive-depth step
`U(K,i+1)` of the unit filtration onto itself. -/
theorem map_powMonoidHom_unitFiltration_succ_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K]))
    (i : ℕ) :
    (unitFiltration K (i + 1)).map (powMonoidHom n) = unitFiltration K (i + 1) := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr fun x hx ↦ pow_mem hx n) fun x hx ↦ ?_
  -- `𝒪[K]` is Henselian: it is complete for the adic topology of its maximal ideal, which Mathlib
  -- records for the uniformity attached to the topological additive group `K`.
  have : HenselianLocalRing 𝒪[K] :=
    { is_henselian f hf a₀ h₁ h₂ := by
        let := IsTopologicalAddGroup.rightUniformSpace K
        have := isUniformAddGroup_of_addCommGroup (G := K)
        exact (IsAdicComplete.henselianRing 𝒪[K] 𝓂[K]).is_henselian f hf a₀ h₁ (h₂.map _) }
  obtain ⟨u, hu, hux⟩ := mem_unitFiltration_iff_exists.mp hx
  obtain ⟨a, ha, ha1⟩ := HenselianLocalRing.exists_pow_eq_of_sub_one_mem
    (Ideal.pow_le_self i.succ_ne_zero) hn hu
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have haU : IsUnit a := (isUnit_pow_iff hn0).mp (ha ▸ u.isUnit)
  refine ⟨Units.map (Subring.subtype 𝒪[K]).toMonoidHom haU.unit,
    (mem_unitFiltration_succ_congr i _).mpr (by simpa using ha1), ?_⟩
  ext
  simp [← hux, ← ha]

/-- For `n` invertible in `𝒪[K]`, every principal unit of `K` is an `n`-th power. -/
theorem unitFiltration_one_le_range_powMonoidHom_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    unitFiltration K 1 ≤ (powMonoidHom n : Kˣ →* Kˣ).range :=
  map_powMonoidHom_unitFiltration_succ_of_isUnit hn 0 ▸ Subgroup.map_le_range _ _

/-- **The power subgroup is open away from the residue characteristic.** For `n` invertible in
`𝒪[K]`, the subgroup `(Kˣ)ⁿ` of `n`-th powers is open in `Kˣ`. -/
theorem isOpen_range_powMonoidHom_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) :=
  Subgroup.isOpen_mono (unitFiltration_one_le_range_powMonoidHom_of_isUnit hn)
    (isOpen_unitFiltration 1)

/-- For `n` invertible in `𝒪[K]`, the subgroup `(Kˣ)ⁿ` of `n`-th powers is closed in `Kˣ`. -/
theorem isClosed_range_powMonoidHom_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    IsClosed ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_range_powMonoidHom_of_isUnit hn)

/-- A subgroup `H` of `Kˣ` is open as soon as the exponent of `Kˣ ⧸ H` is invertible in `𝒪[K]`:
`H` then contains the power subgroup attached to that exponent. -/
theorem isOpen_of_isUnit_exponent {H : Subgroup Kˣ}
    (hH : IsUnit (Monoid.exponent (Kˣ ⧸ H) : 𝒪[K])) : IsOpen (H : Set Kˣ) := by
  refine Subgroup.isOpen_mono ?_ (isOpen_range_powMonoidHom_of_isUnit hH)
  rintro _ ⟨y, rfl⟩
  simpa [← QuotientGroup.eq_one_iff] using Monoid.pow_exponent_eq_one (y : Kˣ ⧸ H)

/-- A subgroup of `Kˣ` whose index is invertible in `𝒪[K]` is open. Such a subgroup has finite
index, since the index `0` of an infinite-index subgroup is not a unit. -/
theorem isOpen_of_isUnit_index {H : Subgroup Kˣ} (hH : IsUnit (H.index : 𝒪[K])) :
    IsOpen (H : Set Kˣ) :=
  isOpen_of_isUnit_exponent <|
    isUnit_of_dvd_unit (Nat.cast_dvd_cast Group.exponent_dvd_nat_card) hH

end TauCeti
