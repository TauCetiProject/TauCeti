/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Data.Finset.Max
import TauCeti.LinearAlgebra.Quotient.PiSpanSingleton

/-!
# Units of the `p`-adic integers

Complements to Mathlib's `PadicInt` API on the units of `ℤ_p`: `1 + x` is a unit whenever
`p ∣ x`, because `ℤ_p` is a local ring whose maximal ideal is `pℤ_p`. This is the criterion
that makes `1 + p^f ℤ_p` a subgroup of `ℤ_pˣ`.

The unit group `ℤ_pˣ` is a profinite group: it is the closed unit sphere of the compact
totally disconnected space `ℤ_p`, and the topology of the units is the subspace topology because
`ℤ_p` is a complete normed ring. The instances `CompactSpace ℤ_[p]ˣ` and
`TotallyDisconnectedSpace ℤ_[p]ˣ` are recorded here.

Two consequences of the ultrametric divisibility in `ℤ_p` are recorded as well: an element
divides every element of no larger norm, so that a finite family of `p`-adic integers is a common
multiple `q • w` of a family `w` with a coordinate equal to `1`, namely at an index of maximal norm.
This is the shape in which the exponent vector of a relator of a free pro-`p` group is read.

## Main results

* `PadicInt.isUnit_one_add_of_dvd`: `1 + x` is a unit of `ℤ_[p]` whenever `p ∣ x`.
* `PadicInt.isUnit_two`: `2` is a unit of `ℤ_[p]` for odd `p`.
* `PadicInt.pow_p_dvd_natCast_iff`: `p ^ n` divides a natural number in `ℤ_[p]` exactly when it
  does in `ℕ`.
* `PadicInt.dvd_of_norm_le`: in `ℤ_[p]`, `y ∣ x` whenever `‖x‖ ≤ ‖y‖`.
* `PadicInt.exists_apply_eq_one_and_eq_smul`: a finite family in `ℤ_[p]` is `q • w` with
  `w i₀ = 1` at some index `i₀`.
* `PadicInt.units_neg_one_ne_one`: `-1 ≠ 1` in `ℤ_[p]ˣ`.
* `PadicInt.range_units_val`: the units of `ℤ_[p]` are the elements of norm `1`.
* `Padic.exists_eq_zpow_valuation_mul`: every nonzero `x : ℚ_[p]` is `p ^ v(x)` times a unit of
  `ℤ_[p]`.
* `Padic.inv_natCast_le_norm_natCast`: the `p`-adic norm of a positive integer `m` is at least
  `1 / m`.
* `PadicInt.compactSpace_units`, `PadicInt.totallyDisconnectedSpace_units`: `ℤ_[p]ˣ` is a
  profinite group.
-/

public section

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- In `ℤ_p`, `1 + x` is a unit whenever `p ∣ x`. -/
theorem isUnit_one_add_of_dvd {x : ℤ_[p]} (hx : (p : ℤ_[p]) ∣ x) : IsUnit (1 + x) :=
  IsLocalRing.isUnit_of_mem_nonunits_one_sub_self _ <| by
    rw [sub_add_cancel_left, mem_nonunits, norm_neg]
    exact (norm_lt_one_iff_dvd x).mpr hx

/-- A natural number prime to `p` is a unit in `ℤ_p`. -/
theorem isUnit_natCast_of_coprime {n : ℕ} (h : p.Coprime n) : IsUnit (n : ℤ_[p]) :=
  isUnit_iff.mpr (norm_natCast_eq_one_iff.mpr h)

/-- Every prime number `ℓ` is a unit in `ℤ_p` or generates a maximal ideal of `ℤ_p`: it is a unit
for `ℓ ≠ p` and generates the maximal ideal for `ℓ = p`. -/
theorem isUnit_natCast_or_isMaximal_span {ℓ : ℕ} (hℓ : ℓ.Prime) :
    IsUnit (ℓ : ℤ_[p]) ∨ (Ideal.span {(ℓ : ℤ_[p])}).IsMaximal := by
  by_cases h : ℓ = p
  · subst h
    exact .inr (maximalIdeal_eq_span_p (p := ℓ) ▸ IsLocalRing.maximalIdeal.isMaximal _)
  · exact .inl (isUnit_natCast_of_coprime ((Nat.coprime_primes Fact.out hℓ).mpr (Ne.symm h)))

/-- `2` is a unit in `ℤ_p` for every odd prime `p`. -/
theorem isUnit_two (hp : p ≠ 2) : IsUnit (2 : ℤ_[p]) :=
  isUnit_iff.mpr <| by
    exact_mod_cast norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hp)

/-- `p ^ n` divides a natural number in `ℤ_p` exactly when it divides it in `ℕ`: the natural
number version of `PadicInt.pow_p_dvd_int_iff`. -/
@[simp]
theorem pow_p_dvd_natCast_iff (n a : ℕ) : (p : ℤ_[p]) ^ n ∣ (a : ℤ_[p]) ↔ p ^ n ∣ a := by
  rw [← Int.cast_natCast a, pow_p_dvd_int_iff, ← Nat.cast_pow, Int.natCast_dvd_natCast]

/-- `-1 ≠ 1` in `ℤ_pˣ`: the unit group has an element of order two. -/
theorem units_neg_one_ne_one : (-1 : ℤ_[p]ˣ) ≠ 1 := fun h ↦ by
  have := congrArg Units.val h
  rw [Units.val_neg, Units.val_one] at this
  exact (by norm_num : (-1 : ℤ_[p]) ≠ 1) this

/-- The units of `ℤ_p` are the elements of norm `1`. -/
theorem range_units_val : Set.range (Units.val : ℤ_[p]ˣ → ℤ_[p]) = {x | ‖x‖ = 1} :=
  -- `IsUnit x` is by definition `∃ u : ℤ_[p]ˣ, ↑u = x`, that is `x ∈ Set.range Units.val`.
  Set.ext fun _ ↦ isUnit_iff

/-- `ℤ_pˣ` is compact: it is the closed unit sphere of the compact space `ℤ_p`, and the topology
on the units of the complete normed ring `ℤ_p` is the subspace topology. -/
instance compactSpace_units : CompactSpace ℤ_[p]ˣ := by
  have h : IsCompact (Set.range (Units.val : ℤ_[p]ˣ → ℤ_[p])) := by
    rw [range_units_val]
    exact (isClosed_eq continuous_norm continuous_const).isCompact
  rw [← Set.image_univ] at h
  exact isCompact_univ_iff.mp (Units.isOpenEmbedding_val.isInducing.isCompact_iff.mpr h)

/-- `ℤ_pˣ` is totally disconnected, as a subspace of the ultrametric space `ℤ_p`. -/
instance totallyDisconnectedSpace_units : TotallyDisconnectedSpace ℤ_[p]ˣ :=
  ⟨Units.isOpenEmbedding_val.isEmbedding.isTotallyDisconnected
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

/-- **Divisibility from the norm**: in `ℤ_p`, `y` divides every `x` with `‖x‖ ≤ ‖y‖`, because `x`
then lies in the ideal `p^{v_p(y)} ℤ_p = y ℤ_p` when `y ≠ 0`, and vanishes when `y = 0`. -/
theorem dvd_of_norm_le {x y : ℤ_[p]} (h : ‖x‖ ≤ ‖y‖) : y ∣ x := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [norm_zero] at h
    rw [norm_le_zero_iff.1 h]
  have hx : x ∈ Ideal.span {(p : ℤ_[p]) ^ y.valuation} :=
    (norm_le_pow_iff_mem_span_pow x y.valuation).1 (h.trans_eq (norm_eq_zpow_neg_valuation hy))
  rw [Ideal.mem_span_singleton] at hx
  have := (Units.mul_left_dvd (u := unitCoeff hy)).2 hx
  rwa [← unitCoeff_spec hy] at this

/-- **A finite family of `p`-adic integers is a multiple of a family with a coordinate `1`**: for
`v : ι → ℤ_p` with `ι` finite and nonempty there are an index `i₀`, a scalar `q` and a family `w`
with `w i₀ = 1` and `v = q • w`. One may take `i₀` of maximal norm and `q = v i₀`, which then
divides every coordinate. -/
theorem exists_apply_eq_one_and_eq_smul {ι : Type*} [Finite ι] [Nonempty ι] (v : ι → ℤ_[p]) :
    ∃ (i₀ : ι) (q : ℤ_[p]) (w : ι → ℤ_[p]), w i₀ = 1 ∧ v = q • w := by
  classical
  cases nonempty_fintype ι
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_max_image Finset.univ (fun i ↦ ‖v i‖) Finset.univ_nonempty
  obtain ⟨w, hw, hv⟩ :=
    TauCeti.exists_eq_smul_of_forall_dvd fun i ↦ dvd_of_norm_le (hi₀ i (Finset.mem_univ i))
  exact ⟨i₀, v i₀, w, hw, hv⟩

end PadicInt

namespace Padic

variable {p : ℕ} [Fact p.Prime]

/-- Every nonzero `p`-adic number is `p ^ v(x)` times a unit of `ℤ_[p]`. -/
theorem exists_eq_zpow_valuation_mul {x : ℚ_[p]} (hx : x ≠ 0) :
    ∃ u : ℤ_[p]ˣ, x = (p : ℚ_[p]) ^ x.valuation * u := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hy : ‖x * (p : ℚ_[p]) ^ (-x.valuation)‖ = 1 := by
    have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    rw [norm_mul, norm_zpow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hx, inv_zpow',
      neg_neg, ← zpow_add₀ hp', neg_add_cancel, zpow_zero]
  refine ⟨PadicInt.mkUnits hy, ?_⟩
  rw [PadicInt.mkUnits_eq, mul_left_comm, ← zpow_add₀ hp, add_neg_cancel, zpow_zero, mul_one]

/-- The `p`-adic norm of a positive integer `m` is at least `1 / m`. -/
theorem inv_natCast_le_norm_natCast (m : ℕ) [NeZero m] : (m : ℝ)⁻¹ ≤ ‖(m : ℚ_[p])‖ := by
  rw [Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr (NeZero.ne m)),
    Padic.valuation_natCast, zpow_neg, zpow_natCast]
  gcongr
  · exact pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m)) pow_padicValNat_dvd

end Padic
