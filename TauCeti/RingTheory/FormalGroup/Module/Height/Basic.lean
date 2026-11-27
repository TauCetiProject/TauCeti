/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Module.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.RingTheory.FormalGroup.Height.Basic
import TauCeti.RingTheory.LocalRing.Module
import TauCeti.RingTheory.PowerSeries.Order
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Height of a formal module

For a formal module over a local ring `R` with scalars in a DVR `O`, the height is computed on
the special fibre. It is infinite when the reduced uniformizer action is zero. Otherwise it is
the logarithm of the order of that action with base `Nat.card (ResidueField O)`.

The residue cardinality enters through scalar linearity. If a nonzero homomorphism of formal
modules starts in degree `n`, comparison of leading coefficients shows that every residue scalar
satisfies `x ^ n = x`. The binomial gcd in `FormalGroup.coeff_mul_lazardGcd_eq_zero_of_le_order`
forces `n` to be a power of the residue characteristic in degrees greater than one. The order of
Frobenius then gives the residue-field degree as a divisor of the exponent.

## References

* E. Viehmann and K. Ziegler, *Formal moduli of formal O_K-modules*, Astérisque 312 (2007),
  57–66, Lemma 2.1 and Definition 2.2.
-/

public section

open IsLocalRing

namespace TauCeti.FormalModule

variable {O R : Type*} [CommRing O] [CommRing R] [Algebra O R] {F G : FormalGroup R}

namespace Hom

variable {ρ : FormalModule O F} {τ : FormalModule O G}

/-- The leading degree of a formal-module homomorphism fixes every residue scalar under
exponentiation, even when the leading coefficient is a zero divisor. -/
theorem pow_eq_self_of_order [IsLocalRing O] (f : Hom ρ τ) {n : ℕ}
    (hn : f.toPowerSeries.order = n) (x : ResidueField O) : x ^ n = x := by
  obtain ⟨a, rfl⟩ := residue_surjective x
  have h := congrArg (fun g : FormalGroupHom F G ↦ PowerSeries.coeff n g.toPowerSeries)
    (f.comp_act a)
  simp only [FormalGroupHom.comp_toPowerSeries] at h
  rw [PowerSeries.coeff_subst_eq_mul_pow (ρ.act a).zero_constantCoeff hn.ge,
    PowerSeries.coeff_subst_eq_mul f.zero_constantCoeff (τ.act a).zero_constantCoeff hn.ge] at h
  simp only [Algebra.algebraMap_self_apply, coeff_one_act] at h
  rw [← sub_eq_zero, ← map_pow, ← map_sub, residue_eq_zero_iff]
  apply IsLocalRing.mem_maximalIdeal_of_smul_eq_zero (PowerSeries.order_eq_nat.mp hn).1
  rw [Algebra.smul_def, map_sub, map_pow]
  linear_combination h

/-- A nonzero formal-module homomorphism has order a power of the residue cardinality of
the local scalar ring. If the residue field is infinite, only order one is possible. -/
theorem exists_order_eq_pow [IsLocalRing O] (f : Hom ρ τ) (hf : f.toPowerSeries ≠ 0) :
    ∃ h : ℕ, f.toPowerSeries.order = (Nat.card (ResidueField O) ^ h : ℕ) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (PowerSeries.order_eq_top.not.mpr hf)
  by_cases h1 : n = 1
  · exact ⟨0, by simpa [h1] using hn.symm⟩
  have hn0 := PowerSeries.toNat_order_ne_zero f.zero_constantCoeff hf
  rw [← hn, ENat.toNat_natCast] at hn0
  -- In degree greater than one all residue scalars are roots of a nonzero polynomial X^n - X.
  have : Finite (ResidueField O) := by
    by_contra! hinf
    have heq : (Polynomial.X : Polynomial (ResidueField O)) ^ n = Polynomial.X :=
      Polynomial.funext fun x ↦ by simpa using f.pow_eq_self_of_order hn.symm x
    exact h1 (by simpa using congrArg Polynomial.natDegree heq)
  let p := ringChar (ResidueField O)
  have hp : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField O) p⟩
  -- The binomial gcd annihilates the leading coefficient, so its residue is zero.
  have hd : (lazardGcd n : O) ∈ maximalIdeal O := by
    apply IsLocalRing.mem_maximalIdeal_of_smul_eq_zero (PowerSeries.order_eq_nat.mp hn.symm).1
    simpa only [Algebra.smul_def, map_natCast, mul_comm] using
      F.coeff_mul_lazardGcd_eq_zero_of_le_order G f.hom hn.le
  have hd' := (residue_eq_zero_iff _).2 hd
  rw [map_natCast, CharP.cast_eq_zero_iff (ResidueField O) p] at hd'
  obtain ⟨i, rfl⟩ := (prime_dvd_lazardGcd_iff hp.out hn0).mp hd'
  let : Algebra (ZMod p) (ResidueField O) := ZMod.algebra _ _
  have hdiv : Module.finrank (ZMod p) (ResidueField O) ∣ i := by
    rw [← FiniteField.orderOf_frobeniusAlgHom]
    apply orderOf_dvd_of_pow_eq_one
    ext x
    simpa only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card,
      AlgHom.one_apply] using! f.pow_eq_self_of_order hn.symm x
  obtain ⟨h, rfl⟩ := hdiv
  exact ⟨h, by simpa only [pow_mul, FiniteField.pow_finrank_eq_natCard] using hn.symm⟩

end Hom

variable (ρ : FormalModule O F)

/-- If `a` divides `b`, the action series of `b` has order at least that of `a`. -/
theorem order_act_le_of_dvd {a b : O} (h : a ∣ b) :
    (ρ.act a).toPowerSeries.order ≤ (ρ.act b).toPowerSeries.order := by
  obtain ⟨c, rfl⟩ := h
  rw [ρ.act_mul, FormalGroupHom.comp_toPowerSeries]
  exact PowerSeries.le_order_subst_left' (ρ.act c).zero_constantCoeff

/-- Associated scalars act by series of the same order. -/
theorem order_act_eq_of_associated {a b : O} (h : Associated a b) :
    (ρ.act a).toPowerSeries.order = (ρ.act b).toPowerSeries.order :=
  le_antisymm (ρ.order_act_le_of_dvd h.dvd) (ρ.order_act_le_of_dvd h.symm.dvd)

/-- Over a ring without zero divisors, the orders of scalar actions multiply under composition. -/
@[simp]
theorem order_act_mul [NoZeroDivisors R] (a b : O) :
    (ρ.act (a * b)).toPowerSeries.order =
      (ρ.act a).toPowerSeries.order * (ρ.act b).toPowerSeries.order := by
  rw [ρ.act_mul, FormalGroupHom.comp_toPowerSeries, PowerSeries.order_subst
    (ρ.act b).zero_constantCoeff, mul_comm]

/-- The order of the action of a scalar power is the corresponding power of the order. -/
@[simp]
theorem order_act_pow [IsDomain R] (a : O) (n : ℕ) :
    (ρ.act (a ^ n)).toPowerSeries.order = (ρ.act a).toPowerSeries.order ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ρ.order_act_mul, ih, pow_succ]

/-- The action series on the special fibre is the reduction of the original action series. -/
theorem map_residue_act_toPowerSeries [IsLocalRing R] (a : O) :
    ((ρ.map (IsScalarTower.toAlgHom O R (ResidueField R))).act a).toPowerSeries =
      PowerSeries.map (residue R) (ρ.act a).toPowerSeries := by
  rw [map_act, FormalGroupHom.map_toPowerSeries, IsScalarTower.coe_toAlgHom,
    ResidueField.algebraMap_eq]

section Local

variable [IsDomain O] [IsDiscreteValuationRing O] [IsLocalRing R]

/-- The height of a formal module over a local base is read on its special fibre. It is
infinite when the uniformizer acts by zero there. For finite residue cardinality `q`, finite
height `h` means that the reduced action has order `q ^ h`. -/
noncomputable def height : ℕ∞ :=
  let π := (IsDiscreteValuationRing.exists_irreducible O).choose
  ENat.map (Nat.log (Nat.card (ResidueField O)))
    (PowerSeries.map (residue R) (ρ.act π).toPowerSeries).order

/-- Any uniformizer can be used to compute the height on the special fibre. -/
theorem height_eq_of_irreducible {π : O} (hπ : Irreducible π) :
    ρ.height = ENat.map (Nat.log (Nat.card (ResidueField O)))
      (PowerSeries.map (residue R) (ρ.act π).toPowerSeries).order := by
  let τ := ρ.map (IsScalarTower.toAlgHom O R (ResidueField R))
  have h := τ.order_act_eq_of_associated (IsDiscreteValuationRing.associated_of_irreducible O
    (IsDiscreteValuationRing.exists_irreducible O).choose_spec hπ)
  unfold height
  apply congrArg (ENat.map (Nat.log (Nat.card (ResidueField O))))
  simpa only [τ, map_residue_act_toPowerSeries] using h

/-- Infinite height means that the uniformizer acts by zero on the special fibre. -/
theorem height_eq_top_iff {π : O} (hπ : Irreducible π) :
    ρ.height = ⊤ ↔ PowerSeries.map (residue R) (ρ.act π).toPowerSeries = 0 := by
  rw [ρ.height_eq_of_irreducible hπ]
  exact ENat.map_eq_top_iff.trans PowerSeries.order_eq_top

/-- Finite height is characterized by the first nonzero degree of the reduced uniformizer action. -/
theorem height_eq_natCast_iff {π : O} (hπ : Irreducible π) {h : ℕ} :
    ρ.height = h ↔ (PowerSeries.map (residue R) (ρ.act π).toPowerSeries).order =
      (Nat.card (ResidueField O) ^ h : ℕ) := by
  let τ := ρ.map (IsScalarTower.toAlgHom O R (ResidueField R))
  let φ : Hom τ τ := ⟨τ.act π, τ.act_comp_act_comm π⟩
  have hφ : φ.toPowerSeries = PowerSeries.map (residue R) (ρ.act π).toPowerSeries :=
    ρ.map_residue_act_toPowerSeries π
  rw [ρ.height_eq_of_irreducible hπ, ← hφ]
  by_cases hz : φ.toPowerSeries = 0
  · rw [hz, PowerSeries.order_zero, ENat.map_top]
    exact iff_of_false (ENat.top_ne_natCast _) (ENat.top_ne_natCast _)
  obtain ⟨i, hi⟩ := φ.exists_order_eq_pow hz
  rcases finite_or_infinite (ResidueField O) with hfin | hinf
  · have hq : 1 < Nat.card (ResidueField O) := Finite.one_lt_card
    rw [hi, ENat.map_natCast, Nat.log_pow hq]
    exact ENat.natCast_inj.trans ((Nat.pow_right_injective hq).eq_iff.symm.trans
      ENat.natCast_inj.symm)
  · have hn := PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mpr φ.zero_constantCoeff
    rw [Nat.card_eq_zero_of_infinite] at hi ⊢
    obtain rfl : i = 0 := by cases i <;> simp_all
    rw [hi, ENat.map_natCast]
    have heq : Nat.log 0 (0 ^ 0) = h ↔ 0 ^ 0 = (0 : ℕ) ^ h := by cases h <;> simp
    exact ENat.natCast_inj.trans (heq.trans ENat.natCast_inj.symm)

/-- Local base change preserves height. The induced map of residue fields is injective. -/
@[simp]
theorem height_map {S : Type*} [CommRing S] [IsLocalRing S] [Algebra O S]
    (g : R →ₐ[O] S) [IsLocalHom g] : (ρ.map g).height = ρ.height := by
  unfold height
  apply congrArg (ENat.map _)
  rw [map_act, FormalGroupHom.map_toPowerSeries, ← RingHom.comp_apply, ← PowerSeries.map_comp,
    ← ResidueField.map_comp_residue, PowerSeries.map_comp, RingHom.comp_apply,
    PowerSeries.order_map_of_injective (ResidueField.map (g : R →+* S)).injective]

/-- A homomorphism nonzero on the special fibre preserves formal-module height. -/
theorem Hom.height_eq {ρ : FormalModule O F} {τ : FormalModule O G} (f : Hom ρ τ)
    (hf : PowerSeries.map (residue R) f.toPowerSeries ≠ 0) : ρ.height = τ.height := by
  unfold height
  apply congrArg (ENat.map _)
  let π := (_root_.IsDiscreteValuationRing.exists_irreducible O).choose
  let g := f.toFormalGroupHom.map (residue R)
  have h := congrArg (fun k : FormalGroupHom F G ↦ (k.map (residue R)).toPowerSeries.order)
    (f.comp_act π)
  simp only [FormalGroupHom.map_comp, FormalGroupHom.comp_toPowerSeries] at h
  rw [PowerSeries.order_subst ((ρ.act π).map (residue R)).zero_constantCoeff,
    PowerSeries.order_subst g.zero_constantCoeff] at h
  simp only [g, FormalGroupHom.map_toPowerSeries] at h
  have h0 := PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mpr g.zero_constantCoeff
  have ht := PowerSeries.order_eq_top.not.mpr hf
  rw [FormalGroupHom.map_toPowerSeries] at h0
  rw [mul_comm _ (PowerSeries.map (residue R) f.toPowerSeries).order] at h
  exact le_antisymm ((ENat.mul_le_mul_left_iff h0 ht).mp h.le)
    ((ENat.mul_le_mul_left_iff h0 ht).mp h.ge)

/-- Changing the formal coordinate preserves height. -/
@[simp]
theorem height_conj (e : FormalGroupIso F G) : (ρ.conj e).height = ρ.height := by
  apply ((ρ.conjHom e).height_eq _).symm
  simpa only [conjHom_toFormalGroupHom, ← FormalGroupHom.map_toPowerSeries,
    ← FormalGroupIso.map_toHom] using (e.map (residue R)).toHom_toPowerSeries_ne_zero

/-- On the special fibre of a local formal module the uniformizer has zero tangent action,
so its height is at least one. -/
theorem one_le_height [IsLocalHom (algebraMap O R)] : 1 ≤ ρ.height := by
  by_contra! h
  have hz : ρ.height = 0 := Order.lt_one_iff.mp h
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible O
  have hord := (ρ.height_eq_natCast_iff (h := 0) hπ).mp hz
  rw [pow_zero, Nat.cast_one, PowerSeries.order_eq_one_iff_of_constantCoeff_eq_zero
    (by simp [(ρ.act π).zero_constantCoeff])] at hord
  apply hord
  rw [PowerSeries.coeff_map, ρ.coeff_one_act, residue_eq_zero_iff]
  exact map_nonunit _ _ hπ.not_isUnit

end Local

end TauCeti.FormalModule
