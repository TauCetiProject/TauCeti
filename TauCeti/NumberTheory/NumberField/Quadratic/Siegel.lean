/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.NumberField.Quadratic.Model
public import TauCeti.NumberTheory.NumberField.Quadratic.Radicand
import TauCeti.NumberTheory.FundamentalDiscriminant
import TauCeti.NumberTheory.LSeries.Quadratic.Siegel
import TauCeti.NumberTheory.NumberField.ClassNumber.RingEquiv
import TauCeti.NumberTheory.NumberField.Quadratic.DedekindZeta
import TauCeti.NumberTheory.QuadraticOrder.Field

/-!
# Siegel's class-number lower bound and finiteness of imaginary quadratic fields

Combining Siegel's lower bound `c₀ q ^ (-ε) ≤ Re L(1, χ)` (`TauCeti.quadratic_LFunction_siegel`)
with the analytic class-number lower bound `√|D| Re L(1, χ_D) / π ≤ h(K)`
(`TauCeti.NumberField.sqrt_mul_LFunction_one_re_div_le_classNumber`) for an imaginary quadratic
number field `K` of discriminant `D` gives

`c |D| ^ (1 / 2 - ε) ≤ h(K)`

uniformly over all imaginary quadratic fields, with `c = c₀ / π > 0`.

Taking `ε = 1 / 4` bounds `|D| ≤ (B / c) ^ 4` whenever `h(K) ≤ B` (including `B = 0` and `B = 1`).
Consequently:
* only finitely many negative fundamental discriminants `D` and negative squarefree radicands `d`
  have `classNumber ℚ(√D) ≤ B` (respectively `classNumber ℚ(√d) ≤ B`), and in particular each class
  number `h` has a finite fiber;
* up to `ℚ`-algebra isomorphism (`NumberField.existsUnique_neg_squarefree_algEquiv`), imaginary
  quadratic fields of class number at most `B` fall into finitely many isomorphism classes;
* `classNumber (K i) → ∞` along any family of imaginary quadratic fields with `|discr (K i)| → ∞`,
  and `classNumber ℚ(√(d i)) → ∞` along squarefree radicands `d i → -∞`.

Because the constant in Siegel's theorem is ineffective, these finiteness theorems do not furnish an
explicit discriminant threshold or numerical enumeration.

## Main results

* `QuadraticAlgebra.discr_eq_of_isFundamentalDiscr`: for a nonsquare fundamental discriminant `D`,
  `NumberField.discr ℚ(√D) = D`.
* `QuadraticAlgebra.abs_le_abs_discr`: for squarefree nonsquare `d`,
  `|d| ≤ |NumberField.discr ℚ(√d)|`.
* `TauCeti.imaginary_classNumber_lower_bound`: `c |discr L| ^ (1 / 2 - ε) ≤ classNumber L` for all
  imaginary quadratic fields `L`.
* `TauCeti.imaginary_discr_bounded_of_classNumber_le`: `|discr L| ≤ C` for all imaginary quadratic
  fields `L` with `classNumber L ≤ B`.
* `TauCeti.NumberField.finite_neg_isFundamentalDiscr_of_classNumber_le`,
  `TauCeti.NumberField.finite_neg_isFundamentalDiscr_of_classNumber_eq`: finiteness of negative
  fundamental discriminants with bounded or prescribed class number.
* `TauCeti.NumberField.finite_neg_squarefree_of_classNumber_le`,
  `TauCeti.NumberField.finite_neg_squarefree_of_classNumber_eq`: the corresponding finiteness
  statements for negative squarefree radicands.
* `TauCeti.NumberField.exists_finset_neg_squarefree_algEquiv_of_classNumber_le`: finiteness of
  imaginary quadratic fields of class number at most `B` up to `ℚ`-algebra isomorphism.
* `TauCeti.NumberField.tendsto_classNumber_atTop_of_tendsto_natAbs_discr`,
  `TauCeti.NumberField.tendsto_classNumber_quadraticAlgebra_of_tendsto_atBot`: divergence of the
  class number as `|discr| → ∞`.

## References

* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Davenport, *Multiplicative Number Theory*, Chapter 21.
-/

public section

universe u

open Filter Module NumberField
open scoped Topology

namespace QuadraticAlgebra

/-- **The discriminant of `ℚ(√D)` for a fundamental discriminant `D`.** If `D` is a nonsquare
fundamental discriminant (in particular any negative fundamental discriminant), then the quadratic
field `QuadraticAlgebra ℚ D 0` has discriminant `D`. -/
theorem discr_eq_of_isFundamentalDiscr {D : ℤ} [Fact (¬ IsSquare D)]
    (hD : Int.IsFundamentalDiscr D) :
    NumberField.discr (QuadraticAlgebra ℚ (D : ℚ) 0) = D := by
  have hmod := hD.emod_four_eq_zero_or_one
  rw [← TauCeti.GlobalNumberFields.NumberFieldOrder.discr_maximal,
    ← (TauCeti.QuadraticOrder.numberFieldOrder_eq_maximal_iff D hmod).mpr hD,
    TauCeti.QuadraticOrder.numberFieldOrder_discr]

/-- For a squarefree nonsquare integer `d`, `|d|` is bounded by `|NumberField.discr ℚ(√d)|`. -/
theorem abs_le_abs_discr {d : ℤ} [Fact (¬ IsSquare d)] (hsf : Squarefree d) :
    |d| ≤ |NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0)| := by
  by_cases hd4 : d % 4 = 1
  · rw [discr_eq_of_mod_four_eq_one hsf hd4]
  · rw [discr_eq_four_mul_of_mod_four_ne_one hsf hd4, abs_mul,
      abs_of_nonneg (by omega : (0 : ℤ) ≤ 4)]
    linarith [abs_nonneg d]

end QuadraticAlgebra

namespace TauCeti

/-- **Siegel's class-number lower bound for imaginary quadratic fields.** For every `ε > 0` there
exists `c > 0` such that every imaginary quadratic number field `L` satisfies
`c |discr L| ^ (1 / 2 - ε) ≤ classNumber L`. -/
theorem imaginary_classNumber_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (L : Type u) [Field L] [NumberField L] [NumberField.IsTotallyComplex L],
        Module.finrank ℚ L = 2 →
        c * Real.rpow (|NumberField.discr L| : ℝ) (1 / 2 - ε) ≤
          (NumberField.classNumber L : ℝ) := by
  obtain ⟨c₀, hc₀, hsiegel⟩ := quadratic_LFunction_siegel ε hε
  refine ⟨c₀ / Real.pi, div_pos hc₀ Real.pi_pos, fun L _ _ _ hL ↦ ?_⟩
  have hD : Int.IsFundamentalDiscr (discr L) := Multiquadratic.isFundamentalDiscr_discr hL
  have : NeZero (discr L).natAbs := hD.neZero_natAbs
  set χ : DirichletCharacter ℂ (discr L).natAbs :=
    (Multiquadratic.fundamentalDiscriminantChar (discr L) hD).ringHomComp (Int.castRingHom ℂ)
  have hχp : χ.IsPrimitive :=
    (DirichletCharacter.isPrimitive_ringHomComp_iff _ _ Int.cast_injective).mpr
      (Multiquadratic.isPrimitive_fundamentalDiscriminantChar hD)
  have hL1 := hsiegel (discr L).natAbs χ hχp
    ((Multiquadratic.fundamentalDiscriminantChar_isQuadratic hD).comp (Int.castRingHom ℂ))
    (Multiquadratic.ringHomComp_fundamentalDiscriminantChar_discr_ne_one hL)
  rw [Nat.cast_natAbs, Int.cast_abs] at hL1
  have hcnf := NumberField.sqrt_mul_LFunction_one_re_div_le_classNumber hL
  have hDpos : 0 < |(discr L : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero L))
  calc c₀ / Real.pi * |(discr L : ℝ)| ^ (1 / 2 - ε)
      = √|(discr L : ℝ)| * (c₀ * |(discr L : ℝ)| ^ (-ε)) / Real.pi := by
        rw [Real.sqrt_eq_rpow, sub_eq_add_neg, Real.rpow_add hDpos]
        ring
    _ ≤ √|(discr L : ℝ)| * (χ.LFunction 1).re / Real.pi := by
        gcongr
        exact hL1
    _ ≤ (classNumber L : ℝ) := hcnf

/-- **Discriminant bound for imaginary quadratic fields of bounded class number.** For every `B`,
there exists `C` such that every imaginary quadratic field `L` with `classNumber L ≤ B` satisfies
`|discr L| ≤ C`. -/
theorem imaginary_discr_bounded_of_classNumber_le (B : ℕ) :
    ∃ C : ℝ,
      ∀ (L : Type u) [Field L] [NumberField L] [NumberField.IsTotallyComplex L],
        Module.finrank ℚ L = 2 →
        NumberField.classNumber L ≤ B →
        (|NumberField.discr L| : ℝ) ≤ C := by
  obtain ⟨c, hc, hlb⟩ := imaginary_classNumber_lower_bound.{u} (1 / 4) (by norm_num)
  refine ⟨((B : ℝ) / c) ^ (4 : ℝ), fun L _ _ _ hL hB ↦ ?_⟩
  have h1 := (hlb L hL).trans (Nat.cast_le.mpr hB)
  have hexp : (1 / 2 : ℝ) - 1 / 4 = 1 / 4 := by norm_num
  rw [hexp] at h1
  have hdiv : |(discr L : ℝ)| ^ (1 / 4 : ℝ) ≤ (B : ℝ) / c := by
    rw [le_div_iff₀ hc, mul_comm]
    exact h1
  have hD0 : 0 ≤ |(discr L : ℝ)| := abs_nonneg _
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hD0 _) hdiv (by norm_num : (0 : ℝ) ≤ 4)
  have hmul4 : (1 / 4 : ℝ) * 4 = 1 := by norm_num
  rwa [← Real.rpow_mul hD0, hmul4, Real.rpow_one] at hpow

namespace NumberField

/-- **Finiteness of negative fundamental discriminants of bounded class number.** For every `B : ℕ`
(including `B = 0` and `B = 1`), only finitely many negative fundamental discriminants `D` satisfy
`classNumber ℚ(√D) ≤ B`. -/
theorem finite_neg_isFundamentalDiscr_of_classNumber_le (B : ℕ) :
    {D : ℤ | ∃ (_ : Fact (¬ IsSquare D)), D < 0 ∧ Int.IsFundamentalDiscr D ∧
      NumberField.classNumber (QuadraticAlgebra ℚ (D : ℚ) 0) ≤ B}.Finite := by
  obtain ⟨C, hC⟩ := imaginary_discr_bounded_of_classNumber_le.{0} B
  refine (Set.finite_Icc (-⌊C⌋) 0).subset fun D ⟨hns, hDneg, hfund, hB⟩ ↦ ?_
  have : IsTotallyComplex (QuadraticAlgebra ℚ (D : ℚ) 0) :=
    QuadraticAlgebra.isTotallyComplex_iff.mpr (by exact_mod_cast hDneg)
  have hb := hC (QuadraticAlgebra ℚ (D : ℚ) 0) (QuadraticAlgebra.finrank_eq_two _ _) hB
  rw [← Int.cast_abs, QuadraticAlgebra.discr_eq_of_isFundamentalDiscr hfund, abs_of_neg hDneg] at hb
  exact ⟨neg_le.mp (Int.le_floor.mpr hb), hDneg.le⟩

/-- **Finite fibers of the class number over negative fundamental discriminants.** For every
`h : ℕ`, only finitely many negative fundamental discriminants `D` satisfy
`classNumber ℚ(√D) = h`. -/
theorem finite_neg_isFundamentalDiscr_of_classNumber_eq (h : ℕ) :
    {D : ℤ | ∃ (_ : Fact (¬ IsSquare D)), D < 0 ∧ Int.IsFundamentalDiscr D ∧
      NumberField.classNumber (QuadraticAlgebra ℚ (D : ℚ) 0) = h}.Finite :=
  (finite_neg_isFundamentalDiscr_of_classNumber_le h).subset
    fun _ ⟨hns, hneg, hfund, heq⟩ ↦ ⟨hns, hneg, hfund, heq.le⟩

/-- **Finiteness of negative squarefree radicands of bounded class number.** For every `B : ℕ`
(including `B = 0` and `B = 1`), only finitely many negative squarefree integers `d` satisfy
`classNumber ℚ(√d) ≤ B`. -/
theorem finite_neg_squarefree_of_classNumber_le (B : ℕ) :
    {d : ℤ | ∃ (_ : Fact (¬ IsSquare d)), d < 0 ∧ Squarefree d ∧
      NumberField.classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) ≤ B}.Finite := by
  obtain ⟨C, hC⟩ := imaginary_discr_bounded_of_classNumber_le.{0} B
  refine (Set.finite_Icc (-⌊C⌋) 0).subset fun d ⟨hns, hdneg, hsf, hB⟩ ↦ ?_
  have : IsTotallyComplex (QuadraticAlgebra ℚ (d : ℚ) 0) :=
    QuadraticAlgebra.isTotallyComplex_iff.mpr (by exact_mod_cast hdneg)
  have hb := hC (QuadraticAlgebra ℚ (d : ℚ) 0) (QuadraticAlgebra.finrank_eq_two _ _) hB
  rw [← Int.cast_abs] at hb
  have hd_le : -d ≤ |discr (QuadraticAlgebra ℚ (d : ℚ) 0)| :=
    (abs_of_neg hdneg).symm.trans_le (QuadraticAlgebra.abs_le_abs_discr hsf)
  have hle : ((-d : ℤ) : ℝ) ≤ C := (Int.cast_le.mpr hd_le).trans hb
  exact ⟨neg_le.mp (Int.le_floor.mpr hle), hdneg.le⟩

/-- **Finite fibers of the class number over negative squarefree radicands.** For every `h : ℕ`,
only finitely many negative squarefree integers `d` satisfy `classNumber ℚ(√d) = h`. -/
theorem finite_neg_squarefree_of_classNumber_eq (h : ℕ) :
    {d : ℤ | ∃ (_ : Fact (¬ IsSquare d)), d < 0 ∧ Squarefree d ∧
      NumberField.classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) = h}.Finite :=
  (finite_neg_squarefree_of_classNumber_le h).subset
    fun _ ⟨hns, hneg, hsf, heq⟩ ↦ ⟨hns, hneg, hsf, heq.le⟩

/-- **Finiteness of imaginary quadratic fields of bounded class number up to `ℚ`-isomorphism.** For
every `B : ℕ`, there exists a finite set `S` of negative squarefree radicands, each of class number
at most `B`, such that every imaginary quadratic number field `L` with `classNumber L ≤ B` is
`ℚ`-isomorphic to `QuadraticAlgebra ℚ d 0` for a unique `d ∈ S`. -/
theorem exists_finset_neg_squarefree_algEquiv_of_classNumber_le (B : ℕ) :
    ∃ S : Finset ℤ,
      (∀ d ∈ S, ∃ (_ : Fact (¬ IsSquare d)), d < 0 ∧ Squarefree d ∧
        NumberField.classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) ≤ B) ∧
      ∀ (L : Type u) [Field L] [NumberField L] [NumberField.IsTotallyComplex L],
        Module.finrank ℚ L = 2 → NumberField.classNumber L ≤ B →
        ∃! d : ℤ, d ∈ S ∧ Nonempty (L ≃ₐ[ℚ] QuadraticAlgebra ℚ (d : ℚ) 0) := by
  have hfin := finite_neg_squarefree_of_classNumber_le B
  refine ⟨hfin.toFinset, fun d hd ↦ hfin.mem_toFinset.mp hd, fun L _ _ _ hL hB ↦ ?_⟩
  obtain ⟨d, ⟨hdneg, hsf, ⟨e⟩⟩, huniq⟩ := existsUnique_neg_squarefree_algEquiv hL
  have hns : Fact (¬ IsSquare d) := ⟨not_isSquare_of_neg hdneg⟩
  have hmem : d ∈ hfin.toFinset := hfin.mem_toFinset.mpr
    ⟨hns, hdneg, hsf, (e.symm.toRingEquiv.classNumber_eq).trans_le hB⟩
  refine ⟨d, ⟨hmem, ⟨e⟩⟩, fun d' ⟨hd'mem, he'⟩ ↦ ?_⟩
  obtain ⟨_, hd'neg, hd'sf, _⟩ := hfin.mem_toFinset.mp hd'mem
  exact huniq d' ⟨hd'neg, hd'sf, he'⟩

/-- **The class number tends to `∞` as `|discr| → ∞`** along any family of imaginary quadratic
number fields. -/
theorem tendsto_classNumber_atTop_of_tendsto_natAbs_discr
    {ι : Type*} {l : Filter ι} {K : ι → Type u}
    [∀ i, Field (K i)] [∀ i, NumberField (K i)] [∀ i, NumberField.IsTotallyComplex (K i)]
    (hK : ∀ i, Module.finrank ℚ (K i) = 2)
    (hdiscr : Tendsto (fun i ↦ (NumberField.discr (K i)).natAbs) l atTop) :
    Tendsto (fun i ↦ NumberField.classNumber (K i)) l atTop := by
  rw [tendsto_atTop]
  intro B
  obtain ⟨C, hC⟩ := imaginary_discr_bounded_of_classNumber_le.{u} B
  filter_upwards [hdiscr.eventually (eventually_ge_atTop (⌊max C 0⌋₊ + 1))] with i hi
  by_contra hlt
  have hle : |(discr (K i) : ℝ)| ≤ max C 0 :=
    (hC (K i) (hK i) (Nat.le_of_lt (not_le.mp hlt))).trans (le_max_left _ _)
  rw [← Int.cast_abs, ← Nat.cast_natAbs] at hle
  have hlt_floor : ((discr (K i)).natAbs : ℝ) < (⌊max C 0⌋₊ + 1 : ℕ) := by
    push_cast
    exact hle.trans_lt (Nat.lt_floor_add_one _)
  exact (not_lt_of_ge hi) (Nat.cast_lt.mp hlt_floor)

/-- **The class number of `ℚ(√(d i))` tends to `∞` as `d i → -∞`** along squarefree radicands. -/
theorem tendsto_classNumber_quadraticAlgebra_of_tendsto_atBot
    {ι : Type*} {l : Filter ι} {d : ι → ℤ} [∀ i, Fact (¬ IsSquare (d i))]
    (hsf : ∀ i, Squarefree (d i)) (hbot : Tendsto d l atBot) :
    Tendsto (fun i ↦ NumberField.classNumber (QuadraticAlgebra ℚ (d i : ℚ) 0)) l atTop := by
  rw [tendsto_atTop]
  intro B
  obtain ⟨C, hC⟩ := imaginary_discr_bounded_of_classNumber_le.{0} B
  set M : ℤ := min (-1) (-⌊C⌋ - 1)
  filter_upwards [hbot.eventually (eventually_le_atBot M)] with i hi
  have hdneg : d i < 0 := lt_of_le_of_lt (hi.trans (min_le_left _ _)) (by omega)
  have : IsTotallyComplex (QuadraticAlgebra ℚ (d i : ℚ) 0) :=
    QuadraticAlgebra.isTotallyComplex_iff.mpr (by exact_mod_cast hdneg)
  by_contra hlt
  have hb := hC (QuadraticAlgebra ℚ (d i : ℚ) 0) (QuadraticAlgebra.finrank_eq_two _ _)
    (Nat.le_of_lt (not_le.mp hlt))
  rw [← Int.cast_abs] at hb
  have hd_le : -d i ≤ |discr (QuadraticAlgebra ℚ (d i : ℚ) 0)| :=
    (abs_of_neg hdneg).symm.trans_le (QuadraticAlgebra.abs_le_abs_discr (hsf i))
  have hle : ((-d i : ℤ) : ℝ) ≤ C := (Int.cast_le.mpr hd_le).trans hb
  have hfloor : -d i ≤ ⌊C⌋ := Int.le_floor.mpr hle
  have hM : d i ≤ -⌊C⌋ - 1 := hi.trans (min_le_right _ _)
  omega

end NumberField

end TauCeti
