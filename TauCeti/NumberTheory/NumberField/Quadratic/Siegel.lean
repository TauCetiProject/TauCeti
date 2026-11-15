/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import TauCeti.NumberTheory.BinaryQuadraticForm.PrimitiveReduced
public import TauCeti.NumberTheory.NumberField.QuadraticAlgebra
import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.ClassNumber
import TauCeti.NumberTheory.LSeries.Quadratic.Siegel
import TauCeti.NumberTheory.NumberField.ClassNumber.RingEquiv
import TauCeti.NumberTheory.NumberField.Quadratic.DedekindZeta
import TauCeti.NumberTheory.NumberField.Quadratic.Model
import TauCeti.NumberTheory.NumberField.Quadratic.Radicand
import TauCeti.NumberTheory.QuadraticOrder.Field

/-!
# Class-number lower bounds and finiteness for imaginary quadratic fields

Combining Siegel's lower bound `Re L(1, χ) ≥ c q ^ (-ε)` (`TauCeti.quadratic_LFunction_siegel`)
with the analytic class number inequality `h(K) ≥ √|D| Re L(1, χ_D) / π`
(`TauCeti.NumberField.sqrt_mul_LFunction_one_re_div_le_classNumber`) yields Siegel's class-number
estimate `h(K) ≥ c(ε) |D| ^ (1 / 2 - ε)` for every imaginary quadratic field `K` of discriminant
`D` (`TauCeti.imaginary_classNumber_lower_bound`).

Specializing to `ε = 1 / 4` bounds `|D|` uniformly in terms of any upper bound `h(K) ≤ B`
(`TauCeti.imaginary_discr_bounded_of_classNumber_le`). This implies the Gauss–Heilbronn–Siegel
qualitative consequences for imaginary quadratic fields:

* `h(K) → ∞` as `|D| → ∞` (`TauCeti.exists_le_imaginary_classNumber_of_le_natAbs_discr`,
  `TauCeti.tendsto_card_primitiveReducedForms_atTop`);
* finiteness of negative fundamental discriminants of class number at most `B`, of prescribed class
  number `B`, and in particular of class number one
  (`TauCeti.finite_neg_isFundamentalDiscr_card_primitiveReducedForms_le`,
  `TauCeti.finite_neg_isFundamentalDiscr_card_primitiveReducedForms_eq`,
  `TauCeti.finite_neg_isFundamentalDiscr_classNumber_le`,
  `TauCeti.finite_neg_isFundamentalDiscr_classNumber_eq_one`);
* finiteness of negative squarefree radicands `d` whose model `ℚ(√d)` has class number at most `B`
  or equal to `B` (`TauCeti.finite_neg_squarefree_classNumber_le`,
  `TauCeti.finite_neg_squarefree_classNumber_eq`);
* a finite irredundant set of negative squarefree radicands classifying all imaginary quadratic
  number fields of class number at most `B` up to `ℚ`-algebra isomorphism
  (`TauCeti.exists_finset_neg_squarefree_algEquiv_iff_classNumber_le`).

Because `TauCeti.quadratic_LFunction_siegel` is ineffective, the constants and finite sets obtained
here are existential rather than explicitly enumerated.

## Main results

* `TauCeti.imaginary_classNumber_lower_bound`: `c |D| ^ (1 / 2 - ε) ≤ classNumber L` for every
  imaginary quadratic field `L`.
* `TauCeti.imaginary_discr_bounded_of_classNumber_le`: `classNumber L ≤ B` implies `|D| ≤ C`.
* `TauCeti.exists_le_imaginary_classNumber_of_le_natAbs_discr` and
  `TauCeti.tendsto_card_primitiveReducedForms_atTop`: divergence of the class number with `|D|`.
* `TauCeti.finite_neg_isFundamentalDiscr_card_primitiveReducedForms_le`,
  `TauCeti.finite_neg_isFundamentalDiscr_classNumber_le`,
  `TauCeti.finite_neg_squarefree_classNumber_le`, and
  `TauCeti.exists_finset_neg_squarefree_algEquiv_iff_classNumber_le`: finiteness of discriminants,
  radicands, and `ℚ`-isomorphism classes of imaginary quadratic fields of bounded class number.

## References

* C. L. Siegel, *Über die Classenzahl quadratischer Zahlkörper*, Acta Arith. 1 (1935), 83–86.
* H. Davenport, *Multiplicative Number Theory*, Chapter 21.
-/

public section

open Filter Finset NumberField
open scoped Topology

universe u

namespace TauCeti

/-- **Siegel's class-number lower bound for imaginary quadratic fields.** For every `ε > 0`, there
exists `c > 0` such that `c |discr L| ^ (1 / 2 - ε) ≤ classNumber L` for every imaginary quadratic
number field `L`. -/
theorem imaginary_classNumber_lower_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (L : Type u) [Field L] [NumberField L] [NumberField.IsTotallyComplex L],
        Module.finrank ℚ L = 2 →
        c * |(NumberField.discr L : ℝ)| ^ (1 / 2 - ε) ≤ NumberField.classNumber L := by
  obtain ⟨c₀, hc₀, hsieg⟩ := quadratic_LFunction_siegel hε
  refine ⟨c₀ / Real.pi, div_pos hc₀ Real.pi_pos, fun L _ _ _ hL ↦ ?_⟩
  set D := NumberField.discr L
  let χ : DirichletCharacter ℂ D.natAbs :=
    (Multiquadratic.fundamentalDiscriminantChar D
      (Multiquadratic.isFundamentalDiscr_discr hL)).ringHomComp (Int.castRingHom ℂ)
  have hχq : χ.IsQuadratic := (Multiquadratic.fundamentalDiscriminantChar_isQuadratic _).comp _
  have hχ1 : χ ≠ 1 := Multiquadratic.ringHomComp_fundamentalDiscriminantChar_discr_ne_one hL
  have hDpos : 0 < |(D : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero L))
  have hq : (D.natAbs : ℝ) = |(D : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hLlo : c₀ * |(D : ℝ)| ^ (-ε) ≤ (χ.LFunction 1).re := by
    simpa [hq] using hsieg D.natAbs χ hχq hχ1
  calc
    c₀ / Real.pi * |(D : ℝ)| ^ (1 / 2 - ε)
      = √|(D : ℝ)| * (c₀ * |(D : ℝ)| ^ (-ε)) / Real.pi := by
      rw [sub_eq_add_neg, Real.rpow_add hDpos, ← Real.sqrt_eq_rpow]
      ring
    _ ≤ √|(D : ℝ)| * (χ.LFunction 1).re / Real.pi := by gcongr
    _ ≤ NumberField.classNumber L := NumberField.sqrt_mul_LFunction_one_re_div_le_classNumber hL

/-- **Discriminant bound for imaginary quadratic fields of bounded class number.** For every `B`,
there is a constant `C` such that every imaginary quadratic field `L` with `classNumber L ≤ B` has
`|discr L| ≤ C`. -/
theorem imaginary_discr_bounded_of_classNumber_le (B : ℕ) :
    ∃ C : ℝ, ∀ (L : Type u) [Field L] [NumberField L] [NumberField.IsTotallyComplex L],
      Module.finrank ℚ L = 2 → NumberField.classNumber L ≤ B →
      |(NumberField.discr L : ℝ)| ≤ C := by
  obtain ⟨c, hc, hlo⟩ := imaginary_classNumber_lower_bound.{u} (ε := 1 / 4) (by norm_num)
  refine ⟨(B / c) ^ (4 : ℕ), fun L _ _ _ hL hB ↦ ?_⟩
  have hD0 : 0 ≤ |(NumberField.discr L : ℝ)| := abs_nonneg _
  have hexp : (1 / 2 - 1 / 4 : ℝ) = 1 / 4 := by norm_num
  have h14 : c * |(NumberField.discr L : ℝ)| ^ (1 / 4 : ℝ) ≤ B := by
    have h := (hlo L hL).trans (Nat.cast_le.mpr hB)
    rwa [hexp] at h
  have hdiv : |(NumberField.discr L : ℝ)| ^ (1 / 4 : ℝ) ≤ B / c :=
    (le_div_iff₀ hc).mpr (by linarith)
  calc
    |(NumberField.discr L : ℝ)| = (|(NumberField.discr L : ℝ)| ^ (1 / 4 : ℝ)) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hD0]
      norm_num
    _ ≤ (B / c) ^ (4 : ℕ) := pow_le_pow_left₀ (by positivity) hdiv 4

/-- **Divergence of the class number of imaginary quadratic fields.** For every `B`, there exists
`N` such that every imaginary quadratic field `L` with `N ≤ (discr L).natAbs` satisfies
`B ≤ classNumber L`. -/
theorem exists_le_imaginary_classNumber_of_le_natAbs_discr (B : ℕ) :
    ∃ N : ℕ, ∀ (L : Type u) [Field L] [NumberField L] [NumberField.IsTotallyComplex L],
      Module.finrank ℚ L = 2 → N ≤ (NumberField.discr L).natAbs →
      B ≤ NumberField.classNumber L := by
  rcases eq_or_ne B 0 with rfl | _
  · exact ⟨0, fun _ _ _ _ _ _ ↦ Nat.zero_le _⟩
  obtain ⟨C, hC⟩ := imaginary_discr_bounded_of_classNumber_le.{u} (B - 1)
  refine ⟨⌊max 0 C⌋₊ + 1, fun L _ _ _ hL hN ↦ ?_⟩
  by_contra! hlt
  have hle : |(NumberField.discr L : ℝ)| ≤ C := hC L hL (Nat.le_sub_one_of_lt hlt)
  have hN_real : (⌊max 0 C⌋₊ + 1 : ℝ) ≤ |(NumberField.discr L : ℝ)| := by
    have hcast : ((⌊max 0 C⌋₊ + 1 : ℕ) : ℝ) ≤ ((NumberField.discr L).natAbs : ℝ) :=
      Nat.cast_le.mpr hN
    simpa [Nat.cast_natAbs, Int.cast_abs] using hcast
  have hClt : C < (⌊max 0 C⌋₊ + 1 : ℝ) :=
    (le_max_right 0 C).trans_lt (Nat.lt_floor_add_one _)
  linarith

/-- **Class numbers of negative fundamental discriminants tend to infinity.** Along negative
fundamental discriminants `-n`, the class number `#(primitiveReducedForms n)` of `ℚ(√(-n))` tends
to `∞` as `n → ∞`. -/
theorem tendsto_card_primitiveReducedForms_atTop :
    Tendsto (fun n : ℕ ↦ #(primitiveReducedForms n))
      (atTop ⊓ 𝓟 {n : ℕ | Int.IsFundamentalDiscr (-(n : ℤ))}) atTop := by
  rw [tendsto_atTop]
  intro B
  obtain ⟨N, hN⟩ := exists_le_imaginary_classNumber_of_le_natAbs_discr.{0} B
  rw [eventually_inf_principal, eventually_atTop]
  refine ⟨max N 1, fun n hn hfund ↦ ?_⟩
  have : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le zero_lt_one ((le_max_right N 1).trans hn))⟩
  have hlt0 : ((-n : ℤ) : ℚ) < 0 := by
    exact_mod_cast neg_neg_of_pos (Int.natCast_pos.mpr (NeZero.pos n))
  have : IsTotallyComplex (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) :=
    QuadraticAlgebra.isTotallyComplex_iff.mpr hlt0
  rw [← BinaryQuadraticForm.classNumber_eq_card_primitiveReducedForms n hfund]
  refine hN (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) (QuadraticAlgebra.finrank_eq_two _ _) ?_
  rw [QuadraticAlgebra.discr_eq_of_isFundamentalDiscr hfund, Int.natAbs_neg, Int.natAbs_natCast]
  exact (le_max_left N 1).trans hn

/-- **Finiteness of negative fundamental discriminants with bounded class number** (read on
primitive reduced binary quadratic forms). -/
theorem finite_neg_isFundamentalDiscr_card_primitiveReducedForms_le (B : ℕ) :
    {D : ℤ | D < 0 ∧ Int.IsFundamentalDiscr D ∧
      #(primitiveReducedForms D.natAbs) ≤ B}.Finite := by
  obtain ⟨C, hC⟩ := imaginary_discr_bounded_of_classNumber_le.{0} B
  let M : ℤ := ⌊max 0 C⌋₊ + 1
  refine (Set.finite_Icc (-M) 0).subset fun D ⟨hDneg, hDfund, hB⟩ ↦ ?_
  have : Fact (¬ IsSquare D) := ⟨not_isSquare_of_neg hDneg⟩
  have : IsTotallyComplex (QuadraticAlgebra ℚ (D : ℚ) 0) :=
    QuadraticAlgebra.isTotallyComplex_iff.mpr (by exact_mod_cast hDneg)
  have hcl : NumberField.classNumber (QuadraticAlgebra ℚ (D : ℚ) 0) ≤ B := by
    rwa [BinaryQuadraticForm.classNumber_eq_card_primitiveReducedForms_of_discr_eq (n := D.natAbs)
      (QuadraticAlgebra.finrank_eq_two (D : ℚ) 0)
      (by rw [QuadraticAlgebra.discr_eq_of_isFundamentalDiscr hDfund]; omega)]
  have hbound := hC (QuadraticAlgebra ℚ (D : ℚ) 0) (QuadraticAlgebra.finrank_eq_two _ _) hcl
  rw [QuadraticAlgebra.discr_eq_of_isFundamentalDiscr hDfund] at hbound
  have habs : |(D : ℝ)| < (M : ℝ) := by
    refine hbound.trans_lt ?_
    have hlt := (le_max_right 0 C).trans_lt (Nat.lt_floor_add_one (max 0 C))
    simpa [M] using hlt
  have hlo : ((-M : ℤ) : ℝ) < (D : ℝ) := by simpa using neg_lt_of_abs_lt habs
  exact ⟨(Int.cast_lt.mp hlo).le, hDneg.le⟩

/-- **Finite fibers of the class number on negative fundamental discriminants.** For every `B`,
only finitely many negative fundamental discriminants `D` satisfy
`#(primitiveReducedForms |D|) = B`. -/
theorem finite_neg_isFundamentalDiscr_card_primitiveReducedForms_eq (B : ℕ) :
    {D : ℤ | D < 0 ∧ Int.IsFundamentalDiscr D ∧
      #(primitiveReducedForms D.natAbs) = B}.Finite :=
  (finite_neg_isFundamentalDiscr_card_primitiveReducedForms_le B).subset
    fun _ ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3.le⟩

/-- **Finiteness of negative fundamental discriminants with bounded field class number.** -/
theorem finite_neg_isFundamentalDiscr_classNumber_le (B : ℕ) :
    {D : ℤ | ∃ (_ : Fact (¬ IsSquare D)), D < 0 ∧ Int.IsFundamentalDiscr D ∧
      NumberField.classNumber (QuadraticAlgebra ℚ (D : ℚ) 0) ≤ B}.Finite := by
  refine (finite_neg_isFundamentalDiscr_card_primitiveReducedForms_le B).subset ?_
  rintro D ⟨_, hDneg, hDfund, hB⟩
  refine ⟨hDneg, hDfund, ?_⟩
  rwa [← BinaryQuadraticForm.classNumber_eq_card_primitiveReducedForms_of_discr_eq
    (QuadraticAlgebra.finrank_eq_two (D : ℚ) 0)
    (by rw [QuadraticAlgebra.discr_eq_of_isFundamentalDiscr hDfund]; omega)]

/-- **Gauss's class-number-one finiteness theorem.** Only finitely many negative fundamental
discriminants `D` have `classNumber ℚ(√D) = 1`. -/
theorem finite_neg_isFundamentalDiscr_classNumber_eq_one :
    {D : ℤ | ∃ (_ : Fact (¬ IsSquare D)), D < 0 ∧ Int.IsFundamentalDiscr D ∧
      NumberField.classNumber (QuadraticAlgebra ℚ (D : ℚ) 0) = 1}.Finite :=
  (finite_neg_isFundamentalDiscr_classNumber_le 1).subset
    fun _ ⟨h, h1, h2, h3⟩ ↦ ⟨h, h1, h2, h3.le⟩

/-- **Finiteness of negative squarefree radicands of bounded class number.** For every `B`, only
finitely many negative squarefree integers `d` satisfy `classNumber ℚ(√d) ≤ B`. -/
theorem finite_neg_squarefree_classNumber_le (B : ℕ) :
    {d : ℤ | ∃ (_ : Fact (¬ IsSquare d)), d < 0 ∧ Squarefree d ∧
      NumberField.classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) ≤ B}.Finite := by
  obtain ⟨C, hC⟩ := imaginary_discr_bounded_of_classNumber_le.{0} B
  let M : ℤ := ⌊max 0 C⌋₊ + 1
  refine (Set.finite_Icc (-M) 0).subset ?_
  rintro d ⟨_, hdneg, hdsf, hB⟩
  have : IsTotallyComplex (QuadraticAlgebra ℚ (d : ℚ) 0) :=
    QuadraticAlgebra.isTotallyComplex_iff.mpr (by exact_mod_cast hdneg)
  have hbound := hC (QuadraticAlgebra ℚ (d : ℚ) 0) (QuadraticAlgebra.finrank_eq_two _ _) hB
  have hd_le : |(d : ℝ)| ≤ |(NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0) : ℝ)| := by
    by_cases hd4 : d % 4 = 1
    · rw [QuadraticAlgebra.discr_eq_of_mod_four_eq_one hdsf hd4]
    · rw [QuadraticAlgebra.discr_eq_four_mul_of_mod_four_ne_one hdsf hd4, Int.cast_mul,
        Int.cast_ofNat, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      linarith [abs_nonneg (d : ℝ)]
  have habs : |(d : ℝ)| < (M : ℝ) := by
    refine (hd_le.trans hbound).trans_lt ?_
    have hlt := (le_max_right 0 C).trans_lt (Nat.lt_floor_add_one (max 0 C))
    simpa [M] using hlt
  have hlo : ((-M : ℤ) : ℝ) < (d : ℝ) := by simpa using neg_lt_of_abs_lt habs
  exact ⟨(Int.cast_lt.mp hlo).le, hdneg.le⟩

/-- **Finite fibers of the class number on negative squarefree radicands.** -/
theorem finite_neg_squarefree_classNumber_eq (B : ℕ) :
    {d : ℤ | ∃ (_ : Fact (¬ IsSquare d)), d < 0 ∧ Squarefree d ∧
      NumberField.classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) = B}.Finite :=
  (finite_neg_squarefree_classNumber_le B).subset
    fun _ ⟨h, h1, h2, h3⟩ ↦ ⟨h, h1, h2, h3.le⟩

/-- **Finiteness of imaginary quadratic fields of bounded class number up to isomorphism.** For
every `B`, there exists a finite set `S` of negative squarefree integers, each of whose models
`ℚ(√d)` has class number at most `B`, such that an arbitrary imaginary quadratic field `L` has
`classNumber L ≤ B` if and only if `L` is `ℚ`-isomorphic to `QuadraticAlgebra ℚ d 0` for some
(necessarily unique, by `NumberField.existsUnique_neg_squarefree_algEquiv`) `d ∈ S`. -/
theorem exists_finset_neg_squarefree_algEquiv_iff_classNumber_le (B : ℕ) :
    ∃ S : Finset ℤ,
      (∀ d ∈ S, ∃ (_ : Fact (¬ IsSquare d)),
        d < 0 ∧ Squarefree d ∧
          NumberField.classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) ≤ B) ∧
      ∀ (L : Type u) [Field L] [NumberField L] [NumberField.IsTotallyComplex L],
        Module.finrank ℚ L = 2 →
        (NumberField.classNumber L ≤ B ↔
          ∃ d ∈ S, Nonempty (L ≃ₐ[ℚ] QuadraticAlgebra ℚ (d : ℚ) 0)) := by
  have hfin := finite_neg_squarefree_classNumber_le B
  refine ⟨hfin.toFinset, fun d hd ↦ hfin.mem_toFinset.mp hd, fun L _ _ _ hL ↦ ?_⟩
  constructor
  · intro hB
    obtain ⟨d, ⟨hdneg, hdsf, ⟨e⟩⟩, -⟩ :=
      _root_.NumberField.existsUnique_neg_squarefree_algEquiv hL
    have : Fact (¬ IsSquare d) := ⟨not_isSquare_of_neg hdneg⟩
    refine ⟨d, hfin.mem_toFinset.mpr ⟨inferInstance, hdneg, hdsf, ?_⟩, ⟨e⟩⟩
    rwa [← RingEquiv.classNumber_eq e.toRingEquiv]
  · rintro ⟨d, hd, ⟨e⟩⟩
    obtain ⟨_, _, _, hcl⟩ := hfin.mem_toFinset.mp hd
    rwa [RingEquiv.classNumber_eq e.toRingEquiv]

end TauCeti
