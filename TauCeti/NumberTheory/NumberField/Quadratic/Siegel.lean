/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.Character
public import TauCeti.NumberTheory.NumberField.Quadratic.ClassNumber
public import TauCeti.NumberTheory.NumberField.Quadratic.Radicand
import TauCeti.Algebra.Squarefree
import TauCeti.NumberTheory.LSeries.Quadratic.Siegel
import TauCeti.NumberTheory.NumberField.Quadratic.DedekindZeta

/-!
# Siegel's class-number lower bound and finiteness of imaginary quadratic fields

Combining the analytic class number inequality `h(K) ≥ √|D| L(1, χ_D) / π`
(`TauCeti.NumberField.sqrt_mul_LFunction_one_re_div_le_classNumber`) with Siegel's lower bound
`L(1, χ_D) ≥ c(ε) |D| ^ (-ε)` (`TauCeti.Multiquadratic.exists_pos_forall_rpow_le_LFunction_one_re`)
yields **Siegel's class-number bound**: for every `ε > 0` there is an (ineffective) constant
`c > 0`, independent of the universe `u`, such that every imaginary quadratic number field
`K : Type u` satisfies

`c * |discr K| ^ (1 / 2 - ε) ≤ classNumber K`.

Evaluating at `ε = 1 / 4` gives `|discr K| ≤ (B / c) ^ 4` whenever `classNumber K ≤ B`, from which
class-number divergence and finiteness of imaginary quadratic fields, squarefree radicands, and
negative fundamental discriminants of bounded or prescribed class number follow.

## Main results

* `TauCeti.NumberField.isTotallyComplex_iff_discr_lt_zero`: a quadratic number field is totally
  complex if and only if its discriminant is negative.
* `TauCeti.NumberField.exists_pos_forall_rpow_abs_discr_le_classNumber`: Siegel's lower bound
  `c * |discr K| ^ (1 / 2 - ε) ≤ classNumber K`.
* `TauCeti.NumberField.exists_abs_discr_le_of_classNumber_le` and
  `TauCeti.NumberField.exists_le_classNumber_of_le_abs_discr`: bounded class number bounds
  `|discr K|`, and `classNumber K → ∞` as `|discr K| → ∞`.
* `TauCeti.NumberField.exists_finset_neg_squarefree_algEquiv_of_classNumber_le`: up to `ℚ`-algebra
  isomorphism, only finitely many imaginary quadratic fields have `classNumber K ≤ B`.
* `TauCeti.NumberField.finite_neg_squarefree_of_classNumber_le` and
  `TauCeti.NumberField.finite_neg_squarefree_of_classNumber_eq`: finiteness of negative squarefree
  radicands `d` with `classNumber ℚ(√d) ≤ B` or `= B`.
* `TauCeti.NumberField.exists_squarefree_discr_quadraticAlgebra_eq`,
  `TauCeti.NumberField.finite_neg_isFundamentalDiscr_of_classNumber_le`, and
  `TauCeti.NumberField.finite_neg_isFundamentalDiscr_of_classNumber_eq`: squarefree model
  realization and finiteness of negative fundamental discriminants of bounded or prescribed class
  number.

## References

* C. L. Siegel, *Über die Classenzahl quadratischer Zahlkörper*, Acta Arith. 1 (1935), 83–86.
* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Davenport, *Multiplicative Number Theory*, Chapter 21.
-/

public section

universe u

open Module NumberField
open scoped Real

namespace TauCeti.NumberField

/-- **A quadratic field is totally complex if and only if its discriminant is negative.** In terms
of a squarefree radicand `d`, `discr K` is `d` or `4 * d`, which has the same sign as `d`. -/
theorem isTotallyComplex_iff_discr_lt_zero {K : Type*} [Field K] [NumberField K]
    (hK : finrank ℚ K = 2) : IsTotallyComplex K ↔ discr K < 0 := by
  obtain ⟨θ, d, hmin, hgen, hsf⟩ := exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top hK
  rw [isTotallyComplex_iff_neg_of_minpoly_eq_X_sq_sub_C hmin hgen]
  by_cases hd4 : d % 4 = 1
  · rw [NumberField.discr_eq_of_squarefree_of_mod_four_eq_one hmin hgen hsf hd4]
  · rw [NumberField.discr_eq_four_mul_of_mod_four_ne_one hmin hgen hsf hd4]
    omega

/-- **Siegel's class-number lower bound for imaginary quadratic fields.** For every `ε > 0` there
exists `c > 0` (independent of the universe `u`) such that every totally complex quadratic number
field `K : Type u` satisfies `c * |discr K| ^ (1 / 2 - ε) ≤ classNumber K`. -/
theorem exists_pos_forall_rpow_abs_discr_le_classNumber {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K],
        finrank ℚ K = 2 →
        c * |(discr K : ℝ)| ^ ((1 : ℝ) / 2 - ε) ≤ classNumber K := by
  obtain ⟨c₀, hc₀, hS⟩ := TauCeti.Multiquadratic.exists_pos_forall_rpow_le_LFunction_one_re hε
  refine ⟨c₀ / π, div_pos hc₀ Real.pi_pos, fun K _ _ _ hK ↦ ?_⟩
  have hD : Int.IsFundamentalDiscr (discr K) := TauCeti.Multiquadratic.isFundamentalDiscr_discr hK
  have hD_neg : discr K < 0 := (isTotallyComplex_iff_discr_lt_zero hK).mp inferInstance
  have hD1 : discr K ≠ 1 := by omega
  have hL : c₀ * |(discr K : ℝ)| ^ (-ε) ≤
      ((TauCeti.Multiquadratic.fundamentalDiscriminantCharCast ℂ (discr K) hD).LFunction 1).re :=
    hS (discr K) hD hD1
  have hchar : (TauCeti.Multiquadratic.fundamentalDiscriminantChar (discr K) hD).ringHomComp
      (Int.castRingHom ℂ) =
      TauCeti.Multiquadratic.fundamentalDiscriminantCharCast ℂ (discr K) hD := by
    ext a; simp
  have hD_pos : 0 < |(discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have hcnf := sqrt_mul_LFunction_one_re_div_le_classNumber hK
  rw [hchar] at hcnf
  refine le_trans ?_ hcnf
  have hmul : √|(discr K : ℝ)| * (c₀ * |(discr K : ℝ)| ^ (-ε)) / π ≤
      √|(discr K : ℝ)| *
        ((TauCeti.Multiquadratic.fundamentalDiscriminantCharCast ℂ (discr K) hD).LFunction 1).re /
          π :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg _)) Real.pi_pos.le
  refine le_trans ?_ hmul
  rw [Real.sqrt_eq_rpow, mul_left_comm _ c₀, ← Real.rpow_add hD_pos,
    show (1 / 2 : ℝ) + -ε = (1 : ℝ) / 2 - ε by ring, mul_div_right_comm]

/-- **Bounded class number bounds the discriminant of an imaginary quadratic field.** For every
`B : ℕ` there exists `C : ℝ` such that every totally complex quadratic number field `K : Type u`
with `classNumber K ≤ B` satisfies `|discr K| ≤ C`. -/
theorem exists_abs_discr_le_of_classNumber_le (B : ℕ) :
    ∃ C : ℝ, ∀ (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K],
      finrank ℚ K = 2 → classNumber K ≤ B → |(discr K : ℝ)| ≤ C := by
  obtain ⟨c, hc, hS⟩ :=
    exists_pos_forall_rpow_abs_discr_le_classNumber.{u} (ε := 1 / 4) (by norm_num)
  refine ⟨((B : ℝ) / c) ^ (4 : ℝ), fun K _ _ _ hK hB ↦ ?_⟩
  have hlo : c * |(discr K : ℝ)| ^ (1 / 4 : ℝ) ≤ B := by
    refine (le_trans ?_ (hS K hK)).trans (Nat.cast_le.mpr hB)
    exact le_of_eq (by congr 2; norm_num)
  have hquarter : |(discr K : ℝ)| ^ (1 / 4 : ℝ) ≤ (B : ℝ) / c :=
    (le_div_iff₀' hc).mpr hlo
  have hpow := Real.rpow_le_rpow
    (Real.rpow_nonneg (abs_nonneg _) _) hquarter (by norm_num : (0 : ℝ) ≤ 4)
  rwa [← Real.rpow_mul (abs_nonneg _), show (1 / 4 : ℝ) * 4 = 1 by norm_num, Real.rpow_one] at hpow

/-- **Divergence of the imaginary quadratic class number.** For every `B : ℕ` there exists `C : ℝ`
such that every totally complex quadratic number field `K : Type u` with `C ≤ |discr K|` satisfies
`B ≤ classNumber K`. -/
theorem exists_le_classNumber_of_le_abs_discr (B : ℕ) :
    ∃ C : ℝ, ∀ (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K],
      finrank ℚ K = 2 → C ≤ |(discr K : ℝ)| → B ≤ classNumber K := by
  rcases eq_or_ne B 0 with rfl | hB0
  · exact ⟨0, fun _ _ _ _ _ _ ↦ Nat.zero_le _⟩
  · have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
    obtain ⟨C₀, hC₀⟩ := exists_abs_discr_le_of_classNumber_le.{u} (B - 1)
    refine ⟨C₀ + 1, fun K _ _ _ hK hle ↦ ?_⟩
    by_contra! hlt
    have h1 := hC₀ K hK (by omega)
    linarith

/-- **Finiteness of imaginary quadratic fields of bounded class number up to isomorphism.** For
every `B : ℕ` there exists a finite set `S` of negative squarefree integers such that every totally
complex quadratic number field `K : Type u` with `classNumber K ≤ B` is `ℚ`-isomorphic to
`QuadraticAlgebra ℚ d 0` for some `d ∈ S`. -/
theorem exists_finset_neg_squarefree_algEquiv_of_classNumber_le (B : ℕ) :
    ∃ S : Finset ℤ, (∀ d ∈ S, d < 0 ∧ Squarefree d) ∧
      ∀ (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K],
        finrank ℚ K = 2 → classNumber K ≤ B →
        ∃ d ∈ S, Nonempty (K ≃ₐ[ℚ] QuadraticAlgebra ℚ (d : ℚ) 0) := by
  classical
  obtain ⟨C, hC⟩ := exists_abs_discr_le_of_classNumber_le.{u} B
  set M : ℤ := (⌈max C 0⌉₊ : ℤ)
  set S : Finset ℤ := (Finset.Icc (-M) (-1)).filter Squarefree
  refine ⟨S, fun d hd ↦ ?_, fun K _ _ _ hK hB ↦ ?_⟩
  · obtain ⟨hIcc, hsf⟩ := Finset.mem_filter.mp hd
    exact ⟨by linarith [(Finset.mem_Icc.mp hIcc).2], hsf⟩
  · obtain ⟨θ, d, hmin, hgen, hsf, hneg⟩ :=
      exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top_of_isTotallyComplex hK
    have hd_le_discr : ((-d : ℤ) : ℝ) ≤ |(discr K : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast (by
        by_cases hd4 : d % 4 = 1
        · rw [NumberField.discr_eq_of_squarefree_of_mod_four_eq_one hmin hgen hsf hd4,
            abs_of_neg hneg]
        · rw [NumberField.discr_eq_four_mul_of_mod_four_ne_one hmin hgen hsf hd4,
            abs_of_neg (by omega)]
          omega : -d ≤ |discr K|)
    have hd_le_M : ((-d : ℤ) : ℝ) ≤ (M : ℝ) :=
      (hd_le_discr.trans (hC K hK hB)).trans
        ((le_max_left C 0).trans (by simpa [M] using Nat.le_ceil (max C 0)))
    have hdM : -d ≤ M := by exact_mod_cast hd_le_M
    have hd_mem : d ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hsf⟩
    exact ⟨d, hd_mem, nonempty_algEquiv_quadraticAlgebra hK hmin⟩

/-- **Finiteness of negative squarefree radicands with bounded class number.** For every `B : ℕ`,
only finitely many negative squarefree integers `d` satisfy
`classNumber (QuadraticAlgebra ℚ d 0) ≤ B`. -/
theorem finite_neg_squarefree_of_classNumber_le (B : ℕ) :
    {d : ℤ | d < 0 ∧ Squarefree d ∧
      ∃ (_ : Fact (¬ IsSquare d)), classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) ≤ B}.Finite := by
  obtain ⟨S, hS_prop, hS⟩ := exists_finset_neg_squarefree_algEquiv_of_classNumber_le.{0} B
  refine S.finite_toSet.subset fun d ⟨hneg, hsf, _, hB⟩ ↦ ?_
  have : IsTotallyComplex (QuadraticAlgebra ℚ (d : ℚ) 0) :=
    (QuadraticAlgebra.isTotallyComplex_iff (a := (d : ℚ))).mpr (Int.cast_lt_zero.mpr hneg)
  obtain ⟨e, heS, hφ⟩ := hS (QuadraticAlgebra ℚ (d : ℚ) 0) (QuadraticAlgebra.finrank_eq_two _ _) hB
  have hde : d = e :=
    (existsUnique_squarefree_algEquiv (QuadraticAlgebra.finrank_eq_two (d : ℚ) 0)).unique
      ⟨hsf, ⟨AlgEquiv.refl⟩⟩ ⟨(hS_prop e heS).2, hφ⟩
  exact hde ▸ heS

/-- **Finite fibers of the imaginary quadratic class number on radicands.** For every `B : ℕ`,
only finitely many negative squarefree integers `d` satisfy
`classNumber (QuadraticAlgebra ℚ d 0) = B`. -/
theorem finite_neg_squarefree_of_classNumber_eq (B : ℕ) :
    {d : ℤ | d < 0 ∧ Squarefree d ∧
      ∃ (_ : Fact (¬ IsSquare d)), classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) = B}.Finite :=
  (finite_neg_squarefree_of_classNumber_le B).subset
    fun _ ⟨hneg, hsf, hns, hB⟩ ↦ ⟨hneg, hsf, hns, hB.le⟩

/-- **Realization of fundamental discriminants by squarefree quadratic models.** Every fundamental
discriminant `D ≠ 1` is the field discriminant of `QuadraticAlgebra ℚ d 0` for a squarefree
nonsquare integer `d` of the same sign as `D`. -/
theorem exists_squarefree_discr_quadraticAlgebra_eq {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hD1 : D ≠ 1) :
    ∃ d : ℤ, Squarefree d ∧ (D < 0 ↔ d < 0) ∧
      ∃ (_ : Fact (¬ IsSquare d)), discr (QuadraticAlgebra ℚ (d : ℚ) 0) = D := by
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hD with ⟨hmod1, hsf⟩ | ⟨hmod0, hmsf, hm4⟩
  · have hns : Fact (¬ IsSquare D) :=
      ⟨mt Rat.isSquare_intCast_iff.mpr (not_isSquare_intCast_of_squarefree_of_ne_one hsf hD1)⟩
    exact ⟨D, hsf, Iff.rfl, hns, QuadraticAlgebra.discr_eq_of_mod_four_eq_one hsf hmod1⟩
  · set m : ℤ := D / 4
    have hDm : D = 4 * m := (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hmod0)).symm
    have hm_ne1 : m ≠ 1 := by omega
    have hm_mod : m % 4 ≠ 1 := by omega
    have hns : Fact (¬ IsSquare m) :=
      ⟨mt Rat.isSquare_intCast_iff.mpr (not_isSquare_intCast_of_squarefree_of_ne_one hmsf hm_ne1)⟩
    refine ⟨m, hmsf, by omega, hns, ?_⟩
    rw [QuadraticAlgebra.discr_eq_four_mul_of_mod_four_ne_one hmsf hm_mod, ← hDm]

/-- **Finiteness of negative fundamental discriminants of bounded class number.** For every `B : ℕ`,
only finitely many negative fundamental discriminants `D` arise as `discr K` for a quadratic number
field `K` with `classNumber K ≤ B`. -/
theorem finite_neg_isFundamentalDiscr_of_classNumber_le (B : ℕ) :
    {D : ℤ | D < 0 ∧ Int.IsFundamentalDiscr D ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K),
        finrank ℚ K = 2 ∧ discr K = D ∧ classNumber K ≤ B}.Finite := by
  obtain ⟨C, hC⟩ := exists_abs_discr_le_of_classNumber_le.{0} B
  set M : ℤ := (⌈max C 0⌉₊ : ℤ)
  refine (Set.finite_Icc (-M) 0).subset fun D ⟨hneg, _, K, _, _, hK, hDK, hB⟩ ↦ ?_
  have : IsTotallyComplex K := (isTotallyComplex_iff_discr_lt_zero hK).mpr (hDK ▸ hneg)
  have hle : ((-D : ℤ) : ℝ) ≤ (M : ℝ) := by
    have h1 : ((-D : ℤ) : ℝ) = |(discr K : ℝ)| := by
      rw [hDK, ← Int.cast_abs, abs_of_neg hneg]
    exact (h1.trans_le (hC K hK hB)).trans
      ((le_max_left C 0).trans (by simpa [M] using Nat.le_ceil (max C 0)))
  have hDM : -D ≤ M := by exact_mod_cast hle
  exact ⟨by omega, hneg.le⟩

/-- **Finite fibers of the imaginary quadratic class number on fundamental discriminants.** For
every `B : ℕ`, only finitely many negative fundamental discriminants `D` arise as `discr K` for a
quadratic number field `K` with `classNumber K = B`. -/
theorem finite_neg_isFundamentalDiscr_of_classNumber_eq (B : ℕ) :
    {D : ℤ | D < 0 ∧ Int.IsFundamentalDiscr D ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K),
        finrank ℚ K = 2 ∧ discr K = D ∧ classNumber K = B}.Finite :=
  (finite_neg_isFundamentalDiscr_of_classNumber_le B).subset
    fun _ ⟨hneg, hD, K, hF, hNF, hK, hDK, hB⟩ ↦ ⟨hneg, hD, K, hF, hNF, hK, hDK, hB.le⟩

end TauCeti.NumberField
