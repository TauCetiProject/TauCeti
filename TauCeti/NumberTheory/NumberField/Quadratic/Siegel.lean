/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.QuadraticAlgebra
public import TauCeti.NumberTheory.NumberField.QuadraticAlgebra
import TauCeti.NumberTheory.LSeries.Quadratic.Siegel
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Discriminant
import TauCeti.NumberTheory.NumberField.ClassNumber.RingEquiv
import TauCeti.NumberTheory.NumberField.Quadratic.DedekindZeta
import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace
import TauCeti.NumberTheory.NumberField.Quadratic.Model
import TauCeti.NumberTheory.NumberField.Quadratic.Radicand
import TauCeti.NumberTheory.QuadraticOrder.Field

/-!
# Siegel's lower bound and finiteness for class numbers of imaginary quadratic fields

For every `ε > 0` there is `C > 0` such that every imaginary quadratic field `K` has class number
`h(K) ≥ C |disc K| ^ (1 / 2 - ε)` (`TauCeti.NumberField.imaginary_classNumber_lower_bound`). This
combines Siegel's theorem `L(1, χ_D) ≥ c |D| ^ (-ε)`
(`TauCeti.Multiquadratic.quadratic_LFunction_siegel`), applied to the quadratic character `χ_D` of
the discriminant `D` of `K` at its level `|D|`, with the class number formula in the form
`h ≥ √|D| L(1, χ_D) / π` (`TauCeti.NumberField.sqrt_mul_LFunction_one_re_div_le_classNumber`).

Taking `ε = 1 / 4` bounds the discriminant of an imaginary quadratic field in terms of its class
number (`TauCeti.NumberField.imaginary_discr_bounded_of_classNumber_le`). The bounds are
ineffective, because the constant in Siegel's theorem is. From this follow divergence
`classNumber K → ∞` as `|discr K| → ∞` and finiteness of imaginary quadratic fields up to
isomorphism, of negative squarefree radicands, and of negative fundamental discriminants with
bounded or prescribed class number.

## Main results

* `TauCeti.NumberField.imaginary_classNumber_lower_bound`: `h(K) ≥ C |disc K| ^ (1 / 2 - ε)`.
* `TauCeti.NumberField.imaginary_discr_bounded_of_classNumber_le`: for every `B` there is `C` with
  `|disc K| ≤ C` whenever `h(K) ≤ B`.
* `TauCeti.NumberField.exists_le_classNumber_of_le_abs_discr`: `h(K) → ∞` as `|disc K| → ∞`.
* `TauCeti.NumberField.finite_neg_squarefree_of_classNumber_le` and
  `TauCeti.NumberField.finite_neg_squarefree_of_classNumber_eq`: finiteness of negative squarefree
  radicands `d` with `classNumber ℚ(√d) ≤ B` or `= B`.
* `TauCeti.NumberField.exists_finset_neg_squarefree_algEquiv_of_classNumber_le`: exact finite
  classification of imaginary quadratic fields with `h(K) ≤ B` by negative squarefree radicands.
* `TauCeti.NumberField.finite_neg_isFundamentalDiscr_of_classNumber_le` and
  `TauCeti.NumberField.finite_neg_isFundamentalDiscr_of_classNumber_eq`: finiteness of negative
  fundamental discriminants `D` with `classNumber ℚ(√D) ≤ B` or `= B`.
* `TauCeti.NumberField.finite_neg_discr_of_classNumber_le` and
  `TauCeti.NumberField.finite_neg_discr_of_classNumber_eq`: finiteness of negative discriminants of
  abstract quadratic fields `K : Type u` with bounded or prescribed class number.

## References

* C. L. Siegel, *Über die Classenzahl quadratischer Zahlkörper*, Acta Arith. 1 (1935), 83–86.
* H. Davenport, *Multiplicative Number Theory*, Chapter 21.
-/

public section

open Module NumberField TauCeti.Multiquadratic

namespace TauCeti.NumberField

universe u

/-- **Siegel's lower bound for class numbers.** For every `ε > 0` there is `C > 0` such that every
imaginary quadratic field `K` has class number at least `C |disc K| ^ (1 / 2 - ε)`. The constant is
ineffective. -/
theorem imaginary_classNumber_lower_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K], finrank ℚ K = 2 →
      C * |(discr K : ℝ)| ^ (1 / 2 - ε) ≤ classNumber K := by
  obtain ⟨c, hc, hS⟩ := quadratic_LFunction_siegel hε
  refine ⟨c / Real.pi, div_pos hc Real.pi_pos, fun K _ _ _ hK ↦ ?_⟩
  have hfd := isFundamentalDiscr_discr hK
  have := hfd.neZero_natAbs
  have hχ := hS _ ((fundamentalDiscriminantChar (discr K) hfd).ringHomComp (Int.castRingHom ℂ))
    ((fundamentalDiscriminantChar_isQuadratic hfd).comp _)
    (ringHomComp_fundamentalDiscriminantChar_discr_ne_one hK)
  rw [Nat.cast_natAbs, Int.cast_abs] at hχ
  have hD : 0 < |(discr K : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  calc c / Real.pi * |(discr K : ℝ)| ^ (1 / 2 - ε)
      = √|(discr K : ℝ)| * (c * |(discr K : ℝ)| ^ (-ε)) / Real.pi := by
        rw [Real.sqrt_eq_rpow, sub_eq_add_neg, Real.rpow_add hD]
        ring
    _ ≤ √|(discr K : ℝ)| * (DirichletCharacter.LFunction
          ((fundamentalDiscriminantChar (discr K) hfd).ringHomComp (Int.castRingHom ℂ)) 1).re /
            Real.pi := by
        gcongr
    _ ≤ classNumber K := sqrt_mul_LFunction_one_re_div_le_classNumber hK

/-- **Discriminants of bounded class number are bounded.** For every `B` there is `C` such that
every imaginary quadratic field `K` with class number at most `B` has `|disc K| ≤ C`. The bound is
ineffective. -/
theorem imaginary_discr_bounded_of_classNumber_le (B : ℕ) :
    ∃ C : ℝ, ∀ (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K], finrank ℚ K = 2 →
      classNumber K ≤ B → |(discr K : ℝ)| ≤ C := by
  obtain ⟨C, hC, h⟩ := imaginary_classNumber_lower_bound.{u} (ε := 1 / 4) (by norm_num)
  refine ⟨(B / C) ^ 4, fun K _ _ _ hK hB ↦ ?_⟩
  have hD : 0 ≤ |(discr K : ℝ)| := abs_nonneg _
  have h4 : |(discr K : ℝ)| ^ (1 / 4 : ℝ) ≤ B / C := by
    rw [le_div_iff₀ hC, mul_comm]
    have := h K hK
    norm_num at this
    exact this.trans (by exact_mod_cast hB)
  calc |(discr K : ℝ)| = (|(discr K : ℝ)| ^ (1 / 4 : ℝ)) ^ 4 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hD]
        norm_num
    _ ≤ (B / C) ^ 4 := by gcongr

/-- **Divergence of the imaginary quadratic class number.** For every `B : ℕ` there exists `C : ℝ`
such that every totally complex quadratic number field `K : Type u` with `C ≤ |discr K|` satisfies
`B ≤ classNumber K`. -/
theorem exists_le_classNumber_of_le_abs_discr (B : ℕ) :
    ∃ C : ℝ, ∀ (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K],
      finrank ℚ K = 2 → C ≤ |(discr K : ℝ)| → B ≤ classNumber K := by
  rcases eq_or_ne B 0 with rfl | _
  · exact ⟨0, fun _ _ _ _ _ _ ↦ Nat.zero_le _⟩
  · obtain ⟨C₀, hC₀⟩ := imaginary_discr_bounded_of_classNumber_le.{u} (B - 1)
    refine ⟨C₀ + 1, fun K _ _ _ hK hle ↦ ?_⟩
    by_contra! hlt
    have h1 := hC₀ K hK (by omega)
    linarith

private theorem neg_le_ceil_of_classNumber_le {B : ℕ} {C : ℝ}
    (hC : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K],
      finrank ℚ K = 2 → classNumber K ≤ B → |(discr K : ℝ)| ≤ C)
    {a : ℤ} (hneg : a < 0) [Fact (¬ IsSquare a)]
    (hdiscr : (-a : ℤ) ≤ |discr (QuadraticAlgebra ℚ (a : ℚ) 0)|)
    (hB : classNumber (QuadraticAlgebra ℚ (a : ℚ) 0) ≤ B) :
    -a ≤ (⌈max C 0⌉₊ : ℤ) := by
  have : IsTotallyComplex (QuadraticAlgebra ℚ (a : ℚ) 0) :=
    (QuadraticAlgebra.isTotallyComplex_iff (a := (a : ℚ))).mpr (Int.cast_lt_zero.mpr hneg)
  have hcast : ((-a : ℤ) : ℝ) ≤ |(discr (QuadraticAlgebra ℚ (a : ℚ) 0) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hdiscr
  have hle : ((-a : ℤ) : ℝ) ≤ ((⌈max C 0⌉₊ : ℤ) : ℝ) :=
    hcast.trans <| (hC _ (QuadraticAlgebra.finrank_eq_two _ _) hB).trans <|
      (le_max_left C 0).trans (by simpa using Nat.le_ceil (max C 0))
  exact_mod_cast hle

/-- **Finiteness of negative squarefree radicands with bounded class number.** For every `B : ℕ`,
only finitely many negative squarefree integers `d` satisfy
`classNumber (QuadraticAlgebra ℚ d 0) ≤ B`. -/
theorem finite_neg_squarefree_of_classNumber_le (B : ℕ) :
    {d : ℤ | d < 0 ∧ Squarefree d ∧
      ∃ (_ : Fact (¬ IsSquare d)), classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) ≤ B}.Finite := by
  obtain ⟨C, hC⟩ := imaginary_discr_bounded_of_classNumber_le.{0} B
  refine (Set.finite_Icc (-(⌈max C 0⌉₊ : ℤ)) 0).subset fun d ⟨hneg, hsf, hns, hB⟩ ↦ ?_
  have : Fact (¬ IsSquare d) := hns
  have hdiscr : (-d : ℤ) ≤ |discr (QuadraticAlgebra ℚ (d : ℚ) 0)| := by
    by_cases hd4 : d % 4 = 1
    · rw [QuadraticAlgebra.discr_eq_of_mod_four_eq_one hsf hd4, abs_of_neg hneg]
    · rw [QuadraticAlgebra.discr_eq_four_mul_of_mod_four_ne_one hsf hd4, abs_of_neg (by omega)]
      omega
  have hM := neg_le_ceil_of_classNumber_le hC hneg hdiscr hB
  exact ⟨by omega, hneg.le⟩

/-- **Finite fibers of the imaginary quadratic class number on radicands.** For every `B : ℕ`,
only finitely many negative squarefree integers `d` satisfy
`classNumber (QuadraticAlgebra ℚ d 0) = B`. -/
theorem finite_neg_squarefree_of_classNumber_eq (B : ℕ) :
    {d : ℤ | d < 0 ∧ Squarefree d ∧
      ∃ (_ : Fact (¬ IsSquare d)), classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) = B}.Finite :=
  (finite_neg_squarefree_of_classNumber_le B).subset
    fun _ ⟨hneg, hsf, hns, hB⟩ ↦ ⟨hneg, hsf, hns, hB.le⟩

/-- **Finiteness of imaginary quadratic fields of bounded class number up to isomorphism.** For
every `B : ℕ` there exists a finite set `S` consisting precisely of the negative squarefree
integers `d` with `classNumber (QuadraticAlgebra ℚ d 0) ≤ B`, such that every totally complex
quadratic number field `K : Type u` with `classNumber K ≤ B` is `ℚ`-isomorphic to
`QuadraticAlgebra ℚ d 0` for some `d ∈ S`. -/
theorem exists_finset_neg_squarefree_algEquiv_of_classNumber_le (B : ℕ) :
    ∃ S : Finset ℤ,
      (∀ d : ℤ, d ∈ S ↔ d < 0 ∧ Squarefree d ∧
        ∃ (_ : Fact (¬ IsSquare d)), classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) ≤ B) ∧
      ∀ (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K],
        finrank ℚ K = 2 → classNumber K ≤ B →
        ∃ d ∈ S, Nonempty (K ≃ₐ[ℚ] QuadraticAlgebra ℚ (d : ℚ) 0) := by
  classical
  have hfin := finite_neg_squarefree_of_classNumber_le B
  refine ⟨hfin.toFinset, fun d ↦ hfin.mem_toFinset, fun K _ _ _ hK hB ↦ ?_⟩
  obtain ⟨d, ⟨hneg, hsf, ⟨φ⟩⟩, -⟩ := existsUnique_neg_squarefree_algEquiv hK
  have hns : Fact (¬ IsSquare d) := ⟨not_isSquare_of_neg hneg⟩
  have hB' : classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) ≤ B := by
    rw [φ.symm.toRingEquiv.classNumber_eq]
    exact hB
  exact ⟨d, hfin.mem_toFinset.mpr ⟨hneg, hsf, hns, hB'⟩, ⟨φ⟩⟩

/-- **Finiteness of negative fundamental discriminants with bounded class number.** For every
`B : ℕ`, only finitely many negative fundamental discriminants `D` satisfy
`classNumber (QuadraticAlgebra ℚ D 0) ≤ B`. -/
theorem finite_neg_isFundamentalDiscr_of_classNumber_le (B : ℕ) :
    {D : ℤ | D < 0 ∧ Int.IsFundamentalDiscr D ∧
      ∃ (_ : Fact (¬ IsSquare D)), classNumber (QuadraticAlgebra ℚ (D : ℚ) 0) ≤ B}.Finite := by
  obtain ⟨C, hC⟩ := imaginary_discr_bounded_of_classNumber_le.{0} B
  refine (Set.finite_Icc (-(⌈max C 0⌉₊ : ℤ)) 0).subset fun D ⟨hneg, hD, hns, hB⟩ ↦ ?_
  have : Fact (¬ IsSquare D) := hns
  have hdiscr : (-D : ℤ) ≤ |discr (QuadraticAlgebra ℚ (D : ℚ) 0)| := by
    rw [QuadraticAlgebra.discr_eq_iff_isFundamentalDiscr.mpr hD, abs_of_neg hneg]
  have hDM := neg_le_ceil_of_classNumber_le hC hneg hdiscr hB
  exact ⟨by omega, hneg.le⟩

/-- **Finite fibers of the imaginary quadratic class number on fundamental discriminants.** For
every `B : ℕ`, only finitely many negative fundamental discriminants `D` satisfy
`classNumber (QuadraticAlgebra ℚ D 0) = B`. -/
theorem finite_neg_isFundamentalDiscr_of_classNumber_eq (B : ℕ) :
    {D : ℤ | D < 0 ∧ Int.IsFundamentalDiscr D ∧
      ∃ (_ : Fact (¬ IsSquare D)), classNumber (QuadraticAlgebra ℚ (D : ℚ) 0) = B}.Finite :=
  (finite_neg_isFundamentalDiscr_of_classNumber_le B).subset
    fun _ ⟨hneg, hD, hns, hB⟩ ↦ ⟨hneg, hD, hns, hB.le⟩

/-- **Finiteness of negative discriminants of imaginary quadratic fields of bounded class number.**
For every `B : ℕ`, only finitely many negative integers `D` arise as `discr K` for a quadratic
number field `K : Type u` with `classNumber K ≤ B`. -/
theorem finite_neg_discr_of_classNumber_le (B : ℕ) :
    {D : ℤ | D < 0 ∧
      ∃ (K : Type u) (_ : Field K) (_ : NumberField K),
        finrank ℚ K = 2 ∧ discr K = D ∧ classNumber K ≤ B}.Finite := by
  refine (finite_neg_isFundamentalDiscr_of_classNumber_le B).subset
    fun D ⟨hneg, K, _, _, hK, hDK, hB⟩ ↦ ?_
  have hfd : Int.IsFundamentalDiscr D := hDK ▸ isFundamentalDiscr_discr hK
  have hns : Fact (¬ IsSquare (discr K)) := ⟨not_isSquare_discr hK⟩
  obtain ⟨φ⟩ := nonempty_algEquiv_quadraticAlgebra_discr hK
  have heq : classNumber (QuadraticAlgebra ℚ ((discr K : ℤ) : ℚ) 0) = classNumber K :=
    φ.symm.toRingEquiv.classNumber_eq
  subst hDK
  exact ⟨hneg, hfd, hns, heq ▸ hB⟩

/-- **Finite fibers of the imaginary quadratic class number on discriminants.** For every `B : ℕ`,
only finitely many negative integers `D` arise as `discr K` for a quadratic number field
`K : Type u` with `classNumber K = B`. -/
theorem finite_neg_discr_of_classNumber_eq (B : ℕ) :
    {D : ℤ | D < 0 ∧
      ∃ (K : Type u) (_ : Field K) (_ : NumberField K),
        finrank ℚ K = 2 ∧ discr K = D ∧ classNumber K = B}.Finite :=
  (finite_neg_discr_of_classNumber_le.{u} B).subset
    fun _ ⟨hneg, K, hF, hNF, hK, hDK, hB⟩ ↦ ⟨hneg, K, hF, hNF, hK, hDK, hB.le⟩

end TauCeti.NumberField
