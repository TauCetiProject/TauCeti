/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import TauCeti.NumberTheory.NumberField.QuadraticAlgebra
import TauCeti.NumberTheory.LSeries.Quadratic.Siegel
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Character
import TauCeti.NumberTheory.NumberField.ClassNumber.RingEquiv
import TauCeti.NumberTheory.NumberField.Quadratic.DedekindZeta
import TauCeti.NumberTheory.NumberField.Quadratic.Model
import TauCeti.NumberTheory.NumberField.Quadratic.Radicand

/-!
# Siegel's class-number lower bound and finiteness for imaginary quadratic fields

Combining Siegel's theorem `DirichletCharacter.quadratic_LFunction_siegel` for quadratic Dirichlet
characters with the analytic class-number lower bound
`h(L) ≥ √|discr L| · Re L(1, χ_{discr L}) / π`
(`TauCeti.NumberField.sqrt_mul_LFunction_one_re_div_le_classNumber`), every `ε > 0` admits a
positive constant `c` such that every imaginary quadratic field `L` satisfies

`c * |discr L| ^ (1 / 2 - ε) ≤ classNumber L`.

Specializing to `ε = 1 / 4` bounds `|discr L|` uniformly in terms of any upper bound `B` on
`classNumber L`. Consequently:

* `classNumber L → ∞` uniformly as `|discr L| → ∞` across imaginary quadratic fields;
* for every `B`, only finitely many negative fundamental discriminants `D` and only finitely many
  negative squarefree radicands `d` yield imaginary quadratic fields `ℚ(√D)` or `ℚ(√d)` of class
  number at most `B` (and hence of exact class number `B`);
* up to `ℚ`-algebra isomorphism, imaginary quadratic fields of class number at most `B` are
  classified by a single finite set of negative squarefree models `ℚ(√d)`.

Because Siegel's constant is ineffective, the discriminant and finiteness bounds here are
ineffective; determining the exact list for `B = 1` requires separate effective methods.

## Main results

* `TauCeti.NumberField.imaginary_classNumber_lower_bound`: `c * |discr L| ^ (1 / 2 - ε) ≤ h(L)`
  uniformly across imaginary quadratic fields `L`.
* `TauCeti.NumberField.imaginary_discr_bounded_of_classNumber_le` and
  `TauCeti.NumberField.imaginary_natAbs_discr_bounded_of_classNumber_le`: uniform upper bounds on
  `|discr L|` from `classNumber L ≤ B`.
* `TauCeti.NumberField.lt_imaginary_classNumber_of_natAbs_discr_gt`: uniform divergence of the
  imaginary quadratic class number with `|discr L|`.
* `TauCeti.NumberField.finite_isFundamentalDiscr_neg_classNumber_le`: finiteness of negative
  fundamental discriminants `D` with `classNumber ℚ(√D) ≤ B`.
* `TauCeti.NumberField.finite_squarefree_neg_classNumber_le` and
  `TauCeti.NumberField.finite_squarefree_neg_classNumber_eq`: finiteness of negative squarefree `d`
  with `classNumber ℚ(√d) ≤ B` (respectively `= B`).
* `TauCeti.NumberField.exists_finset_neg_squarefree_classNumber_le_iff`: finite `ℚ`-algebra
  isomorphism classification of imaginary quadratic fields with `classNumber L ≤ B`.

## References

* C. L. Siegel, *Über die Classenzahl quadratischer Zahlkörper*, Acta Arith. 1 (1935), 83–86.
* H. Davenport, *Multiplicative Number Theory*, Chapter 21.
-/

public section

open NumberField TauCeti.Multiquadratic

namespace TauCeti.NumberField

universe u

/-- **Siegel's class-number lower bound for imaginary quadratic fields.** For every `ε > 0`, there
is an (ineffective) constant `c > 0` such that `c * |discr L| ^ (1 / 2 - ε) ≤ classNumber L` for
every imaginary quadratic number field `L`. -/
theorem imaginary_classNumber_lower_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (L : Type u) [Field L] [NumberField L]
      [NumberField.IsTotallyComplex L], Module.finrank ℚ L = 2 →
      c * (|NumberField.discr L| : ℝ) ^ (1 / 2 - ε) ≤
        (NumberField.classNumber L : ℝ) := by
  obtain ⟨C, hC, hsiegel⟩ := DirichletCharacter.quadratic_LFunction_siegel hε
  refine ⟨C / Real.pi, div_pos hC Real.pi_pos, fun L _ _ _ hL ↦ ?_⟩
  set hD : Int.IsFundamentalDiscr (NumberField.discr L) := isFundamentalDiscr_discr hL
  set χ : DirichletCharacter ℂ (NumberField.discr L).natAbs :=
    (fundamentalDiscriminantChar (NumberField.discr L) hD).ringHomComp (Int.castRingHom ℂ)
  have hquad : χ.IsQuadratic :=
    (fundamentalDiscriminantChar_isQuadratic hD).comp (Int.castRingHom ℂ)
  have hL1 := hsiegel (NumberField.discr L).natAbs χ hquad
    (ringHomComp_fundamentalDiscriminantChar_discr_ne_one hL)
  have habs_eq : ((NumberField.discr L).natAbs : ℝ) = (|NumberField.discr L| : ℝ) := by
    rw [Nat.cast_natAbs, ← Int.cast_abs]
  rw [habs_eq] at hL1
  have hDpos : 0 < (|NumberField.discr L| : ℝ) := by
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero L)
  have hsqrt : √|(NumberField.discr L : ℝ)| = (|NumberField.discr L| : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Int.cast_abs, Real.sqrt_eq_rpow]
  have hcnf : √|(NumberField.discr L : ℝ)| * (χ.LFunction 1).re / Real.pi ≤
      (NumberField.classNumber L : ℝ) :=
    sqrt_mul_LFunction_one_re_div_le_classNumber hL
  calc C / Real.pi * (|NumberField.discr L| : ℝ) ^ ((1 : ℝ) / 2 - ε)
      = (|NumberField.discr L| : ℝ) ^ ((1 : ℝ) / 2) *
          (C * (|NumberField.discr L| : ℝ) ^ (-ε)) / Real.pi := by
        rw [sub_eq_add_neg, Real.rpow_add hDpos]; ring
    _ ≤ √|(NumberField.discr L : ℝ)| * (χ.LFunction 1).re / Real.pi := by
        rw [hsqrt]; gcongr
    _ ≤ (NumberField.classNumber L : ℝ) := hcnf

/-- **Bounded class number implies bounded discriminant.** For every bound `B`, there is a constant
`C` such that every imaginary quadratic field `L` with `classNumber L ≤ B` satisfies
`|discr L| ≤ C`. -/
theorem imaginary_discr_bounded_of_classNumber_le (B : ℕ) :
    ∃ C : ℝ, ∀ (L : Type u) [Field L] [NumberField L]
      [NumberField.IsTotallyComplex L], Module.finrank ℚ L = 2 →
      NumberField.classNumber L ≤ B → (|NumberField.discr L| : ℝ) ≤ C := by
  obtain ⟨c, hc, hlow⟩ := imaginary_classNumber_lower_bound.{u} (ε := 1 / 4) (by norm_num)
  refine ⟨((B : ℝ) / c) ^ (4 : ℝ), fun L _ _ _ hL hB ↦ ?_⟩
  have hD0 : 0 < (|NumberField.discr L| : ℝ) := by
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero L)
  have hqtr : (1 : ℝ) / 2 - 1 / 4 = 1 / 4 := by norm_num
  have h1 : c * (|NumberField.discr L| : ℝ) ^ ((1 : ℝ) / 4) ≤ B := by
    have hlowL := hlow L hL
    rw [hqtr] at hlowL
    exact hlowL.trans (by exact_mod_cast hB)
  have h2 : (|NumberField.discr L| : ℝ) ^ ((1 : ℝ) / 4) ≤ (B : ℝ) / c :=
    (le_div_iff₀ hc).mpr (by linarith)
  calc (|NumberField.discr L| : ℝ)
      = ((|NumberField.discr L| : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℝ) := by
        rw [← Real.rpow_mul hD0.le]; norm_num
    _ ≤ ((B : ℝ) / c) ^ (4 : ℝ) := Real.rpow_le_rpow (by positivity) h2 (by norm_num)

/-- Natural-number discriminant bound for imaginary quadratic fields of class number at most `B`. -/
theorem imaginary_natAbs_discr_bounded_of_classNumber_le (B : ℕ) :
    ∃ D₀ : ℕ, ∀ (L : Type u) [Field L] [NumberField L]
      [NumberField.IsTotallyComplex L], Module.finrank ℚ L = 2 →
      NumberField.classNumber L ≤ B → (NumberField.discr L).natAbs ≤ D₀ := by
  obtain ⟨C, hC⟩ := imaginary_discr_bounded_of_classNumber_le.{u} B
  refine ⟨⌊max C 0⌋₊, fun L _ _ _ hL hB ↦ Nat.le_floor ?_⟩
  rw [Nat.cast_natAbs, Int.cast_abs]
  exact (hC L hL hB).trans (le_max_left C 0)

/-- **Uniform divergence of the imaginary quadratic class number.** For every `B`, all imaginary
quadratic fields of sufficiently large discriminant satisfy `B < classNumber L`. -/
theorem lt_imaginary_classNumber_of_natAbs_discr_gt (B : ℕ) :
    ∃ D₀ : ℕ, ∀ (L : Type u) [Field L] [NumberField L]
      [NumberField.IsTotallyComplex L], Module.finrank ℚ L = 2 →
      D₀ < (NumberField.discr L).natAbs → B < NumberField.classNumber L := by
  obtain ⟨D₀, hD₀⟩ := imaginary_natAbs_discr_bounded_of_classNumber_le.{u} B
  exact ⟨D₀, fun L _ _ _ hL hgt ↦ lt_of_not_ge fun hle ↦ hgt.not_ge (hD₀ L hL hle)⟩

/-- **Finiteness of negative fundamental discriminants with bounded class number.** For every `B`,
only finitely many negative fundamental discriminants `D` satisfy `classNumber ℚ(√D) ≤ B`. -/
theorem finite_isFundamentalDiscr_neg_classNumber_le (B : ℕ) :
    {D : ℤ | D < 0 ∧ Int.IsFundamentalDiscr D ∧
      ∀ [Fact (¬ IsSquare D)],
        NumberField.classNumber (QuadraticAlgebra ℚ (D : ℚ) 0) ≤ B}.Finite := by
  obtain ⟨D₀, hD₀⟩ := imaginary_natAbs_discr_bounded_of_classNumber_le.{0} B
  refine (Set.finite_Icc (-(D₀ : ℤ)) 0).subset fun D ⟨hneg, hfund, hB⟩ ↦ ?_
  have : Fact (¬ IsSquare D) := ⟨not_isSquare_of_neg hneg⟩
  have hnegQ : (D : ℚ) < 0 := by exact_mod_cast hneg
  have : IsTotallyComplex (QuadraticAlgebra ℚ (D : ℚ) 0) :=
    QuadraticAlgebra.isTotallyComplex_iff.mpr hnegQ
  have hle := hD₀ (QuadraticAlgebra ℚ (D : ℚ) 0) (QuadraticAlgebra.finrank_eq_two _ _) hB
  rw [QuadraticAlgebra.discr_eq_of_isFundamentalDiscr hfund] at hle
  exact ⟨by omega, hneg.le⟩

private lemma neg_natAbs_discr_le_of_squarefree {d : ℤ} [Fact (¬ IsSquare d)]
    (hneg : d < 0) (hsf : Squarefree d) :
    -((NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0)).natAbs : ℤ) ≤ d := by
  by_cases hd4 : d % 4 = 1
  · rw [QuadraticAlgebra.discr_eq_of_mod_four_eq_one hsf hd4]
    omega
  · rw [QuadraticAlgebra.discr_eq_four_mul_of_mod_four_ne_one hsf hd4]
    omega

/-- **Finiteness of negative squarefree radicands with bounded class number.** For every `B`, only
finitely many negative squarefree integers `d` satisfy `classNumber ℚ(√d) ≤ B`. -/
theorem finite_squarefree_neg_classNumber_le (B : ℕ) :
    {d : ℤ | d < 0 ∧ Squarefree d ∧
      ∀ [Fact (¬ IsSquare d)],
        NumberField.classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) ≤ B}.Finite := by
  obtain ⟨D₀, hD₀⟩ := imaginary_natAbs_discr_bounded_of_classNumber_le.{0} B
  refine (Set.finite_Icc (-(D₀ : ℤ)) 0).subset fun d ⟨hneg, hsf, hB⟩ ↦ ?_
  have : Fact (¬ IsSquare d) := ⟨not_isSquare_of_neg hneg⟩
  have hnegQ : (d : ℚ) < 0 := by exact_mod_cast hneg
  have : IsTotallyComplex (QuadraticAlgebra ℚ (d : ℚ) 0) :=
    QuadraticAlgebra.isTotallyComplex_iff.mpr hnegQ
  have hle := hD₀ (QuadraticAlgebra ℚ (d : ℚ) 0) (QuadraticAlgebra.finrank_eq_two _ _) hB
  have hdiscr := neg_natAbs_discr_le_of_squarefree hneg hsf
  exact ⟨by omega, hneg.le⟩

/-- **Finiteness of imaginary quadratic radicands of a prescribed class number.** For every `B`,
only finitely many negative squarefree integers `d` satisfy `classNumber ℚ(√d) = B`. -/
theorem finite_squarefree_neg_classNumber_eq (B : ℕ) :
    {d : ℤ | d < 0 ∧ Squarefree d ∧
      ∀ [Fact (¬ IsSquare d)],
        NumberField.classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) = B}.Finite :=
  (finite_squarefree_neg_classNumber_le B).subset fun _ ⟨hneg, hsf, hB⟩ ↦ ⟨hneg, hsf, hB.le⟩

/-- **Finite isomorphism classification of imaginary quadratic fields with bounded class number.**
For every `B`, there is a finite set `S` of negative squarefree integers such that an imaginary
quadratic field `L` has `classNumber L ≤ B` if and only if it is `ℚ`-algebra isomorphic to
`QuadraticAlgebra ℚ d 0` for a (necessarily unique) `d ∈ S`. -/
theorem exists_finset_neg_squarefree_classNumber_le_iff (B : ℕ) :
    ∃ S : Finset ℤ, (∀ d ∈ S, d < 0 ∧ Squarefree d) ∧
      ∀ (L : Type u) [Field L] [NumberField L] [NumberField.IsTotallyComplex L],
        Module.finrank ℚ L = 2 →
        (NumberField.classNumber L ≤ B ↔
          ∃! d : ℤ, d ∈ S ∧ Nonempty (L ≃ₐ[ℚ] QuadraticAlgebra ℚ (d : ℚ) 0)) := by
  classical
  have hfin := finite_squarefree_neg_classNumber_le B
  refine ⟨hfin.toFinset, fun d hd ↦ ?_, fun L _ _ _ hL ↦ ?_⟩
  · obtain ⟨hneg, hsf, -⟩ := hfin.mem_toFinset.mp hd
    exact ⟨hneg, hsf⟩
  · constructor
    · intro hB
      obtain ⟨d, ⟨hd_neg, hd_sf, ⟨φ⟩⟩, hd_uniq⟩ := existsUnique_neg_squarefree_algEquiv hL
      have hmem : d ∈ hfin.toFinset := hfin.mem_toFinset.mpr
        ⟨hd_neg, hd_sf, fun {_} ↦ (RingEquiv.classNumber_eq φ.toRingEquiv).symm.trans_le hB⟩
      refine ⟨d, ⟨hmem, ⟨φ⟩⟩, fun d' ⟨hmem', ⟨ψ'⟩⟩ ↦ ?_⟩
      obtain ⟨hd'_neg, hd'_sf, -⟩ := hfin.mem_toFinset.mp hmem'
      exact hd_uniq d' ⟨hd'_neg, hd'_sf, ⟨ψ'⟩⟩
    · rintro ⟨d, ⟨hmem, ⟨ψ⟩⟩, -⟩
      obtain ⟨hd_neg, -, hBd⟩ := hfin.mem_toFinset.mp hmem
      have : Fact (¬ IsSquare d) := ⟨not_isSquare_of_neg hd_neg⟩
      exact (RingEquiv.classNumber_eq ψ.toRingEquiv).trans_le hBd

end TauCeti.NumberField
