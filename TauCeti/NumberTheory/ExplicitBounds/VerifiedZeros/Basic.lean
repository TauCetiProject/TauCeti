/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.CriticalLine
import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Conjugate
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis

/-!
# Bounded-height Riemann hypotheses and verified zero-free strips

Explicit analytic number theory takes finite numerical verifications of the Riemann hypothesis and
of the generalized Riemann hypothesis as named hypotheses rather than axioms. This file defines
those bounded-height propositions and establishes their structural properties and bridges to
certified zero-counting rectangles.

## Main definitions

* `TauCeti.RiemannHypothesisUpTo H`: every zero `ρ` of `riemannZeta` in the open critical strip
  `0 < Re ρ < 1` with `|Im ρ| ≤ H` has `Re ρ = 1 / 2`.
* `TauCeti.DirichletGRHUpTo q H`: for every primitive Dirichlet character `χ` modulo `q`, every
  zero `ρ` of `χ.LFunction` in `0 < Re ρ < 1` with `|Im ρ| ≤ H` has `Re ρ = 1 / 2`.
* `TauCeti.ZetaZeroFreeUpTo H`: `riemannZeta` has no zero `ρ` in `0 < Re ρ < 1` with `|Im ρ| ≤ H`.
* `TauCeti.ZetaFirstOrdinateRecord`: every zero `s` of `riemannZeta` in the upper half-plane
  `0 < Im s` satisfies `14.134725 ≤ Im s`.

## Main results

* Antitonicity (`RiemannHypothesisUpTo.mono`, `DirichletGRHUpTo.mono`, `ZetaZeroFreeUpTo.mono`)
  and one-sided ordinate reductions (`riemannHypothesisUpTo_iff_pos_im`,
  `dirichletGRHUpTo_iff_nonneg_im`).
* Unconditional real-segment nonvanishing (`zetaZeroFreeUpTo_zero`, `riemannHypothesisUpTo_zero`)
  from `TauCeti.riemannZeta_lt_zero`, and empty-primitive-set moduli
  (`dirichletGRHUpTo_of_mod_four_eq_two`, `dirichletGRHUpTo_two`).
* Equivalence at modulus `1` (`dirichletGRHUpTo_one_iff`), passage to imprimitive characters modulo
  `q` via divisors `f ∣ q` (`forall_LFunction_re_eq_half_iff_dirichletGRHUpTo`), and global limits
  as `H → ∞` (`forall_riemannHypothesisUpTo_iff`, `forall_dirichletGRHUpTo_iff`,
  `forall_forall_dirichletGRHUpTo_iff`).
* Equivalence with `TauCeti.LFunctions.AllOnCriticalLine` on `Icc 0 1 ×ℂ Icc (-H) H` for all real
  `H` (`riemannHypothesisUpTo_iff_allOnCriticalLine`, `dirichletGRHUpTo_iff_allOnCriticalLine`),
  together with `HasZerosInRects` certificate bridges
  (`riemannHypothesisUpTo_of_hasZerosInRects_zetaEntireCompletion`,
  `riemannHypothesisUpTo_of_hasZerosInRects_completedRiemannZeta`,
  `dirichletGRHUpTo_of_hasZerosInRects`).

## References

* D. J. Platt, *Numerical computations concerning the GRH*, Math. Comp. 85 (2016), 3009–3027.
* D. J. Platt and T. S. Trudgian, *The Riemann hypothesis is true up to `3·10¹²`*, Bull. Lond.
  Math. Soc. 53 (2021), 792–797.
* H. Kadiri, *Une région explicite sans zéros pour la fonction `ζ` de Riemann*, Acta Arith. 117
  (2005), 303–339.
* A. Chirre and H. A. Helfgott, *Explicit bounds for sums of `μ` and `Λ`*, Appendix B.
-/

public section

open Complex ComplexConjugate Set TauCeti.LFunctions
open scoped ComplexOrder

namespace TauCeti

/-! ### Bounded-height Riemann hypotheses -/

/-- **The Riemann hypothesis up to height `H`.** Every zero `ρ` of `riemannZeta` in the open
critical strip `0 < Re ρ < 1` with `|Im ρ| ≤ H` lies on the critical line `Re ρ = 1 / 2`. -/
def RiemannHypothesisUpTo (H : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ H → ρ.re = 1 / 2

theorem riemannHypothesisUpTo_def (H : ℝ) :
    RiemannHypothesisUpTo H =
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ H → ρ.re = 1 / 2 :=
  (rfl)

/-- Apply `RiemannHypothesisUpTo H` to locate a zero on the critical line. -/
theorem RiemannHypothesisUpTo.re_eq {H : ℝ} (h : RiemannHypothesisUpTo H) {ρ : ℂ}
    (h0 : riemannZeta ρ = 0) (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) (him : |ρ.im| ≤ H) :
    ρ.re = 1 / 2 :=
  h ρ h0 hre0 hre1 him

/-- `RiemannHypothesisUpTo` is antitone in the height bound `H`. -/
theorem RiemannHypothesisUpTo.mono {H H' : ℝ} (h : RiemannHypothesisUpTo H') (hle : H ≤ H') :
    RiemannHypothesisUpTo H :=
  fun ρ h0 hre0 hre1 him ↦ h ρ h0 hre0 hre1 (him.trans hle)

/-- **The generalized Riemann hypothesis modulo `q` up to height `H`.** For every primitive
Dirichlet character `χ` modulo `q`, every zero `ρ` of `χ.LFunction` in the open critical strip
`0 < Re ρ < 1` with `|Im ρ| ≤ H` lies on the critical line `Re ρ = 1 / 2`. -/
def DirichletGRHUpTo (q : ℕ) [NeZero q] (H : ℝ) : Prop :=
  ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
    0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ H → ρ.re = 1 / 2

theorem dirichletGRHUpTo_def (q : ℕ) [NeZero q] (H : ℝ) :
    DirichletGRHUpTo q H =
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
        ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
          0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ H → ρ.re = 1 / 2 :=
  (rfl)

/-- Apply `DirichletGRHUpTo q H` to a primitive character and a zero in the bounded strip. -/
theorem DirichletGRHUpTo.re_eq {q : ℕ} [NeZero q] {H : ℝ} (h : DirichletGRHUpTo q H)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {ρ : ℂ}
    (h0 : χ.LFunction ρ = 0) (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) (him : |ρ.im| ≤ H) :
    ρ.re = 1 / 2 :=
  h χ hχ ρ h0 hre0 hre1 him

/-- `DirichletGRHUpTo q` is antitone in the height bound `H`. -/
theorem DirichletGRHUpTo.mono {q : ℕ} [NeZero q] {H H' : ℝ} (h : DirichletGRHUpTo q H')
    (hle : H ≤ H') : DirichletGRHUpTo q H :=
  fun χ hχ ρ h0 hre0 hre1 him ↦ h χ hχ ρ h0 hre0 hre1 (him.trans hle)

/-- `DirichletGRHUpTo q H` holds vacuously for `H < 0`. -/
theorem dirichletGRHUpTo_of_neg {q : ℕ} [NeZero q] {H : ℝ} (hH : H < 0) :
    DirichletGRHUpTo q H :=
  fun _ _ ρ _ _ _ him ↦ absurd ((abs_nonneg ρ.im).trans him) hH.not_ge

/-! ### Zero-free height bounds and first-ordinate records for `ζ` -/

/-- **Zero-freeness of `riemannZeta` in the open critical strip up to height `H`.** Every zero `ρ`
of `riemannZeta` with `0 < Re ρ < 1` has `H < |Im ρ|`. -/
def ZetaZeroFreeUpTo (H : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → H < |ρ.im|

theorem zetaZeroFreeUpTo_def (H : ℝ) :
    ZetaZeroFreeUpTo H = ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → H < |ρ.im| :=
  (rfl)

/-- Apply `ZetaZeroFreeUpTo H` to lower-bound the ordinate of a zero in the critical strip. -/
theorem ZetaZeroFreeUpTo.lt_abs_im {H : ℝ} (h : ZetaZeroFreeUpTo H) {ρ : ℂ}
    (h0 : riemannZeta ρ = 0) (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) : H < |ρ.im| :=
  h ρ h0 hre0 hre1

/-- `ZetaZeroFreeUpTo` is antitone in the height bound `H`. -/
theorem ZetaZeroFreeUpTo.mono {H H' : ℝ} (h : ZetaZeroFreeUpTo H') (hle : H ≤ H') :
    ZetaZeroFreeUpTo H :=
  fun ρ h0 hre0 hre1 ↦ hle.trans_lt (h ρ h0 hre0 hre1)

/-- Absence of zeros up to height `H` implies `RiemannHypothesisUpTo H`. -/
theorem ZetaZeroFreeUpTo.riemannHypothesisUpTo {H : ℝ} (h : ZetaZeroFreeUpTo H) :
    RiemannHypothesisUpTo H :=
  fun ρ h0 hre0 hre1 him ↦ absurd (h ρ h0 hre0 hre1) him.not_gt

/-- `ZetaZeroFreeUpTo H` holds unconditionally for `H < 0`. -/
theorem zetaZeroFreeUpTo_of_neg {H : ℝ} (hH : H < 0) : ZetaZeroFreeUpTo H :=
  fun ρ _ _ _ ↦ hH.trans_le (abs_nonneg ρ.im)

/-- **Unconditional absence of real zeros of `ζ` in `(0, 1)`.** Because `ζ(σ) < 0` for real
`0 < σ < 1` (`TauCeti.riemannZeta_lt_zero`), every zero of `riemannZeta` in the open critical strip
has strictly nonzero imaginary part. -/
@[simp]
theorem zetaZeroFreeUpTo_zero : ZetaZeroFreeUpTo 0 := by
  intro ρ h0 hre0 hre1
  rw [abs_pos]
  intro him
  have hρ : ρ = (ρ.re : ℂ) := by apply Complex.ext <;> simp [him]
  rw [hρ] at h0
  exact (riemannZeta_lt_zero hre0 hre1).ne h0

/-- `RiemannHypothesisUpTo 0` holds unconditionally because `riemannZeta` has no zeros on the open
real segment `(0, 1)`. -/
@[simp]
theorem riemannHypothesisUpTo_zero : RiemannHypothesisUpTo 0 :=
  zetaZeroFreeUpTo_zero.riemannHypothesisUpTo

/-- `RiemannHypothesisUpTo H` holds unconditionally whenever `H ≤ 0`. -/
theorem riemannHypothesisUpTo_of_nonpos {H : ℝ} (hH : H ≤ 0) : RiemannHypothesisUpTo H :=
  riemannHypothesisUpTo_zero.mono hH

/-- Because `riemannZeta` commutes with complex conjugation and has no real zeros in `(0, 1)`,
every zero `ρ` of `riemannZeta` in the open critical strip has a companion zero (`ρ` or `conj ρ`)
with the same real part in the upper half-plane, of ordinate `|Im ρ|`. -/
theorem exists_riemannZeta_eq_zero_im_eq_abs {ρ : ℂ} (h0 : riemannZeta ρ = 0) (hre0 : 0 < ρ.re)
    (hre1 : ρ.re < 1) :
    ∃ ρ' : ℂ, riemannZeta ρ' = 0 ∧ ρ'.re = ρ.re ∧ 0 < ρ'.im ∧ ρ'.im = |ρ.im| := by
  rcases lt_or_gt_of_ne (abs_pos.mp (zetaZeroFreeUpTo_zero ρ h0 hre0 hre1)) with hneg | hpos
  · exact ⟨conj ρ, by rw [riemannZeta_conj, h0, map_zero], conj_re ρ,
      by simpa using neg_pos.mpr hneg, by rw [conj_im, abs_of_neg hneg]⟩
  · exact ⟨ρ, h0, rfl, hpos, (abs_of_pos hpos).symm⟩

/-- Because `riemannZeta` commutes with complex conjugation and has no real zeros in `(0, 1)`,
`RiemannHypothesisUpTo H` depends only on zeros in the upper half-plane `0 < Im ρ ≤ H`. -/
theorem riemannHypothesisUpTo_iff_pos_im {H : ℝ} :
    RiemannHypothesisUpTo H ↔
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ H → ρ.re = 1 / 2 := by
  refine ⟨fun h ρ h0 hre0 hre1 him0 himH ↦
    h ρ h0 hre0 hre1 ((abs_of_pos him0).trans_le himH), fun h ρ h0 hre0 hre1 him ↦ ?_⟩
  obtain ⟨ρ', h0', hre, hpos, him'⟩ := exists_riemannZeta_eq_zero_im_eq_abs h0 hre0 hre1
  rw [← hre] at hre0 hre1 ⊢
  exact h ρ' h0' hre0 hre1 hpos (him' ▸ him)

/-- **First-ordinate record for `riemannZeta`.** Every zero of `riemannZeta` in the upper
half-plane `0 < Im s` has ordinate at least `14.134725`. -/
def ZetaFirstOrdinateRecord : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.im → 14.134725 ≤ s.im

theorem zetaFirstOrdinateRecord_def :
    ZetaFirstOrdinateRecord = ∀ s : ℂ, riemannZeta s = 0 → 0 < s.im → 14.134725 ≤ s.im :=
  (rfl)

/-- Because all zeros of `riemannZeta` outside `0 < Re s < 1` are real trivial zeros, restricting
`ZetaFirstOrdinateRecord` to the open critical strip gives an equivalent statement. -/
theorem zetaFirstOrdinateRecord_iff_mem_Ioo :
    ZetaFirstOrdinateRecord ↔
      ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ∈ Ioo 0 1 → 0 < ρ.im → 14.134725 ≤ ρ.im := by
  refine ⟨fun h ρ h0 _ him ↦ h ρ h0 him, fun h s h0 him ↦ h s h0 ?_ him⟩
  refine re_mem_Ioo_of_riemannZeta_eq_zero h0 ?_
  rintro ⟨n, rfl⟩
  simp at him

/-- `ZetaFirstOrdinateRecord` implies `ZetaZeroFreeUpTo H` for every `H < 14.134725`. -/
theorem ZetaFirstOrdinateRecord.zetaZeroFreeUpTo (h : ZetaFirstOrdinateRecord) {H : ℝ}
    (hH : H < 14.134725) : ZetaZeroFreeUpTo H := by
  intro ρ h0 hre0 hre1
  obtain ⟨ρ', h0', -, hpos, him⟩ := exists_riemannZeta_eq_zero_im_eq_abs h0 hre0 hre1
  exact hH.trans_le (him ▸ h ρ' h0' hpos)

/-- `ZetaFirstOrdinateRecord` yields the standard low-lying zero-free height `ZetaZeroFreeUpTo 14`.
-/
theorem ZetaFirstOrdinateRecord.zetaZeroFreeUpTo_fourteen (h : ZetaFirstOrdinateRecord) :
    ZetaZeroFreeUpTo 14 :=
  h.zetaZeroFreeUpTo (by norm_num)

/-- `ZetaFirstOrdinateRecord` implies `RiemannHypothesisUpTo H` for every `H < 14.134725`. -/
theorem ZetaFirstOrdinateRecord.riemannHypothesisUpTo (h : ZetaFirstOrdinateRecord) {H : ℝ}
    (hH : H < 14.134725) : RiemannHypothesisUpTo H :=
  (h.zetaZeroFreeUpTo hH).riemannHypothesisUpTo

/-! ### Character symmetries, degenerate moduli, imprimitive lift, and `H → ∞` limits -/

/-- Because `χ` and `χ⁻¹` are simultaneously primitive modulo `q` and conjugation exchanges their
zeros, `DirichletGRHUpTo q H` depends only on zeros with `0 ≤ Im ρ ≤ H`. -/
theorem dirichletGRHUpTo_iff_nonneg_im {q : ℕ} [NeZero q] {H : ℝ} :
    DirichletGRHUpTo q H ↔
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → ∀ ρ : ℂ, χ.LFunction ρ = 0 →
        0 < ρ.re → ρ.re < 1 → 0 ≤ ρ.im → ρ.im ≤ H → ρ.re = 1 / 2 := by
  refine ⟨fun h χ hχ ρ h0 hre0 hre1 him0 himH ↦
    h χ hχ ρ h0 hre0 hre1 ((abs_of_nonneg him0).trans_le himH),
    fun h χ hχ ρ h0 hre0 hre1 him ↦ ?_⟩
  rcases le_or_gt 0 ρ.im with hnonneg | hneg
  · exact h χ hχ ρ h0 hre0 hre1 hnonneg ((le_abs_self ρ.im).trans him)
  · have hinv0 : χ⁻¹.LFunction (conj ρ) = 0 :=
      (DirichletCharacter.LFunction_inv_conj_eq_zero_iff χ ρ).2 h0
    have him' : (conj ρ).im ≤ H := by
      rw [conj_im]
      exact (abs_of_neg hneg ▸ him : -ρ.im ≤ H)
    simpa using h χ⁻¹ hχ.inv (conj ρ) hinv0 (by simpa using hre0) (by simpa using hre1)
      (by simpa using hneg.le) him'

/-- If no primitive Dirichlet character of level `q` exists, `DirichletGRHUpTo q H` holds for every
`H`. -/
theorem dirichletGRHUpTo_of_forall_not_isPrimitive {q : ℕ} [NeZero q]
    (h : ∀ χ : DirichletCharacter ℂ q, ¬χ.IsPrimitive) (H : ℝ) :
    DirichletGRHUpTo q H :=
  fun χ hχ ↦ absurd hχ (h χ)

/-- Twice an odd integer admits no primitive Dirichlet characters, so `DirichletGRHUpTo (2 * m) H`
holds unconditionally for every odd `m` and real `H`. -/
theorem dirichletGRHUpTo_two_mul_of_odd {m : ℕ} (hm : _root_.Odd m) [NeZero (2 * m)] (H : ℝ) :
    DirichletGRHUpTo (2 * m) H :=
  dirichletGRHUpTo_of_forall_not_isPrimitive
    (fun χ ↦ DirichletCharacter.not_isPrimitive_two_mul χ hm) H

/-- For every modulus `q ≡ 2 (mod 4)` and every `H : ℝ`, `DirichletGRHUpTo q H` holds
unconditionally. -/
theorem dirichletGRHUpTo_of_mod_four_eq_two {q : ℕ} [NeZero q] (hq : q % 4 = 2) (H : ℝ) :
    DirichletGRHUpTo q H := by
  have hm : _root_.Odd (q / 2) := Nat.odd_iff.mpr (by omega)
  have h2m : 2 * (q / 2) = q := by omega
  generalize hk : q / 2 = k at hm h2m
  subst h2m
  exact dirichletGRHUpTo_two_mul_of_odd hm H

/-- Modulo `2` there are no primitive characters, so `DirichletGRHUpTo 2 H` holds unconditionally.
-/
@[simp]
theorem dirichletGRHUpTo_two (H : ℝ) : DirichletGRHUpTo 2 H :=
  dirichletGRHUpTo_of_mod_four_eq_two rfl H

/-- At modulus `1`, `DirichletGRHUpTo 1 H` is equivalent to `RiemannHypothesisUpTo H`. -/
@[simp]
theorem dirichletGRHUpTo_one_iff {H : ℝ} :
    DirichletGRHUpTo 1 H ↔ RiemannHypothesisUpTo H := by
  refine ⟨fun h ρ h0 hre0 hre1 him ↦
    h 1 DirichletCharacter.isPrimitive_one_level_one ρ
      (by rwa [DirichletCharacter.LFunction_modOne_eq]) hre0 hre1 him,
    fun h χ _ ρ h0 hre0 hre1 him ↦ ?_⟩
  rw [DirichletCharacter.LFunction_modOne_eq] at h0
  exact h ρ h0 hre0 hre1 him

/-- `RiemannHypothesisUpTo H` holds for all `H : ℝ` if and only if `RiemannHypothesis` holds. -/
theorem forall_riemannHypothesisUpTo_iff :
    (∀ H : ℝ, RiemannHypothesisUpTo H) ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_mem_Ioo]
  exact ⟨fun h ρ h0 hre ↦ h |ρ.im| ρ h0 hre.1 hre.2 le_rfl,
    fun h _ ρ h0 hre0 hre1 _ ↦ h ρ h0 ⟨hre0, hre1⟩⟩

/-- `DirichletGRHUpTo q H` holds for all `H : ℝ` if and only if `DirichletGRH χ` holds for every
primitive character `χ` modulo `q`. -/
theorem forall_dirichletGRHUpTo_iff {q : ℕ} [NeZero q] :
    (∀ H : ℝ, DirichletGRHUpTo q H) ↔
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → DirichletGRH χ := by
  simp_rw [DirichletCharacter.dirichletGRH_iff_mem_Ioo]
  exact ⟨fun h χ hχ ρ h0 hre ↦ h |ρ.im| χ hχ ρ h0 hre.1 hre.2 le_rfl,
    fun h _ χ hχ ρ h0 hre0 hre1 _ ↦ h χ hχ ρ h0 ⟨hre0, hre1⟩⟩

/-- `DirichletGRHUpTo q H` holds for all positive moduli `q` and heights `H` if and only if `GRH`
holds. -/
theorem forall_forall_dirichletGRHUpTo_iff :
    (∀ (q : ℕ) [NeZero q] (H : ℝ), DirichletGRHUpTo q H) ↔ GRH := by
  rw [grh_iff_isPrimitive]
  exact forall_congr' fun q ↦ forall_congr' fun _ ↦ forall_dirichletGRHUpTo_iff

/-- **Passage to imprimitive characters.** Every Dirichlet character modulo `q` (primitive or not)
has all its zeros in `0 < Re ρ < 1` with `|Im ρ| ≤ H` on `Re ρ = 1 / 2` if and only if
`DirichletGRHUpTo f H` holds for every divisor `f` of `q`. -/
theorem forall_LFunction_re_eq_half_iff_dirichletGRHUpTo {q : ℕ} [NeZero q] {H : ℝ} :
    (∀ χ : DirichletCharacter ℂ q, ∀ ρ : ℂ, χ.LFunction ρ = 0 →
      0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ H → ρ.re = 1 / 2) ↔
    ∀ (f : ℕ) [NeZero f], f ∣ q → DirichletGRHUpTo f H := by
  have hne_one {ρ : ℂ} (hre1 : ρ.re < 1) : ρ ≠ 1 := fun h1 ↦ by simp [h1] at hre1
  refine ⟨fun h f _ hfq ψ _ ρ h0 hre0 hre1 him ↦ ?_, fun h χ ρ h0 hre0 hre1 him ↦ ?_⟩
  · exact h (DirichletCharacter.changeLevel hfq ψ) ρ
      ((DirichletCharacter.LFunction_changeLevel_eq_zero_iff ψ hfq hre0 (.inr (hne_one hre1))).2
        h0) hre0 hre1 him
  · exact h χ.conductor χ.conductor_dvd_level χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
      ρ ((χ.LFunction_primitiveCharacter_eq_zero_iff hre0 (.inr (hne_one hre1))).2 h0) hre0 hre1 him

/-- At modulus `2`, all zeros of all characters modulo `2` in `0 < Re ρ < 1` with `|Im ρ| ≤ H` lie
on the critical line if and only if `RiemannHypothesisUpTo H` holds, since the extra Euler factor
`1 - 2 ^ (-s)` vanishes only on `Re s = 0`. -/
theorem forall_LFunction_modTwo_re_eq_half_iff {H : ℝ} :
    (∀ χ : DirichletCharacter ℂ 2, ∀ ρ : ℂ, χ.LFunction ρ = 0 →
      0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ H → ρ.re = 1 / 2) ↔
    RiemannHypothesisUpTo H := by
  rw [forall_LFunction_re_eq_half_iff_dirichletGRHUpTo]
  refine ⟨fun h ↦ dirichletGRHUpTo_one_iff.mp (h 1 (one_dvd 2)), fun h f _ hf ↦ ?_⟩
  have hle : f ≤ 2 := Nat.le_of_dvd (by decide) hf
  have hpos : 0 < f := NeZero.pos f
  interval_cases f
  · exact dirichletGRHUpTo_one_iff.mpr h
  · exact dirichletGRHUpTo_two H

/-! ### Agreement with `AllOnCriticalLine` and `HasZerosInRects` certificates -/

/-- For every `H : ℝ`, `RiemannHypothesisUpTo H` is equivalent to `AllOnCriticalLine` for
`completedRiemannZeta` on the closed critical-strip box `Icc 0 1 ×ℂ Icc (-H) H`. -/
theorem riemannHypothesisUpTo_iff_allOnCriticalLine {H : ℝ} :
    RiemannHypothesisUpTo H ↔
      AllOnCriticalLine completedRiemannZeta univ (Icc 0 1 ×ℂ Icc (-H) H) :=
  (allOnCriticalLine_Icc_reProdIm_Icc_iff
    fun _ ↦ zero_lt_divisor_completedRiemannZeta_iff_mem_Ioo).symm

/-- For every `H : ℝ`, `RiemannHypothesisUpTo H` is equivalent to `AllOnCriticalLine` for
`zetaEntireCompletion` on `Icc 0 1 ×ℂ Icc (-H) H`. -/
theorem riemannHypothesisUpTo_iff_allOnCriticalLine_zetaEntireCompletion {H : ℝ} :
    RiemannHypothesisUpTo H ↔
      AllOnCriticalLine zetaEntireCompletion univ (Icc 0 1 ×ℂ Icc (-H) H) := by
  rw [riemannHypothesisUpTo_iff_allOnCriticalLine]
  simp only [allOnCriticalLine_iff, zero_lt_divisor_zetaEntireCompletion_iff]

/-- For every `H : ℝ`, `DirichletGRHUpTo q H` is equivalent to `AllOnCriticalLine` for
`χ.completedLFunction` on `Icc 0 1 ×ℂ Icc (-H) H` for every primitive character `χ` modulo `q`. -/
theorem dirichletGRHUpTo_iff_allOnCriticalLine {q : ℕ} [NeZero q] {H : ℝ} :
    DirichletGRHUpTo q H ↔
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
        AllOnCriticalLine χ.completedLFunction univ (Icc 0 1 ×ℂ Icc (-H) H) :=
  forall_congr' fun _ ↦ imp_congr_right fun hχ ↦
    (allOnCriticalLine_Icc_reProdIm_Icc_iff fun _ ↦ hχ.zero_lt_divisor_completedLFunction_iff).symm

/-- For every `H : ℝ`, `DirichletGRHUpTo q H` is equivalent to `AllOnCriticalLine` for
`(dirichletData χ hχ).entireCompletion` on `Icc 0 1 ×ℂ Icc (-H) H` for every primitive character `χ`
modulo `q`. -/
theorem dirichletGRHUpTo_iff_allOnCriticalLine_entireCompletion {q : ℕ} [NeZero q] {H : ℝ} :
    DirichletGRHUpTo q H ↔
      ∀ (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        AllOnCriticalLine (dirichletData χ hχ).entireCompletion univ (Icc 0 1 ×ℂ Icc (-H) H) := by
  rw [dirichletGRHUpTo_iff_allOnCriticalLine]
  refine forall_congr' fun χ ↦ forall_congr' fun hχ ↦ ?_
  simp only [allOnCriticalLine_iff, zero_lt_divisor_dirichletData_entireCompletion_iff χ hχ,
    hχ.zero_lt_divisor_completedLFunction_iff]

/-- **Certificate bridge for `zetaEntireCompletion`.** A `HasZerosInRects` certificate of
`zetaEntireCompletion` on a rectangle covering `Ioo 0 1 ×ℂ Ioc 0 H` whose subrectangles satisfy
`AllOnCriticalLine` implies `RiemannHypothesisUpTo H`. Conjugation and real-segment nonvanishing
supply `-H ≤ Im ρ ≤ 0`. -/
theorem riemannHypothesisUpTo_of_hasZerosInRects_zetaEntireCompletion {H : ℝ} {z w : ℂ}
    {Bs : List (ℂ × ℂ)} {ms : List ℕ}
    (hcert : HasZerosInRects zetaEntireCompletion univ z w Bs ms)
    (hsub : Ioo 0 1 ×ℂ Ioc 0 H ⊆ Rectangle z w)
    (hBs : ∀ B ∈ Bs, AllOnCriticalLine zetaEntireCompletion univ (Rectangle B.1 B.2)) :
    RiemannHypothesisUpTo H := by
  rw [riemannHypothesisUpTo_iff_pos_im]
  intro ρ h0 hre0 hre1 him0 himH
  have hpos : 0 < MeromorphicOn.divisor zetaEntireCompletion univ ρ :=
    zero_lt_divisor_zetaEntireCompletion_iff.2
      (zero_lt_divisor_completedRiemannZeta_iff_mem_Ioo.2 ⟨h0, hre0, hre1⟩)
  exact allOnCriticalLine_iff.mp (hcert.allOnCriticalLine hBs) ρ
    (hsub ⟨⟨hre0, hre1⟩, ⟨him0, himH⟩⟩) hpos

/-- **Upper-strip certificate bridge for `completedRiemannZeta`.** Combining
`RiemannHypothesisUpTo H₀` (for example from `ZetaZeroFreeUpTo H₀` with `0 < H₀`, avoiding the
poles `0` and `1` on the real axis) with a `HasZerosInRects` certificate of
`completedRiemannZeta` covering `Ioo 0 1 ×ℂ Ioc H₀ H` yields `RiemannHypothesisUpTo H`. -/
theorem riemannHypothesisUpTo_of_hasZerosInRects_completedRiemannZeta {H₀ H : ℝ} {z w : ℂ}
    {Bs : List (ℂ × ℂ)} {ms : List ℕ}
    (h₀ : RiemannHypothesisUpTo H₀)
    (hcert : HasZerosInRects completedRiemannZeta univ z w Bs ms)
    (hsub : Ioo 0 1 ×ℂ Ioc H₀ H ⊆ Rectangle z w)
    (hBs : ∀ B ∈ Bs, AllOnCriticalLine completedRiemannZeta univ (Rectangle B.1 B.2)) :
    RiemannHypothesisUpTo H := by
  rw [riemannHypothesisUpTo_iff_pos_im]
  intro ρ h0 hre0 hre1 him0 himH
  rcases le_or_gt ρ.im H₀ with hle | hgt
  · exact h₀ ρ h0 hre0 hre1 ((abs_of_pos him0).trans_le hle)
  · have hpos : 0 < MeromorphicOn.divisor completedRiemannZeta univ ρ :=
      zero_lt_divisor_completedRiemannZeta_iff_mem_Ioo.2 ⟨h0, hre0, hre1⟩
    exact allOnCriticalLine_iff.mp (hcert.allOnCriticalLine hBs) ρ
      (hsub ⟨⟨hre0, hre1⟩, ⟨hgt, himH⟩⟩) hpos

/-- **Certificate bridge for `DirichletGRHUpTo`.** If every primitive character `χ` modulo `q` has
a `HasZerosInRects` certificate of `χ.completedLFunction` covering `Ioo 0 1 ×ℂ Icc 0 H` whose
subrectangles satisfy `AllOnCriticalLine`, then `DirichletGRHUpTo q H` holds. Conjugation against
`χ⁻¹` covers `-H ≤ Im ρ < 0`. -/
theorem dirichletGRHUpTo_of_hasZerosInRects {q : ℕ} [NeZero q] {H : ℝ}
    (hcert : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ∃ (z w : ℂ) (Bs : List (ℂ × ℂ)) (ms : List ℕ),
        HasZerosInRects χ.completedLFunction univ z w Bs ms ∧
        Ioo 0 1 ×ℂ Icc 0 H ⊆ Rectangle z w ∧
        ∀ B ∈ Bs, AllOnCriticalLine χ.completedLFunction univ (Rectangle B.1 B.2)) :
    DirichletGRHUpTo q H := by
  rw [dirichletGRHUpTo_iff_nonneg_im]
  intro χ hχ ρ h0 hre0 hre1 him0 himH
  obtain ⟨z, w, Bs, ms, hc, hsub, hBs⟩ := hcert χ hχ
  have hpos : 0 < MeromorphicOn.divisor χ.completedLFunction univ ρ :=
    hχ.zero_lt_divisor_completedLFunction_iff.2 ⟨h0, hre0, hre1⟩
  exact allOnCriticalLine_iff.mp (hc.allOnCriticalLine hBs) ρ
    (hsub ⟨⟨hre0, hre1⟩, ⟨him0, himH⟩⟩) hpos

end TauCeti
