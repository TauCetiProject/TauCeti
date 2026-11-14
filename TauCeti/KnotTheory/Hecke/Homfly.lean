/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo.Trace
public import TauCeti.KnotTheory.Hecke
public import TauCeti.KnotTheory.Homfly.Reduced

import Mathlib.Tactic.LinearCombination

/-!
# Regularity of the Ocneanu braid invariant and comparison with Jimbo and HOMFLY

For a Markov trace `τ` with parameter `z`, the normalized braid trace
`TauCeti.MarkovBraid.heckeTrace β τ C l` requires `C * l * z = 1` and
`C * l⁻¹ * (z - (q - q⁻¹)) = 1` for Markov invariance, which forces the unlink factor `C` to be a
unit. Specializations with zero or non-unit unlink factor—such as the Conway–Alexander
specialization `l = ±1` (`C = 0`) or roots of unity where a quantum dimension `[N]_q` vanishes—do
not admit such a parameter `z`.

Using the two-parameter homogenized Ocneanu trace
`TauCeti.InfiniteTypeAHeckeAlgebra.homogenizedOcneanuTrace`, we define
`TauCeti.MarkovBraid.regularHeckeTrace β q C l` directly from `(q, C, l)` with no division by `C`.
Positive stabilization holds unconditionally (`l * l⁻¹ = 1`), and negative stabilization requires
only the polynomial relation `C * (q - q⁻¹) = l⁻¹ - l`, which remains regular at `C = 0`. Whenever
`C * z = l⁻¹` (in particular whenever `C * l * z = 1`), `regularHeckeTrace` agrees with
`heckeTrace (ocneanuTrace R q z) C l` (`regularHeckeTrace_eq_heckeTrace_of_mul_eq`).

We verify the two-strand unlink and both single-crossing closures (`σ₀` and `σ₀⁻¹`) for both
`heckeTrace` and `regularHeckeTrace`, and then establish the native comparisons:

* **Jimbo weighted and reduced traces:** over every commutative ring `R`, for all `N : ℕ` and
  `q : Rˣ`, `β.jimboTrace q` equals `δ_N * β.regularHeckeTrace q δ_N ((q ^ N)⁻¹)` with no
  invertibility hypotheses (`jimboTrace_eq_mul_regularHeckeTrace`), and over a field with
  `δ_N ≠ 0`, `β.jimboReducedTrace q` equals both `regularHeckeTrace` and the Ocneanu `heckeTrace`
  at `z = q ^ N / δ_N` (`jimboReducedTrace_eq_heckeTrace`).
* **Two-variable HOMFLY polynomial:** for any homomorphism `f : K →+* R` from a field `K` to a
  commutative ring `R` and any units `q u l : Rˣ` with `u = q - q⁻¹`, evaluating `β.reducedHomfly K`
  at `z = u` and `a = l⁻¹` gives `β.regularHeckeTrace q ((l⁻¹ - l) * u⁻¹) l`—including across the
  zero-factor locus `l = ±1` (`eval₂_reducedHomfly_eq_regularHeckeTrace`)—and coincides with the
  Ocneanu `heckeTrace` whenever `(l⁻¹ - l) * u⁻¹ * z = l⁻¹` (`eval₂_reducedHomfly_eq_heckeTrace`).

## Main definitions

* `TauCeti.MarkovBraid.regularHeckeTrace`: the homogenized Ocneanu braid-closure trace, regular at
  zero or non-unit unlink factors `C`.
* `TauCeti.regularHeckeBraidInvariant`: its descent to `Quot MarkovEquiv` when
  `C * (q - q⁻¹) = l⁻¹ - l`.

## Main results

* `TauCeti.MarkovBraid.heckeTrace_two_strand_one`,
  `TauCeti.MarkovBraid.heckeTrace_sigma_two`, and
  `TauCeti.MarkovBraid.heckeTrace_sigma_two_inv`: explicit values on the two-strand unlink and both
  one-crossing closures.
* `TauCeti.MarkovBraid.regularHeckeTrace_eq_heckeTrace`: agreement of `regularHeckeTrace` with the
  Ocneanu `heckeTrace` when `C * l * z = 1`.
* `TauCeti.MarkovBraid.eq_regularHeckeTrace_of_skein`: skein characterization valid for arbitrary
  `C : R` (including `C = 0`).
* `TauCeti.MarkovBraid.jimboTrace_eq_mul_regularHeckeTrace` and
  `TauCeti.MarkovBraid.jimboReducedTrace_eq_heckeTrace`: comparison with the `N`-colour Jimbo braid
  invariants.
* `TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_regularHeckeTrace`,
  `TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_heckeTrace`, and
  `TauCeti.MarkovBraid.eval₂_homfly_eq_mul_heckeTrace`: comparison with `reducedHomfly` and
  `homfly`.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 5–6.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553.
-/

public section

open LaurentPolynomial
open scoped BigOperators

namespace TauCeti

open BraidGroup InfiniteTypeAHeckeAlgebra KnotTheory

section TwoStrandChecks

variable {R : Type*} [CommRing R] {q : Rˣ} {z : R}
  {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}

namespace MarkovBraid

/-- The two-strand unlink closure `⟨1, 1⟩` has normalized Hecke trace `C`. -/
theorem heckeTrace_two_strand_one (h₁ : τ 1 = 1) (C : R) (l : Rˣ) :
    heckeTrace ⟨1, 1⟩ τ C l = C := by
  simpa using heckeTrace_one (n := 1) h₁ C l

/-- Before imposing `C * l * z = 1`, the single positive crossing on two strands has normalized
Hecke trace `C * l * z`. -/
theorem heckeTrace_sigma_two_eq (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ) :
    heckeTrace ⟨1, sigma (n := 2) 0⟩ τ C l = C * (l : R) * z := by
  have hT : τ (T q 0) = z := by
    simpa [hτ.map_one] using hτ.map_mul_T (one_mem (stage R q 1))
  have hexp : ArtinGroup.exponentSum (CoxeterMatrix.A 1) (sigma (n := 2) 0) =
      Multiplicative.ofAdd 1 := exponentSum_sigma (0 : Fin (2 - 1))
  simp [heckeTrace_def, hexp, val_unitT, hT]

/-- When `C * l * z = 1`, the single positive crossing on two strands closes to `1`. -/
theorem heckeTrace_sigma_two (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (hpos : C * (l : R) * z = 1) :
    heckeTrace ⟨1, sigma (n := 2) 0⟩ τ C l = 1 := by
  rw [heckeTrace_sigma_two_eq hτ, hpos]

/-- Before imposing `C * l⁻¹ * (z - (q - q⁻¹)) = 1`, the single negative crossing on two strands
has normalized Hecke trace `C * l⁻¹ * (z - (q - q⁻¹))`. -/
theorem heckeTrace_sigma_two_inv_eq (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ) :
    heckeTrace ⟨1, (sigma (n := 2) 0)⁻¹⟩ τ C l =
      C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) := by
  have hT : τ ↑(unitT q 0)⁻¹ = z - ((q : R) - ↑q⁻¹) := by
    simpa only [one_mul, hτ.map_one, mul_one] using
      hτ.map_mul_val_inv_unitT (one_mem (stage R q 1))
  have hexp : ArtinGroup.exponentSum (CoxeterMatrix.A 1) (sigma (n := 2) 0) =
      Multiplicative.ofAdd 1 := exponentSum_sigma (0 : Fin (2 - 1))
  simp only [heckeTrace_def, pow_one, map_inv, hexp, toAdd_inv, toAdd_ofAdd, zpow_neg_one,
    braidHom_sigma, Fin.val_zero, hT]

/-- When `C * l⁻¹ * (z - (q - q⁻¹)) = 1`, the single negative crossing on two strands closes to
`1`. -/
theorem heckeTrace_sigma_two_inv (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) :
    heckeTrace ⟨1, (sigma (n := 2) 0)⁻¹⟩ τ C l = 1 := by
  rw [heckeTrace_sigma_two_inv_eq hτ, hneg]

end MarkovBraid

end TwoStrandChecks

section RegularHeckeTrace

variable {R : Type*} [CommRing R]

namespace MarkovBraid

/-- **The regularized Ocneanu braid trace.** Built from the degree-`β.predStrands` homogenized
Ocneanu trace at `(l⁻¹, C)`, this expression requires no Markov parameter `z = (C * l)⁻¹` and
therefore remains defined when the unlink factor `C` is zero or a non-unit. -/
noncomputable def regularHeckeTrace (β : MarkovBraid) (q : Rˣ) (C : R) (l : Rˣ) : R :=
  ↑(l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid)) *
    homogenizedOcneanuTrace R q ↑l⁻¹ C β.predStrands
      (InfiniteTypeAHeckeAlgebra.braidHom R q (β.predStrands + 1) β.braid)

/-- Defining formula for `regularHeckeTrace`. -/
theorem regularHeckeTrace_def (β : MarkovBraid) (q : Rˣ) (C : R) (l : Rˣ) :
    β.regularHeckeTrace q C l =
      ↑(l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid)) *
        homogenizedOcneanuTrace R q ↑l⁻¹ C β.predStrands
          (InfiniteTypeAHeckeAlgebra.braidHom R q (β.predStrands + 1) β.braid) :=
  (rfl)

private theorem regularHeckeTrace_eq_heckeTrace_one (n : ℕ) (b : BraidGroup (n + 1))
    (q : Rˣ) (C : R) (l : Rˣ) :
    regularHeckeTrace ⟨n, b⟩ q C l =
      heckeTrace ⟨n, b⟩ (homogenizedOcneanuTrace R q ↑l⁻¹ C n) 1 l := by
  simp [regularHeckeTrace_def, heckeTrace_def]

/-- Whenever `C * z = l⁻¹`, `regularHeckeTrace` coincides with the normalized Hecke trace of
`ocneanuTrace R q z`. -/
theorem regularHeckeTrace_eq_heckeTrace_of_mul_eq (β : MarkovBraid) {q : Rˣ} {C z : R} {l : Rˣ}
    (hz : C * z = ↑l⁻¹) :
    β.regularHeckeTrace q C l = β.heckeTrace (ocneanuTrace R q z) C l := by
  rcases β with ⟨n, b⟩
  rw [regularHeckeTrace_def, heckeTrace_def, ← hz,
    homogenizedOcneanuTrace_const_mul z C (braidHom_mem_stage b)]
  ring

/-- Whenever `C * l * z = 1`, `regularHeckeTrace` coincides with the normalized Hecke trace of
`ocneanuTrace R q z`. -/
theorem regularHeckeTrace_eq_heckeTrace (β : MarkovBraid) {q : Rˣ} {C z : R} {l : Rˣ}
    (hpos : C * (l : R) * z = 1) :
    β.regularHeckeTrace q C l = β.heckeTrace (ocneanuTrace R q z) C l := by
  refine regularHeckeTrace_eq_heckeTrace_of_mul_eq β ?_
  calc C * z = C * ((l : R) * ↑l⁻¹) * z := by rw [Units.mul_inv, mul_one]
    _ = (C * (l : R) * z) * ↑l⁻¹ := by ring
    _ = ↑l⁻¹ := by rw [hpos, one_mul]

/-- Naturality of `regularHeckeTrace` along an `R`-algebra `S`. -/
theorem map_regularHeckeTrace {S : Type*} [CommRing S] [Algebra R S] (β : MarkovBraid)
    {q : Rˣ} {q' : Sˣ} (hq : algebraMap R S q = q') (C : R) {l : Rˣ} {l' : Sˣ}
    (hl : algebraMap R S l = l') :
    algebraMap R S (β.regularHeckeTrace q C l) =
      β.regularHeckeTrace q' (algebraMap R S C) l' := by
  have hlu : Units.map (algebraMap R S).toMonoidHom l = l' := Units.ext hl
  have hlinv : algebraMap R S (↑l⁻¹ : R) = ↑l'⁻¹ := by
    rw [← hlu, ← map_inv (Units.map (algebraMap R S).toMonoidHom), Units.coe_map]
    rfl
  have hw : algebraMap R S ↑(l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid)) =
      ↑(l' ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid)) := by
    rw [← hlu, ← map_zpow (Units.map (algebraMap R S).toMonoidHom), Units.coe_map]
    rfl
  rw [regularHeckeTrace_def, regularHeckeTrace_def, _root_.map_mul, hw,
    map_homogenizedOcneanuTrace hq, hlinv, map_braidHom]

/-- The identity braid on `n + 1` strands has `regularHeckeTrace` equal to `C ^ n`. -/
@[simp]
theorem regularHeckeTrace_one (n : ℕ) (q : Rˣ) (C : R) (l : Rˣ) :
    regularHeckeTrace ⟨n, 1⟩ q C l = C ^ n := by
  simp [regularHeckeTrace_def]

/-- Every braid on one strand has `regularHeckeTrace` equal to `1`. -/
@[simp]
theorem regularHeckeTrace_one_strand (q : Rˣ) (C : R) (l : Rˣ) (b : BraidGroup 1) :
    regularHeckeTrace ⟨0, b⟩ q C l = 1 := by
  rw [eq_one_of_le_one le_rfl b, regularHeckeTrace_one, pow_zero]

/-- The two-strand unlink closure `⟨1, 1⟩` has `regularHeckeTrace` equal to `C`. -/
theorem regularHeckeTrace_two_strand_one (q : Rˣ) (C : R) (l : Rˣ) :
    regularHeckeTrace ⟨1, 1⟩ q C l = C := by
  simp

/-- Adding an uncrossed strand multiplies `regularHeckeTrace` by `C`, even when `C = 0`. -/
@[simp]
theorem regularHeckeTrace_strandIncl {n : ℕ} (q : Rˣ) (C : R) (l : Rˣ) (b : BraidGroup (n + 1)) :
    regularHeckeTrace ⟨n + 1, strandIncl b⟩ q C l = C * regularHeckeTrace ⟨n, b⟩ q C l := by
  simp only [regularHeckeTrace_def, exponentSum_strandIncl, braidHom_strandIncl,
    homogenizedOcneanuTrace_succ_of_mem_stage _ _ (braidHom_mem_stage b)]
  ring

/-- Conjugation preserves `regularHeckeTrace`. -/
@[simp]
theorem regularHeckeTrace_conj {n : ℕ} (q : Rˣ) (C : R) (l : Rˣ) (b c : BraidGroup (n + 1)) :
    regularHeckeTrace ⟨n, c * b * c⁻¹⟩ q C l = regularHeckeTrace ⟨n, b⟩ q C l := by
  rw [regularHeckeTrace_eq_heckeTrace_one, regularHeckeTrace_eq_heckeTrace_one]
  exact heckeTrace_conj (homogenizedOcneanuTrace_mul_comm _ _ _) 1 l b c

/-- Positive Markov stabilization preserves `regularHeckeTrace` unconditionally for every `q`, `C`,
and `l`. -/
@[simp]
theorem regularHeckeTrace_stabilize {n : ℕ} (q : Rˣ) (C : R) (l : Rˣ) (b : BraidGroup (n + 1)) :
    regularHeckeTrace ⟨n + 1, strandIncl b * sigma (Fin.last n)⟩ q C l =
      regularHeckeTrace ⟨n, b⟩ q C l := by
  simp only [regularHeckeTrace_def, map_mul, exponentSum_strandIncl, exponentSum_sigma,
    toAdd_mul, toAdd_ofAdd, zpow_add, zpow_one, Units.val_mul, braidHom_strandIncl, braidHom_sigma,
    val_unitT, Fin.val_last]
  rw [homogenizedOcneanuTrace_mul_T _ _ (braidHom_mem_stage b)]
  calc ((l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ b) : Rˣ) : R) * l *
        (↑l⁻¹ * homogenizedOcneanuTrace R q ↑l⁻¹ C n (braidHom R q (n + 1) b))
      = ↑(l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ b)) * ((l : R) * ↑l⁻¹) *
          homogenizedOcneanuTrace R q ↑l⁻¹ C n (braidHom R q (n + 1) b) := by ring
    _ = _ := by rw [Units.mul_inv, mul_one]

/-- Negative Markov stabilization preserves `regularHeckeTrace` whenever
`C * (q - q⁻¹) = l⁻¹ - l`. This relation requires no inverse for `C` and holds in particular at
`C = 0` when `l = ±1`. -/
theorem regularHeckeTrace_stabilizeInv {n : ℕ} (q : Rˣ) (C : R) (l : Rˣ)
    (hstab : C * ((q : R) - ↑q⁻¹) = (↑l⁻¹ : R) - (l : R)) (b : BraidGroup (n + 1)) :
    regularHeckeTrace ⟨n + 1, strandIncl b * (sigma (Fin.last n))⁻¹⟩ q C l =
      regularHeckeTrace ⟨n, b⟩ q C l := by
  simp only [regularHeckeTrace_def, map_mul, map_inv, exponentSum_strandIncl, exponentSum_sigma,
    toAdd_mul, toAdd_inv, toAdd_ofAdd, zpow_add, zpow_neg_one, Units.val_mul, braidHom_strandIncl,
    braidHom_sigma, Fin.val_last]
  rw [homogenizedOcneanuTrace_mul_val_inv_unitT _ _ (braidHom_mem_stage b)]
  have hw : (↑l⁻¹ : R) - ((q : R) - ↑q⁻¹) * C = (l : R) := by linear_combination -hstab
  rw [hw]
  calc ((l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ b) : Rˣ) : R) * ↑l⁻¹ *
        ((l : R) * homogenizedOcneanuTrace R q ↑l⁻¹ C n (braidHom R q (n + 1) b))
      = ↑(l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ b)) * ((↑l⁻¹ : R) * l) *
          homogenizedOcneanuTrace R q ↑l⁻¹ C n (braidHom R q (n + 1) b) := by ring
    _ = _ := by rw [Units.inv_mul, mul_one]

/-- The single positive crossing on two strands closes to `1` in `regularHeckeTrace`, for any `q`,
`C`, and `l`. -/
@[simp]
theorem regularHeckeTrace_sigma_two (q : Rˣ) (C : R) (l : Rˣ) :
    regularHeckeTrace ⟨1, sigma (n := 2) 0⟩ q C l = 1 := by
  simpa using regularHeckeTrace_stabilize (n := 0) q C l 1

/-- Before imposing `C * (q - q⁻¹) = l⁻¹ - l`, the single negative crossing on two strands has
`regularHeckeTrace` equal to `l⁻¹ * (l⁻¹ - (q - q⁻¹) * C)`. -/
theorem regularHeckeTrace_sigma_two_inv_eq (q : Rˣ) (C : R) (l : Rˣ) :
    regularHeckeTrace ⟨1, (sigma (n := 2) 0)⁻¹⟩ q C l =
      (↑l⁻¹ : R) * ((↑l⁻¹ : R) - ((q : R) - ↑q⁻¹) * C) := by
  have hexp : ArtinGroup.exponentSum (CoxeterMatrix.A 1) (sigma (n := 2) 0) =
      Multiplicative.ofAdd 1 := exponentSum_sigma (0 : Fin (2 - 1))
  rw [regularHeckeTrace_def]
  simp only [map_inv, hexp, toAdd_inv, toAdd_ofAdd, zpow_neg_one, braidHom_sigma, Fin.val_zero]
  rw [← one_mul (↑(unitT q 0)⁻¹ : InfiniteTypeAHeckeAlgebra R q),
    homogenizedOcneanuTrace_mul_val_inv_unitT _ _ (one_mem (stage R q 1)),
    homogenizedOcneanuTrace_one, pow_zero, mul_one]

/-- When `C * (q - q⁻¹) = l⁻¹ - l`, the single negative crossing on two strands closes to `1` in
`regularHeckeTrace`. -/
theorem regularHeckeTrace_sigma_two_inv (q : Rˣ) (C : R) (l : Rˣ)
    (hstab : C * ((q : R) - ↑q⁻¹) = (↑l⁻¹ : R) - (l : R)) :
    regularHeckeTrace ⟨1, (sigma (n := 2) 0)⁻¹⟩ q C l = 1 := by
  simpa using regularHeckeTrace_stabilizeInv (n := 0) q C l hstab 1

/-- Oriented skein relation for `regularHeckeTrace` in any braid context. -/
theorem regularHeckeTrace_skein {n : ℕ} (q : Rˣ) (C : R) (l : Rˣ)
    (b c : BraidGroup (n + 1)) (i : Fin n) :
    (↑l⁻¹ : R) * regularHeckeTrace ⟨n, b * sigma (n := n + 1) i * c⟩ q C l -
        (l : R) * regularHeckeTrace ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ q C l =
      ((q : R) - ↑q⁻¹) * regularHeckeTrace ⟨n, b * c⟩ q C l := by
  simp only [regularHeckeTrace_eq_heckeTrace_one]
  exact heckeTrace_skein 1 l b c i

end MarkovBraid

/-- Every generating Markov move preserves `regularHeckeTrace` when `C * (q - q⁻¹) = l⁻¹ - l`. -/
theorem IsMarkovMove.regularHeckeTrace_eq {β γ : MarkovBraid} (h : IsMarkovMove β γ)
    (q : Rˣ) (C : R) (l : Rˣ) (hstab : C * ((q : R) - ↑q⁻¹) = (↑l⁻¹ : R) - (l : R)) :
    β.regularHeckeTrace q C l = γ.regularHeckeTrace q C l := by
  cases h with
  | conj b c => exact MarkovBraid.regularHeckeTrace_conj q C l b c
  | stabilize b => exact MarkovBraid.regularHeckeTrace_stabilize q C l b
  | stabilizeInv b => exact MarkovBraid.regularHeckeTrace_stabilizeInv q C l hstab b

/-- Markov-equivalent braids have equal `regularHeckeTrace` when `C * (q - q⁻¹) = l⁻¹ - l`. -/
theorem MarkovEquiv.regularHeckeTrace_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    (q : Rˣ) (C : R) (l : Rˣ) (hstab : C * ((q : R) - ↑q⁻¹) = (↑l⁻¹ : R) - (l : R)) :
    β.regularHeckeTrace q C l = γ.regularHeckeTrace q C l :=
  h.induction (fun hmove ↦ hmove.regularHeckeTrace_eq q C l hstab)
    (fun _ ↦ rfl) (fun _ ih ↦ ih.symm) (fun _ _ ih ih' ↦ ih.trans ih')

/-- The regularized Ocneanu invariant descended to `Quot MarkovEquiv`. Unlike `heckeBraidInvariant`,
this requires only `C * (q - q⁻¹) = l⁻¹ - l` and remains defined when `C = 0` or `C` is a
non-unit. -/
noncomputable def regularHeckeBraidInvariant (q : Rˣ) (C : R) (l : Rˣ)
    (hstab : C * ((q : R) - ↑q⁻¹) = (↑l⁻¹ : R) - (l : R)) : Quot MarkovEquiv → R :=
  Quot.lift (fun β ↦ β.regularHeckeTrace q C l)
    (fun _ _ h ↦ h.regularHeckeTrace_eq q C l hstab)

/-- Evaluation of `regularHeckeBraidInvariant` on a braid representative. -/
@[simp]
theorem regularHeckeBraidInvariant_mk (q : Rˣ) (C : R) (l : Rˣ)
    (hstab : C * ((q : R) - ↑q⁻¹) = (↑l⁻¹ : R) - (l : R)) (β : MarkovBraid) :
    regularHeckeBraidInvariant q C l hstab (Quot.mk MarkovEquiv β) =
      β.regularHeckeTrace q C l :=
  (rfl)

/-- **Skein characterization of `regularHeckeTrace`.** Any Markov invariant `F` satisfying
`l⁻¹ * F(σᵢ c) - l * F(σᵢ⁻¹ c) = (q - q⁻¹) * F(c)`, scaled by `C` on adding an uncrossed strand,
and equal to `1` on the unknot equals `regularHeckeTrace` whenever `C * (q - q⁻¹) = l⁻¹ - l`
(including at `C = 0`). -/
theorem MarkovBraid.eq_regularHeckeTrace_of_skein {q : Rˣ} {C : R} {l : Rˣ}
    (hstab : C * ((q : R) - ↑q⁻¹) = (↑l⁻¹ : R) - (l : R)) {F : MarkovBraid → R}
    (hF : ∀ β γ, MarkovEquiv β γ → F β = F γ)
    (hs : ∀ n (c : BraidGroup (n + 1)) (i : Fin n),
      (↑l⁻¹ : R) * F ⟨n, sigma (n := n + 1) i * c⟩ -
          (l : R) * F ⟨n, (sigma (n := n + 1) i)⁻¹ * c⟩ =
        ((q : R) - ↑q⁻¹) * F ⟨n, c⟩)
    (hι : ∀ n (b : BraidGroup (n + 1)), F ⟨n + 1, strandIncl b⟩ = C * F ⟨n, b⟩)
    (h₁ : F ⟨0, 1⟩ = 1) :
    F = fun β ↦ β.regularHeckeTrace q C l :=
  eq_of_skein l⁻¹ ((q : R) - ↑q⁻¹) C hF
    (fun _ _ h ↦ h.regularHeckeTrace_eq q C l hstab)
    (by simpa only [smul_eq_mul, inv_inv] using hs)
    (fun n c i ↦ by
      simpa only [smul_eq_mul, inv_inv, one_mul] using regularHeckeTrace_skein q C l 1 c i)
    (by simpa only [smul_eq_mul] using hι)
    (fun n b ↦ by rw [smul_eq_mul, regularHeckeTrace_strandIncl])
    (by rw [h₁, regularHeckeTrace_one_strand])

end RegularHeckeTrace

section JimboComparison

namespace MarkovBraid

/-- **Unconditional comparison of `jimboTrace` with `regularHeckeTrace`.** Over every commutative
ring `R`, for every number of colours `N`, unit `q : Rˣ`, and braid `β`, the writhe-normalized
`N`-colour Jimbo trace equals the quantum dimension `δ_N` times `regularHeckeTrace` at
`C = δ_N` and `l = (q ^ N)⁻¹`. No division by `δ_N` or `q - q⁻¹` is required. -/
theorem jimboTrace_eq_mul_regularHeckeTrace {R : Type*} [CommRing R] (N : ℕ) (β : MarkovBraid)
    (q : Rˣ) :
    β.jimboTrace (N := N) q =
      (∑ a : Fin N, jimboWeight q a) *
        β.regularHeckeTrace q (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) := by
  rcases β with ⟨n, b⟩
  rw [jimboTrace_def, regularHeckeTrace_def, ← TypeAHeckeAlgebra.jimboWeightedTrace_braidHom,
    TypeAHeckeAlgebra.jimboWeightedTrace_eq_mul_homogenizedOcneanuTrace,
    TypeAHeckeAlgebra.toInfinite_braidHom, inv_inv, inv_zpow', zpow_neg]
  ring

/-- When `c * δ_N = 1`, `jimboTrace` equals `δ_N` times the normalized Ocneanu `heckeTrace` at
Markov parameter `c * q ^ N`. -/
theorem jimboTrace_eq_mul_heckeTrace {R : Type*} [CommRing R] {N : ℕ} {q : Rˣ} {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) (β : MarkovBraid) :
    β.jimboTrace (N := N) q =
      (∑ a : Fin N, jimboWeight q a) *
        β.heckeTrace (ocneanuTrace R q (c * ↑(q ^ N)))
          (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) := by
  have hz : (∑ a : Fin N, jimboWeight q a) * (c * ↑(q ^ N)) = ↑((q ^ N)⁻¹)⁻¹ := by
    rw [inv_inv, ← mul_assoc, mul_comm _ c, hc, one_mul]
  rw [jimboTrace_eq_mul_regularHeckeTrace, regularHeckeTrace_eq_heckeTrace_of_mul_eq β hz]

/-- Rescaled form of `jimboTrace_eq_mul_heckeTrace`: when `c * δ_N = 1`, multiplying `jimboTrace` by
`c` recovers the normalized Ocneanu `heckeTrace` directly. -/
theorem mul_jimboTrace_eq_heckeTrace {R : Type*} [CommRing R] {N : ℕ} {q : Rˣ} {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) (β : MarkovBraid) :
    c * β.jimboTrace (N := N) q =
      β.heckeTrace (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) := by
  rw [jimboTrace_eq_mul_heckeTrace hc, ← mul_assoc, hc, one_mul]

/-- Over a field where the `N`-colour quantum dimension `δ_N` is nonzero, `jimboReducedTrace`
coincides with `regularHeckeTrace` at `C = δ_N` and `l = (q ^ N)⁻¹`. -/
theorem jimboReducedTrace_eq_regularHeckeTrace {K : Type*} [Field K] {N : ℕ} (β : MarkovBraid)
    {q : Kˣ} (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    β.jimboReducedTrace (N := N) q =
      β.regularHeckeTrace q (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) := by
  rw [jimboReducedTrace_def, jimboTrace_eq_mul_regularHeckeTrace, mul_div_cancel_left₀ _ hδ]

/-- **Comparison of `jimboReducedTrace` with the Ocneanu `heckeTrace`.** Over a field where the
`N`-colour quantum dimension `δ_N` is nonzero, `jimboReducedTrace` equals the normalized Ocneanu
braid invariant at `z = q ^ N / δ_N`, `C = δ_N`, and `l = (q ^ N)⁻¹`. -/
theorem jimboReducedTrace_eq_heckeTrace {K : Type*} [Field K] {N : ℕ} (β : MarkovBraid)
    {q : Kˣ} (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    β.jimboReducedTrace (N := N) q =
      β.heckeTrace (ocneanuTrace K q (↑(q ^ N) / ∑ a : Fin N, jimboWeight q a))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) := by
  have hz : (∑ a : Fin N, jimboWeight q a) * (↑(q ^ N) / ∑ a : Fin N, jimboWeight q a) =
      ↑((q ^ N)⁻¹)⁻¹ := by
    rw [inv_inv, mul_div_cancel₀ _ hδ]
  rw [jimboReducedTrace_eq_regularHeckeTrace β hδ, regularHeckeTrace_eq_heckeTrace_of_mul_eq β hz]

end MarkovBraid

end JimboComparison

section HomflyComparison

variable {K R : Type*} [Field K] [CommRing R]

/-- Evaluating the HOMFLY unknot polynomial `(a - a⁻¹) z⁻¹` at `z = u` and `a` gives
`(a - a⁻¹) * u⁻¹`. -/
@[simp]
theorem KnotTheory.eval₂_homflyUnknot (f : K →+* R) (u a : Rˣ) :
    eval₂ (eval₂ f u) a (homflyUnknot K) = ((a : R) - ↑a⁻¹) * ↑u⁻¹ := by
  simp [homflyUnknot_def]

namespace MarkovBraid

/-- **Comparison of `reducedHomfly` with `regularHeckeTrace`.** For any ring homomorphism
`f : K →+* R` from a field `K` to a commutative ring `R` and any units `q u l : Rˣ` with
`u = q - q⁻¹`, evaluating `β.reducedHomfly K` at `z = u` and `a = l⁻¹` yields
`β.regularHeckeTrace q ((l⁻¹ - l) * u⁻¹) l`. Because `regularHeckeTrace` requires no inverse of
`C = (l⁻¹ - l) * u⁻¹`, this holds across zero-factor specializations such as `l = ±1`. -/
theorem eval₂_reducedHomfly_eq_regularHeckeTrace (β : MarkovBraid) (f : K →+* R)
    (q u l : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (eval₂ f u) l⁻¹ (β.reducedHomfly K) =
      β.regularHeckeTrace q (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) l := by
  let e : LaurentPolynomial (LaurentPolynomial K) →+* R := eval₂ (eval₂ f u) l⁻¹
  have heT1 : e (LaurentPolynomial.T 1) = (↑l⁻¹ : R) := by simp [e]
  have heTneg1 : e (LaurentPolynomial.T (-1)) = (l : R) := by simp [e]
  have hez : e (C (LaurentPolynomial.T 1)) = (u : R) := by simp [e]
  have heU : e (homflyUnknot K) = ((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹ := by
    simp [e]
  have hstab : (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) * ((q : R) - ↑q⁻¹) = (↑l⁻¹ : R) - (l : R) := by
    rw [← hu, mul_assoc, Units.inv_mul, mul_one]
  have h := eq_regularHeckeTrace_of_skein hstab
    (F := fun γ ↦ e (γ.reducedHomfly K))
    (fun _ _ h ↦ congrArg e (h.reducedHomfly_eq K))
    (fun n c i ↦ ?_)
    (fun n b ↦ ?_)
    (by simp [e])
  · exact congrFun h β
  · simpa only [one_mul, map_sub, map_mul, heT1, heTneg1, hez, hu] using
      congrArg e (reducedHomfly_skein K (1 : BraidGroup (n + 1)) c i)
  · rw [reducedHomfly_strandIncl, map_mul, heU]

/-- **Comparison of `reducedHomfly` with the Ocneanu `heckeTrace`.** Whenever `z : R` satisfies
`((l⁻¹ - l) * u⁻¹) * z = l⁻¹` (in particular whenever `((l⁻¹ - l) * u⁻¹) * l * z = 1`), evaluating
`β.reducedHomfly K` at `z_HOMFLY = u = q - q⁻¹` and `a = l⁻¹` gives the normalized Ocneanu trace
`β.heckeTrace (ocneanuTrace R q z) ((l⁻¹ - l) * u⁻¹) l`. -/
theorem eval₂_reducedHomfly_eq_heckeTrace (β : MarkovBraid) (f : K →+* R)
    (q u l : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) {z : R}
    (hz : (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) * z = ↑l⁻¹) :
    eval₂ (eval₂ f u) l⁻¹ (β.reducedHomfly K) =
      β.heckeTrace (ocneanuTrace R q z) (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) l := by
  rw [eval₂_reducedHomfly_eq_regularHeckeTrace β f q u l hu,
    regularHeckeTrace_eq_heckeTrace_of_mul_eq β hz]

/-- Field form of `eval₂_reducedHomfly_eq_heckeTrace`: over a field `L` with `q - q⁻¹ ≠ 0` and
`l⁻¹ - l ≠ 0`, `reducedHomfly` specializes to Jones's Ocneanu braid invariant with Markov parameter
`z = l⁻¹ * (q - q⁻¹) / (l⁻¹ - l)` and unlink factor `C = (l⁻¹ - l) / (q - q⁻¹)`. -/
theorem eval₂_reducedHomfly_eq_heckeTrace_div {L : Type*} [Field L] (β : MarkovBraid)
    (f : K →+* L) {q l : Lˣ} (hq : (q : L) - ↑q⁻¹ ≠ 0) (hl : (↑l⁻¹ : L) - (l : L) ≠ 0) :
    eval₂ (eval₂ f (Units.mk0 ((q : L) - ↑q⁻¹) hq)) l⁻¹ (β.reducedHomfly K) =
      β.heckeTrace
        (ocneanuTrace L q (((↑l⁻¹ : L) * ((q : L) - ↑q⁻¹)) / ((↑l⁻¹ : L) - (l : L))))
        (((↑l⁻¹ : L) - (l : L)) / ((q : L) - ↑q⁻¹)) l := by
  have hC : (((↑l⁻¹ : L) - (l : L)) * ↑(Units.mk0 ((q : L) - ↑q⁻¹) hq)⁻¹) =
      ((↑l⁻¹ : L) - (l : L)) / ((q : L) - ↑q⁻¹) := by
    simp [div_eq_mul_inv]
  have hz : (((↑l⁻¹ : L) - (l : L)) / ((q : L) - ↑q⁻¹)) *
      (((↑l⁻¹ : L) * ((q : L) - ↑q⁻¹)) / ((↑l⁻¹ : L) - (l : L))) = ↑l⁻¹ := by
    field_simp
  rw [eval₂_reducedHomfly_eq_regularHeckeTrace β f q (Units.mk0 ((q : L) - ↑q⁻¹) hq) l rfl,
    hC, regularHeckeTrace_eq_heckeTrace_of_mul_eq β hz]

/-- **Comparison of unreduced `homfly` with `regularHeckeTrace`.** Evaluating `β.homfly K` at
`z_HOMFLY = u = q - q⁻¹` and `a = l⁻¹` gives `((l⁻¹ - l) * u⁻¹)` times `regularHeckeTrace`,
valid across all `l : Rˣ` including `l = ±1`. -/
theorem eval₂_homfly_eq_mul_regularHeckeTrace (β : MarkovBraid) (f : K →+* R)
    (q u l : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (eval₂ f u) l⁻¹ (β.homfly K) =
      (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) *
        β.regularHeckeTrace q (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) l := by
  rw [← homflyUnknot_mul_reducedHomfly, _root_.map_mul, eval₂_homflyUnknot, inv_inv,
    eval₂_reducedHomfly_eq_regularHeckeTrace β f q u l hu]

/-- **Comparison of unreduced `homfly` with the Ocneanu `heckeTrace`.** When
`((l⁻¹ - l) * u⁻¹) * z = l⁻¹`, evaluating `β.homfly K` at `z_HOMFLY = u = q - q⁻¹` and `a = l⁻¹`
gives `((l⁻¹ - l) * u⁻¹)` times the normalized Ocneanu trace. -/
theorem eval₂_homfly_eq_mul_heckeTrace (β : MarkovBraid) (f : K →+* R)
    (q u l : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) {z : R}
    (hz : (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) * z = ↑l⁻¹) :
    eval₂ (eval₂ f u) l⁻¹ (β.homfly K) =
      (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) *
        β.heckeTrace (ocneanuTrace R q z) (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) l := by
  rw [eval₂_homfly_eq_mul_regularHeckeTrace β f q u l hu,
    regularHeckeTrace_eq_heckeTrace_of_mul_eq β hz]

end MarkovBraid

end HomflyComparison

end TauCeti
