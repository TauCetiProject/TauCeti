/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Polynomial
public import TauCeti.KnotTheory.Hecke

import Mathlib.Tactic.LinearCombination

/-!
# Regularized Ocneanu braid invariant

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

This module establishes the evaluation laws, two-strand checks, Markov invariance, descent to
`Quot MarkovEquiv`, and skein characterization of `regularHeckeTrace`, without importing Jimbo
representations or the HOMFLY construction. Comparisons with Jimbo and HOMFLY invariants are proved
in `TauCeti.KnotTheory.Hecke.Homfly`.

## Main definitions

* `TauCeti.MarkovBraid.regularHeckeTrace`: the homogenized Ocneanu braid-closure trace, regular at
  zero or non-unit unlink factors `C`.
* `TauCeti.regularHeckeBraidInvariant`: its descent to `Quot MarkovEquiv` when
  `C * (q - q⁻¹) = l⁻¹ - l`.

## Main results

* `TauCeti.MarkovBraid.regularHeckeTrace_eq_heckeTrace_of_mul_eq` and
  `TauCeti.MarkovBraid.regularHeckeTrace_eq_heckeTrace`: agreement of `regularHeckeTrace` with the
  Ocneanu `heckeTrace` when `C * z = l⁻¹` or `C * l * z = 1`.
* `TauCeti.MarkovBraid.regularHeckeTrace_two_strand_one`,
  `TauCeti.MarkovBraid.regularHeckeTrace_sigma_two`, and
  `TauCeti.MarkovBraid.regularHeckeTrace_sigma_two_inv`: explicit values on the two-strand unlink
  and both single-crossing closures.
* `TauCeti.MarkovEquiv.regularHeckeTrace_eq` and
  `TauCeti.MarkovBraid.eq_regularHeckeTrace_of_skein`: Markov invariance and skein characterization
  valid for arbitrary `C : R` (including `C = 0`).

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 5–6.
* C. Kassel and V. Turaev, *Braid Groups*, Springer GTM 247 (2008), Section 4.2.
-/

public section

namespace TauCeti

open BraidGroup InfiniteTypeAHeckeAlgebra

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

end TauCeti
