/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot
public import TauCeti.RingTheory.AdjoinRoot.Basic
public import TauCeti.RingTheory.PowerSeries.Entire.Division
public import TauCeti.RingTheory.PowerSeries.Entire.Eval
import Mathlib.Tactic.LinearCombination

/-!
# Resultants of monic polynomials and entire power series

Let `P` be a monic polynomial of degree `d` over a complete normed commutative ring `R`. Division
by `P` sends an entire series `F` to a remainder `F %ₘ P` of degree less than `d`
(`PowerSeries.modByMonic`), and hence to an element of the finite free `R`-algebra
`R[X] ⧸ (P) = AdjoinRoot P` of rank `d`. The *entire resultant* `Res(P, F)` is the determinant of
multiplication by this element, that is, its norm `Algebra.norm R`. For a polynomial `F` it is the
classical resultant of `P` and `F`, and if `P = ∏ (X - aᵢ)` it is the product `∏ F(aᵢ)` of the
values of `F` at the roots of `P`.

Over an ultrametric ring with `‖1‖ = 1`, division is unique, so reduction modulo `P` is a ring
homomorphism from entire series onto `AdjoinRoot P` with kernel `P` times the entire series
(`PowerSeries.IsEntire.mkAdjoinRoot`, in `TauCeti.RingTheory.PowerSeries.Entire.Division`), and
the entire resultant is the norm of this reduction. It is then multiplicative in `F`, depends
only on `F` modulo `P`, and is a unit exactly when `P` and `F` are coprime in the ring of entire
series. It satisfies a Bézout identity `Res(P, F) = P * G + H * F` with `G` entire and `H` a
polynomial of degree less than `d`.

These are the algebraic identities through which entire series, such as the Fredholm
determinants of compact operators, are reduced modulo polynomial factors.

## Main definitions

* `Polynomial.entireResultant`: the resultant `Res(P, F)` of a polynomial and a power series.

## Main results

* `Polynomial.entireResultant_coe`: on polynomials, the entire resultant is the polynomial
  resultant, read at any degree bound for the second argument.
* `Polynomial.entireResultant_eq_prod_evalAt`: if `P = ∏ (X - aᵢ)`, then `Res(P, F) = ∏ F(aᵢ)`;
  in particular `Res(X - a, F) = F(a)` (`Polynomial.entireResultant_X_sub_C`).
* `Polynomial.entireResultant_map`: compatibility with continuous coefficient homomorphisms.
* `Polynomial.entireResultant_add_mul` and `Polynomial.entireResultant_mul`: invariance modulo
  `P` and multiplicativity in `F`.
* `Polynomial.exists_C_entireResultant_eq`: the Bézout identity `Res(P, F) = P * G + H * F`.
* `Polynomial.isUnit_entireResultant_iff`: `Res(P, F)` is a unit exactly when `P` and `F` are
  coprime in the ring of entire series.

## References

* R. F. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127 (1997),
  Appendix A3.
-/

public section

open scoped PowerSeries

open PowerSeries (IsEntire)

namespace Polynomial

section TopologicalRing

variable {R : Type*} [CommRing R] [TopologicalSpace R] {P : R[X]}

/-- The *entire resultant* `Res(P, F)` of a polynomial `P` and a power series `F`: the norm over
`R` of the class of the remainder `F.modByMonic P` in `AdjoinRoot P`, that is, the determinant of
multiplication by that remainder on `R[X] ⧸ (P)`. It is meaningful for monic `P` and entire `F`,
when `F` is congruent to its remainder modulo `P`
(`PowerSeries.IsEntire.modByMonic_add_divByMonic`). -/
noncomputable def entireResultant (P : R[X]) (F : R⟦X⟧) : R :=
  Algebra.norm R (AdjoinRoot.mk P (F.modByMonic P))

/-- The entire resultant is the norm of the class of the remainder. -/
theorem entireResultant_def (P : R[X]) (F : R⟦X⟧) :
    entireResultant P F = Algebra.norm R (AdjoinRoot.mk P (F.modByMonic P)) :=
  (rfl)

/-- For monic `P`, the entire resultant of `P` and `F` is the polynomial resultant of `P` and the
remainder of `F`. -/
theorem entireResultant_eq_resultant (hP : P.Monic) (F : R⟦X⟧) :
    entireResultant P F = P.resultant (F.modByMonic P) :=
  AdjoinRoot.norm_mk_eq_resultant hP _

/-- For monic `P`, the entire resultant of `P` and `F` is the polynomial resultant of `P` and the
remainder of `F`, read at any degree bound for the remainder. -/
theorem entireResultant_eq_resultant_of_natDegree_le (hP : P.Monic) {F : R⟦X⟧} {n : ℕ}
    (hn : (F.modByMonic P).natDegree ≤ n) :
    entireResultant P F = P.resultant (F.modByMonic P) P.natDegree n :=
  AdjoinRoot.norm_mk_eq_resultant_of_natDegree_le hP hn

/-- The resultant with the polynomial `1` is `1`: the quotient algebra `R[X] ⧸ (1)` has rank
zero. This holds for every `F`, including `F = 0`. -/
@[simp]
theorem entireResultant_one_left (F : R⟦X⟧) : entireResultant 1 F = 1 := by
  simp [entireResultant_eq_resultant monic_one]

/-- The resultant of a monic `P` with `0` is `0 ^ deg P`: it vanishes unless `P = 1`. -/
@[simp]
theorem entireResultant_zero_right (hP : P.Monic) : entireResultant P 0 = 0 ^ P.natDegree := by
  simp [entireResultant_eq_resultant hP]

end TopologicalRing

section Normed

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] {P : R[X]} {F : R⟦X⟧}

/-- **Agreement with the polynomial resultant.** For monic `P` and a polynomial `g`, the entire
resultant is the resultant of `P` and `g`, read at any degree bound `n` for `g`. -/
theorem entireResultant_coe (hP : P.Monic) (g : R[X]) {n : ℕ} (hn : g.natDegree ≤ n) :
    entireResultant P g = P.resultant g P.natDegree n := by
  rw [entireResultant_def, PowerSeries.modByMonic_coe g hP, AdjoinRoot.mk_modByMonic,
    AdjoinRoot.norm_mk_eq_resultant_of_natDegree_le hP hn]

/-- The resultant of a monic `P` with `1` is `1`: multiplication by `1` has determinant `1`. -/
@[simp]
theorem entireResultant_one_right (hP : P.Monic) : entireResultant P 1 = 1 := by
  rw [entireResultant_def, ← Polynomial.coe_one, PowerSeries.modByMonic_coe _ hP,
    AdjoinRoot.mk_modByMonic, map_one, map_one]

/-- The resultant of a monic `P` with itself is `0 ^ deg P`: it vanishes unless `P = 1`. -/
@[simp]
theorem entireResultant_self (hP : P.Monic) : entireResultant P P = 0 ^ P.natDegree := by
  rw [entireResultant_coe hP P le_rfl, resultant_self]

/-- **The entire resultant at a split polynomial.** If `P = ∏ i, (X - aᵢ)`, then `Res(P, F)` is the
product `∏ i, F(aᵢ)` of the values of the entire series `F` at the roots of `P`. The roots may
repeat. -/
theorem entireResultant_eq_prod_evalAt {ι : Type*} [Fintype ι] {a : ι → R}
    (hP : P = ∏ i, (X - C (a i))) (hF : F.IsEntire) :
    entireResultant P F = ∏ i, F.evalAt (a i) := by
  have hm : P.Monic := hP ▸ monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (a i)
  rw [entireResultant_def, AdjoinRoot.norm_mk_eq_prod_eval hP]
  refine Finset.prod_congr rfl fun i _ ↦ (hF.evalAt_eq_eval_modByMonic hm ?_).symm
  rw [hP, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- The resultant with a linear factor is a value: `Res(X - a, F) = F(a)` for entire `F`. -/
@[simp]
theorem entireResultant_X_sub_C (a : R) (hF : F.IsEntire) :
    entireResultant (X - C a) F = F.evalAt a := by
  simpa using entireResultant_eq_prod_evalAt (ι := Unit) (a := fun _ ↦ a) (by simp) hF

/-- **Base change.** A continuous coefficient homomorphism `φ` carries the entire resultant of
`P` and `F` to that of their images. -/
theorem entireResultant_map {S : Type*} [CommRing S] [TopologicalSpace S] [T2Space S]
    (hP : P.Monic) (hF : F.IsEntire) (φ : R →+* S) (hφ : Continuous φ) :
    entireResultant (P.map φ) (PowerSeries.map φ F) = φ (entireResultant P F) := by
  nontriviality S
  rw [entireResultant_eq_resultant hP,
    entireResultant_eq_resultant_of_natDegree_le (hP.map φ)
      (n := (F.modByMonic P).natDegree) (by
        rw [hF.map_modByMonic hP φ hφ]
        exact natDegree_map_le),
    hF.map_modByMonic hP φ hφ, hP.natDegree_map, resultant_map_map]

/-- **The Bézout identity for the entire resultant.** For monic `P` and entire `F` there are an
entire series `G` and a polynomial `H` of degree less than `deg P` with
`Res(P, F) = P * G + H * F`. -/
theorem exists_C_entireResultant_eq (hP : P.Monic) (hF : F.IsEntire) :
    ∃ G : R⟦X⟧, G.IsEntire ∧ ∃ H : R[X], H.degree < P.natDegree ∧
      (PowerSeries.C (entireResultant P F) : R⟦X⟧) = P * G + H * F := by
  have hdiv := hF.modByMonic_add_divByMonic hP
  set r := F.modByMonic P
  set q := F.divByMonic P
  by_cases hd : P.natDegree = 0
  · -- Here `P = 1`, the resultant is `1`, and `1 = P * 1 + 0 * F`.
    obtain rfl := eq_one_of_monic_natDegree_zero hP hd
    exact ⟨1, PowerSeries.isEntire_one, 0, by simp, by simp⟩
  obtain ⟨u, v, -, hv, huv⟩ :=
    exists_mul_add_mul_eq_C_resultant P r le_rfl le_rfl (Or.inl hd)
  refine ⟨u - q * v, (PowerSeries.isEntire_coe u).sub ((hF.divByMonic P).mul
    (PowerSeries.isEntire_coe v)), v, ?_, ?_⟩
  · exact hv
  · rw [entireResultant_eq_resultant hP, ← Polynomial.coe_C, ← huv, ← hdiv]
    push_cast
    ring

end Normed

section Ultrametric

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] [IsUltrametricDist R] [NormOneClass R]
  {P : R[X]} {F G : R⟦X⟧}

/-- The entire resultant of `P` and `F` is the norm of the reduction of `F` modulo `P`. -/
theorem entireResultant_eq_norm_mkAdjoinRoot (hP : P.Monic) (F : IsEntire.subring R) :
    entireResultant P F = Algebra.norm R (IsEntire.mkAdjoinRoot hP F) := by
  rw [IsEntire.mkAdjoinRoot_apply, entireResultant_def]

/-- **Invariance modulo `P`.** The entire resultant `Res(P, F)` depends only on `F` modulo `P`. -/
theorem entireResultant_add_mul (hP : P.Monic) (hF : F.IsEntire) (hG : G.IsEntire) :
    entireResultant P (F + P * G) = entireResultant P F := by
  have hdiv := hF.modByMonic_add_divByMonic hP
  rw [entireResultant_def, entireResultant_def, ← hdiv, add_assoc, ← mul_add,
    ((hF.divByMonic P).add hG).modByMonic_coe_add_coe_mul hP, AdjoinRoot.mk_modByMonic, hdiv]

/-- **Multiplicativity.** `Res(P, F * G) = Res(P, F) * Res(P, G)` for entire `F` and `G`. -/
theorem entireResultant_mul (hP : P.Monic) (hF : F.IsEntire) (hG : G.IsEntire) :
    entireResultant P (F * G) = entireResultant P F * entireResultant P G := by
  have h := map_mul ((Algebra.norm R).comp (IsEntire.mkAdjoinRoot hP).toMonoidHom)
    ⟨F, IsEntire.mem_subring.mpr hF⟩ ⟨G, IsEntire.mem_subring.mpr hG⟩
  simpa [entireResultant_def] using h

/-- **The entire resultant detects coprimality.** For monic `P` and entire `F`, `Res(P, F)` is a
unit exactly when `P` and `F` are coprime in the ring of entire series. -/
theorem isUnit_entireResultant_iff (hP : P.Monic) (hF : F.IsEntire) :
    IsUnit (entireResultant P F) ↔
      IsCoprime (⟨P, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe P)⟩ : IsEntire.subring R)
        ⟨F, IsEntire.mem_subring.mpr hF⟩ := by
  refine ⟨fun h ↦ ?_, fun ⟨a, b, hab⟩ ↦ ?_⟩
  · -- A polynomial Bézout relation `u * P + v * r = 1` for the remainder `r` gives an entire one.
    rw [entireResultant_eq_resultant hP, isUnit_resultant_iff_isCoprime hP] at h
    obtain ⟨u, v, huv⟩ := h
    have hdiv := hF.modByMonic_add_divByMonic hP
    refine ⟨⟨u - v * F.divByMonic P, IsEntire.mem_subring.mpr ((PowerSeries.isEntire_coe u).sub
      ((PowerSeries.isEntire_coe v).mul (hF.divByMonic P)))⟩,
      ⟨v, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe v)⟩, Subtype.ext ?_⟩
    have huv' := congrArg (fun p : R[X] ↦ (p : R⟦X⟧)) huv
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_one] at huv'
    simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_one]
    linear_combination huv' - (v : R⟦X⟧) * hdiv
  · -- Reducing `a * P + b * F = 1` modulo `P` makes the reduction of `F` a unit.
    have hred := congrArg (IsEntire.mkAdjoinRoot hP) hab
    rw [map_add, map_mul, map_mul, map_one, IsEntire.mkAdjoinRoot_coe, AdjoinRoot.mk_self,
      mul_zero, zero_add] at hred
    rw [entireResultant_eq_norm_mkAdjoinRoot hP ⟨F, IsEntire.mem_subring.mpr hF⟩]
    exact (IsUnit.of_mul_eq_one_right _ hred).map (Algebra.norm R)

end Ultrametric

end Polynomial
