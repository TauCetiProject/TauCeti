/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Jimbo.Normalization
public import TauCeti.KnotTheory.TemperleyLieb
import Mathlib.Logic.Equiv.Bool

/-!
# Comparing the two-colour Jimbo and Temperley–Lieb traces

The spin model of the Jones representation is the two-colour Jimbo representation at
`q = a²`, after reversing the names of the two colours and multiplying each positive
crossing by `a`. The enhancement weights differ by a minus sign on each strand.
These changes account for the exact sign relating the two writhe-normalized traces.

The comparison works over arbitrary commutative rings, including parameters where the
unknot value vanishes. It identifies the two braid algorithms without division or a
geometric classification theorem for braid closures.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math.
  92 (1988), 527–553.

The comparison uses the spin model `TemperleyLieb.spinRep` and the canonical-word
Jimbo representation, with Mathlib's `LinearMap.toMatrixAlgEquiv` to compare operators.
-/

public section

noncomputable section

open Function Finsupp Matrix

namespace TauCeti.KnotTheory

open TemperleyLieb

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Reverse the two colours so that the spin `true` has colour zero. -/
private def spinColour : Bool ≃ Fin 2 := Equiv.boolNot.trans finTwoEquiv.symm

private def spinWord : (Fin n → Bool) ≃ (Fin n → Fin 2) :=
  Equiv.piCongrRight fun _ => spinColour

private theorem spinWord_apply (s : Fin n → Bool) :
    spinWord s = fun i => if s i then 0 else 1 := by
  funext i
  simp only [spinWord, Equiv.piCongrRight_apply, Pi.map_apply, spinColour, Equiv.trans_apply]
  cases s i <;> rfl

private def spinBasis : Module.Basis (Fin n → Bool) R ((Fin n → Fin 2) →₀ R) :=
  Finsupp.basisSingleOne.reindex spinWord.symm

private theorem spinBasis_apply (s : Fin n → Bool) :
    spinBasis (R := R) s = single (spinWord s) 1 := by
  simp [spinBasis]

private theorem spinBasis_repr (v : (Fin n → Fin 2) →₀ R) (s : Fin n → Bool) :
    (spinBasis (R := R)).repr v s = v (spinWord s) := by
  simp [spinBasis]

private theorem spinWord_apply_apply (s : Fin n → Bool) (i : Fin n) :
    spinWord s i = if s i then 0 else 1 := congrFun (spinWord_apply s) i

private theorem spinWord_comp_swap (s : Fin n → Bool) (j k : Fin n) :
    spinWord (s ∘ Equiv.swap j k) = spinWord s ∘ Equiv.swap j k := (rfl)

private theorem jimboGenerator_spinBasis (a : Rˣ) (j k : Fin n) :
    LinearMap.toMatrixAlgEquiv (spinBasis (R := R)) (jimboGenerator (a ^ 2) j k) =
      (a : R) • ((a : R) • 1 + (↑(a⁻¹) : R) • spinGenerator (a ^ 2) j k) := by
  ext s t
  rw [LinearMap.toMatrixAlgEquiv_apply, spinBasis_apply, jimboGenerator_single_one,
    spinBasis_repr]
  simp only [apply_ite (fun v : (Fin n → Fin 2) →₀ R => v (spinWord s)),
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply, ← spinWord_comp_swap, Equiv.apply_eq_iff_eq,
    Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, spinGenerator_apply]
  by_cases h : ∀ l ∉ ({j, k} : Finset (Fin n)), s l = t l
  · have heq : s = t ↔ s j = t j ∧ s k = t k := by
      constructor
      · rintro rfl; simp
      · rintro ⟨hj, hk⟩
        funext l
        by_cases hlj : l = j
        · simpa [hlj] using hj
        by_cases hlk : l = k
        · simpa [hlk] using hk
        exact h l (by simp [hlj, hlk])
    have hswap : s = t ∘ Equiv.swap j k ↔ s j = t k ∧ s k = t j := by
      constructor
      · intro hs
        constructor <;> simp [hs]
      · rintro ⟨hj, hk⟩
        funext l
        by_cases hlj : l = j
        · simp [hlj, hj]
        by_cases hlk : l = k
        · simp [hlk, hk]
        simp [Equiv.swap_apply_of_ne_of_ne hlj hlk, h l (by simp [hlj, hlk])]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, and_imp] at h ⊢
    simp only [eq_comm (a := t) (b := s), eq_comm (a := t ∘ Equiv.swap j k) (b := s),
      heq, hswap, spinWord_apply_apply]
    generalize s j = sj, s k = sk, t j = tj, t k = tk
    cases sj <;> cases sk <;> cases tj <;> cases tk <;>
      simp [Units.val_pow_eq_pow_val] <;> grind [a.mul_inv]
  · have hne : s ≠ t := by rintro rfl; exact h (by simp)
    have hswapne : t ∘ Equiv.swap j k ≠ s := by
      intro hs
      apply h
      intro l hl
      have hl' : l ≠ j ∧ l ≠ k := by simpa using hl
      simpa [Equiv.swap_apply_of_ne_of_ne hl'.1 hl'.2] using (congrFun hs l).symm
    simp only [hne.symm, hswapne, h, ite_false, mul_zero]
    split_ifs <;> simp

private def twistedSpinJones (a : Rˣ) :
    BraidGroup n →* (Matrix (Fin n → Bool) (Fin n → Bool) R)ˣ where
  toFun b := Units.map (algebraMap R _).toMonoidHom
      (a ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ b)) *
    Units.map (spinRep (a ^ 2) (jonesDelta_eq_neg_sq_add_inv_sq a)).toMonoidHom (jones n a b)
  map_one' := by simp
  map_mul' b c := by
    apply Units.ext
    simp only [map_mul, toAdd_mul, zpow_add, Units.val_mul, Units.coe_map]
    simp [Algebra.algebraMap_eq_smul_one]

private theorem twistedSpinJones_apply (a : Rˣ) (b : BraidGroup n) :
    (twistedSpinJones a b : Matrix (Fin n → Bool) (Fin n → Bool) R) =
      (↑(a ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ b)) : R) •
        spinRep (a ^ 2) (jonesDelta_eq_neg_sq_add_inv_sq a)
          (jones n a b : TemperleyLieb R (jonesDelta a) n) := by
  dsimp [twistedSpinJones]
  simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

private theorem jimbo_matrix_eq_twistedSpinJones (a : Rˣ) :
    (Units.map (LinearMap.toMatrixAlgEquiv (spinBasis (R := R) (n := n))).toAlgHom.toMonoidHom).comp
        (jimbo (Fin 2) (a ^ 2)) = twistedSpinJones a := by
  apply BraidGroup.hom_ext
  intro i
  apply Units.ext
  have hj : BraidGroup.strand i = (⟨i, by have := i.isLt; omega⟩ : Fin n) :=
    Fin.ext (BraidGroup.val_strand i)
  have hk : BraidGroup.strandSucc i = (⟨i + 1, by have := i.isLt; omega⟩ : Fin n) :=
    Fin.ext (BraidGroup.val_strandSucc i)
  simpa [twistedSpinJones_apply, crossing_def, hj, hk] using
    jimboGenerator_spinBasis a (BraidGroup.strand i) (BraidGroup.strandSucc i)

/-- At `q = a²`, reversing the two colours identifies the Jimbo coefficient of any braid
with its Jones spin-model coefficient times `a` raised to the exponent sum. -/
theorem jimbo_apply_single_eq_spinRep_jones (a : Rˣ) (b : BraidGroup n)
    (s t : Fin n → Bool) :
    (jimbo (Fin 2) (a ^ 2) b : Module.End R ((Fin n → Fin 2) →₀ R))
        (single (fun i => if t i then 0 else 1) 1) (fun i => if s i then 0 else 1) =
      (↑(a ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ b)) : R) *
        spinRep (a ^ 2) (jonesDelta_eq_neg_sq_add_inv_sq a)
          (jones n a b : TemperleyLieb R (jonesDelta a) n) s t := by
  have h := congrArg (fun u : (Matrix (Fin n → Bool) (Fin n → Bool) R)ˣ => (u : Matrix _ _ R) s t)
    (DFunLike.congr_fun (jimbo_matrix_eq_twistedSpinJones a) b)
  simpa [LinearMap.toMatrixAlgEquiv_apply, spinBasis_apply, spinBasis_repr,
    spinWord_apply, twistedSpinJones_apply] using h


private theorem jimboWeight_spin (q : Rˣ) (b : Bool) :
    jimboWeight q (if b then (0 : Fin 2) else 1) = -markovWeight q b := by
  cases b <;> simp [jimboWeight_def]

/-- The two-colour Jimbo weighted trace equals the Jones spin trace, with the factor
`a` for each unit of exponent sum and a minus sign for each strand. -/
theorem jimboWeightedTrace_eq_markovTrace_jones (a : Rˣ) (b : BraidGroup n) :
    jimboWeightedTrace (N := 2) (a ^ 2) b =
      (-1 : R) ^ n * (↑(a ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ b)) : R) *
        markovTrace (a ^ 2) (jonesDelta_eq_neg_sq_add_inv_sq a)
          (jones n a b : TemperleyLieb R (jonesDelta a) n) := by
  rw [jimboWeightedTrace_eq_sum, ← (spinWord (n := n)).sum_comp]
  simp_rw [spinWord_apply, jimbo_apply_single_eq_spinRep_jones, jimboWeight_spin,
    Finset.prod_neg, Finset.card_univ, Fintype.card_fin, ← spinWeight_def]
  rw [markovTrace_apply, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.diagonal_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

end TauCeti.KnotTheory

namespace TauCeti.MarkovBraid

open KnotTheory TemperleyLieb

variable {R : Type*} [CommRing R]

/-- The Temperley–Lieb Jones trace and the two-colour Jimbo trace at `q = a²` agree
up to the sign `(-1)^(number of strands - exponent sum)`. The sign includes their
opposite unknot values; no invertibility of that value is required. -/
theorem jonesTrace_eq_jimboTrace_two (β : MarkovBraid) (a : Rˣ) :
    β.jonesTrace a =
      (↑((-1 : Rˣ) ^ ((β.predStrands + 1 : ℕ) -
        Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid) : ℤ)) : R) *
        β.jimboTrace (N := 2) (a ^ 2) := by
  rw [jonesTrace_def, jimboTrace_def, jimboWeightedTrace_eq_markovTrace_jones]
  let w := Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid)
  have hsign : (-1 : Rˣ) ^ ((β.predStrands + 1 : ℕ) - w : ℤ) *
      (-1) ^ (β.predStrands + 1) = (-1) ^ (-w) := by
    rw [zpow_sub, zpow_natCast, zpow_neg]
    have hs : (-1 : Rˣ) ^ (β.predStrands + 1) * (-1) ^ (β.predStrands + 1) = 1 := by
      rw [← mul_pow]
      simp
    calc _ = ((-1 : Rˣ) ^ (β.predStrands + 1) * (-1) ^ (β.predStrands + 1)) *
        ((-1) ^ w)⁻¹ := by ac_rfl
         _ = _ := by rw [hs, one_mul]
  have hunit : (-a ^ 3 : Rˣ) ^ (-w) =
      (-1) ^ ((β.predStrands + 1 : ℕ) - w : ℤ) * ((a ^ 2) ^ 2) ^ (-w) *
        (-1) ^ (β.predStrands + 1) * a ^ w := by
    rw [neg_eq_neg_one_mul, mul_zpow]
    calc _ = (-1 : Rˣ) ^ (-w) * ((((a ^ 2) ^ 2) ^ (-w)) * a ^ w) := by
           congr 1
           group
         _ = _ := by rw [← hsign]; ac_rfl
  have hval := congrArg (fun u : Rˣ => (u : R)) hunit
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at hval
  rw [hval]
  ring

end TauCeti.MarkovBraid
