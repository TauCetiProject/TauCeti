/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.UpperTriangular.Contribution

/-!
# The total upper-triangular contribution

The upper-triangular representatives of determinant `n > 0` are the matrices
`(a b; 0 d)` with `ad = n`, `a, d > 0`, and `0 ≤ b < d`.  The trace of such a matrix on
degree-`w` binary forms depends only on `(a, d)`, while its coefficient in Popa--Zagier's
explicit Hecke element is supported on `0 ≤ b ≤ d - a`.

This file sums the individual contribution computed in
`UpperTriangular/Contribution.lean`.  For a fixed factor pair `ad = n`, the coefficients sum
to `d - a` when `a < d`, to `1/6` when `a = d`, and to zero when `d < a`.  Thus the full
upper-triangular contribution is a divisor sum weighted by the Eichler--Selberg polynomial
`P_{w+2}(a+d,n)`.  This is an intermediate sum over canonical upper-triangular
representatives, not over conjugacy classes; it is one ingredient of the assembly of the
level-one trace formula, in which the conjugacy-type contributions are combined separately.

## Main result

* `TauCeti.PopaZagier.sum_upperTriangularCoeff`: the coefficient sum for one positive factor
  pair.
* `TauCeti.TraceFormulaMatrixModule.sum_trace_popaZagierElement_single_upperTriangularRep`:
  the sum over all canonical upper-triangular representatives as an explicit sum over the
  positive factor pairs of `n`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105--122, arXiv:1711.00327, §4.
-/

public section

open Matrix MvPolynomial MulOpposite MonoidAlgebra

namespace TauCeti

namespace PopaZagier

/-- For a fixed positive factor pair `(a, d)`, summing the Popa--Zagier coefficients over
`0 ≤ b < d` gives `d - a`, except that the scalar pair `a = d` has weight `1/6`. -/
theorem sum_upperTriangularCoeff (a d : ℕ) (ha : 0 < a) :
    ∑ b ∈ Finset.range d, upperTriangularCoeff a b d =
      if a < d then ((d - a : ℕ) : ℚ) else if a = d then 1 / 6 else 0 := by
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha
  have hcoeff : ∀ b : ℤ,
      upperTriangularCoeff a b d = (weight !![(a : ℤ), b; 0, d] : ℚ) / 12 := fun b ↦ by
    rw [weight_upperTriangular _ _ _ haZ, upperTriangularCoeff_def]
    split_ifs <;> norm_num
  have himg : (Finset.range d).image (Nat.cast : ℕ → ℤ) = Finset.Ico (0 : ℤ) d := by
    ext b
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Ico]
    exact ⟨fun ⟨k, hk, hkb⟩ ↦ hkb ▸ ⟨Nat.cast_nonneg k, by exact_mod_cast hk⟩,
      fun ⟨hb0, _⟩ ↦ ⟨b.toNat, by omega, Int.toNat_of_nonneg hb0⟩⟩
  calc
    ∑ b ∈ Finset.range d, upperTriangularCoeff a b d
        = ∑ b ∈ Finset.Ico (0 : ℤ) d, upperTriangularCoeff a b d := by
          rw [← himg, Finset.sum_image fun _ _ _ _ h ↦ Nat.cast_injective h]
    _ = ((∑ b ∈ Finset.Ico (0 : ℤ) d, weight !![(a : ℤ), b; 0, d] : ℤ) : ℚ) / 12 := by
          simp_rw [hcoeff, div_eq_mul_inv, ← Finset.sum_mul, Int.cast_sum]
    _ = _ := by
          rw [sum_Ico_weight_upperTriangular a d haZ]
          rcases lt_trichotomy a d with had | rfl | hda
          · have hadZ : (a : ℤ) < d := by exact_mod_cast had
            simp [had, hadZ, Nat.cast_sub had.le]
          · norm_num
          · have hdaZ : (d : ℤ) < a := by exact_mod_cast hda
            simp [hda.not_gt, hda.ne', hdaZ.not_gt, hdaZ.ne']

end PopaZagier

namespace TraceFormulaMatrixModule

/-- **The summed upper-triangular contribution.** Let `n > 0` and let `w` be even. Summing the
trace contributions of Popa--Zagier's explicit element over the canonical representatives
`(a b; 0 d)` gives

`Σ_{ad=n} c(a,d) P_{w+2}(a+d,n)`,

where `c(a,d) = d-a` for `a<d`, `c(a,a)=1/6`, and `c(a,d)=0` for `d<a`.

The scalar coefficient `1/6` is deliberately retained: the scalar conjugacy class is combined
with the other conjugacy types only in the final trace formula. -/
theorem sum_trace_popaZagierElement_single_upperTriangularRep (n w : ℕ) (hn : 0 < n)
    (hw : Even w) :
    ∑ A : ↥(FixedDetMatrices.reps (n : ℤ)),
        LinearMap.trace ℚ (homogeneousSubmodule (Fin 2) ℚ w)
          (periodAction hw
            (single (mk A.val) ((popaZagierElement ℚ n).coeff (mk A.val)))) =
      ∑ p ∈ n.divisorsAntidiagonal,
        (if p.1 < p.2 then ((p.2 - p.1 : ℕ) : ℚ)
          else if p.1 = p.2 then 1 / 6 else 0) *
            (Polynomial.dickson 2 (n : ℚ) w).eval ((p.1 + p.2 : ℕ) : ℚ) := by
  classical
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  let e := FixedDetMatrices.repsEquiv hnZ
  let contribution (A : ↥(FixedDetMatrices.reps (n : ℤ))) : ℚ :=
    LinearMap.trace ℚ (homogeneousSubmodule (Fin 2) ℚ w)
      (periodAction hw (single (mk A.val) ((popaZagierElement ℚ n).coeff (mk A.val))))
  calc
    ∑ A : ↥(FixedDetMatrices.reps (n : ℤ)), contribution A =
        ∑ x : Σ p : ↥n.divisorsAntidiagonal, Fin p.val.2, contribution (e.symm x) :=
      Fintype.sum_equiv e contribution (fun x ↦ contribution (e.symm x)) fun A ↦ by simp [e]
    _ = ∑ x : Σ p : ↥n.divisorsAntidiagonal, Fin p.val.2,
        PopaZagier.upperTriangularCoeff x.1.val.1 (x.2 : ℕ) x.1.val.2 *
          (Polynomial.dickson 2 (n : ℚ) w).eval ((x.1.val.1 + x.1.val.2 : ℕ) : ℚ) := by
      apply Fintype.sum_congr
      intro x
      dsimp only [contribution]
      obtain ⟨hc, ha, -, -⟩ := (e.symm x).property
      rw [trace_popaZagierElement_single_upperTriangular w hw (e.symm x).val hc ha]
      have hmatrix : (e.symm x).val.val =
          !![(x.1.val.1 : ℤ), (x.2 : ℕ); 0, (n : ℤ).sign * x.1.val.2] := by
        simpa only [e] using FixedDetMatrices.coe_repsEquiv_symm_apply hnZ x
      have hsign : (n : ℤ).sign = 1 := Int.sign_eq_one_of_pos (by exact_mod_cast hn)
      rw [hmatrix, hsign]
      simp
    _ = ∑ p : ↥n.divisorsAntidiagonal,
        (if p.val.1 < p.val.2 then ((p.val.2 - p.val.1 : ℕ) : ℚ)
          else if p.val.1 = p.val.2 then 1 / 6 else 0) *
            (Polynomial.dickson 2 (n : ℚ) w).eval ((p.val.1 + p.val.2 : ℕ) : ℚ) := by
      rw [Fintype.sum_sigma' (fun (p : ↥n.divisorsAntidiagonal) (b : Fin p.val.2) ↦
        PopaZagier.upperTriangularCoeff p.val.1 b p.val.2 *
          (Polynomial.dickson 2 (n : ℚ) w).eval ((p.val.1 + p.val.2 : ℕ) : ℚ))]
      apply Fintype.sum_congr
      intro p
      have ha : 0 < p.val.1 :=
        Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal p.property)
      calc
        ∑ b : Fin p.val.2, PopaZagier.upperTriangularCoeff p.val.1 b p.val.2 *
            (Polynomial.dickson 2 (n : ℚ) w).eval ((p.val.1 + p.val.2 : ℕ) : ℚ) =
            ∑ b ∈ Finset.range p.val.2, PopaZagier.upperTriangularCoeff p.val.1 b p.val.2 *
              (Polynomial.dickson 2 (n : ℚ) w).eval ((p.val.1 + p.val.2 : ℕ) : ℚ) :=
          by simpa using Fin.sum_univ_eq_sum_range (fun b : ℕ ↦
            PopaZagier.upperTriangularCoeff p.val.1 b p.val.2 *
              (Polynomial.dickson 2 (n : ℚ) w).eval ((p.val.1 + p.val.2 : ℕ) : ℚ)) p.val.2
        _ = _ := by
          rw [← Finset.sum_mul, PopaZagier.sum_upperTriangularCoeff p.val.1 p.val.2 ha]
    _ = _ := by
      simpa using n.divisorsAntidiagonal.sum_coe_sort (fun p ↦
        (if p.1 < p.2 then ((p.2 - p.1 : ℕ) : ℚ)
          else if p.1 = p.2 then 1 / 6 else 0) *
            (Polynomial.dickson 2 (n : ℚ) w).eval ((p.1 + p.2 : ℕ) : ℚ))

end TraceFormulaMatrixModule

end TauCeti
