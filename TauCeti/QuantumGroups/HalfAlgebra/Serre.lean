/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.HalfAlgebra.Basic
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Basic

import TauCeti.Algebra.FreeAlgebra
import TauCeti.Algebra.Star.Free

/-!
# The quantum Serre elements lie in the radical of the form

Let `D` be a symmetrizable Cartan datum and `q` an element of a field `K`. The bicharacter
`χ(αᵢ, αⱼ) = q^(dᵢ aᵢⱼ) = qᵢ^(aᵢⱼ)` (`TauCeti.cartanBraiding`) is symmetric, and the positive
part `f` of the quantized enveloping algebra is the free algebra `T = K⟨θᵢ⟩` modulo the radical
`J` of Lusztig's form for this `χ` (`TauCeti.Half`).

For `i ≠ j` and `m = 1 - aᵢⱼ`, the quantum Serre element of `T` is
`Sᵢⱼ = ∑_(r + s = m) (-1)^r θᵢ^(r) θⱼ θᵢ^(s)`, with divided powers in `qᵢ`; it is
`QuantizedEnvelopingAlgebra.serreSum D q (FreeAlgebra.ι K) i j`. This file shows that every left
skew derivative `Lₖ` kills `Sᵢⱼ`, provided `[m]_(qᵢ)! ≠ 0`. Since `Sᵢⱼ` has no constant term and
the common kernel of the `Lₖ` modulo `J` consists of the scalars, `Sᵢⱼ` lies in `J`: the quantum
Serre relations hold in `f`. It also records how `Sᵢⱼ` transforms under word reversal and the
diagonal scalings, from which the right skew derivatives kill it as well.

The two computations behind the vanishing are the alternating `q`-binomial identity, for `Lⱼ`,
and the rank-one formula `Lᵢ θᵢ^(n + 1) = qᵢ^n θᵢ^(n)`, which makes the contributions of
neighbouring summands to `Lᵢ Sᵢⱼ` cancel in pairs.

## Main results

* `TauCeti.freeRemove_quantumDividedPower_succ`: `Lᵢ θᵢ^(n + 1) = t^n θᵢ^(n)` when `χ i i = t²`
  and `[n + 1]_t! ≠ 0`.
* `TauCeti.freeRemove_serreSum`, `TauCeti.freeRemoveRight_serreSum`: the left and right skew
  derivatives kill the quantum Serre elements.
* `TauCeti.serreSum_mem_halfRadical`: the quantum Serre elements lie in the radical `J`.
* `TauCeti.serreSum_halfGenerator_eq_zero`: the quantum Serre relations hold in `f`.
* `TauCeti.star_serreSum`, `TauCeti.freeHalfScale_serreSum`: word reversal and the diagonal
  scalings send `Sᵢⱼ` to a scalar multiple of itself; `TauCeti.freeHalfScale_quantumDividedPower_ι`
  does the same for the divided powers `θᵢ^(r)`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §1.4.
* I. Heckenberger, *Lusztig isomorphisms for Drinfel'd doubles of bosonizations of Nichols
  algebras of diagonal type*, J. Algebra 323 (2010), Lemma 4.23.
-/

public section

noncomputable section

namespace TauCeti

open FreeAlgebra Finset QuantizedEnvelopingAlgebra

variable {I X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

/-! ### Skew derivatives of divided powers -/

section DividedPower

variable [DecidableEq I] (χ : I → I → K)

/-- In rank one, the left skew derivative lowers a divided power:
`Lᵢ θᵢ^(n + 1) = t^n θᵢ^(n)` when `χ i i = t²` and `[n + 1]_t! ≠ 0`. -/
theorem freeRemove_quantumDividedPower_succ {i : I} {t : K} (ht : χ i i = t ^ 2) {n : ℕ}
    (hn : quantumFactorial t (n + 1) ≠ 0) :
    freeRemove χ i (quantumDividedPower t (ι K i) (n + 1)) =
      t ^ n • quantumDividedPower t (ι K i) n := by
  have hsub := sub_inv_ne_zero_of_quantumFactorial_ne_zero n.succ_ne_zero hn
  rw [quantumFactorial_succ, mul_ne_zero_iff] at hn
  simp only [quantumDividedPower_def, map_smul, freeRemove_ι_pow_succ, ht, ← pow_mul,
    sum_range_pow_two_mul_eq_pow_mul_quantumInteger hsub, smul_smul, quantumFactorial_succ]
  congr 1
  field_simp [hn.1, hn.2]

end DividedPower

/-! ### Word reversal and the torus on the quantum Serre elements -/

section Symmetry

variable (D : CartanDatum I X Y) (q : K)

/-- Word reversal sends the quantum Serre element `Sᵢⱼ` to `(-1)^(1 - aᵢⱼ) Sᵢⱼ`. -/
theorem star_serreSum (i j : I) :
    star (serreSum D q (ι K) i j) = (-1 : K) ^ D.serreLength i j • serreSum D q (ι K) i j := by
  rw [← MulOpposite.unop_op (star _), ← FreeAlgebra.starHom_apply, map_serreSum]
  simp only [FreeAlgebra.starHom_apply, star_ι, unop_serreSum]

/-- A diagonal scaling `θₗ ↦ cₗ θₗ` multiplies the divided power `θᵢ^(r)` by `cᵢ^r`. -/
theorem freeHalfScale_quantumDividedPower_ι (c : I → K) (t : K) (i : I) (r : ℕ) :
    freeHalfScale c (quantumDividedPower t (ι K i) r) =
      c i ^ r • quantumDividedPower t (ι K i) r := by
  simp only [map_quantumDividedPower, freeHalfScale_ι, quantumDividedPower_smul]

/-- A diagonal scaling `θₗ ↦ cₗ θₗ` multiplies the quantum Serre element `Sᵢⱼ` by
`cᵢ^(1 - aᵢⱼ) cⱼ`, its value on the degree of `Sᵢⱼ`. -/
theorem freeHalfScale_serreSum (c : I → K) (i j : I) :
    freeHalfScale c (serreSum D q (ι K) i j) =
      (c i ^ D.serreLength i j * c j) • serreSum D q (ι K) i j := by
  rw [map_serreSum, ← serreSum_smul]
  simp

end Symmetry

/-! ### The skew derivatives of the quantum Serre elements -/

section Serre

variable [DecidableEq I] (D : CartanDatum I X Y) (q : K)

/-- The left skew derivative `Lⱼ` kills the quantum Serre element `Sᵢⱼ`: it removes the single
`θⱼ`, and the resulting coefficient of `θᵢ^(m)` is the alternating `q`-binomial sum. -/
private theorem freeRemove_serreSum_right {i j : I} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    freeRemove (cartanBraiding D q) j (serreSum D q (ι K) i j) = 0 := by
  set t := q ^ D.symmetrizer i
  set m := D.serreLength i j
  set P : ℕ → FreeAlgebra K I := quantumDividedPower t (ι K i)
  have ht : t ≠ 0 := ne_zero_of_sub_inv_ne_zero
    (sub_inv_ne_zero_of_quantumFactorial_ne_zero (D.serreLength_ne_zero hij) hfac)
  have hχ : cartanBraiding D q j i = t ^ (1 - (m : ℤ)) := by
    rw [← cartanBraiding_symm, cartanBraiding_apply, D.natCast_serreLength hij, sub_sub_cancel]
  have hP : ∀ r, freeRemove (cartanBraiding D q) j (P r) = 0 := fun r => by
    simp [P, quantumDividedPower_def, freeRemove_ι_pow_of_ne _ hij.symm]
  have hσ : ∀ r, freeHalfScale (cartanBraiding D q j) (P r) = (t ^ (1 - (m : ℤ))) ^ r • P r :=
    fun r => by simp only [P, freeHalfScale_quantumDividedPower_ι, hχ]
  have hterm : ∀ r ∈ range (m + 1), freeRemove (cartanBraiding D q) j
      ((-1 : K) ^ r • (P r * ι K j * P (m - r))) =
      ((-1 : K) ^ r * t ^ ((r : ℤ) * (1 - (m : ℤ))) * quantumBinomial t m r) • P m := by
    intro r hr
    have hrm : r + (m - r) = m := Nat.add_sub_of_le (Nat.lt_succ_iff.mp (mem_range.mp hr))
    have hmul : P r * P (m - r) = quantumBinomial t m r • P m := by
      have h := quantumDividedPower_mul_quantumDividedPower (q := t) (ι K i) (a := r)
        (b := m - r) (by rwa [hrm])
      rwa [hrm] at h
    simp only [map_smul, SigmaDerivation.leibniz, hP, hσ, freeRemove_ι, ↓reduceIte,
      zero_mul, mul_zero, zero_add, add_zero, one_mul, smul_mul_assoc, hmul,
      smul_smul, ← zpow_natCast, ← zpow_mul, mul_comm (1 - (m : ℤ)) (r : ℤ), mul_assoc]
  rw [serreSum_def, map_sum, sum_congr rfl hterm, ← sum_smul,
    sum_neg_one_pow_mul_zpow_one_sub_mul_quantumBinomial ht (D.serreLength_ne_zero hij),
    zero_smul]

/-- The left skew derivative `Lᵢ` kills the quantum Serre element `Sᵢⱼ`: the contribution of
differentiating the left factor `θᵢ^(r + 1)` cancels that of differentiating the right factor
`θᵢ^(m - r)` in the neighbouring summand. -/
private theorem freeRemove_serreSum_left {i j : I} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    freeRemove (cartanBraiding D q) i (serreSum D q (ι K) i j) = 0 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (D.serreLength_ne_zero hij)
  have hcartan : D.cartan i j = -(n : ℤ) := by
    have := D.natCast_serreLength hij; rw [hn] at this; push_cast at this; omega
  rw [hn] at hfac
  rw [serreSum_def, hn]
  set t := q ^ D.symmetrizer i
  set L := freeRemove (cartanBraiding D q) i
  set P : ℕ → FreeAlgebra K I := quantumDividedPower t (ι K i)
  have ht : t ≠ 0 := ne_zero_of_sub_inv_ne_zero
    (sub_inv_ne_zero_of_quantumFactorial_ne_zero n.succ_ne_zero hfac)
  -- `Lᵢ θᵢ^(r + 1) = t^r θᵢ^(r)` for `r ≤ n`, and `Lᵢ θᵢ^(0) = 0`.
  have hL : ∀ r ≤ n, L (P (r + 1)) = t ^ r • P r := fun r hr =>
    freeRemove_quantumDividedPower_succ _ (cartanBraiding_self D q i)
      (quantumFactorial_ne_zero_of_le (by omega) hfac)
  have hL0 : L (P 0) = 0 := by simp [L, P]
  have hσ : ∀ r, freeHalfScale (cartanBraiding D q i) (P r) = t ^ (2 * r) • P r := fun r => by
    rw [freeHalfScale_quantumDividedPower_ι, cartanBraiding_self, ← pow_mul]
  -- Expand each summand by the Leibniz rule into a left and a right contribution.
  set a : ℕ → FreeAlgebra K I := fun r => (-1 : K) ^ r • (L (P r) * ι K j * P (n + 1 - r))
  set b : ℕ → FreeAlgebra K I := fun r =>
    ((-1 : K) ^ r * t ^ (2 * r) * t ^ (-(n : ℤ))) • (P r * ι K j * L (P (n + 1 - r)))
  have hterm : ∀ r ∈ range (n + 1 + 1), L ((-1 : K) ^ r • (P r * ι K j * P (n + 1 - r))) =
      b r + a r := fun r _ => by
    simp only [L, map_smul, SigmaDerivation.leibniz, map_mul, hσ, freeHalfScale_ι,
      cartanBraiding_apply, hcartan, freeRemove_ι, hij, ↓reduceIte, mul_zero, zero_add, a, b,
      smul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 2
    ring
  have ha : ∑ r ∈ range (n + 1 + 1), a r = ∑ r ∈ range (n + 1), a (r + 1) := by
    rw [sum_range_succ']; simp [a, hL0]
  have hb : ∑ r ∈ range (n + 1 + 1), b r = ∑ r ∈ range (n + 1), b r := by
    rw [sum_range_succ]; simp [b, hL0]
  rw [map_sum, sum_congr rfl hterm, sum_add_distrib, ha, hb, ← sum_add_distrib]
  refine sum_eq_zero fun r hr => ?_
  have hrn : r ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hr)
  -- The two contributions are `∓ t^r θᵢ^(r) θⱼ θᵢ^(n - r)`.
  have hexp : t ^ (2 * r) * t ^ (-(n : ℤ)) * t ^ (n - r) = t ^ r := by
    rw [← zpow_natCast, ← zpow_natCast t (n - r), ← zpow_natCast t r, ← zpow_add₀ ht,
      ← zpow_add₀ ht]
    congr 1; push_cast [hrn]; ring
  simp only [a, b, show n + 1 - (r + 1) = n - r by omega, show n + 1 - r = n - r + 1 by omega,
    hL r hrn, hL (n - r) (Nat.sub_le n r), smul_mul_assoc, mul_smul_comm, smul_smul, ← add_smul]
  convert zero_smul K (P r * ι K j * P (n - r)) using 2
  linear_combination (-1 : K) ^ r * hexp

/-- **The left skew derivatives kill the quantum Serre elements.** For `i ≠ j` and
`[1 - aᵢⱼ]_(qᵢ)! ≠ 0`, every `Lₖ` for `χ = cartanBraiding D q` vanishes on
`Sᵢⱼ = ∑_(r + s = 1 - aᵢⱼ) (-1)^r θᵢ^(r) θⱼ θᵢ^(s)`. -/
theorem freeRemove_serreSum {i j : I} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) (k : I) :
    freeRemove (cartanBraiding D q) k (serreSum D q (ι K) i j) = 0 := by
  by_cases hki : k = i
  · subst hki
    exact freeRemove_serreSum_left D q hij hfac
  by_cases hkj : k = j
  · subst hkj
    exact freeRemove_serreSum_right D q hij hfac
  rw [serreSum_def, map_sum]
  refine sum_eq_zero fun r _ => ?_
  simp [quantumDividedPower_def, SigmaDerivation.leibniz, freeRemove_ι_pow_of_ne _ hki, hkj]

/-- **The right skew derivatives kill the quantum Serre elements.** For `i ≠ j` and
`[1 - aᵢⱼ]_(qᵢ)! ≠ 0`, every `Rₖ` for `χ = cartanBraiding D q` vanishes on `Sᵢⱼ`. -/
theorem freeRemoveRight_serreSum {i j : I} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) (k : I) :
    freeRemoveRight (cartanBraiding D q) k (serreSum D q (ι K) i j) = 0 := by
  rw [freeRemoveRight_eq_star, star_serreSum, map_smul, freeRemove_serreSum D q hij hfac,
    smul_zero, star_zero]

/-- **The quantum Serre elements lie in the radical of the form.** For `i ≠ j` and
`[1 - aᵢⱼ]_(qᵢ)! ≠ 0`, the element `Sᵢⱼ = ∑_(r + s = 1 - aᵢⱼ) (-1)^r θᵢ^(r) θⱼ θᵢ^(s)` of the
free algebra lies in the radical `J` of Lusztig's form for `χ = cartanBraiding D q`. -/
theorem serreSum_mem_halfRadical {i j : I} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    serreSum D q (ι K) i j ∈ halfRadical (cartanBraiding D q) := by
  have h := (forall_freeRemove_mem_halfRadical_iff (cartanBraiding_symm D q)).1 fun k => by
    rw [freeRemove_serreSum D q hij hfac]; exact zero_mem _
  have h0 : algebraMapInv (serreSum D q (ι K) i j) = 0 := by
    simp [serreSum_def, quantumDividedPower_def, algebraMapInv_ι]
  simpa [h0] using h

/-- **The quantum Serre relations hold in the half quantum algebra `f`.** For `i ≠ j` and
`[1 - aᵢⱼ]_(qᵢ)! ≠ 0`, `∑_(r + s = 1 - aᵢⱼ) (-1)^r θᵢ^(r) θⱼ θᵢ^(s) = 0` in `f`. -/
theorem serreSum_halfGenerator_eq_zero {i j : I} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    serreSum D q (halfGenerator (cartanBraiding D q) (cartanBraiding_symm D q)) i j = 0 := by
  have h := (halfMk_eq_zero_iff (cartanBraiding D q) (cartanBraiding_symm D q) _).2
    (serreSum_mem_halfRadical D q hij hfac)
  simpa only [map_serreSum, halfMk_ι] using h

end Serre

end TauCeti
