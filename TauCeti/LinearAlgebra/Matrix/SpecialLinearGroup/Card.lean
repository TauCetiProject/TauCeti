/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.Ideal.Maps

import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.ZMod.LocalRing
import TauCeti.Data.ZMod.MulCastHom
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.RingTheory.LocalRing.RingHom

/-!
# The order of special linear groups over `ℤ/Nℤ`

The order of `SL₂(ℤ/Nℤ)` is `N³ ∏_{p ∣ N} (1 - 1/p²)`. It is the index of the principal congruence
subgroup `Γ(N)` in `SL₂(ℤ)`, and for `N ≥ 3` twice the index in `PSL₂(ℤ)` of the image of `Γ(N)`,
the order of `SL₂(ℤ/Nℤ)/{±1}`.

The formula comes from two reductions, valid for `SL n` of any size:

* **Prime powers.** The reduction `ℤ/mʳ → ℤ/m` is a surjective local homomorphism with kernel of
  order `m ^ (r - 1)`. Along such a map the orders of `GL n` and of the units are multiplied by
  `|ker| ^ (n²)` and `|ker|`, so that of `SL n = ker det` is multiplied by `|ker| ^ (n² - 1)`.
* **Coprime moduli.** By the Chinese remainder theorem `SL n (ℤ/abℤ) ≃* SL n (ℤ/aℤ) × SL n (ℤ/bℤ)`
  for coprime `a` and `b`.

Combined with `|SL₂(𝔽_p)| = p (p² - 1)` this gives the closed formula, stated with denominators
cleared. At `N = 0` both sides vanish, since `SL n R` is infinite for an infinite ring `R` and
`n ≥ 2`.

## Main results

* `Matrix.SpecialLinearGroup.instInfinite`: `SL n R` is infinite for infinite `R` and `n ≥ 2`.
* `Matrix.natCard_SL_eq_natCard_ker_pow_mul`: `|SL n R| = |ker f| ^ (n² - 1) · |SL n S|` for a
  surjective local homomorphism `f : R →+* S` out of a finite ring.
* `Matrix.natCard_SL_zmod_pow`: `|SL n (ℤ/mʳ)| = m ^ ((r - 1)(n² - 1)) · |SL n (ℤ/m)|`.
* `Matrix.natCard_SL_zmod_mul`: `|SL n (ℤ/ab)| = |SL n (ℤ/a)| · |SL n (ℤ/b)|` for coprime `a`, `b`.
* `Matrix.natCard_SL_zmod_eq_prod_factorization`: the order of `SL n (ℤ/N)` as a product over the
  prime powers exactly dividing `N`.
* `TauCeti.natCard_SL_fin_two`, `TauCeti.natCard_SL_fin_two_zmod`: `|SL₂(𝔽_q)| = q (q² - 1)`.
* `TauCeti.natCard_SL_fin_two_zmod_mul_prod_primeFactors`: `|SL₂(ℤ/N)| = N³ ∏_{p ∣ N} (1 - 1/p²)`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228,
  Springer, 2005, §1.2 (the index of `Γ(N)`).
-/

public section

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

/-- `SL n R` is infinite when `R` is and `n` has two distinct indices `i ≠ j`: the transvections
`1 + c E_{ij}` are pairwise distinct. -/
instance instInfinite {n R : Type*} [Fintype n] [DecidableEq n] [Nontrivial n] [CommRing R]
    [Infinite R] : Infinite (SpecialLinearGroup n R) := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  refine Infinite.of_injective
    (fun c : R ↦ ⟨Matrix.transvection i j c, det_transvection_of_ne i j hij c⟩) fun a b h ↦ ?_
  simpa [Matrix.transvection, hij] using congrFun (congrFun (congrArg Subtype.val h) i) j

end Matrix.SpecialLinearGroup

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The order of `SL n` along a surjective local homomorphism.** If `f : R →+* S` is a
surjective homomorphism of commutative rings that reflects units and `R` is finite, then
`|SL n R| = |ker f| ^ (n² - 1) · |SL n S|`. The general linear groups and the unit groups grow by
the factors `|ker f| ^ (n²)` and `|ker f|`, and `SL n` is the kernel of the surjective determinant.
-/
theorem natCard_SL_eq_natCard_ker_pow_mul {R S : Type*} [CommRing R] [CommRing S] [Finite R]
    (f : R →+* S) [IsLocalHom f] (hf : Function.Surjective f) :
    Nat.card (SpecialLinearGroup n R) =
      Nat.card (RingHom.ker f) ^ (Fintype.card n * Fintype.card n - 1) *
        Nat.card (SpecialLinearGroup n S) := by
  cases isEmpty_or_nonempty n with
  | inl _ =>
    -- Over the empty index type both special linear groups are trivial.
    simp [Nat.card_unique]
  | inr _ =>
    have := Finite.of_surjective f hf
    have hR := card_SL_mul_card_units (n := n) (R := R)
    rw [natCard_GL_eq_natCard_ker_pow_mul f hf, ← card_SL_mul_card_units (n := n) (R := S),
      f.natCard_units_eq_natCard_ker_mul hf] at hR
    have hn : Fintype.card n * Fintype.card n = (Fintype.card n * Fintype.card n - 1) + 1 :=
      (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by simp [Fintype.card_ne_zero]))).symm
    rw [hn, pow_succ] at hR
    refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.card_pos (α := RingHom.ker f))
      (Nat.card_pos (α := Sˣ))) ?_
    rw [hR]
    ring

/-- **The order of `SL n` over `ℤ/mʳ`**: for `r ≠ 0`,
`|SL n (ℤ/mʳ)| = m ^ ((r - 1)(n² - 1)) · |SL n (ℤ/m)|`. At `m = 0` both sides are the order of
`SL n ℤ`, which vanishes when the power of `m` does, as `SL n ℤ` is then infinite. -/
theorem natCard_SL_zmod_pow {m r : ℕ} (hr : r ≠ 0) :
    Nat.card (SpecialLinearGroup n (ZMod (m ^ r))) =
      m ^ ((r - 1) * (Fintype.card n * Fintype.card n - 1)) *
        Nat.card (SpecialLinearGroup n (ZMod m)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [zero_pow hr]
    rcases Nat.eq_zero_or_pos ((r - 1) * (Fintype.card n * Fintype.card n - 1)) with h | h
    · rw [h, pow_zero, one_mul]
    · -- a positive exponent forces two distinct indices, so `SL n ℤ` is infinite
      have hn := Nat.pos_of_ne_zero (right_ne_zero_of_mul h.ne')
      have : Nontrivial n := Fintype.one_lt_card_iff_nontrivial.mp <| by
        by_contra hc
        have := Nat.mul_self_le_mul_self (not_lt.mp hc)
        omega
      rw [zero_pow h.ne', zero_mul, Nat.card_eq_zero_of_infinite]
  have : NeZero m := ⟨hm⟩
  have : NeZero (m ^ r) := ⟨pow_ne_zero _ hm⟩
  have := ZMod.isLocalHom_castHom_pow (n := m) hr
  rw [natCard_SL_eq_natCard_ker_pow_mul _ (ZMod.castHom_surjective (dvd_pow_self m hr)),
    ZMod.natCard_ker_castHom m (pow_sub_one_mul hr m) hm, pow_mul]

/-- **The order of `SL n (ℤ/N)` is multiplicative in `N`**: for coprime `a` and `b`, the Chinese
remainder theorem gives `SL n (ℤ/ab) ≃* SL n (ℤ/a) × SL n (ℤ/b)`. -/
theorem natCard_SL_zmod_mul {a b : ℕ} (hab : a.Coprime b) :
    Nat.card (SpecialLinearGroup n (ZMod (a * b))) =
      Nat.card (SpecialLinearGroup n (ZMod a)) * Nat.card (SpecialLinearGroup n (ZMod b)) := by
  rw [← Nat.card_prod]
  exact Nat.card_congr ((SpecialLinearGroup.mapEquiv n (ZMod.chineseRemainder hab)).trans
    (SpecialLinearGroup.prodEquiv n (ZMod a) (ZMod b))).toEquiv

/-- **The order of `SL n (ℤ/N)`** as a product over the prime factorization of `N ≠ 0`:
`|SL n (ℤ/N)| = ∏_{pᵏ ∥ N} p ^ ((k - 1)(n² - 1)) · |SL n (𝔽_p)|`. -/
theorem natCard_SL_zmod_eq_prod_factorization {N : ℕ} (hN : N ≠ 0) :
    Nat.card (SpecialLinearGroup n (ZMod N)) = N.factorization.prod fun p k ↦
      p ^ ((k - 1) * (Fintype.card n * Fintype.card n - 1)) *
        Nat.card (SpecialLinearGroup n (ZMod p)) := by
  rw [Nat.multiplicative_factorization (fun N ↦ Nat.card (SpecialLinearGroup n (ZMod N)))
    (fun _ _ ↦ natCard_SL_zmod_mul)
    (Nat.card_eq_one_iff_unique.mpr ⟨⟨fun _ _ ↦ Subtype.ext (Subsingleton.elim _ _)⟩, ⟨1⟩⟩) hN]
  refine Finsupp.prod_congr fun p hp ↦ ?_
  exact natCard_SL_zmod_pow (Finsupp.mem_support_iff.mp hp)

end Matrix

namespace TauCeti

/-- **The order of `SL₂` over a field** `𝔽_q` is `q (q² - 1)`. For an infinite field both sides
vanish. -/
theorem natCard_SL_fin_two (F : Type*) [Field F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rcases finite_or_infinite F with _ | _
  · have h := Matrix.card_SL_mul_card_units (n := Fin 2) (R := F)
    rw [natCard_GL_fin_two_eq_sq_sub_one_mul, Nat.card_units] at h
    refine Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt (Finite.one_lt_card (α := F))) ?_
    rw [h]
    ring
  · simp [Nat.card_eq_zero_of_infinite]

/-- **The order of `SL₂(𝔽_p)`** is `p (p² - 1)`. -/
theorem natCard_SL_fin_two_zmod (p : ℕ) [Fact p.Prime] :
    Nat.card SL(2, ZMod p) = p * (p ^ 2 - 1) := by
  rw [natCard_SL_fin_two, Nat.card_zmod]

/-- **The order of `SL₂(ℤ/Nℤ)`** is `N³ ∏_{p ∣ N} (1 - 1/p²)`, here with the denominators
cleared. At `N = 0` both sides vanish, since `SL₂(ℤ)` is infinite. -/
theorem natCard_SL_fin_two_zmod_mul_prod_primeFactors (N : ℕ) :
    Nat.card SL(2, ZMod N) * ∏ p ∈ N.primeFactors, p ^ 2 =
      N ^ 3 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [Nat.card_eq_zero_of_infinite]
  rw [Matrix.natCard_SL_zmod_eq_prod_factorization hN, Finsupp.prod, Nat.support_factorization,
    ← Finset.prod_mul_distrib]
  rw [show N ^ 3 = (N.factorization.prod (· ^ ·)) ^ 3 by
    rw [Nat.prod_factorization_pow_eq_self hN]]
  rw [Finsupp.prod, Nat.support_factorization, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero
    (Finsupp.mem_support_iff.mp (Nat.support_factorization N ▸ hp))
  rw [natCard_SL_fin_two_zmod, hk, Fintype.card_fin, Nat.add_sub_cancel]
  ring

end TauCeti
