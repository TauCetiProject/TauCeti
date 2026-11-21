/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import TauCeti.GroupTheory.Subgroup.IsSubnormal
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.SignedQuotient
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Solvable
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.Data.ZMod.MulCastHom
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Projective
import TauCeti.LinearAlgebra.Projectivization.PSL.Simple

/-!
# Structure, cardinality, signed quotients, and composition factors of `SL₂(ℤ/Nℤ)`

This file develops the finite-group arithmetic of `SL₂(ℤ/Nℤ)` and its signed quotient
`Q_N = SL₂(ℤ/Nℤ) ⧸ {±I}` (`TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N)`, defined over general
rings in `TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.SignedQuotient`):

1. **Chinese remainder decompositions and reduction**: `SL(n, ℤ/MNℤ) ≃* SL(n, ℤ/Mℤ) × SL(n, ℤ/Nℤ)`
   for coprime `M, N`, the prime-power decomposition
   `SL(n, ℤ/Nℤ) ≃* ∀ p : N.primeFactors, SL(n, ℤ/p^{v_p(N)}ℤ)` for `N ≠ 0`, and surjectivity of
   `SL₂(ℤ/Nℤ) →* SL₂(ℤ/Mℤ)` whenever `M ∣ N`.
2. **Prime-power kernel and exact orders**: for `0 < p` and `1 ≤ k`, the kernel of
   `SL₂(ℤ/p^{k+1}ℤ) →* SL₂(ℤ/p^kℤ)` is in explicit bijection with `(ZMod p)³` via matrices
   `I + p^k X` of trace zero (`det(I + p^k X) = 1` since `p^{2k} ≡ 0 mod p^{k+1}`). Combined with
   `|SL₂(𝔽_p)| = p(p² - 1)`, this gives `|SL₂(ℤ/p^kℤ)| = p^{3k - 2}(p² - 1)`, the cleared Euler
   product `|SL₂(ℤ/Nℤ)| · ∏_{p ∣ N} p² = N³ · ∏_{p ∣ N} (p² - 1)`, and the `p`-group / solvability
   structure of `ker(SL₂(ℤ/p^kℤ) →* SL₂(𝔽_p))`.
3. **Orders of `Q_N = SL₂(ℤ/Nℤ) ⧸ {±I}` vs. `PSL₂(ℤ/Nℤ)`**: over composite moduli with square roots
   of `1` other than `±1` (such as `N = 8` or `N = 12`), the center of `SL₂(ℤ/Nℤ)` is strictly
   larger than `{±I}`, so `Q_N` has strictly larger order than `PSL₂(ℤ/Nℤ)` (`192` vs. `96` at
   `N = 8`; `576` vs. `288` at `N = 12`).
4. **Simple composition factors of quotients of `SL₂(ℤ/Nℤ)`**: every nonabelian simple subnormal
   section of a quotient of `SL₂(ℤ/Nℤ)` (`N ≠ 0`) is isomorphic to `PSL₂(𝔽_ℓ)` for a prime
   `ℓ ≥ 5` dividing `N`. Moreover, `PSL₂(𝔽_p) ≃* PSL₂(𝔽_q)` implies `p = q` for all primes `p, q`,
   and no alternating group `A_α` with `6 ≤ Nat.card α` is isomorphic to any `PSL₂(𝔽_ℓ)` or occurs
   as a subnormal section of `SL₂(ℤ/Nℤ)`.

The factorization product and cleared Euler product proofs are adapted from Mathlib's
`Nat.totient_eq_prod_factorization` and `Nat.totient_mul_prod_primeFactors`.

## References

* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton University
  Press, 1971, §1.6.
* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228,
  Springer, 2005, §1.2 and Exercise 1.2.3.
-/

public section

open Matrix

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

/-! ### Chinese remainder decompositions and reduction modulo divisors -/

/-- For coprime `M` and `N`, `SL(n, ℤ/(MN)ℤ)` splits as `SL(n, ℤ/Mℤ) × SL(n, ℤ/Nℤ)`. -/
noncomputable def zmodMulEquivProd (n : Type*) [Fintype n] [DecidableEq n] {M N : ℕ}
    (h : M.Coprime N) :
    SpecialLinearGroup n (ZMod (M * N)) ≃*
      SpecialLinearGroup n (ZMod M) × SpecialLinearGroup n (ZMod N) :=
  (mapEquiv n (ZMod.chineseRemainder h)).trans (prodEquiv n (ZMod M) (ZMod N))

@[simp]
theorem zmodMulEquivProd_apply_fst {n : Type*} [Fintype n] [DecidableEq n] {M N : ℕ}
    (h : M.Coprime N) (A : SpecialLinearGroup n (ZMod (M * N))) :
    (zmodMulEquivProd n h A).1 = map (ZMod.castHom (dvd_mul_right M N) (ZMod M)) A := by
  ext i j
  exact congrArg (· (A i j)) <| Subsingleton.elim
    ((RingHom.fst (ZMod M) (ZMod N)).comp (ZMod.chineseRemainder h).toRingHom)
    (ZMod.castHom (dvd_mul_right M N) (ZMod M))

@[simp]
theorem zmodMulEquivProd_apply_snd {n : Type*} [Fintype n] [DecidableEq n] {M N : ℕ}
    (h : M.Coprime N) (A : SpecialLinearGroup n (ZMod (M * N))) :
    (zmodMulEquivProd n h A).2 = map (ZMod.castHom (dvd_mul_left N M) (ZMod N)) A := by
  ext i j
  exact congrArg (· (A i j)) <| Subsingleton.elim
    ((RingHom.snd (ZMod M) (ZMod N)).comp (ZMod.chineseRemainder h).toRingHom)
    (ZMod.castHom (dvd_mul_left N M) (ZMod N))

/-- For `N ≠ 0`, `SL(n, ℤ/Nℤ)` decomposes as the product of `SL(n, ℤ/p^{v_p(N)}ℤ)` over the prime
factors of `N`. -/
noncomputable def zmodEquivPi (n : Type*) [Fintype n] [DecidableEq n] {N : ℕ} (hN : N ≠ 0) :
    SpecialLinearGroup n (ZMod N) ≃*
      ∀ p : N.primeFactors, SpecialLinearGroup n (ZMod (p ^ N.factorization p)) :=
  (mapEquiv n (ZMod.equivPi N hN)).trans
    (piEquiv n fun p : N.primeFactors ↦ ZMod (p ^ N.factorization p))

@[simp]
theorem zmodEquivPi_apply {n : Type*} [Fintype n] [DecidableEq n] {N : ℕ} (hN : N ≠ 0)
    (A : SpecialLinearGroup n (ZMod N)) (p : N.primeFactors) :
    zmodEquivPi n hN A p =
      map (ZMod.castHom (Nat.ordProj_dvd N p) (ZMod (p ^ N.factorization p))) A := by
  ext i j
  exact congrArg (· (A i j)) <| Subsingleton.elim
    ((Pi.evalRingHom (fun q : N.primeFactors ↦ ZMod (q ^ N.factorization q)) p).comp
      (ZMod.equivPi N hN).toRingHom)
    (ZMod.castHom (Nat.ordProj_dvd N p) (ZMod (p ^ N.factorization p)))

/-- **Strong approximation between finite levels**: whenever `M ∣ N`, the natural reduction
`SL₂(ℤ/Nℤ) →* SL₂(ℤ/Mℤ)` is surjective. -/
theorem map_zmod_castHom_surjective {M N : ℕ} (h : M ∣ N) :
    Function.Surjective
      (map (ZMod.castHom h (ZMod M)) : SL(2, ZMod N) →* SL(2, ZMod M)) := fun A ↦ by
  obtain ⟨γ, rfl⟩ := map_intCast_zmod_surjective (d := M) A
  refine ⟨map (Int.castRingHom (ZMod N)) γ, ?_⟩
  rw [← MonoidHom.comp_apply, map_comp_map,
    RingHom.ext_int ((ZMod.castHom h (ZMod M)).comp (Int.castRingHom (ZMod N)))
      (Int.castRingHom (ZMod M))]

/-! ### Prime-power congruence kernels and cardinality of `SL₂(ℤ/Nℤ)` -/

section PrimePowerKernel

private theorem mulCastHom_mul_eq_zero {p k : ℕ} (hk : 1 ≤ k) (u v : ZMod p) :
    ZMod.mulCastHom (p ^ k) (pow_succ' p k).symm u *
      ZMod.mulCastHom (p ^ k) (pow_succ' p k).symm v = 0 := by
  have hsq := ZMod.ker_castHom_sq_eq_bot (p ^ k) (pow_succ' p k).symm (dvd_pow_self p (by omega))
  rw [pow_two] at hsq
  exact Ideal.mem_bot.mp <| hsq ▸ Ideal.mul_mem_mul
    (RingHom.mem_ker.mpr (ZMod.castHom_mulCastHom (p ^ k) (pow_succ' p k).symm u))
    (RingHom.mem_ker.mpr (ZMod.castHom_mulCastHom (p ^ k) (pow_succ' p k).symm v))

private theorem det_one_add_mulCastHom {p k : ℕ} (hk : 1 ≤ k) (a b c : ZMod p) :
    (!![1 + ZMod.mulCastHom (p ^ k) (pow_succ' p k).symm a,
          ZMod.mulCastHom (p ^ k) (pow_succ' p k).symm b;
        ZMod.mulCastHom (p ^ k) (pow_succ' p k).symm c,
          1 - ZMod.mulCastHom (p ^ k) (pow_succ' p k).symm a] :
        Matrix (Fin 2) (Fin 2) (ZMod (p ^ (k + 1)))).det = 1 := by
  simp only [Matrix.det_fin_two_of]
  linear_combination -mulCastHom_mul_eq_zero hk a a - mulCastHom_mul_eq_zero hk b c

/-- **Explicit parametrization of the `p^k → p^{k+1}` congruence kernel.** For `0 < p` and
`1 ≤ k`, the kernel of `SL₂(ℤ/p^{k+1}ℤ) →* SL₂(ℤ/p^kℤ)` corresponds bijectively to `(ZMod p)³`
via `(a, b, c) ↦ !![1 + p^k a, p^k b; p^k c, 1 - p^k a]`. -/
noncomputable def kerMapZModPowSuccEquiv {p k : ℕ} [NeZero p] (hk : 1 ≤ k) :
    (ZMod p × ZMod p × ZMod p) ≃
      (map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))) :
        SL(2, ZMod (p ^ (k + 1))) →* SL(2, ZMod (p ^ k))).ker :=
  let m : ZMod p →+ ZMod (p ^ (k + 1)) := ZMod.mulCastHom (p ^ k) (pow_succ' p k).symm
  Equiv.ofBijective
    (fun t ↦
      let g : SL(2, ZMod (p ^ (k + 1))) :=
        .mk !![1 + m t.1, m t.2.1; m t.2.2, 1 - m t.1] (det_one_add_mulCastHom hk t.1 t.2.1 t.2.2)
      ⟨g, by
        rw [MonoidHom.mem_ker]
        simp_rw [ext_iff, map_apply_coe, Matrix.map_apply]
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [g, m, -ZMod.castHom_apply, ZMod.castHom_mulCastHom]⟩)
    ⟨fun ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ h ↦ by
      have hinj := ZMod.mulCastHom_injective (p ^ k) (pow_succ' p k).symm
        (pow_ne_zero k (NeZero.ne p))
      have h00 : m a₁ = m a₂ := by simpa [m] using congrArg (fun M ↦ M.val 0 0) h
      have h01 : m b₁ = m b₂ := congrArg (fun M ↦ M.val 0 1) h
      have h10 : m c₁ = m c₂ := congrArg (fun M ↦ M.val 1 0) h
      exact Prod.ext (hinj h00) (Prod.ext (hinj h01) (hinj h10)),
     fun M ↦ by
      have hM : ∀ i j, ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))
          (M.val i j - (1 : Matrix (Fin 2) (Fin 2) _) i j) = 0 := fun i j ↦ by
        rw [map_sub, sub_eq_zero]
        simpa [Matrix.one_apply] using congrArg (fun X : SL(2, ZMod (p ^ k)) ↦ X i j) M.property
      obtain ⟨a, ha⟩ :=
        (ZMod.exact_mulCastHom_castHom (p ^ k) (pow_succ' p k).symm _).mp (by simpa using hM 0 0)
      obtain ⟨b, hb⟩ :=
        (ZMod.exact_mulCastHom_castHom (p ^ k) (pow_succ' p k).symm _).mp (by simpa using hM 0 1)
      obtain ⟨c, hc⟩ :=
        (ZMod.exact_mulCastHom_castHom (p ^ k) (pow_succ' p k).symm _).mp (by simpa using hM 1 0)
      obtain ⟨d, hd⟩ :=
        (ZMod.exact_mulCastHom_castHom (p ^ k) (pow_succ' p k).symm _).mp (by simpa using hM 1 1)
      have h00 : M.val 0 0 = 1 + m a := by linear_combination -ha
      have h11' : M.val 1 1 = 1 + m d := by linear_combination -hd
      have hdet := fin_two_mul_sub_mul_eq_one M.val
      rw [h00, ← hb, ← hc, h11'] at hdet
      have h11 : M.val 1 1 = 1 - m a := by
        rw [h11']
        linear_combination hdet - mulCastHom_mul_eq_zero hk a d + mulCastHom_mul_eq_zero hk b c
      refine ⟨(a, b, c), ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [m, h00, hb, hc, h11]⟩

/-- The `(0, 0)` entry of `kerMapZModPowSuccEquiv hk t` is `1 + p^k · t.1.val` in
`ZMod (p ^ (k + 1))`. -/
@[simp]
theorem kerMapZModPowSuccEquiv_apply_zero_zero {p k : ℕ} [NeZero p] (hk : 1 ≤ k)
    (t : ZMod p × ZMod p × ZMod p) :
    (kerMapZModPowSuccEquiv hk t : SL(2, ZMod (p ^ (k + 1)))) 0 0 =
      1 + (p : ZMod (p ^ (k + 1))) ^ k * (t.1.val : ZMod (p ^ (k + 1))) := by
  unfold kerMapZModPowSuccEquiv
  simp only [Equiv.ofBijective_apply, coe_mk, Matrix.of_apply,
    Matrix.cons_val_zero, ZMod.mulCastHom_apply, ZMod.cast_eq_val, Nat.cast_pow]
  rw [mul_comm]

/-- The `(0, 1)` entry of `kerMapZModPowSuccEquiv hk t` is `p^k · t.2.1.val` in
`ZMod (p ^ (k + 1))`. -/
@[simp]
theorem kerMapZModPowSuccEquiv_apply_zero_one {p k : ℕ} [NeZero p] (hk : 1 ≤ k)
    (t : ZMod p × ZMod p × ZMod p) :
    (kerMapZModPowSuccEquiv hk t : SL(2, ZMod (p ^ (k + 1)))) 0 1 =
      (p : ZMod (p ^ (k + 1))) ^ k * (t.2.1.val : ZMod (p ^ (k + 1))) := by
  unfold kerMapZModPowSuccEquiv
  simp only [Equiv.ofBijective_apply, coe_mk, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ZMod.mulCastHom_apply,
    ZMod.cast_eq_val, Nat.cast_pow]
  rw [mul_comm]

/-- The `(1, 0)` entry of `kerMapZModPowSuccEquiv hk t` is `p^k · t.2.2.val` in
`ZMod (p ^ (k + 1))`. -/
@[simp]
theorem kerMapZModPowSuccEquiv_apply_one_zero {p k : ℕ} [NeZero p] (hk : 1 ≤ k)
    (t : ZMod p × ZMod p × ZMod p) :
    (kerMapZModPowSuccEquiv hk t : SL(2, ZMod (p ^ (k + 1)))) 1 0 =
      (p : ZMod (p ^ (k + 1))) ^ k * (t.2.2.val : ZMod (p ^ (k + 1))) := by
  unfold kerMapZModPowSuccEquiv
  simp only [Equiv.ofBijective_apply, coe_mk, Matrix.of_apply,
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one, ZMod.mulCastHom_apply,
    ZMod.cast_eq_val, Nat.cast_pow]
  rw [mul_comm]

/-- The `(1, 1)` entry of `kerMapZModPowSuccEquiv hk t` is `1 - p^k · t.1.val` in
`ZMod (p ^ (k + 1))`. -/
@[simp]
theorem kerMapZModPowSuccEquiv_apply_one_one {p k : ℕ} [NeZero p] (hk : 1 ≤ k)
    (t : ZMod p × ZMod p × ZMod p) :
    (kerMapZModPowSuccEquiv hk t : SL(2, ZMod (p ^ (k + 1)))) 1 1 =
      1 - (p : ZMod (p ^ (k + 1))) ^ k * (t.1.val : ZMod (p ^ (k + 1))) := by
  unfold kerMapZModPowSuccEquiv
  simp only [Equiv.ofBijective_apply, coe_mk, Matrix.of_apply,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, ZMod.mulCastHom_apply, ZMod.cast_eq_val,
    Nat.cast_pow]
  rw [mul_comm]

/-- For `0 < p` and `1 ≤ k`, the kernel of `SL₂(ℤ/p^{k+1}ℤ) →* SL₂(ℤ/p^kℤ)` has order `p³`. -/
theorem card_ker_map_zmod_pow_succ {p k : ℕ} [NeZero p] (hk : 1 ≤ k) :
    Nat.card (map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))) :
      SL(2, ZMod (p ^ (k + 1))) →* SL(2, ZMod (p ^ k))).ker = p ^ 3 := by
  rw [← Nat.card_congr (kerMapZModPowSuccEquiv hk)]
  simp [ZMod.card, pow_three]

/-- Stepping from `p^k` to `p^{k+1}` (`1 ≤ k`, `0 < p`) multiplies `|SL₂(ℤ/p^kℤ)|` by `p³`. -/
theorem card_fin_two_zmod_pow_succ {p k : ℕ} [NeZero p] (hk : 1 ≤ k) :
    Nat.card SL(2, ZMod (p ^ (k + 1))) = p ^ 3 * Nat.card SL(2, ZMod (p ^ k)) := by
  rw [← Subgroup.card_ker_mul_card_of_surjective
      (map_zmod_castHom_surjective (pow_dvd_pow p (Nat.le_succ k))),
    card_ker_map_zmod_pow_succ hk]

/-- For a prime `p`, `|SL₂(𝔽_p)| = p(p² - 1)`. -/
theorem card_fin_two_zmod_prime {p : ℕ} (hp : p.Prime) :
    Nat.card SL(2, ZMod p) = p * (p ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Matrix.card_SL_field, Fin.prod_univ_two, ZMod.card]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  rw [show p ^ 2 - p = p * (p - 1) by rw [sq, Nat.mul_sub_left_distrib, mul_one],
    ← mul_assoc, Nat.mul_div_cancel _ (Nat.sub_pos_of_lt hp.one_lt), mul_comm]

/-- **Prime-power order of `SL₂`:** for prime `p` and `1 ≤ k`,
`|SL₂(ℤ/p^kℤ)| = p^{3k - 2}(p² - 1)`. -/
theorem card_fin_two_zmod_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    Nat.card SL(2, ZMod (p ^ k)) = p ^ (3 * k - 2) * (p ^ 2 - 1) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  induction k, hk using Nat.le_induction with
  | base => rw [pow_one, card_fin_two_zmod_prime hp]
  | succ m hm ih =>
    rw [card_fin_two_zmod_pow_succ hm, ih, ← mul_assoc, ← pow_add]
    congr 1; exact congrArg (p ^ ·) (by omega)

/-- For prime `p` and `1 ≤ k`, the kernel of reduction `SL₂(ℤ/p^kℤ) →* SL₂(𝔽_p)` has order
`p^{3(k - 1)}`. -/
theorem card_ker_map_zmod_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    Nat.card (map (ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)) :
      SL(2, ZMod (p ^ k)) →* SL(2, ZMod p)).ker = p ^ (3 * (k - 1)) := by
  have hpos : 0 < p * (p ^ 2 - 1) :=
    Nat.mul_pos hp.pos (Nat.sub_pos_of_lt (by nlinarith [hp.two_le]))
  refine Nat.mul_right_cancel hpos ?_
  have hdiv : p ∣ p ^ k := dvd_pow_self p (by omega)
  have hlag := Subgroup.card_ker_mul_card_of_surjective (map_zmod_castHom_surjective hdiv)
  rw [card_fin_two_zmod_prime hp, card_fin_two_zmod_prime_pow hp hk] at hlag
  rw [hlag, ← mul_assoc, ← pow_succ]
  congr 1; exact congrArg (p ^ ·) (by omega)

/-- For prime `p` and `1 ≤ k`, the kernel of `SL₂(ℤ/p^kℤ) →* SL₂(𝔽_p)` is a `p`-group. -/
theorem isPGroup_ker_map_zmod_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    IsPGroup p (map (ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)) :
      SL(2, ZMod (p ^ k)) →* SL(2, ZMod p)).ker :=
  IsPGroup.of_card (card_ker_map_zmod_prime_pow hp hk)

/-- For prime `p` and `1 ≤ k`, the kernel of `SL₂(ℤ/p^kℤ) →* SL₂(𝔽_p)` is solvable. -/
theorem isSolvable_ker_map_zmod_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    Group.IsSolvable (map (ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)) :
      SL(2, ZMod (p ^ k)) →* SL(2, ZMod p)).ker := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  exact (isPGroup_ker_map_zmod_prime_pow hp hk).isNilpotent.to_isSolvable

end PrimePowerKernel

/-! ### Multiplicativity and global formulas for `|SL₂(ℤ/Nℤ)|` -/

/-- `|SL(n, ℤ/(MN)ℤ)| = |SL(n, ℤ/Mℤ)| · |SL(n, ℤ/Nℤ)|` for coprime `M` and `N`. -/
theorem card_zmod_mul_of_coprime (n : Type*) [Fintype n] [DecidableEq n] {M N : ℕ}
    (h : M.Coprime N) :
    Nat.card (SpecialLinearGroup n (ZMod (M * N))) =
      Nat.card (SpecialLinearGroup n (ZMod M)) * Nat.card (SpecialLinearGroup n (ZMod N)) := by
  rw [Nat.card_congr (zmodMulEquivProd n h).toEquiv, Nat.card_prod]

/-- At modulus `1`, `SL(n, ℤ/1ℤ)` is the trivial one-element group. -/
theorem card_zmod_one (n : Type*) [Fintype n] [DecidableEq n] :
    Nat.card (SpecialLinearGroup n (ZMod 1)) = 1 := by
  have : Subsingleton (SpecialLinearGroup n (ZMod 1)) :=
    Subtype.coe_injective.subsingleton
  exact Nat.card_unique

/-- **Factorization formula for `|SL₂(ℤ/Nℤ)|`:** for `N ≠ 0`,
`|SL₂(ℤ/Nℤ)| = ∏_{p^k ∥ N} p^{3k - 2}(p² - 1)`.

Adapted from Mathlib's `Nat.totient_eq_prod_factorization`. -/
theorem card_fin_two_zmod_eq_prod_factorization {N : ℕ} (hN : N ≠ 0) :
    Nat.card SL(2, ZMod N) = N.factorization.prod fun p k ↦ p ^ (3 * k - 2) * (p ^ 2 - 1) := by
  rw [Nat.multiplicative_factorization (fun n ↦ Nat.card SL(2, ZMod n))
    (fun _ _ ↦ card_zmod_mul_of_coprime (Fin 2)) (card_zmod_one (Fin 2)) hN]
  refine Finsupp.prod_congr fun p hp ↦ ?_
  exact card_fin_two_zmod_prime_pow (Nat.prime_of_mem_primeFactors hp)
    (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp))

/-- **Cleared Euler product for `|SL₂(ℤ/Nℤ)|`:**
`|SL₂(ℤ/Nℤ)| · ∏_{p ∣ N} p² = N³ · ∏_{p ∣ N} (p² - 1)` for every `N : ℕ` (both sides vanish at
`N = 0`, where `SL₂(ℤ/0ℤ) = SL₂(ℤ)` is infinite).

Adapted from Mathlib's `Nat.totient_mul_prod_primeFactors`. -/
theorem card_fin_two_zmod_mul_prod_primeFactors_sq (N : ℕ) :
    Nat.card SL(2, ZMod N) * ∏ p ∈ N.primeFactors, p ^ 2 =
      N ^ 3 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  by_cases hN : N = 0
  · subst hN
    have hinf : Infinite SL(2, ZMod 0) :=
      Infinite.of_injective
        (fun m : ZMod 0 ↦ (transvection (by decide : (0 : Fin 2) ≠ 1) m : SL(2, ZMod 0)))
        fun a b h ↦ by
          have := congrArg (fun M : SL(2, ZMod 0) ↦ (M : Matrix (Fin 2) (Fin 2) (ZMod 0)) 0 1) h
          simpa [transvection_coe] using this
    simp [Nat.card_eq_zero_of_infinite]
  rw [card_fin_two_zmod_eq_prod_factorization hN, Nat.prod_factorization_eq_prod_primeFactors]
  conv_rhs =>
    arg 1
    rw [Nat.prod_primeFactors_pow_factorization hN, ← Finset.prod_pow]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  have hk : 1 ≤ N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  rw [mul_right_comm, ← pow_add, ← pow_mul]
  congr 1
  exact congrArg (p ^ ·) (by omega)

/-- At modulus `8`, `|SL₂(ℤ/8ℤ)| = 384`. -/
theorem card_fin_two_zmod_eight : Nat.card SL(2, ZMod 8) = 384 :=
  card_fin_two_zmod_prime_pow (p := 2) (k := 3) Nat.prime_two (by omega)

/-- At modulus `12`, `|SL₂(ℤ/12ℤ)| = 1152`. -/
theorem card_fin_two_zmod_twelve : Nat.card SL(2, ZMod 12) = 1152 := by
  rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, card_zmod_mul_of_coprime (Fin 2) (by decide),
    card_fin_two_zmod_prime_pow Nat.prime_two (by omega), card_fin_two_zmod_prime Nat.prime_three]
  norm_num

/-- `-1 = 1` in `SL₂(ℤ/Nℤ)` if and only if `N ∣ 2`. -/
theorem neg_one_eq_one_zmod_iff {N : ℕ} : (-1 : SL(2, ZMod N)) = 1 ↔ N ∣ 2 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h00 := congrArg (fun M : SL(2, ZMod N) ↦ (M : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0) h
    simp only [coe_neg, coe_one, Matrix.neg_apply, Matrix.one_apply_eq] at h00
    exact (ZMod.natCast_eq_zero_iff 2 N).mp (by rw [Nat.cast_ofNat]; linear_combination -h00)
  · have h2 : (2 : ZMod N) = 0 := by
      simpa only [Nat.cast_ofNat] using (ZMod.natCast_eq_zero_iff 2 N).mpr h
    have hneg : (-1 : ZMod N) = 1 := by linear_combination -h2
    ext i j; fin_cases i <;> fin_cases j <;> simp [hneg]

end Matrix.SpecialLinearGroup

/-! ### Orders of `{±I}` and the signed quotient `Q_N = SL₂(ℤ/Nℤ) ⧸ {±I}` -/

namespace TauCeti.Matrix.SpecialLinearGroup

open _root_.Matrix.SpecialLinearGroup

/-- When `N ∣ 2` (`N = 1` or `N = 2`), `{±I} ≤ SL₂(ℤ/Nℤ)` is trivial of order `1`. -/
theorem card_negOneSubgroup_zmod_eq_one_of_dvd_two {N : ℕ} (h : N ∣ 2) :
    Nat.card (negOneSubgroup (Fin 2) (ZMod N)) = 1 := by
  rw [Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall]
  intro g hg
  rcases mem_negOneSubgroup_iff.mp hg with rfl | rfl
  · rfl
  · exact neg_one_eq_one_zmod_iff.mpr h

/-- When `¬ (N ∣ 2)`, `{±I} ≤ SL₂(ℤ/Nℤ)` has order `2`. -/
theorem card_negOneSubgroup_zmod_eq_two {N : ℕ} (h : ¬ N ∣ 2) :
    Nat.card (negOneSubgroup (Fin 2) (ZMod N)) = 2 := by
  have hcard : Nat.card (negOneSubgroup (Fin 2) (ZMod N)) =
      Nat.card ({1, -1} : Set SL(2, ZMod N)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ by simp)
  rw [hcard, Nat.card_coe_set_eq]
  exact Set.ncard_pair fun heq ↦ h (neg_one_eq_one_zmod_iff.mp heq.symm)

end TauCeti.Matrix.SpecialLinearGroup

namespace TauCeti.Matrix.SignedQuotient

open _root_.Matrix.SpecialLinearGroup
open TauCeti.Matrix.SpecialLinearGroup

/-- When `N ∣ 2` (`N = 1` or `N = 2`), `-I = I` modulo `N`, so `|Q_N| = |SL₂(ℤ/Nℤ)|`. -/
theorem card_fin_two_zmod_of_dvd_two {N : ℕ} (h : N ∣ 2) :
    Nat.card (SignedQuotient (Fin 2) (ZMod N)) = Nat.card SL(2, ZMod N) := by
  have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup (negOneSubgroup (Fin 2) (ZMod N))
  rw [card_negOneSubgroup_zmod_eq_one_of_dvd_two h, mul_one] at hlag; exact hlag.symm

/-- When `¬ (N ∣ 2)` (in particular for all `N ≥ 3`, and at `N = 0`), `2 · |Q_N| = |SL₂(ℤ/Nℤ)|`. -/
theorem two_mul_card_fin_two_zmod_of_not_dvd_two {N : ℕ} (h : ¬ N ∣ 2) :
    2 * Nat.card (SignedQuotient (Fin 2) (ZMod N)) = Nat.card SL(2, ZMod N) := by
  have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup (negOneSubgroup (Fin 2) (ZMod N))
  rw [card_negOneSubgroup_zmod_eq_two h, mul_comm] at hlag; exact hlag.symm

/-- For `N ≥ 3`, `2 · |Q_N| = |SL₂(ℤ/Nℤ)|`. -/
theorem two_mul_card_fin_two_zmod {N : ℕ} (hN : 3 ≤ N) :
    2 * Nat.card (SignedQuotient (Fin 2) (ZMod N)) = Nat.card SL(2, ZMod N) :=
  two_mul_card_fin_two_zmod_of_not_dvd_two fun h ↦ by have := Nat.le_of_dvd two_pos h; omega

/-- **Cleared Euler product for `|Q_N|` at `N ≥ 3`:**
`2 · |Q_N| · ∏_{p ∣ N} p² = N³ · ∏_{p ∣ N} (p² - 1)`. -/
theorem two_mul_card_fin_two_zmod_mul_prod_primeFactors_sq {N : ℕ} (hN : 3 ≤ N) :
    2 * Nat.card (SignedQuotient (Fin 2) (ZMod N)) * ∏ p ∈ N.primeFactors, p ^ 2 =
      N ^ 3 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  rw [two_mul_card_fin_two_zmod hN, card_fin_two_zmod_mul_prod_primeFactors_sq]

/-- At level `1`, the signed quotient `Q_1 = SL₂(ℤ/1ℤ) ⧸ {±I}` is trivial of order `1`. -/
@[simp]
theorem card_fin_two_zmod_one : Nat.card (SignedQuotient (Fin 2) (ZMod 1)) = 1 := by
  rw [card_fin_two_zmod_of_dvd_two (one_dvd 2), card_zmod_one]

/-- At level `2`, `-I = I` modulo `2`, so the signed quotient `Q_2 = SL₂(ℤ/2ℤ) ⧸ {±I}` has order
`6 = |SL₂(𝔽₂)|`. -/
@[simp]
theorem card_fin_two_zmod_two : Nat.card (SignedQuotient (Fin 2) (ZMod 2)) = 6 := by
  rw [card_fin_two_zmod_of_dvd_two dvd_rfl, card_fin_two_zmod_prime Nat.prime_two]; norm_num

/-- At level `8`, the signed quotient `Q_8 = SL₂(ℤ/8ℤ) ⧸ {±I}` has order `192 = |SL₂(ℤ/8ℤ)| / 2`,
strictly larger than `|PSL₂(ℤ/8ℤ)| = 96` because `±3I` are extra central elements. -/
theorem card_fin_two_zmod_eight : Nat.card (SignedQuotient (Fin 2) (ZMod 8)) = 192 := by
  have h := two_mul_card_fin_two_zmod (N := 8) (by omega)
  rw [_root_.Matrix.SpecialLinearGroup.card_fin_two_zmod_eight] at h; omega

/-- At level `12`, the signed quotient `Q_12 = SL₂(ℤ/12ℤ) ⧸ {±I}` has order
`576 = |SL₂(ℤ/12ℤ)| / 2`, strictly larger than `|PSL₂(ℤ/12ℤ)| = 288` because `±5I` are extra
central elements. -/
theorem card_fin_two_zmod_twelve : Nat.card (SignedQuotient (Fin 2) (ZMod 12)) = 576 := by
  have h := two_mul_card_fin_two_zmod (N := 12) (by omega)
  rw [_root_.Matrix.SpecialLinearGroup.card_fin_two_zmod_twelve] at h; omega

end TauCeti.Matrix.SignedQuotient

/-! ### Orders, rigidity, and non-isomorphism with alternating groups for `PSL₂(ℤ/Nℤ)` -/

namespace Matrix.ProjectiveSpecialLinearGroup

open Matrix.SpecialLinearGroup

/-- Over `𝔽₂`, the center of `SL₂(𝔽₂)` is trivial, so `|PSL₂(𝔽₂)| = |SL₂(𝔽₂)| = 6`. -/
theorem card_fin_two_zmod_two : Nat.card PSL(2, ZMod 2) = 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.card_congr (TauCeti.Matrix.SignedQuotient.equivPSL (ZMod 2)).toEquiv,
    TauCeti.Matrix.SignedQuotient.card_fin_two_zmod_two]

/-- For an odd prime `p`, `2 · |PSL₂(𝔽_p)| = p(p² - 1)`. -/
theorem two_mul_card_fin_two_zmod_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * Nat.card PSL(2, ZMod p) = p * (p ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← Nat.card_congr (TauCeti.Matrix.SignedQuotient.equivPSL (ZMod p)).toEquiv,
    TauCeti.Matrix.SignedQuotient.two_mul_card_fin_two_zmod (by have := hp.two_le; omega),
    card_fin_two_zmod_prime hp]

/-- At modulus `8`, `ZMod 8` has four square roots of unity (`±1, ±3`), so
`|PSL₂(ℤ/8ℤ)| = |SL₂(ℤ/8ℤ)| / 4 = 96`, half the order `192` of the signed quotient `Q_8`. -/
theorem card_fin_two_zmod_eight : Nat.card PSL(2, ZMod 8) = 96 := by
  have h := card_mul_card_rootsOfUnity 2 two_pos (ZMod 8)
  have h4 : Nat.card (rootsOfUnity 2 (ZMod 8)) = 4 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun u : (ZMod 8)ˣ ↦ mem_rootsOfUnity 2 u),
      Nat.card_eq_fintype_card]
    decide
  rw [SpecialLinearGroup.card_fin_two_zmod_eight, h4] at h
  omega

/-- At modulus `12`, `ZMod 12` has four square roots of unity (`±1, ±5`), so
`|PSL₂(ℤ/12ℤ)| = |SL₂(ℤ/12ℤ)| / 4 = 288`, half the order `576` of the signed quotient `Q_12`. -/
theorem card_fin_two_zmod_twelve : Nat.card PSL(2, ZMod 12) = 288 := by
  have h := card_mul_card_rootsOfUnity 2 two_pos (ZMod 12)
  have h4 : Nat.card (rootsOfUnity 2 (ZMod 12)) = 4 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun u : (ZMod 12)ˣ ↦ mem_rootsOfUnity 2 u),
      Nat.card_eq_fintype_card]
    decide
  rw [SpecialLinearGroup.card_fin_two_zmod_twelve, h4] at h
  omega

/-- **Distinct primes have non-isomorphic projective special linear groups `PSL₂(𝔽_p)`:** if
`PSL₂(𝔽_p) ≃* PSL₂(𝔽_q)` with `p, q` prime, then `p = q`. -/
theorem eq_of_fin_two_zmod_mulEquiv {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (e : PSL(2, ZMod p) ≃* PSL(2, ZMod q)) : p = q := by
  wlog hpq : p ≤ q generalizing p q
  · exact (this hq hp e.symm (by omega)).symm
  rcases hpq.eq_or_lt with rfl | hlt
  · rfl
  · exfalso
    have hcard : Nat.card PSL(2, ZMod p) = Nat.card PSL(2, ZMod q) := Nat.card_congr e.toEquiv
    have hq2 : q ≠ 2 := by have := hp.two_le; omega
    have hq_eq := two_mul_card_fin_two_zmod_prime hq hq2
    by_cases hp2 : p = 2
    · subst hp2
      rw [← hcard, card_fin_two_zmod_two] at hq_eq
      have : 3 * (3 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
        Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1)
      omega
    · have hp_eq := two_mul_card_fin_two_zmod_prime hp hp2
      have h1 : 1 < p ^ 2 := by nlinarith [hp.two_le]
      have h2 : p ^ 2 < q ^ 2 := by nlinarith [hp.two_le]
      have : p * (p ^ 2 - 1) < q * (q ^ 2 - 1) :=
        (Nat.mul_lt_mul_of_pos_right hlt (by omega)).trans
          (Nat.mul_lt_mul_of_pos_left (by omega) hq.pos)
      omega

/-- **No alternating group of degree `≥ 6` is isomorphic to any `PSL₂(𝔽_ℓ)`.** If `ℓ` divided
`|A_n| = n!/2`, primality would give `ℓ ≤ n`, forcing `|PSL₂(𝔽_ℓ)| = ℓ(ℓ² - 1)/2 < n³/2 ≤ n!/2`
for `n ≥ 6`. -/
theorem isEmpty_alternatingGroup_mulEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 6 ≤ Nat.card α) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    IsEmpty (alternatingGroup α ≃* PSL(2, ZMod ℓ)) := ⟨fun e ↦ by
  set n := Nat.card α
  have : Nontrivial α := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card]; omega
  have halt : 2 * Nat.card (alternatingGroup α) = n.factorial := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm]
  have hcard : Nat.card (alternatingGroup α) = Nat.card PSL(2, ZMod ℓ) := Nat.card_congr e.toEquiv
  have h6 : 720 ≤ n.factorial :=
    (by decide : 720 = (6 : ℕ).factorial).trans_le (Nat.factorial_le hα)
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2; rw [hcard, card_fin_two_zmod_two] at halt; omega
  · have hpsl := two_mul_card_fin_two_zmod_prime hℓ hℓ2
    have hℓ_le : ℓ ≤ n := hℓ.dvd_factorial.mp ⟨ℓ ^ 2 - 1, by omega⟩
    have hsub : ℓ ^ 2 - 1 < n ^ 2 := by
      have : 1 ≤ ℓ ^ 2 := Nat.one_le_pow 2 ℓ hℓ.pos
      have : ℓ ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hℓ_le 2
      omega
    have hlt_cube : ℓ * (ℓ ^ 2 - 1) < n ^ 3 := by
      calc ℓ * (ℓ ^ 2 - 1) < ℓ * n ^ 2 := Nat.mul_lt_mul_of_pos_left hsub hℓ.pos
        _ ≤ n * n ^ 2 := Nat.mul_le_mul_right (n ^ 2) hℓ_le
        _ = n ^ 3 := by ring
    have hcube : ∀ m, 6 ≤ m → m ^ 3 ≤ m.factorial := fun m hm ↦ by
      induction m, hm using Nat.le_induction with
      | base => decide
      | succ k hk ih =>
        rw [Nat.factorial_succ]
        have : (k + 1) ^ 2 ≤ k ^ 3 := by nlinarith
        calc (k + 1) ^ 3 = (k + 1) * (k + 1) ^ 2 := by ring
          _ ≤ (k + 1) * k ^ 3 := Nat.mul_le_mul_left _ this
          _ ≤ (k + 1) * k.factorial := Nat.mul_le_mul_left _ ih
    have := hcube n hα; omega⟩

end Matrix.ProjectiveSpecialLinearGroup

/-! ### Classification of nonabelian simple subnormal sections of `SL₂(ℤ/Nℤ)` and its quotients -/

namespace Matrix.SpecialLinearGroup

/-- **Classification of nonabelian simple composition factors of `SL₂(ℤ/Nℤ)`.** For `N ≠ 0`,
every nonabelian simple group `S` occurring as a subnormal section of `SL₂(ℤ/Nℤ)` is isomorphic to
`PSL₂(𝔽_ℓ)` for a prime `ℓ ≥ 5` dividing `N`. -/
theorem exists_prime_dvd_psl_mulEquiv_of_hasSubnormalSection {N : ℕ} (hN : N ≠ 0) {S : Type*}
    [Group S] [IsSimpleGroup S] (hnc : ¬ IsMulCommutative S)
    (hS : TauCeti.HasSubnormalSection SL(2, ZMod N) S) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ ℓ ∣ N ∧ Nonempty (S ≃* PSL(2, ZMod ℓ)) := by
  obtain ⟨⟨ℓ, hℓ_mem⟩, hℓ_sec⟩ := (hS.congr_left (zmodEquivPi (Fin 2) hN)).exists_of_pi
  obtain ⟨hℓ_prime, hℓ_dvd, _⟩ := Nat.mem_primeFactors.mp hℓ_mem
  have hk : 1 ≤ N.factorization ℓ :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by simpa using hℓ_mem))
  let π : SL(2, ZMod (ℓ ^ N.factorization ℓ)) →* SL(2, ZMod ℓ) :=
    map (ZMod.castHom (dvd_pow_self ℓ (by omega)) (ZMod ℓ))
  have hSLℓ : TauCeti.HasSubnormalSection SL(2, ZMod ℓ) S := by
    rcases hℓ_sec.or_of_normal π.ker with hker | hquot
    · have := isSolvable_ker_map_zmod_prime_pow hℓ_prime hk
      exact False.elim (hnc hker.isMulCommutative_of_isSolvable)
    · exact hquot.congr_left (QuotientGroup.quotientKerEquivOfSurjective π
        (map_zmod_castHom_surjective (dvd_pow_self ℓ (by omega))))
  have : Fact ℓ.Prime := ⟨hℓ_prime⟩
  have hℓ5 : 5 ≤ ℓ := by
    by_contra! hlt5
    have hle3 : Nat.card (ZMod ℓ) ≤ 3 := by
      rw [Nat.card_zmod]; rcases hℓ_prime.eq_two_or_odd with rfl | hodd <;> omega
    have := TauCeti.Matrix.SpecialLinearGroup.isSolvable_fin_two_of_natCard_le_three (ZMod ℓ) hle3
    exact hnc hSLℓ.isMulCommutative_of_isSolvable
  rcases hSLℓ.or_of_normal (Subgroup.center SL(2, ZMod ℓ)) with hcen | hpsl
  · exact False.elim (hnc hcen.isMulCommutative_of_isSolvable)
  · have : IsSimpleGroup PSL(2, ZMod ℓ) :=
      ProjectiveSpecialLinearGroup.isSimpleGroup_of_four_le_natCard (by rw [Nat.card_zmod]; omega)
    exact ⟨ℓ, hℓ_prime, hℓ5, hℓ_dvd, hpsl.nonempty_mulEquiv_of_isSimpleGroup⟩

/-- **No alternating group `A_α` of degree `≥ 6` occurs as a subnormal section of `SL₂(ℤ/Nℤ)`**
(`N ≠ 0`). -/
theorem not_hasSubnormalSection_alternatingGroup {N : ℕ} (hN : N ≠ 0) {α : Type*}
    [Fintype α] [DecidableEq α] (hα : 6 ≤ Nat.card α) :
    ¬ TauCeti.HasSubnormalSection SL(2, ZMod N) (alternatingGroup α) := fun hsec ↦ by
  have h5 : 5 ≤ Nat.card α := by omega
  have hsimp := alternatingGroup.isSimpleGroup h5
  have := hsimp.toNontrivial
  have hnc : ¬ IsMulCommutative (alternatingGroup α) := fun _ ↦
    bot_ne_top ((commutator_eq_bot (G := alternatingGroup α)).symm.trans
      (commutator_alternatingGroup_eq_top h5))
  obtain ⟨ℓ, hℓ, -, -, ⟨e⟩⟩ := exists_prime_dvd_psl_mulEquiv_of_hasSubnormalSection hN hnc hsec
  exact (ProjectiveSpecialLinearGroup.isEmpty_alternatingGroup_mulEquiv hα hℓ).false e

/-- **Quotient form of the composition-factor classification for `SL₂(ℤ/Nℤ)`.** Every nonabelian
simple subnormal section `H ⧸ K.subgroupOf H` of any quotient `Q` of `SL₂(ℤ/Nℤ)` (`N ≠ 0`) is
isomorphic to `PSL₂(𝔽_ℓ)` for a prime `ℓ ≥ 5` dividing `N`. -/
theorem exists_prime_dvd_psl_mulEquiv_of_surjective {N : ℕ} (hN : N ≠ 0) {Q : Type*} [Group Q]
    {f : SL(2, ZMod N) →* Q} (hf : Function.Surjective f) {H K : Subgroup Q}
    (hH : H.IsSubnormal) (hKH : K ≤ H) [(K.subgroupOf H).Normal]
    [IsSimpleGroup (H ⧸ K.subgroupOf H)] (hnc : ¬ IsMulCommutative (H ⧸ K.subgroupOf H)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ ℓ ∣ N ∧ Nonempty ((H ⧸ K.subgroupOf H) ≃* PSL(2, ZMod ℓ)) :=
  exists_prime_dvd_psl_mulEquiv_of_hasSubnormalSection hN hnc
    ((TauCeti.HasSubnormalSection.mk_quotient hH hKH).of_surjective hf)

end Matrix.SpecialLinearGroup

namespace TauCeti.Matrix.SignedQuotient

/-- Every nonabelian simple subnormal section of any quotient of `SignedQuotient (Fin 2) (ZMod N)`
(`N ≠ 0`) is isomorphic to `PSL₂(𝔽_ℓ)` for a prime `ℓ ≥ 5` dividing `N`. -/
theorem exists_prime_dvd_psl_mulEquiv_of_surjective {N : ℕ} (hN : N ≠ 0) {Q : Type*} [Group Q]
    {f : SignedQuotient (Fin 2) (ZMod N) →* Q} (hf : Function.Surjective f) {H K : Subgroup Q}
    (hH : H.IsSubnormal) (hKH : K ≤ H) [(K.subgroupOf H).Normal]
    [IsSimpleGroup (H ⧸ K.subgroupOf H)] (hnc : ¬ IsMulCommutative (H ⧸ K.subgroupOf H)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ ℓ ∣ N ∧ Nonempty ((H ⧸ K.subgroupOf H) ≃* PSL(2, ZMod ℓ)) :=
  _root_.Matrix.SpecialLinearGroup.exists_prime_dvd_psl_mulEquiv_of_surjective hN
    (f := f.comp (QuotientGroup.mk' _)) (hf.comp (QuotientGroup.mk'_surjective _)) hH hKH hnc

end TauCeti.Matrix.SignedQuotient
