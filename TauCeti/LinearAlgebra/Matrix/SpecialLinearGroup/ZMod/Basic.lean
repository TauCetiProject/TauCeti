/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.SignedQuotient
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.Data.ZMod.MulCastHom
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

/-!
# Structure, cardinality, and signed quotients of `SL₂(ℤ/Nℤ)`

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
3. **Orders of `Q_N = SL₂(ℤ/Nℤ) ⧸ {±I}` and `PSL₂(𝔽_p)`**: at `N ∣ 2`, `-I = I` so `|Q_N| = |SL₂|`
   (`1` at `N = 1`, `6` at `N = 2`, with `|PSL₂(𝔽₂)| = 6`); for `N ≥ 3`, `2 · |Q_N| = |SL₂(ℤ/Nℤ)|`,
   giving the cleared Euler product `2 · |Q_N| · ∏_{p ∣ N} p² = N³ · ∏_{p ∣ N} (p² - 1)` and
   `2 · |PSL₂(𝔽_p)| = p(p² - 1)` for odd primes `p`.

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

/-- The first component of `zmodMulEquivProd n h A` is reduction modulo `M`. -/
@[simp]
theorem zmodMulEquivProd_apply_fst {n : Type*} [Fintype n] [DecidableEq n] {M N : ℕ}
    (h : M.Coprime N) (A : SpecialLinearGroup n (ZMod (M * N))) :
    (zmodMulEquivProd n h A).1 = map (ZMod.castHom (dvd_mul_right M N) (ZMod M)) A := by
  ext i j
  exact congrArg (· (A i j)) <| Subsingleton.elim
    ((RingHom.fst (ZMod M) (ZMod N)).comp (ZMod.chineseRemainder h).toRingHom)
    (ZMod.castHom (dvd_mul_right M N) (ZMod M))

/-- The second component of `zmodMulEquivProd n h A` is reduction modulo `N`. -/
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

/-- The `p`-th component of `zmodEquivPi n hN A` is reduction modulo `p ^ N.factorization p`. -/
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
      Infinite.of_injective _
        (Matrix.SpecialLinearGroup.transvection_injective (by decide : (0 : Fin 2) ≠ 1))
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
  rw [negOneSubgroup_def, Nat.card_zpowers, neg_one_eq_one_zmod_iff.mpr h, orderOf_one]

/-- When `¬ (N ∣ 2)`, `{±I} ≤ SL₂(ℤ/Nℤ)` has order `2`. -/
theorem card_negOneSubgroup_zmod_eq_two {N : ℕ} (h : ¬ N ∣ 2) :
    Nat.card (negOneSubgroup (Fin 2) (ZMod N)) = 2 := by
  rw [negOneSubgroup_def, Nat.card_zpowers]
  exact orderOf_eq_prime neg_one_sq fun heq ↦ h (neg_one_eq_one_zmod_iff.mp heq)

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

end TauCeti.Matrix.SignedQuotient

/-! ### Prime-field orders of `PSL₂(𝔽_p)` -/

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

end Matrix.ProjectiveSpecialLinearGroup
