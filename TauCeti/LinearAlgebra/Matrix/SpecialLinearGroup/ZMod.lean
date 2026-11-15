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
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Solvable
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.LinearAlgebra.Projectivization.PSL.Simple

/-!
# Structure, cardinality, signed quotients, and composition factors of `SL₂(ℤ/Nℤ)`

This file develops the finite-group arithmetic of `SL₂(ℤ/Nℤ)` and its signed quotient
`Q_N = SL₂(ℤ/Nℤ) ⧸ {±I}` (`Matrix.SignedQuotient (Fin 2) (ZMod N)`):

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
3. **The signed quotient `Q_N = SL₂(ℤ/Nℤ) ⧸ {±I}`**: over composite moduli with square roots of `1`
   other than `±1` (such as `N = 8` or `N = 12`), the center of `SL₂(ℤ/Nℤ)` is strictly larger than
   `{±I}`, so `Q_N` has strictly larger order than `PSL₂(ℤ/Nℤ)` (`192` vs. `96` at `N = 8`; `576`
   vs. `288` at `N = 12`). Over domains (`N` prime or `ℤ`), `Q_N ≃* PSL₂(R)`.
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
  have heq : (RingHom.fst (ZMod M) (ZMod N)).comp (ZMod.chineseRemainder h).toRingHom =
      ZMod.castHom (dvd_mul_right M N) (ZMod M) := Subsingleton.elim _ _
  ext i j
  exact congrArg (fun f : ZMod (M * N) →+* ZMod M ↦ f (A i j)) heq

@[simp]
theorem zmodMulEquivProd_apply_snd {n : Type*} [Fintype n] [DecidableEq n] {M N : ℕ}
    (h : M.Coprime N) (A : SpecialLinearGroup n (ZMod (M * N))) :
    (zmodMulEquivProd n h A).2 = map (ZMod.castHom (dvd_mul_left N M) (ZMod N)) A := by
  have heq : (RingHom.snd (ZMod M) (ZMod N)).comp (ZMod.chineseRemainder h).toRingHom =
      ZMod.castHom (dvd_mul_left N M) (ZMod N) := Subsingleton.elim _ _
  ext i j
  exact congrArg (fun f : ZMod (M * N) →+* ZMod N ↦ f (A i j)) heq

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
  let f₁ : ZMod N →+* ZMod (p ^ N.factorization p) :=
    (Pi.evalRingHom (fun q : N.primeFactors ↦ ZMod (q ^ N.factorization q)) p).comp
      (ZMod.equivPi N hN).toRingHom
  have heq : f₁ = ZMod.castHom (Nat.ordProj_dvd N p) (ZMod (p ^ N.factorization p)) :=
    Subsingleton.elim _ _
  ext i j
  exact congrArg (fun f : ZMod N →+* ZMod (p ^ N.factorization p) ↦ f (A i j)) heq

/-- **Strong approximation between finite levels**: whenever `M ∣ N`, the natural reduction
`SL₂(ℤ/Nℤ) →* SL₂(ℤ/Mℤ)` is surjective. -/
theorem map_zmod_castHom_surjective {M N : ℕ} (h : M ∣ N) :
    Function.Surjective
      (map (ZMod.castHom h (ZMod M)) : SL(2, ZMod N) →* SL(2, ZMod M)) := by
  intro A
  obtain ⟨γ, rfl⟩ := map_intCast_zmod_surjective (d := M) A
  refine ⟨map (Int.castRingHom (ZMod N)) γ, ?_⟩
  rw [← MonoidHom.comp_apply, map_comp_map,
    RingHom.ext_int ((ZMod.castHom h (ZMod M)).comp (Int.castRingHom (ZMod N)))
      (Int.castRingHom (ZMod M))]

/-! ### Prime-power congruence kernels and cardinality of `SL₂(ℤ/Nℤ)` -/

section PrimePowerKernel

/-- Lift `u : ZMod p` into the `p^k`-torsion ideal of `ZMod (p^(k+1))` as `(p^k * u.val)`. -/
private def liftMulPow (p k : ℕ) (u : ZMod p) : ZMod (p ^ (k + 1)) :=
  ((p ^ k * u.val : ℕ) : ZMod (p ^ (k + 1)))

private theorem liftMulPow_injective {p k : ℕ} [NeZero p] :
    Function.Injective (liftMulPow p k) := by
  intro u v huv
  have hp : 0 < p := NeZero.pos p
  have hpk : 0 < p ^ k := pow_pos hp k
  have hu : p ^ k * u.val < p ^ (k + 1) := by
    rw [pow_succ]
    exact Nat.mul_lt_mul_of_pos_left u.val_lt hpk
  have hv : p ^ k * v.val < p ^ (k + 1) := by
    rw [pow_succ]
    exact Nat.mul_lt_mul_of_pos_left v.val_lt hpk
  have hval := congrArg ZMod.val huv
  rw [liftMulPow, liftMulPow, ZMod.val_natCast_of_lt hu, ZMod.val_natCast_of_lt hv] at hval
  exact ZMod.val_injective p (Nat.eq_of_mul_eq_mul_left hpk hval)

private theorem castHom_liftMulPow {p k : ℕ} (u : ZMod p) :
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) (liftMulPow p k u) = 0 := by
  rw [liftMulPow, map_natCast, Nat.cast_mul, ZMod.natCast_self, zero_mul]

private theorem exists_liftMulPow_of_castHom_eq_zero {p k : ℕ} [NeZero p]
    {x : ZMod (p ^ (k + 1))}
    (hx : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) x = 0) :
    ∃ u : ZMod p, liftMulPow p k u = x := by
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  have hxval : ((x.val : ℕ) : ZMod (p ^ k)) = 0 := by
    rw [← map_natCast (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))),
      ZMod.natCast_zmod_val, hx]
  obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff x.val (p ^ k)).mp hxval
  have hlt : p ^ k * m < p ^ k * p := by
    rw [← hm, ← pow_succ]
    exact x.val_lt
  have hmp : m < p := Nat.lt_of_mul_lt_mul_left hlt
  refine ⟨(m : ZMod p), ?_⟩
  rw [liftMulPow, ZMod.val_natCast_of_lt hmp, ← hm, ZMod.natCast_zmod_val]

private theorem liftMulPow_mul_liftMulPow {p k : ℕ} (hk : 1 ≤ k) (u v : ZMod p) :
    liftMulPow p k u * liftMulPow p k v = 0 := by
  rw [liftMulPow, liftMulPow, ← Nat.cast_mul]
  refine (ZMod.natCast_eq_zero_iff _ _).mpr ?_
  have hdvd : p ^ (k + 1) ∣ p ^ k * p ^ k := by
    rw [← pow_add]
    exact pow_dvd_pow p (by omega)
  exact hdvd.trans ⟨u.val * v.val, by ring⟩

private theorem det_one_add_liftMulPow {p k : ℕ} (hk : 1 ≤ k) (a b c : ZMod p) :
    (!![1 + liftMulPow p k a, liftMulPow p k b;
        liftMulPow p k c, 1 - liftMulPow p k a] :
        Matrix (Fin 2) (Fin 2) (ZMod (p ^ (k + 1)))).det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have haa := liftMulPow_mul_liftMulPow hk a a
  have hbc := liftMulPow_mul_liftMulPow hk b c
  linear_combination -haa - hbc

private theorem choose_exists_liftMulPow_eq {p k : ℕ} [NeZero p] {x : ZMod (p ^ (k + 1))}
    {u : ZMod p} {hx : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) x = 0}
    (hu : x = liftMulPow p k u) :
    (exists_liftMulPow_of_castHom_eq_zero hx).choose = u :=
  liftMulPow_injective <| (exists_liftMulPow_of_castHom_eq_zero hx).choose_spec.trans hu

/-- **Explicit parametrization of the `p^k → p^{k+1}` congruence kernel.** For `0 < p` and
`1 ≤ k`, the kernel of `SL₂(ℤ/p^{k+1}ℤ) →* SL₂(ℤ/p^kℤ)` corresponds bijectively to `(ZMod p)³`
via `(a, b, c) ↦ !![1 + p^k a, p^k b; p^k c, 1 - p^k a]`. -/
noncomputable def kerMapZModPowSuccEquiv {p k : ℕ} [NeZero p] (hk : 1 ≤ k) :
    (ZMod p × ZMod p × ZMod p) ≃
      (map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))) :
        SL(2, ZMod (p ^ (k + 1))) →* SL(2, ZMod (p ^ k))).ker where
  toFun t :=
    let A : SL(2, ZMod (p ^ (k + 1))) :=
      ⟨!![1 + liftMulPow p k t.1, liftMulPow p k t.2.1;
          liftMulPow p k t.2.2, 1 - liftMulPow p k t.1],
        det_one_add_liftMulPow hk t.1 t.2.1 t.2.2⟩
    ⟨A, by
      rw [MonoidHom.mem_ker]
      simp_rw [ext_iff, map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      intro i j
      fin_cases i <;> fin_cases j <;> simp [A, -ZMod.castHom_apply, castHom_liftMulPow]⟩
  invFun M :=
    have h00 : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))
        (M.1 0 0 - 1) = 0 := by
      rw [map_sub, map_one, sub_eq_zero]
      exact congrArg (fun X : SL(2, ZMod (p ^ k)) ↦ X 0 0) M.2
    have h01 : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) (M.1 0 1) = 0 :=
      congrArg (fun X : SL(2, ZMod (p ^ k)) ↦ X 0 1) M.2
    have h10 : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) (M.1 1 0) = 0 :=
      congrArg (fun X : SL(2, ZMod (p ^ k)) ↦ X 1 0) M.2
    ((exists_liftMulPow_of_castHom_eq_zero h00).choose,
      (exists_liftMulPow_of_castHom_eq_zero h01).choose,
      (exists_liftMulPow_of_castHom_eq_zero h10).choose)
  left_inv := by
    rintro ⟨a, b, c⟩
    dsimp only
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · apply choose_exists_liftMulPow_eq <;> simp [-ZMod.castHom_apply, castHom_liftMulPow]
    · apply choose_exists_liftMulPow_eq <;> simp [-ZMod.castHom_apply, castHom_liftMulPow]
    · apply choose_exists_liftMulPow_eq <;> simp [-ZMod.castHom_apply, castHom_liftMulPow]
  right_inv := by
    intro M
    dsimp only
    have h00_zero : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))
        (M.1 0 0 - 1) = 0 := by
      rw [map_sub, map_one, sub_eq_zero]
      exact congrArg (fun X : SL(2, ZMod (p ^ k)) ↦ X 0 0) M.2
    have h01_zero : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))
        (M.1 0 1) = 0 :=
      congrArg (fun X : SL(2, ZMod (p ^ k)) ↦ X 0 1) M.2
    have h10_zero : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))
        (M.1 1 0) = 0 :=
      congrArg (fun X : SL(2, ZMod (p ^ k)) ↦ X 1 0) M.2
    have h11_zero : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))
        (M.1 1 1 - 1) = 0 := by
      rw [map_sub, map_one, sub_eq_zero]
      exact congrArg (fun X : SL(2, ZMod (p ^ k)) ↦ X 1 1) M.2
    set a := (exists_liftMulPow_of_castHom_eq_zero h00_zero).choose
    set b := (exists_liftMulPow_of_castHom_eq_zero h01_zero).choose
    set c := (exists_liftMulPow_of_castHom_eq_zero h10_zero).choose
    have ha : M.1 0 0 = 1 + liftMulPow p k a := by
      linear_combination -(exists_liftMulPow_of_castHom_eq_zero h00_zero).choose_spec
    have hb : M.1 0 1 = liftMulPow p k b :=
      (exists_liftMulPow_of_castHom_eq_zero h01_zero).choose_spec.symm
    have hc : M.1 1 0 = liftMulPow p k c :=
      (exists_liftMulPow_of_castHom_eq_zero h10_zero).choose_spec.symm
    obtain ⟨d, hd_spec⟩ := exists_liftMulPow_of_castHom_eq_zero h11_zero
    have hd : M.1 1 1 = 1 + liftMulPow p k d := by linear_combination -hd_spec
    have hdet := fin_two_mul_sub_mul_eq_one M.1
    rw [ha, hb, hc, hd] at hdet
    have had := liftMulPow_mul_liftMulPow hk a d
    have hbc := liftMulPow_mul_liftMulPow hk b c
    have h11 : M.1 1 1 = 1 - liftMulPow p k a := by
      rw [hd]
      linear_combination hdet - had + hbc
    ext i j
    fin_cases i <;> fin_cases j
    · exact ha.symm
    · exact hb.symm
    · exact hc.symm
    · exact h11.symm

/-- For `0 < p` and `1 ≤ k`, the kernel of `SL₂(ℤ/p^{k+1}ℤ) →* SL₂(ℤ/p^kℤ)` has order `p³`. -/
theorem card_ker_map_zmod_pow_succ {p k : ℕ} [NeZero p] (hk : 1 ≤ k) :
    Nat.card (map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))) :
      SL(2, ZMod (p ^ (k + 1))) →* SL(2, ZMod (p ^ k))).ker = p ^ 3 := by
  rw [← Nat.card_congr (kerMapZModPowSuccEquiv hk)]
  simp [ZMod.card, pow_three]

/-- Stepping from `p^k` to `p^{k+1}` (`1 ≤ k`, `0 < p`) multiplies `|SL₂(ℤ/p^kℤ)|` by `p³`. -/
theorem card_fin_two_zmod_pow_succ {p k : ℕ} [NeZero p] (hk : 1 ≤ k) :
    Nat.card SL(2, ZMod (p ^ (k + 1))) = p ^ 3 * Nat.card SL(2, ZMod (p ^ k)) := by
  let φ : SL(2, ZMod (p ^ (k + 1))) →* SL(2, ZMod (p ^ k)) :=
    map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)))
  rw [← Subgroup.card_mul_index φ.ker, card_ker_map_zmod_pow_succ hk, Subgroup.index_ker,
    MonoidHom.range_eq_top_of_surjective φ
      (map_zmod_castHom_surjective (pow_dvd_pow p (Nat.le_succ k))),
    Subgroup.card_top]

/-- For a prime `p`, `|SL₂(𝔽_p)| = p(p² - 1)`. -/
theorem card_fin_two_zmod_prime {p : ℕ} (hp : p.Prime) :
    Nat.card SL(2, ZMod p) = p * (p ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Matrix.card_SL_field, Fin.prod_univ_two, ZMod.card]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  have hsub : p ^ 2 - p = p * (p - 1) := by
    rw [sq, Nat.mul_sub_left_distrib, mul_one]
  rw [hsub, ← mul_assoc, Nat.mul_div_cancel _ (Nat.sub_pos_of_lt hp.one_lt), mul_comm]

/-- **Prime-power order of `SL₂`:** for prime `p` and `1 ≤ k`,
`|SL₂(ℤ/p^kℤ)| = p^{3k - 2}(p² - 1)`. -/
theorem card_fin_two_zmod_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    Nat.card SL(2, ZMod (p ^ k)) = p ^ (3 * k - 2) * (p ^ 2 - 1) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  induction k, hk using Nat.le_induction with
  | base =>
    rw [pow_one, card_fin_two_zmod_prime hp]
  | succ m hm ih =>
    rw [card_fin_two_zmod_pow_succ hm, ih, ← mul_assoc, ← pow_add]
    congr 1
    exact congrArg (p ^ ·) (by omega)

/-- For prime `p` and `1 ≤ k`, the kernel of reduction `SL₂(ℤ/p^kℤ) →* SL₂(𝔽_p)` has order
`p^{3(k - 1)}`. -/
theorem card_ker_map_zmod_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    Nat.card (map (ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)) :
      SL(2, ZMod (p ^ k)) →* SL(2, ZMod p)).ker = p ^ (3 * (k - 1)) := by
  let φ : SL(2, ZMod (p ^ k)) →* SL(2, ZMod p) :=
    map (ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p))
  have hpos : 0 < p * (p ^ 2 - 1) := by
    have hp2 : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
    exact Nat.mul_pos hp.pos (by omega)
  refine Nat.mul_right_cancel hpos ?_
  have hlag := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top_of_surjective φ
      (map_zmod_castHom_surjective (dvd_pow_self p (by omega))),
    Subgroup.card_top, card_fin_two_zmod_prime hp,
    card_fin_two_zmod_prime_pow hp hk] at hlag
  rw [hlag, ← mul_assoc, ← pow_succ]
  congr 1
  exact congrArg (p ^ ·) (by omega)

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
  have : Group.IsNilpotent (map (ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)) :
      SL(2, ZMod (p ^ k)) →* SL(2, ZMod p)).ker :=
    (isPGroup_ker_map_zmod_prime_pow hp hk).isNilpotent
  infer_instance

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

/-! ### The `{±I}` subgroup and the signed quotient `Q_N = SL₂(ℤ/Nℤ) ⧸ {±I}` -/

section SignedQuotient

variable (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R] [Fact (Even (Fintype.card n))]

/-- The central subgroup `{±I} = ⟨-1⟩` of `SL(n, R)`. Over rings with zero divisors (such as
`ZMod 8` or `ZMod 12`), this can be a proper subgroup of `Subgroup.center (SpecialLinearGroup n R)`.
-/
def negOneSubgroup : Subgroup (SpecialLinearGroup n R) :=
  Subgroup.zpowers (-1)

theorem negOneSubgroup_def :
    negOneSubgroup n R = Subgroup.zpowers (-1) := by
  rw [negOneSubgroup]

variable {n R}

@[simp]
theorem mem_negOneSubgroup_iff {g : SpecialLinearGroup n R} :
    g ∈ negOneSubgroup n R ↔ g = 1 ∨ g = -1 := by
  have hsq : (-1 : SpecialLinearGroup n R) ^ (2 : ℤ) = 1 := by
    rw [zpow_two, neg_one_mul, neg_neg]
  rw [negOneSubgroup_def, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, _root_.zpow_mul, hsq]
      simp
    · right
      rw [_root_.zpow_add, zpow_one, _root_.zpow_mul, hsq]
      simp
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero _⟩
    · exact ⟨1, zpow_one _⟩

/-- `negOneSubgroup n R` lies inside the center of `SL(n, R)`. -/
theorem negOneSubgroup_le_center :
    negOneSubgroup n R ≤ Subgroup.center (SpecialLinearGroup n R) := by
  rw [negOneSubgroup_def, Subgroup.zpowers_le]
  exact Subgroup.mem_center_iff.mpr fun g ↦ by rw [neg_one_mul, mul_neg_one]

instance instNormalNegOneSubgroup : (negOneSubgroup n R).Normal :=
  ⟨fun x hx g ↦ by
    rcases mem_negOneSubgroup_iff.mp hx with rfl | rfl <;> simp⟩

/-- Over a commutative ring without zero divisors, `negOneSubgroup (Fin 2) R` is the full center of
`SL₂(R)`. -/
theorem negOneSubgroup_eq_center [NoZeroDivisors R] :
    negOneSubgroup (Fin 2) R = Subgroup.center SL(2, R) := by
  ext g
  rw [mem_negOneSubgroup_iff, mem_center_iff_eq_one_or_eq_neg_one]

/-- `-1 = 1` in `SL₂(ℤ/Nℤ)` if and only if `N ∣ 2`. -/
theorem neg_one_eq_one_zmod_iff {N : ℕ} :
    (-1 : SL(2, ZMod N)) = 1 ↔ N ∣ 2 := by
  constructor
  · intro h
    have h00 := congrArg (fun M : SL(2, ZMod N) ↦ (M : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0) h
    simp only [coe_neg, coe_one, Matrix.neg_apply, Matrix.one_apply_eq] at h00
    have h2 : ((2 : ℕ) : ZMod N) = 0 := by
      rw [Nat.cast_ofNat]
      linear_combination -h00
    exact (ZMod.natCast_eq_zero_iff 2 N).mp h2
  · intro h
    have h2 : (2 : ZMod N) = 0 := by
      simpa only [Nat.cast_ofNat] using (ZMod.natCast_eq_zero_iff 2 N).mpr h
    have hneg : (-1 : ZMod N) = 1 := by linear_combination -h2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hneg]

theorem card_negOneSubgroup_zmod_eq_one_of_dvd_two {N : ℕ} (h : N ∣ 2) :
    Nat.card (negOneSubgroup (Fin 2) (ZMod N)) = 1 := by
  rw [Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall]
  intro g hg
  rcases mem_negOneSubgroup_iff.mp hg with rfl | rfl
  · rfl
  · exact neg_one_eq_one_zmod_iff.mpr h

theorem card_negOneSubgroup_zmod_eq_two {N : ℕ} (h : ¬ N ∣ 2) :
    Nat.card (negOneSubgroup (Fin 2) (ZMod N)) = 2 := by
  have hne : (-1 : SL(2, ZMod N)) ≠ 1 := mt neg_one_eq_one_zmod_iff.mp h
  have heq : Nat.card (negOneSubgroup (Fin 2) (ZMod N)) =
      Nat.card ({1, -1} : Set SL(2, ZMod N)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ mem_negOneSubgroup_iff)
  rw [heq, Nat.card_coe_set_eq]
  exact Set.ncard_pair hne.symm

end SignedQuotient

end Matrix.SpecialLinearGroup

namespace Matrix

/-- **The signed special linear quotient `SL(n, R) ⧸ {±I}`** (`Q_N` when `n = Fin 2` and
`R = ZMod N`), the finite group through which the modular group `PSL₂(ℤ) = SL₂(ℤ) ⧸ {±I}` acts at
principal level `N`. -/
abbrev SignedQuotient (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]
    [Fact (Even (Fintype.card n))] : Type _ :=
  SpecialLinearGroup n R ⧸ SpecialLinearGroup.negOneSubgroup n R

namespace SignedQuotient

open Matrix.SpecialLinearGroup

/-- The canonical quotient homomorphism `SignedQuotient n R →* PSL(n, R)`, dividing out any
remaining central roots of unity beyond `±I`. -/
noncomputable def toPSL (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R]
    [Fact (Even (Fintype.card n))] :
    SignedQuotient n R →* ProjectiveSpecialLinearGroup n R :=
  QuotientGroup.map _ _ (MonoidHom.id _) negOneSubgroup_le_center

@[simp]
theorem toPSL_mk (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R]
    [Fact (Even (Fintype.card n))] (g : SpecialLinearGroup n R) :
    toPSL n R (QuotientGroup.mk g) = QuotientGroup.mk g := by
  rw [toPSL]
  rfl

theorem toPSL_surjective (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R]
    [Fact (Even (Fintype.card n))] :
    Function.Surjective (toPSL n R) := fun x ↦ by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨QuotientGroup.mk g, rfl⟩

/-- Over a commutative ring without zero divisors, `SignedQuotient (Fin 2) R` is canonically
isomorphic to `PSL₂(R)`. -/
noncomputable def equivPSL (R : Type*) [CommRing R] [NoZeroDivisors R] :
    SignedQuotient (Fin 2) R ≃* PSL(2, R) :=
  QuotientGroup.quotientMulEquivOfEq negOneSubgroup_eq_center

@[simp]
theorem equivPSL_mk (R : Type*) [CommRing R] [NoZeroDivisors R] (g : SL(2, R)) :
    equivPSL R (QuotientGroup.mk g) = QuotientGroup.mk g := by
  rw [equivPSL]
  rfl

/-- Extension of scalars on signed quotients `SL(n, R) ⧸ {±I} →* SL(n, S) ⧸ {±I}`. -/
noncomputable def map {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    [Fact (Even (Fintype.card n))] (f : R →+* S) :
    SignedQuotient n R →* SignedQuotient n S :=
  QuotientGroup.map (negOneSubgroup n R) (negOneSubgroup n S)
    (SpecialLinearGroup.map f) (by
      intro g hg
      rw [Subgroup.mem_comap, mem_negOneSubgroup_iff]
      rcases mem_negOneSubgroup_iff.mp hg with rfl | rfl
      · left; exact map_one _
      · right
        ext i j
        by_cases hij : i = j <;> simp [hij])

@[simp]
theorem map_mk {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    [Fact (Even (Fintype.card n))] (f : R →+* S) (g : SpecialLinearGroup n R) :
    map f (QuotientGroup.mk g) = QuotientGroup.mk (SpecialLinearGroup.map f g) := by
  rw [map]
  rfl

/-- When `N ∣ 2` (`N = 1` or `N = 2`), `-I = I` modulo `N`, so `|Q_N| = |SL₂(ℤ/Nℤ)|`. -/
theorem card_fin_two_zmod_of_dvd_two {N : ℕ} (h : N ∣ 2) :
    Nat.card (SignedQuotient (Fin 2) (ZMod N)) = Nat.card SL(2, ZMod N) := by
  have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup (negOneSubgroup (Fin 2) (ZMod N))
  rw [card_negOneSubgroup_zmod_eq_one_of_dvd_two h, mul_one] at hlag
  exact hlag.symm

/-- When `¬ (N ∣ 2)` (in particular for all `N ≥ 3`, and at `N = 0`), `2 · |Q_N| = |SL₂(ℤ/Nℤ)|`. -/
theorem two_mul_card_fin_two_zmod_of_not_dvd_two {N : ℕ} (h : ¬ N ∣ 2) :
    2 * Nat.card (SignedQuotient (Fin 2) (ZMod N)) = Nat.card SL(2, ZMod N) := by
  have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup (negOneSubgroup (Fin 2) (ZMod N))
  rw [card_negOneSubgroup_zmod_eq_two h, mul_comm] at hlag
  exact hlag.symm

/-- For `N ≥ 3`, `2 · |Q_N| = |SL₂(ℤ/Nℤ)|`. -/
theorem two_mul_card_fin_two_zmod {N : ℕ} (hN : 3 ≤ N) :
    2 * Nat.card (SignedQuotient (Fin 2) (ZMod N)) = Nat.card SL(2, ZMod N) :=
  two_mul_card_fin_two_zmod_of_not_dvd_two fun h ↦ by
    have := Nat.le_of_dvd two_pos h
    omega

/-- **Cleared Euler product for `|Q_N|` at `N ≥ 3`:**
`2 · |Q_N| · ∏_{p ∣ N} p² = N³ · ∏_{p ∣ N} (p² - 1)`. -/
theorem two_mul_card_fin_two_zmod_mul_prod_primeFactors_sq {N : ℕ} (hN : 3 ≤ N) :
    2 * Nat.card (SignedQuotient (Fin 2) (ZMod N)) * ∏ p ∈ N.primeFactors, p ^ 2 =
      N ^ 3 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  rw [two_mul_card_fin_two_zmod hN, card_fin_two_zmod_mul_prod_primeFactors_sq]

@[simp]
theorem card_fin_two_zmod_one : Nat.card (SignedQuotient (Fin 2) (ZMod 1)) = 1 := by
  rw [card_fin_two_zmod_of_dvd_two (one_dvd 2), card_zmod_one]

@[simp]
theorem card_fin_two_zmod_two : Nat.card (SignedQuotient (Fin 2) (ZMod 2)) = 6 := by
  rw [card_fin_two_zmod_of_dvd_two dvd_rfl, card_fin_two_zmod_prime Nat.prime_two]
  norm_num

/-! #### Explicit orders at composite levels `N = 8` and `N = 12` vs. `PSL₂(ℤ/Nℤ)` -/

theorem card_sl_fin_two_zmod_eight : Nat.card SL(2, ZMod 8) = 384 :=
  card_fin_two_zmod_prime_pow (p := 2) (k := 3) Nat.prime_two (by omega)

theorem card_fin_two_zmod_eight : Nat.card (SignedQuotient (Fin 2) (ZMod 8)) = 192 := by
  have h := two_mul_card_fin_two_zmod (N := 8) (by omega)
  rw [card_sl_fin_two_zmod_eight] at h
  omega

theorem card_psl_fin_two_zmod_eight : Nat.card PSL(2, ZMod 8) = 96 := by
  have hlag :
      Nat.card SL(2, ZMod 8) = Nat.card PSL(2, ZMod 8) * Nat.card (Subgroup.center SL(2, ZMod 8)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(2, ZMod 8))
  have hcen : Nat.card (Subgroup.center SL(2, ZMod 8)) = 4 := by
    rw [Nat.card_congr (centerMulEquivRootsOfUnityFin 2 two_pos (ZMod 8)).toEquiv,
      Nat.card_congr (Equiv.subtypeEquivRight fun u : (ZMod 8)ˣ ↦ mem_rootsOfUnity 2 u),
      Nat.card_eq_fintype_card]
    decide
  rw [card_sl_fin_two_zmod_eight, hcen] at hlag
  omega

theorem card_sl_fin_two_zmod_twelve : Nat.card SL(2, ZMod 12) = 1152 := by
  have h12 : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
  rw [h12, card_zmod_mul_of_coprime (Fin 2) (by decide),
    card_fin_two_zmod_prime_pow Nat.prime_two (by omega),
    card_fin_two_zmod_prime Nat.prime_three]
  norm_num

theorem card_fin_two_zmod_twelve : Nat.card (SignedQuotient (Fin 2) (ZMod 12)) = 576 := by
  have h := two_mul_card_fin_two_zmod (N := 12) (by omega)
  rw [card_sl_fin_two_zmod_twelve] at h
  omega

theorem card_psl_fin_two_zmod_twelve : Nat.card PSL(2, ZMod 12) = 288 := by
  have hlag : Nat.card SL(2, ZMod 12) =
      Nat.card PSL(2, ZMod 12) * Nat.card (Subgroup.center SL(2, ZMod 12)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(2, ZMod 12))
  have hcen : Nat.card (Subgroup.center SL(2, ZMod 12)) = 4 := by
    rw [Nat.card_congr (centerMulEquivRootsOfUnityFin 2 two_pos (ZMod 12)).toEquiv,
      Nat.card_congr (Equiv.subtypeEquivRight fun u : (ZMod 12)ˣ ↦ mem_rootsOfUnity 2 u),
      Nat.card_eq_fintype_card]
    decide
  rw [card_sl_fin_two_zmod_twelve, hcen] at hlag
  omega

end SignedQuotient

end Matrix

/-! ### Prime orders, uniqueness, and non-isomorphism with alternating groups for `PSL₂(𝔽_p)` -/

namespace Matrix.ProjectiveSpecialLinearGroup

open Matrix.SpecialLinearGroup

theorem card_fin_two_zmod_two : Nat.card PSL(2, ZMod 2) = 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.card_congr (SignedQuotient.equivPSL (ZMod 2)).toEquiv,
    SignedQuotient.card_fin_two_zmod_two]

/-- For an odd prime `p`, `2 · |PSL₂(𝔽_p)| = p(p² - 1)`. -/
theorem two_mul_card_fin_two_zmod_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * Nat.card PSL(2, ZMod p) = p * (p ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp_ge := hp.two_le
  have hp3 : 3 ≤ p := by omega
  rw [← Nat.card_congr (SignedQuotient.equivPSL (ZMod p)).toEquiv,
    SignedQuotient.two_mul_card_fin_two_zmod hp3, card_fin_two_zmod_prime hp]

/-- **Distinct primes have non-isomorphic projective special linear groups `PSL₂(𝔽_p)`:** if
`PSL₂(𝔽_p) ≃* PSL₂(𝔽_q)` with `p, q` prime, then `p = q`. -/
theorem eq_of_fin_two_zmod_mulEquiv {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (e : PSL(2, ZMod p) ≃* PSL(2, ZMod q)) : p = q := by
  have hmono : ∀ {a b : ℕ}, 2 ≤ a → a < b → a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
    intro a b ha hab
    have ha2 : 1 < a ^ 2 := by nlinarith
    have hb2 : a ^ 2 < b ^ 2 := by nlinarith
    calc a * (a ^ 2 - 1) < b * (a ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hab (by omega)
      _ < b * (b ^ 2 - 1) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hcard : Nat.card PSL(2, ZMod p) = Nat.card PSL(2, ZMod q) := Nat.card_congr e.toEquiv
  have hp_ge := hp.two_le
  have hq_ge := hq.two_le
  by_cases hp2 : p = 2
  · subst hp2
    by_contra hq2
    have hq_eq := two_mul_card_fin_two_zmod_prime hq (Ne.symm hq2)
    rw [← hcard, card_fin_two_zmod_two] at hq_eq
    have hq3 : 3 ≤ q := by omega
    have h24 : 24 ≤ q * (q ^ 2 - 1) := by
      calc 24 = 3 * (3 ^ 2 - 1) := by norm_num
        _ ≤ q * (q ^ 2 - 1) := by
          rcases eq_or_lt_of_le hq3 with rfl | hlt
          · exact le_rfl
          · exact (hmono (by omega) hlt).le
    omega
  · by_cases hq2 : q = 2
    · subst hq2
      by_contra hne
      have hp_eq := two_mul_card_fin_two_zmod_prime hp hp2
      rw [hcard, card_fin_two_zmod_two] at hp_eq
      have hp3 : 3 ≤ p := by omega
      have h24 : 24 ≤ p * (p ^ 2 - 1) := by
        calc 24 = 3 * (3 ^ 2 - 1) := by norm_num
          _ ≤ p * (p ^ 2 - 1) := by
            rcases eq_or_lt_of_le hp3 with rfl | hlt
            · exact le_rfl
            · exact (hmono (by omega) hlt).le
      omega
    · have heq : p * (p ^ 2 - 1) = q * (q ^ 2 - 1) := by
        rw [← two_mul_card_fin_two_zmod_prime hp hp2,
          ← two_mul_card_fin_two_zmod_prime hq hq2, hcard]
      rcases lt_trichotomy p q with hlt | rfl | hgt
      · exact absurd heq (hmono hp.two_le hlt).ne
      · rfl
      · exact absurd heq.symm (hmono hq.two_le hgt).ne

/-- **No alternating group of degree `≥ 6` is isomorphic to any `PSL₂(𝔽_ℓ)`.** If `ℓ` divided
`|A_n| = n!/2`, primality would give `ℓ ≤ n`, forcing `|PSL₂(𝔽_ℓ)| = ℓ(ℓ² - 1)/2 < n³/2 ≤ n!/2`
for `n ≥ 6`. -/
theorem isEmpty_alternatingGroup_mulEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 6 ≤ Nat.card α) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    IsEmpty (alternatingGroup α ≃* PSL(2, ZMod ℓ)) := by
  refine ⟨fun e ↦ ?_⟩
  set n := Nat.card α
  have : Nontrivial α := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card]
    omega
  have halt : 2 * Nat.card (alternatingGroup α) = n.factorial := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm]
  have hcard : Nat.card (alternatingGroup α) = Nat.card PSL(2, ZMod ℓ) :=
    Nat.card_congr e.toEquiv
  have h6 : 720 ≤ n.factorial := by
    calc 720 = (6 : ℕ).factorial := by decide
      _ ≤ n.factorial := Nat.factorial_le hα
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    rw [hcard, card_fin_two_zmod_two] at halt
    omega
  · have hpsl := two_mul_card_fin_two_zmod_prime hℓ hℓ2
    have heq : ℓ * (ℓ ^ 2 - 1) = n.factorial := by omega
    have hdvd : ℓ ∣ n.factorial := ⟨ℓ ^ 2 - 1, heq.symm⟩
    have hℓ_le : ℓ ≤ n := hℓ.dvd_factorial.mp hdvd
    have hlt_cube : ℓ * (ℓ ^ 2 - 1) < n ^ 3 := by
      have hℓ2_pos : 1 ≤ ℓ ^ 2 := Nat.one_le_pow 2 ℓ hℓ.pos
      have hsub_lt : ℓ ^ 2 - 1 < n ^ 2 := by
        have : ℓ ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hℓ_le 2
        omega
      calc ℓ * (ℓ ^ 2 - 1) < ℓ * n ^ 2 := Nat.mul_lt_mul_of_pos_left hsub_lt hℓ.pos
        _ ≤ n * n ^ 2 := Nat.mul_le_mul_right (n ^ 2) hℓ_le
        _ = n ^ 3 := by ring
    have hcube : ∀ m, 6 ≤ m → m ^ 3 ≤ m.factorial := fun m hm ↦ by
      induction m, hm using Nat.le_induction with
      | base => decide
      | succ k hk ih =>
        rw [Nat.factorial_succ]
        have hsq : (k + 1) ^ 2 ≤ k ^ 3 := by nlinarith
        calc (k + 1) ^ 3 = (k + 1) * (k + 1) ^ 2 := by ring
          _ ≤ (k + 1) * k ^ 3 := Nat.mul_le_mul_left (k + 1) hsq
          _ ≤ (k + 1) * k.factorial := Nat.mul_le_mul_left (k + 1) ih
    have := hcube n hα
    omega

end Matrix.ProjectiveSpecialLinearGroup

/-! ### Classification of nonabelian simple subnormal sections of `SL₂(ℤ/Nℤ)` and its quotients -/

namespace Matrix.SpecialLinearGroup

/-- **Classification of nonabelian simple composition factors of `SL₂(ℤ/Nℤ)`.** For `N ≠ 0`,
every nonabelian simple group `S` occurring as a subnormal section of `SL₂(ℤ/Nℤ)` is isomorphic to
`PSL₂(𝔽_ℓ)` for a prime `ℓ ≥ 5` dividing `N`. -/
theorem exists_prime_dvd_psl_mulEquiv_of_hasSubnormalSection {N : ℕ} (hN : N ≠ 0) {S : Type*}
    [Group S] [IsSimpleGroup S] (hnc : ¬ IsMulCommutative S)
    (hS : Subgroup.HasSubnormalSection SL(2, ZMod N) S) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ ℓ ∣ N ∧ Nonempty (S ≃* PSL(2, ZMod ℓ)) := by
  obtain ⟨⟨ℓ, hℓ_mem⟩, hℓ_sec⟩ := (hS.congr_left (zmodEquivPi (Fin 2) hN)).exists_of_pi
  obtain ⟨hℓ_prime, hℓ_dvd, _⟩ := Nat.mem_primeFactors.mp hℓ_mem
  have hk : 1 ≤ N.factorization ℓ :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by simpa using hℓ_mem))
  let π : SL(2, ZMod (ℓ ^ N.factorization ℓ)) →* SL(2, ZMod ℓ) :=
    map (ZMod.castHom (dvd_pow_self ℓ (by omega)) (ZMod ℓ))
  have hπ_surj : Function.Surjective π :=
    map_zmod_castHom_surjective (dvd_pow_self ℓ (by omega))
  have hSLℓ : Subgroup.HasSubnormalSection SL(2, ZMod ℓ) S := by
    rcases hℓ_sec.or_of_normal π.ker with hker | hquot
    · have : Group.IsSolvable π.ker := isSolvable_ker_map_zmod_prime_pow hℓ_prime hk
      exact False.elim (hnc hker.isMulCommutative_of_isSolvable)
    · exact hquot.congr_left (QuotientGroup.quotientKerEquivOfSurjective π hπ_surj)
  have : Fact ℓ.Prime := ⟨hℓ_prime⟩
  have hℓ5 : 5 ≤ ℓ := by
    by_contra! hlt5
    by_cases h4 : ℓ = 4
    · subst h4; exact absurd hℓ_prime (by decide)
    · have hle3 : Nat.card (ZMod ℓ) ≤ 3 := by rw [Nat.card_zmod]; omega
      have : Group.IsSolvable SL(2, ZMod ℓ) :=
        TauCeti.Matrix.SpecialLinearGroup.isSolvable_fin_two_of_natCard_le_three (ZMod ℓ) hle3
      exact hnc hSLℓ.isMulCommutative_of_isSolvable
  rcases hSLℓ.or_of_normal (Subgroup.center SL(2, ZMod ℓ)) with hcen | hpsl
  · exact False.elim (hnc hcen.isMulCommutative_of_isSolvable)
  · have hcard4 : 4 ≤ Nat.card (ZMod ℓ) := by rw [Nat.card_zmod]; omega
    have : IsSimpleGroup PSL(2, ZMod ℓ) :=
      ProjectiveSpecialLinearGroup.isSimpleGroup_of_four_le_natCard hcard4
    exact ⟨ℓ, hℓ_prime, hℓ5, hℓ_dvd, hpsl.nonempty_mulEquiv_of_isSimpleGroup⟩

/-- **No alternating group `A_α` of degree `≥ 6` occurs as a subnormal section of `SL₂(ℤ/Nℤ)`**
(`N ≠ 0`). -/
theorem not_hasSubnormalSection_alternatingGroup {N : ℕ} (hN : N ≠ 0) {α : Type*}
    [Fintype α] [DecidableEq α] (hα : 6 ≤ Nat.card α) :
    ¬ Subgroup.HasSubnormalSection SL(2, ZMod N) (alternatingGroup α) := fun hsec ↦ by
  have h5 : 5 ≤ Nat.card α := by omega
  have hsimp : IsSimpleGroup (alternatingGroup α) := alternatingGroup.isSimpleGroup h5
  have : Nontrivial (alternatingGroup α) := hsimp.toNontrivial
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
    ((Subgroup.HasSubnormalSection.mk_quotient hH hKH).of_surjective hf)

end Matrix.SpecialLinearGroup

namespace Matrix.SignedQuotient

/-- Every nonabelian simple subnormal section of any quotient of `SignedQuotient (Fin 2) (ZMod N)`
(`N ≠ 0`) is isomorphic to `PSL₂(𝔽_ℓ)` for a prime `ℓ ≥ 5` dividing `N`. -/
theorem exists_prime_dvd_psl_mulEquiv_of_surjective {N : ℕ} (hN : N ≠ 0) {Q : Type*} [Group Q]
    {f : SignedQuotient (Fin 2) (ZMod N) →* Q} (hf : Function.Surjective f) {H K : Subgroup Q}
    (hH : H.IsSubnormal) (hKH : K ≤ H) [(K.subgroupOf H).Normal]
    [IsSimpleGroup (H ⧸ K.subgroupOf H)] (hnc : ¬ IsMulCommutative (H ⧸ K.subgroupOf H)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ ℓ ∣ N ∧ Nonempty ((H ⧸ K.subgroupOf H) ≃* PSL(2, ZMod ℓ)) :=
  Matrix.SpecialLinearGroup.exists_prime_dvd_psl_mulEquiv_of_surjective hN
    (f := f.comp (QuotientGroup.mk' _)) (hf.comp (QuotientGroup.mk'_surjective _)) hH hKH hnc

end Matrix.SignedQuotient
