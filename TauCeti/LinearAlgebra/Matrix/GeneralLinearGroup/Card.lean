/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Defs
-- `GL` and `SL` occur in the statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
-- Non-public: `Matrix.card_GL_field`, `Matrix.card_SL`, `ZMod.equivPi`, and the prime-power
-- kernel counts are used only in the proofs.
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.RingTheory.ZMod
import Mathlib.SetTheory.Cardinal.NatCard
import TauCeti.Data.ZMod.LocalRing
import TauCeti.Data.ZMod.MulCastHom

/-!
# The order of `GL₂` over a field and over `ZMod N`

Mathlib's `Matrix.card_GL_field` gives `|GL n 𝔽_q| = ∏ i, (qⁿ - qⁱ)`, which in size two reads
`(q² - 1)(q² - q)`. That form is a product of differences, and every index computation in `GL₂`
divides it by the order of a subgroup, so what is wanted is the factored form
`(q - 1)² · q · (q + 1)`, where the natural subtraction has already been carried out. It is
recorded here in the two associations the two maximal tori call for: the split torus has order
`(q - 1)²` and the non-split one `q² - 1`.

The formulas use `q = Nat.card F` and require no chosen enumeration or finiteness assumption.
For an infinite field, both the field and its general linear group have `Nat.card` equal to zero,
so the same identities hold.

Over `ZMod N`, reducing `GL (Fin m) (ZMod (p ^ (k + 1)))` modulo `p` is surjective with kernel in
bijection with `m × m` matrices over `ker (ZMod (p ^ (k + 1)) → ZMod p)` of order `p ^ k`. By
the Chinese remainder theorem this yields the LMFDB factored orders of `GL (Fin 2) (ZMod N)` and
`SpecialLinearGroup (Fin 2) (ZMod N)` for every `N : ℕ` (both sides vanish at `N = 0`).

## Main results

* `TauCeti.natCard_GL_fin_two`: `|GL₂(𝔽_q)| = (q - 1)² · q(q + 1)`.
* `TauCeti.natCard_GL_fin_two_eq_sq_sub_one_mul`: `|GL₂(𝔽_q)| = (q² - 1) · q(q - 1)`.
* `TauCeti.natCard_GL_fin_two_of_card_eq_two`: `|GL₂(𝔽₂)| = 6`.
* `TauCeti.natCard_GL_zmod_prime_pow`: `|GL_m(ℤ/p^{k+1})| = (p^k)^{m²} · |GL_m(𝔽_p)|`.
* `TauCeti.natCard_GL_fin_two_zmod`: `|GL₂(ℤ/N)| = φ(N) · N · (N / ∏_{p∣N} p)² · ∏_{p∣N} (p² - 1)`.
* `TauCeti.natCard_SL_fin_two_zmod`: `|SL₂(ℤ/N)| = N · (N / ∏_{p∣N} p)² · ∏_{p∣N} (p² - 1)`.
-/

public section

open scoped MatrixGroups

namespace TauCeti

section Field

variable (F : Type*) [Field F]

/-- **The order of `GL₂` over a field**, in the factored form `(q - 1)² · q(q + 1)`: the
first factor is the order of the split torus and the second its index. -/
theorem natCard_GL_fin_two :
    Nat.card (GL (Fin 2) F) =
      (Nat.card F - 1) ^ 2 * (Nat.card F * (Nat.card F + 1)) := by
  rcases finite_or_infinite F with hF | hF
  · let := Fintype.ofFinite F
    rw [Matrix.card_GL_field, Fin.prod_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, ← Nat.card_eq_fintype_card]
    simp_rw [pow_two, mul_self_tsub_one]
    rw [← Nat.mul_sub_one]
    ring
  · have hcard : Nat.card (GL (Fin 2) F) = 0 :=
      Finite.card_eq_zero_of_surjective Matrix.GeneralLinearGroup.det_surjective
        (by simp [Nat.card_units])
    simp [hcard]

/-- **The order of `GL₂` over a field**, in the factored form `(q² - 1) · q(q - 1)`: the
first factor is the order of the non-split torus and the second its index. -/
theorem natCard_GL_fin_two_eq_sq_sub_one_mul :
    Nat.card (GL (Fin 2) F) =
      (Nat.card F ^ 2 - 1) * (Nat.card F * (Nat.card F - 1)) := by
  rw [natCard_GL_fin_two F]
  simp_rw [pow_two, mul_self_tsub_one]
  ring

variable {F} in
/-- **`GL₂` over a field with two elements has order `6`.** This is `(q - 1)² · q(q + 1)` at
`q = 2`. -/
theorem natCard_GL_fin_two_of_card_eq_two (hF : Nat.card F = 2) :
    Nat.card (GL (Fin 2) F) = 6 := by
  rw [natCard_GL_fin_two F, hF]
  norm_num

end Field

section ZMod

open Matrix

private theorem map_castHom_prime_pow_surjective (m p k : ℕ) [hp : Fact p.Prime] :
    Function.Surjective (GeneralLinearGroup.map (n := Fin m)
      (ZMod.castHom (dvd_pow_self p k.succ_ne_zero) (ZMod p))) := by
  intro g
  let h := dvd_pow_self p k.succ_ne_zero
  choose a ha using fun i j ↦
    ZMod.castHom_surjective h ((g : Matrix (Fin m) (Fin m) (ZMod p)) i j)
  have hmap : (Matrix.of a).map (ZMod.castHom h (ZMod p)) = g := by
    ext i j
    exact ha i j
  have hunit : IsUnit (Matrix.of a).det := by
    rw [ZMod.isUnit_prime_pow_iff_castHom_ne_zero p (k + 1) k.succ_ne_zero,
      RingHom.map_det, RingHom.mapMatrix_apply, hmap]
    exact (Matrix.isUnits_det_units g).ne_zero
  refine ⟨GeneralLinearGroup.mk'' (Matrix.of a) hunit, ?_⟩
  ext i j
  exact ha i j

/-- **The order of `GL_m(ℤ/p^{k+1})`**: reduction modulo `p` is surjective with kernel of order
`(p ^ k) ^ (m * m)`. -/
theorem natCard_GL_zmod_prime_pow (m p k : ℕ) [hp : Fact p.Prime] :
    Nat.card (GL (Fin m) (ZMod (p ^ (k + 1)))) =
      (p ^ k) ^ (m * m) * Nat.card (GL (Fin m) (ZMod p)) := by
  let h := dvd_pow_self p k.succ_ne_zero
  let f : GL (Fin m) (ZMod (p ^ (k + 1))) →* GL (Fin m) (ZMod p) :=
    GeneralLinearGroup.map (ZMod.castHom h (ZMod p))
  have e : f.ker ≃ (Fin m → Fin m → RingHom.ker (ZMod.castHom h (ZMod p))) :=
    { toFun := fun g i j ↦
        ⟨((g.val : Matrix (Fin m) (Fin m) (ZMod (p ^ (k + 1)))) - 1) i j, by
          have hg := congrArg (fun x : GL (Fin m) (ZMod p) ↦
            (x : Matrix (Fin m) (Fin m) (ZMod p)) i j) (MonoidHom.mem_ker.mp g.property)
          simp only [f, GeneralLinearGroup.map_apply, Units.val_one, Matrix.one_apply] at hg
          rw [RingHom.mem_ker, Matrix.sub_apply, Matrix.one_apply, map_sub]
          split_ifs with hij <;> simp_all⟩
      invFun := fun B ↦
        let A : Matrix (Fin m) (Fin m) (ZMod (p ^ (k + 1))) :=
          1 + Matrix.of fun i j ↦ (B i j : ZMod (p ^ (k + 1)))
        have hA : A.map (ZMod.castHom h (ZMod p)) = 1 := by
          ext i j
          simp only [A, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply,
            map_add, RingHom.mem_ker.mp (B i j).property, add_zero]
          split_ifs <;> simp
        have hu : IsUnit A.det := by
          rw [ZMod.isUnit_prime_pow_iff_castHom_ne_zero p (k + 1) k.succ_ne_zero,
            RingHom.map_det, RingHom.mapMatrix_apply, hA, Matrix.det_one]
          exact one_ne_zero
        ⟨GeneralLinearGroup.mk'' A hu, by
          ext i j
          simpa [f] using congrArg (fun M : Matrix (Fin m) (Fin m) (ZMod p) ↦ M i j) hA⟩
      left_inv := fun g ↦ by ext i j; simp
      right_inv := fun B ↦ by ext i j; simp }
  have hker : Nat.card f.ker = (p ^ k) ^ (m * m) := by
    rw [Nat.card_congr e, Nat.card_fun, Nat.card_fun,
      ZMod.natCard_ker_castHom p (by rw [pow_succ]) hp.out.ne_zero, Nat.card_fin, ← pow_mul,
      mul_comm m m]
  rw [← hker]
  exact (Subgroup.card_ker_mul_card_of_surjective (map_castHom_prime_pow_surjective m p k)).symm

private theorem natCard_GL_fin_two_zmod_factor {N p : ℕ} (hN : N ≠ 0) (hpN : p ∈ N.primeFactors) :
    Nat.card (GL (Fin 2) (ZMod (p ^ N.factorization p))) =
      Nat.totient (p ^ N.factorization p) * p ^ N.factorization p *
        (p ^ (N.factorization p - 1)) ^ 2 * (p ^ 2 - 1) := by
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpN
  have : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < N.factorization p :=
    hp.factorization_pos_of_dvd hN (Nat.dvd_of_mem_primeFactors hpN)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one.mpr hpos
  rw [hk, Nat.add_sub_cancel, natCard_GL_zmod_prime_pow 2 p k,
    natCard_GL_fin_two_eq_sq_sub_one_mul (ZMod p), Nat.card_eq_fintype_card, ZMod.card,
    Nat.totient_prime_pow_succ hp, pow_succ]
  ring

/-- **The order of `GL₂(ℤ/N)`** in the LMFDB factored form
`φ(N) · N · (N / ∏_{p ∣ N} p)² · ∏_{p ∣ N} (p² − 1)`. Holds for all `N : ℕ` (both sides vanish
at `N = 0`). -/
theorem natCard_GL_fin_two_zmod (N : ℕ) :
    Nat.card (GL (Fin 2) (ZMod N)) =
      Nat.totient N * N * (N / ∏ p ∈ N.primeFactors, p) ^ 2 *
        ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  rcases eq_or_ne N 0 with rfl | hN
  · have : Infinite (GL (Fin 2) (ZMod 0)) :=
      Infinite.of_injective
        (fun n : ZMod 0 ↦ GeneralLinearGroup.mk'' !![(1 : ZMod 0), n; 0, 1]
          (by simp [Matrix.det_fin_two_of]))
        fun m n h ↦ by
          simpa using congrArg
            (fun x : GL (Fin 2) (ZMod 0) ↦ (x : Matrix (Fin 2) (Fin 2) (ZMod 0)) 0 1) h
    simp
  have : NeZero N := ⟨hN⟩
  let e : GL (Fin 2) (ZMod N) ≃*
      ∀ p : N.primeFactors, GL (Fin 2) (ZMod ((p : ℕ) ^ N.factorization p)) :=
    (GeneralLinearGroup.mapEquiv (Fin 2) (ZMod.equivPi N hN)).trans (GeneralLinearGroup.piEquiv _)
  rw [Nat.card_congr e.toEquiv, Nat.card_pi,
    Finset.prod_coe_sort N.primeFactors
      (fun p ↦ Nat.card (GL (Fin 2) (ZMod (p ^ N.factorization p)))),
    Finset.prod_congr rfl fun p hp ↦ natCard_GL_fin_two_zmod_factor hN hp]
  simp only [Finset.prod_mul_distrib]
  have htot : ∏ p ∈ N.primeFactors, Nat.totient (p ^ N.factorization p) = N.totient := by
    rw [Nat.totient_eq_prod_factorization hN]
    refine Finset.prod_congr rfl fun p hp ↦ ?_
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [Nat.totient_prime_pow hpr
      (hpr.factorization_pos_of_dvd hN (Nat.dvd_of_mem_primeFactors hp))]
  have hpow : ∏ p ∈ N.primeFactors, p ^ N.factorization p = N :=
    Nat.prod_factorization_pow_eq_self hN
  have hdiv : ∏ p ∈ N.primeFactors, (p ^ (N.factorization p - 1)) ^ 2 =
      (N / ∏ p ∈ N.primeFactors, p) ^ 2 := by
    rw [Finset.prod_pow]
    congr 1
    refine Nat.eq_div_of_mul_eq_left (Finset.prod_ne_zero_iff.mpr fun p hp ↦
      (Nat.prime_of_mem_primeFactors hp).ne_zero) ?_
    rw [← Finset.prod_mul_distrib]
    refine (Finset.prod_congr rfl fun p hp ↦ ?_).trans hpow
    have hpos := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hN
      (Nat.dvd_of_mem_primeFactors hp)
    rw [← pow_succ, Nat.sub_add_cancel hpos]
  rw [htot, hpow, hdiv]

/-- **The order of `SL₂(ℤ/N)`**: `N · (N / ∏_{p ∣ N} p)² · ∏_{p ∣ N} (p² − 1)` for all `N : ℕ`. -/
theorem natCard_SL_fin_two_zmod (N : ℕ) :
    Nat.card SL(2, ZMod N) =
      N * (N / ∏ p ∈ N.primeFactors, p) ^ 2 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  rcases eq_or_ne N 0 with rfl | hN
  · have : Infinite SL(2, ZMod 0) :=
      Infinite.of_injective
        (fun n : ZMod 0 ↦ (⟨!![(1 : ZMod 0), n; 0, 1], by simp⟩ : SL(2, ZMod 0)))
        fun m n h ↦ by
          simpa using congrArg (fun x : SL(2, ZMod 0) ↦ (x : Matrix (Fin 2) (Fin 2) (ZMod 0)) 0 1) h
    simp
  have : NeZero N := ⟨hN⟩
  rw [Matrix.card_SL, natCard_GL_fin_two_zmod N, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, mul_assoc (Nat.totient N), mul_assoc (Nat.totient N),
    Nat.mul_div_right _ (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN)), mul_assoc]

end ZMod

end TauCeti
