/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `GL` occurs in the statements below.
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- Non-public: `Matrix.card_GL_field`, `ZMod.equivPi`, and local-ring/prime-power kernel counts
-- are used only in the proofs.
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.RingTheory.ZMod
import Mathlib.RingTheory.ZMod.LocalRing
import Mathlib.SetTheory.Cardinal.NatCard
import TauCeti.Data.ZMod.MulCastHom
import TauCeti.LinearAlgebra.Matrix.IdealEntries
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse
import TauCeti.RingTheory.LocalRing.RingHom

/-!
# The order of general linear groups

## Over a field

Mathlib's `Matrix.card_GL_field` gives `|GL n 𝔽_q| = ∏ i, (qⁿ - qⁱ)`, which in size two reads
`(q² - 1)(q² - q)`. That form is a product of differences, and every index computation in `GL₂`
divides it by the order of a subgroup, so what is wanted is the factored form
`(q - 1)² · q · (q + 1)`, where the natural subtraction has already been carried out. It is
recorded here in the two associations the two maximal tori call for: the split torus has order
`(q - 1)²` and the non-split one `q² - 1`.

The formulas use `q = Nat.card F` and require no chosen enumeration or finiteness assumption.
For an infinite field, both the field and its general linear group have `Nat.card` equal to zero,
so the same identities hold.

## Along a local surjection

A surjective ring homomorphism `f : R →+* S` that reflects units (`IsLocalHom f`), such as the
reduction `ℤ/pᵏ → 𝔽_p`, multiplies the order of `GL n` by `|ker f| ^ (n²)`: an `n × n` matrix is
invertible exactly when its image is, and the entrywise map on matrices is a surjective local
homomorphism whose kernel is the matrices with entries in `ker f`. Combined with the Chinese
remainder theorem this yields the LMFDB factored order of `GL (Fin 2) (ZMod N)` for every
`N : ℕ` (both sides vanish at `N = 0`).

## Main results

* `Matrix.natCard_GL_eq_natCard_ker_pow_mul`: `|GL n R| = |ker f| ^ (n²) · |GL n S|` for a
  surjective local homomorphism `f : R →+* S`.
* `TauCeti.natCard_GL_fin_two`: `|GL₂(𝔽_q)| = (q - 1)² · q(q + 1)`.
* `TauCeti.natCard_GL_fin_two_eq_sq_sub_one_mul`: `|GL₂(𝔽_q)| = (q² - 1) · q(q - 1)`.
* `TauCeti.natCard_GL_fin_two_of_card_eq_two`: `|GL₂(𝔽₂)| = 6`.
* `TauCeti.natCard_GL_zmod_prime_pow`: `|GL_m(ℤ/p^{k+1})| = (p^k)^{m²} · |GL_m(𝔽_p)|`.
* `TauCeti.natCard_GL_fin_two_zmod`: `|GL₂(ℤ/N)| = φ(N) · N · (N / ∏_{p∣N} p)² · ∏_{p∣N} (p² - 1)`.
-/

public section

namespace Matrix

/-- **The order of `GL n` along a surjective local homomorphism.** If `f : R →+* S` is surjective
and reflects units, then `|GL n R| = |ker f| ^ (n²) · |GL n S|`: this is the unit count of
`RingHom.natCard_units_eq_natCard_ker_mul` for the entrywise map on matrices. -/
theorem natCard_GL_eq_natCard_ker_pow_mul {n R S : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] [CommRing S] (f : R →+* S) [IsLocalHom f] (hf : Function.Surjective f) :
    Nat.card (GL n R) =
      Nat.card (RingHom.ker f) ^ (Fintype.card n * Fintype.card n) * Nat.card (GL n S) := by
  rw [← f.natCard_ker_mapMatrix]
  exact (f.mapMatrix (m := n)).natCard_units_eq_natCard_ker_mul fun M ↦
    ⟨of fun i j ↦ (hf (M i j)).choose, ext fun i j ↦ (hf (M i j)).choose_spec⟩

end Matrix

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

/-- **The order of `GL_m(ℤ/p^{k+1})`**: reduction modulo `p` is a surjective local ring
homomorphism `ℤ/p^{k+1} →+* ℤ/p` with kernel of order `p ^ k`, so the induced map on `GL_m` has
kernel of order `(p ^ k) ^ (m * m)`. -/
theorem natCard_GL_zmod_prime_pow (m p k : ℕ) [hp : Fact p.Prime] :
    Nat.card (GL (Fin m) (ZMod (p ^ (k + 1)))) =
      (p ^ k) ^ (m * m) * Nat.card (GL (Fin m) (ZMod p)) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have := ZMod.isLocalHom_castHom_pow (n := p) k.succ_ne_zero
  rw [Matrix.natCard_GL_eq_natCard_ker_pow_mul
      (ZMod.castHom (dvd_pow_self p k.succ_ne_zero) (ZMod p))
      (ZMod.castHom_surjective (dvd_pow_self p k.succ_ne_zero)),
    ZMod.natCard_ker_castHom p (by rw [pow_succ]) hp.out.ne_zero, Fintype.card_fin]

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

end ZMod

end TauCeti
