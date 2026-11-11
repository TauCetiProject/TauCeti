/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.StrongMultiplicityOne.Basic
public import TauCeti.NumberTheory.ModularForms.Newforms.Fields
import TauCeti.NumberTheory.DirichletCharacter.PrimeValues

/-!
# Strong multiplicity one without a nebentypus hypothesis

The Fourier coefficients of a newform at the indices prime to its level determine its nebentypus:
at a good prime `p` the Hecke recurrence gives `χ(p) = (a_p² - a_{p²}) / p^{k-1}`
(`TauCeti.char_prime_eq_coeff`), and by Dirichlet's theorem on primes in arithmetic progressions a
character is determined by its values at all but finitely many primes
(`DirichletCharacter.changeLevel_eq_changeLevel_of_eventually_apply_prime_eq`). So two newforms
of levels `N` and `M` whose coefficients `a_n` agree at every `n` prime to `N M` outside a finite
set have nebentypes inducing the same character modulo every common multiple of `N` and `M`.

This removes the nebentypus hypothesis from strong multiplicity one stated on indices: such
newforms have the same level and are equal (Miyake, Theorem 4.6.19, for newforms), and at a fixed
level the coefficient and index forms of Miyake, Theorem 4.6.12, hold with no assumption on the
nebentypus. Agreement of the eigenvalues at the primes alone does not see `a_{p²}`, and the
prime form, `HeckeRing.GL2.Newform.eq_of_forall_notMem_prime_eigenvalue_eq`, keeps its nebentypus
hypothesis.

## Main results

All in the namespace `HeckeRing.GL2.Newform`:

* `eventually_dirichletLift_apply_prime_eq_of_forall_notMem_qExpansion_coeff_eq`: newforms whose
  coefficients agree at the good indices outside a finite set have nebentypes agreeing at all but
  finitely many primes.
* `χ_comp_unitsMap_eq_of_forall_notMem_qExpansion_coeff_eq`: their nebentypes induce the same
  character modulo every common multiple of the levels.
* `χ_eq_of_forall_notMem_qExpansion_coeff_eq`: at a fixed level they have the same nebentypus.
* `eq_of_forall_notMem_qExpansion_coeff_eq` and `eq_of_forall_notMem_eigenvalue_eq`: strong
  multiplicity one at a fixed level, on the coefficients and on the eigenvalues at the good indices
  outside a finite set.
* `level_eq_and_coe_eq_of_forall_notMem_qExpansion_coeff_eq`: across levels, such newforms have the
  same level and are the same function.

## References

* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.12 and Theorem 4.6.19.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.8.5 for the Hecke recurrence.
-/

public section

open Filter UpperHalfPlane

namespace HeckeRing.GL2

namespace Newform

variable {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ}

/-- **The coefficients of a newform at its good indices determine its nebentypus at almost all
primes.** If newforms `f` and `g` of levels `N` and `M` have the same Fourier coefficient at every
index `n` prime to `N` and `M` outside a finite set `S`, their zero-extended nebentypes agree at
all but finitely many primes: at a large prime `p`, both `p` and `p²` are good indices outside
`S`, and `χ(p) = (a_p² - a_{p²}) / p^{k-1}`. -/
theorem eventually_dirichletLift_apply_prime_eq_of_forall_notMem_qExpansion_coeff_eq
    (f : Newform N k) (g : Newform M k) {S : Finset ℕ}
    (h : ∀ n : ℕ+, Nat.Coprime (n : ℕ) N → Nat.Coprime (n : ℕ) M → (n : ℕ) ∉ S →
      (qExpansion 1 f.toCuspForm).coeff (n : ℕ) = (qExpansion 1 g.toCuspForm).coeff (n : ℕ)) :
    ∀ᶠ p : ℕ in cofinite, p.Prime → f.dirichletLift p = g.dirichletLift p := by
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_gt_atTop (S.sup id + N + M)] with p hpB hp
  -- a prime larger than `N`, `M` and every element of `S` is good, and so is its square
  have hcop {L : ℕ} [NeZero L] (hL : L < p) : Nat.Coprime p L :=
    hp.coprime_iff_not_dvd.mpr fun hpL ↦ (Nat.le_of_dvd (NeZero.pos L) hpL).not_gt hL
  have hpN : Nat.Coprime p N := hcop (by omega)
  have hpM : Nat.Coprime p M := hcop (by omega)
  have hS {n : ℕ} (hn : p ≤ n) : n ∉ S := fun hnS ↦
    (Finset.le_sup (f := id) hnS).not_gt (by simp only [id]; omega)
  have hp2 : p ≤ p ^ 2 := Nat.le_self_pow two_ne_zero p
  have h₁ := h ⟨p, hp.pos⟩ hpN hpM (hS le_rfl)
  have h₂ := h ⟨p ^ 2, pow_pos hp.pos 2⟩ (hpN.pow_left 2) (hpM.pow_left 2) (hS hp2)
  simp only [PNat.mk_coe] at h₁ h₂
  rw [f.dirichletLift_apply_of_coprime hpN, g.dirichletLift_apply_of_coprime hpM,
    TauCeti.char_prime_eq_coeff f hp hpN, TauCeti.char_prime_eq_coeff g hp hpM, h₁, h₂]

/-- **The coefficients of a newform at its good indices determine its nebentypus.** If newforms
`f` and `g` of levels `N` and `M` have the same Fourier coefficient at every index `n` prime to
`N` and `M` outside a finite set, their nebentypes induce the same character modulo every common
multiple `L` of `N` and `M`. -/
theorem χ_comp_unitsMap_eq_of_forall_notMem_qExpansion_coeff_eq {L : ℕ} [NeZero L]
    (f : Newform N k) (g : Newform M k) (hN : N ∣ L) (hM : M ∣ L) {S : Finset ℕ}
    (h : ∀ n : ℕ+, Nat.Coprime (n : ℕ) N → Nat.Coprime (n : ℕ) M → (n : ℕ) ∉ S →
      (qExpansion 1 f.toCuspForm).coeff (n : ℕ) = (qExpansion 1 g.toCuspForm).coeff (n : ℕ)) :
    f.χ.comp (ZMod.unitsMap hN) = g.χ.comp (ZMod.unitsMap hM) := by
  have := congrArg MulChar.toUnitHom
    (DirichletCharacter.changeLevel_eq_changeLevel_of_eventually_apply_prime_eq hN hM
      (eventually_dirichletLift_apply_prime_eq_of_forall_notMem_qExpansion_coeff_eq f g h))
  rwa [changeLevel_dirichletLift_toUnitHom, changeLevel_dirichletLift_toUnitHom] at this

/-- **Newforms of the same level with the same coefficients at the good indices outside a finite
set have the same nebentypus.** -/
theorem χ_eq_of_forall_notMem_qExpansion_coeff_eq {f g : Newform N k} {S : Finset ℕ}
    (h : ∀ n : ℕ+, Nat.Coprime (n : ℕ) N → (n : ℕ) ∉ S →
      (qExpansion 1 f.toCuspForm).coeff (n : ℕ) = (qExpansion 1 g.toCuspForm).coeff (n : ℕ)) :
    f.χ = g.χ := by
  simpa only [ZMod.unitsMap_self, MonoidHom.comp_id] using
    χ_comp_unitsMap_eq_of_forall_notMem_qExpansion_coeff_eq f g (dvd_refl N) (dvd_refl N)
      fun n hn _ hnS ↦ h n hn hnS

/-- **Strong multiplicity one, on Fourier coefficients** (Miyake's own form of Theorem 4.6.12):
two newforms of level `N` and weight `k` whose `q`-expansion coefficients agree at every index
coprime to `N` outside a finite set are equal. No assumption is made on the nebentypus: the
coefficients determine it (`Newform.χ_eq_of_forall_notMem_qExpansion_coeff_eq`). -/
theorem eq_of_forall_notMem_qExpansion_coeff_eq {f g : Newform N k} {S : Finset ℕ}
    (h : ∀ n : ℕ+, Nat.Coprime (n : ℕ) N → (n : ℕ) ∉ S →
      (qExpansion 1 f.toCuspForm).coeff (n : ℕ) = (qExpansion 1 g.toCuspForm).coeff (n : ℕ)) :
    f = g :=
  eq_of_forall_notMem_prime_eigenvalue_eq (χ_eq_of_forall_notMem_qExpansion_coeff_eq h)
    fun p hp hpN hpS ↦ by
      rw [← f.qExpansion_coeff_eq_eigenvalue ⟨p, hp.pos⟩ hpN,
        ← g.qExpansion_coeff_eq_eigenvalue ⟨p, hp.pos⟩ hpN]
      exact h ⟨p, hp.pos⟩ hpN hpS

/-- **Strong multiplicity one** (Miyake, Theorem 4.6.12, fixed level): two newforms of level `N`
and weight `k` whose eigenvalues agree at every index coprime to `N` outside a finite set are
equal. No assumption is made on the nebentypus. -/
theorem eq_of_forall_notMem_eigenvalue_eq {f g : Newform N k} {S : Finset ℕ}
    (h : ∀ (n : ℕ+) (hn : Nat.Coprime n N), (n : ℕ) ∉ S → f.eigenvalue n hn = g.eigenvalue n hn) :
    f = g :=
  eq_of_forall_notMem_qExpansion_coeff_eq fun n hn hnS ↦ by
    rw [f.qExpansion_coeff_eq_eigenvalue n hn, g.qExpansion_coeff_eq_eigenvalue n hn]
    exact h n hn hnS

/-- **Strong multiplicity one across levels, on Fourier coefficients** (Miyake, Theorem 4.6.19,
for newforms). Let `f`, `g` be newforms of the same weight and of levels `N`, `M` whose
`q`-expansion coefficients agree at every index prime to `N` and `M` outside a finite set. Then
`N = M` and `f` and `g` are the same function on `ℍ`; their nebentypes then agree by
`Newform.χ_comp_unitsMap_eq_of_forall_notMem_qExpansion_coeff_eq`. -/
theorem level_eq_and_coe_eq_of_forall_notMem_qExpansion_coeff_eq (f : Newform N k)
    (g : Newform M k) {S : Finset ℕ}
    (h : ∀ n : ℕ+, Nat.Coprime (n : ℕ) N → Nat.Coprime (n : ℕ) M → (n : ℕ) ∉ S →
      (qExpansion 1 f.toCuspForm).coeff (n : ℕ) = (qExpansion 1 g.toCuspForm).coeff (n : ℕ)) :
    N = M ∧ ⇑f.toCuspForm = ⇑g.toCuspForm := by
  have : NeZero (Nat.lcm N M) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (NeZero.ne M)⟩
  refine level_eq_and_coe_eq_of_forall_notMem_prime_eigenvalue_eq f g (S := S)
    (χ_comp_unitsMap_eq_of_forall_notMem_qExpansion_coeff_eq f g _ _ h) fun p hp hpN hpM hpS ↦ ?_
  rw [← f.qExpansion_coeff_eq_eigenvalue ⟨p, hp.pos⟩ hpN,
    ← g.qExpansion_coeff_eq_eigenvalue ⟨p, hp.pos⟩ hpM]
  exact h ⟨p, hp.pos⟩ hpN hpM hpS

end Newform

end HeckeRing.GL2
