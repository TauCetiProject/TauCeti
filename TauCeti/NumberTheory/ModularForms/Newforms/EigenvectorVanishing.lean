/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Eigenvector
public import TauCeti.NumberTheory.ModularForms.Newforms.MainLemma
public import TauCeti.NumberTheory.ModularForms.Newforms.Nebentypus

/-!
# A good Hecke eigenvector in the new part with `a₁ = 0` vanishes

The one statement both multiplicity one and strong multiplicity one run on. A cusp form in
`S_k(N, χ)` that is an eigenvector of the Hecke ring at every prime not dividing `N` has all its
coefficients determined by `a₁` at the indices coprime to `N`; if `a₁ = 0` those coefficients all
vanish (`qExpansion_coeff_eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_coprime`),
the Main Lemma (`TauCeti.mem_cuspFormsOld_of_forall_coprime_qExpansion_coeff_eq_zero`) then puts
the form in the old part, and the old and new parts meet only in `0`.

Both consumers reach their theorem by producing such an eigenvector: multiplicity one from
`a₁(g) • f - a₁(f) • g`, strong multiplicity one from the difference of two newforms.

## Main results

* `HeckeRing.GL2.eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_mem_cuspFormsNew`.

## References

* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.13.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup TauCeti

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- **A good Hecke eigenvector in the new part with `a₁ = 0` is zero.** Its coefficients vanish
at every index coprime to `N`, so the Main Lemma puts it in the old part, and the old and new
parts of `S_k(N, χ)` meet only in `0`. -/
theorem eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_mem_cuspFormsNew
    {F : cuspFormCharSpace k χ}
    (ha : ∀ p : ℕ, p.Prime → Nat.Coprime p N →
      ∃ c : ℂ, heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p) F = c • F)
    (h1 : (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 = 0)
    (hnew : (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsNew N k) :
    (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 :=
  (Submodule.disjoint_def.mp (disjoint_cuspFormsOld_cuspFormsNew N k)) _
    (mem_cuspFormsOld_of_forall_coprime_qExpansion_coeff_eq_zero F.2 fun n hn ↦
      qExpansion_coeff_eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_coprime
        dvd_rfl ha h1 n hn)
    hnew

end HeckeRing.GL2

end
