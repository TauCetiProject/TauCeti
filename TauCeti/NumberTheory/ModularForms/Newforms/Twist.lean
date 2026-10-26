/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.Newform
public import TauCeti.NumberTheory.ModularForms.Twist.Basic
import TauCeti.NumberTheory.ModularForms.Newforms.Coefficient
import TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
import TauCeti.NumberTheory.ModularForms.Newforms.RingEigenvalue
import TauCeti.NumberTheory.ModularForms.Twist.Hecke

/-!
# The primitive associate of a twisted newform

Let `f` be a newform of level `N` and nebentypus `χ`, and let `ψ` be a Dirichlet character
modulo `M`. For a level `L` with `N * M ∣ L` and `M * M ∣ L`, the twist `f ⊗ ψ` is a cusp form
in `S_k(Γ₁(L), χψ²)` with `q`-expansion `∑ ψ(n) aₙ(f) qⁿ`. At a prime `p ∤ L` it is a
`T_p`-eigenvector with eigenvalue `ψ(p) a_p(f)` (`CuspForm.heckeTCuspNat_twist_eq_smul`), and
its first coefficient is `ψ(1) a₁(f) = 1`. So the twist is a nonzero good Hecke eigenform at
level `L`, and the existence of the newform associated with an eigenform gives a newform `g`
of some level dividing `L`, with nebentypus inducing `χψ²`, such that

`a_p(g) = ψ(p) a_p(f)` at every prime `p ∤ L`.

This `g` is the *primitive associate* of `f ⊗ ψ`. Its uniqueness needs strong multiplicity one
across levels and is not proved here; the sharp level of `g` is not determined here either.

## Main results

* `HeckeRing.GL2.Newform.exists_newform_qExpansion_coeff_prime_eq_twist`: the existence of the
  primitive associate of `f ⊗ ψ`, with its nebentypus and its coefficients at the primes
  `p ∤ L`.

## References

* A. O. L. Atkin, W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of `W`-operators*,
  Invent. Math. 48 (1978).
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.8.4.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup ZMod

open scoped MatrixGroups

namespace HeckeRing.GL2.Newform

variable {M N L : ℕ} [NeZero N] {k : ℤ}

/-- **The primitive associate of a twisted newform.** Let `f` be a newform of level `N` and
nebentypus `χ`, `ψ` a Dirichlet character modulo `M`, and `L` a level with `N * M ∣ L` and
`M * M ∣ L`. Then there is a newform `g` of some level `R ∣ L`, whose nebentypus read at level
`L` is `χψ²`, with `a_p(g) = ψ(p) a_p(f)` at every prime `p ∤ L`. -/
theorem exists_newform_qExpansion_coeff_prime_eq_twist [NeZero M] [NeZero L] (f : Newform N k)
    (ψ : DirichletCharacter ℂ M) (hNL : N * M ∣ L) (hML : M * M ∣ L) :
    ∃ (R : ℕ) (_ : NeZero R) (hR : R ∣ L) (g : Newform R k),
      g.χ.comp (unitsMap hR) = f.χ.comp (unitsMap (dvd_of_mul_right_dvd hNL)) *
        (ψ.toUnitHom.comp (unitsMap (dvd_of_mul_left_dvd hML))) ^ 2 ∧
      ∀ p : ℕ, p.Prime → p.Coprime L →
        (qExpansion 1 g.toCuspForm).coeff p = ψ p * (qExpansion 1 f.toCuspForm).coeff p := by
  have hNL' : N ∣ L := dvd_of_mul_right_dvd hNL
  -- the twist is nonzero, since its first coefficient is `ψ(1) a₁(f) = 1`
  have hF0 : CuspForm.twist ψ hNL hML f.toCuspForm ≠ 0 := fun h ↦ by
    have h1 := CuspForm.qExpansion_twist_coeff ψ hNL hML f.toCuspForm 1
    simp [h, f.qExpansion_coeff_one, UpperHalfPlane.qExpansion_zero] at h1
  obtain ⟨R, _, hR, g, hgχ, hg⟩ :=
    Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul
      (CuspForm.twist_mem_cuspFormCharSpace ψ hNL hML f.mem_charSpace) hF0
      (a := fun p hp hpL ↦ ψ p * f.eigenvalue ⟨p, hp.pos⟩ (hpL.coprime_dvd_right hNL'))
      fun p hp hpL ↦ CuspForm.heckeTCuspNat_twist_eq_smul ψ hNL hML f.mem_charSpace hp hpL
        (f.heckeTCuspNat_eq_eigenvalue_smul hp (hpL.coprime_dvd_right hNL'))
  refine ⟨R, inferInstance, hR, g, hgχ, fun p hp hpL ↦ ?_⟩
  have hg' : (qExpansion 1 g.toCuspForm).coeff p = _ :=
    g.qExpansion_coeff_eq_eigenvalue g.isNorm ⟨p, hp.pos⟩ (hpL.coprime_dvd_right hR)
  have hf' : (qExpansion 1 f.toCuspForm).coeff p = _ :=
    f.qExpansion_coeff_eq_eigenvalue f.isNorm ⟨p, hp.pos⟩ (hpL.coprime_dvd_right hNL')
  rw [hg', hg p hp hpL, hf']

end HeckeRing.GL2.Newform
