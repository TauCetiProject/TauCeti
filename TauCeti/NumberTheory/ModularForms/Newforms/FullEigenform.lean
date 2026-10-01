/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.BadPrime.Eigenvector
public import TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
public import TauCeti.NumberTheory.ModularForms.Newforms.Eigenform

/-!
# Newforms are full Hecke eigenforms

A newform is, by definition, a normalised good Hecke eigenform in the new subspace (Miyake's
*primitive form*): eigen-ness is demanded only at the indices coprime to the level. This file
proves that it is an eigenvector of `T_n` at *every* positive index, including the primes dividing
the level, with eigenvalue the Fourier coefficient `a_n` (Diamond–Shurman, Theorem 5.8.2; Miyake,
Theorem 4.6.13; the bad-prime eigenvalues go back to Atkin–Lehner and Li). This is the bridge
between the two definitions of "newform" in the literature: Diamond–Shurman *define* a newform as
a normalised full eigenform in the new subspace, and their Theorem 5.8.2 is exactly the statement
that Miyake's primitive forms are such.

The textbook route passes through the stability of the new subspace under the bad-prime
operators `U_p`. The route here needs no bad-prime stability: for `p ∣ N` the operator
`U_p = T_p` commutes with the good `T_q` in the commutative `Γ₀(N)` Hecke ring, so `U_p f` is a
good eigenvector of `S_k(N, χ)` with the eigenvalues of `f`, hence the multiple `a₁(U_p f) • f`
of `f` (`Newform.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul`), and
`a₁(U_p f) = a_p(f)`.

## Main definitions

* `HeckeRing.GL2.Newform.toEigenform`: a newform as a full Hecke eigenform.

## Main results

* `HeckeRing.GL2.Newform.heckeUCuspNat_eq_qExpansion_coeff_smul`: `U_p f = a_p(f) • f` for a
  newform `f` and a prime `p ∣ N`, the bad-prime eigenvector equation.
* `HeckeRing.GL2.Newform.heckeTCuspNat_eq_qExpansion_coeff_smul`: `T_p f = a_p(f) • f` at every
  prime `p`, the primes dividing the level (where `T_p = U_p`) included.
* `HeckeRing.GL2.Newform.toEigenform_eigenvalue_eq_qExpansion_coeff`: the eigenvalue of a newform
  at every positive index is its Fourier coefficient there.

## Provenance

The same theorem is proved in the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7bcb0ce220ad53983ec45d987cb5b9002`),
`projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/Newforms/FullEigenform.lean`:
`Newform.heckeT_n_cusp_bad_prime_eq` there is the bad-prime equation `U_p f = a_p(f) • f`, and
`Newform.isFullEigenform` there is `Newform.toEigenform` here, stated as a predicate on the cusp
form rather than as a bundled `Eigenform`. The proofs are independent: the source takes the
textbook route through the stability of the new subspace under the bad-prime `U_p`
(`heckeT_n_cusp_preserves_cuspFormsNewExtended_bad`, via the Petersson adjoint of `U_p`), which
this file does not use.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.2.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.13.
* A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*, Math. Ann. **185** (1970),
  134–160.
* W.-C. W. Li, *Newforms and functional equations*, Math. Ann. **212** (1975), 285–315.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup TauCeti

open scoped MatrixGroups

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-! ### The bad-prime eigenvalues -/

/-- **A newform is an eigenvector of `U_p` at every prime `p` dividing the level, with eigenvalue
`a_p(f)`** (Atkin–Lehner; Li; Diamond–Shurman, Theorem 5.8.2; Miyake, Theorem 4.6.13). Together
with the good eigensystem this makes a newform a full Hecke eigenform (`Newform.toEigenform`).
The statement is on the bad-prime operator `heckeUCuspNat`, matching the `U_p`-spelled API of
`HeckeSlash/BadPrime`; `Newform.heckeTCuspNat_eq_qExpansion_coeff_smul` is the statement at
every prime. -/
theorem heckeUCuspNat_eq_qExpansion_coeff_smul (f : Newform N k) {p : ℕ} (hp : p.Prime)
    (hpN : p ∣ N) :
    heckeUCuspNat k p hp hpN f.toCuspForm =
      (qExpansion 1 f.toCuspForm).coeff p • f.toCuspForm := by
  have : NeZero p := ⟨hp.ne_zero⟩
  -- `U_p f`, in `S_k(N, χ)`
  set G : cuspFormCharSpace k f.χ :=
    heckeRingHomCuspCharSpace k f.χ (heckeTCompositeGamma0 N p) ⟨f.toCuspForm, f.mem_charSpace⟩
    with hG
  have hGcoe : (G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      heckeUCuspNat k p hp hpN f.toCuspForm := by
    rw [hG, heckeTCompositeGamma0_prime N hp,
      coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k f.χ hp]
  -- `U_p f` is an eigenvector of every good `T_q`, with the eigenvalues of `f`
  have hGeig : ∀ (q : ℕ) (hq : q.Prime) (hqN : Nat.Coprime q N),
      heckeTCuspNat k q (_hn := ⟨hq.ne_zero⟩) (G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
        f.eigenvalue ⟨q, hq.pos⟩ hqN • (G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    intro q hq hqN
    have : NeZero q := ⟨hq.ne_zero⟩
    refine heckeTCuspNat_eq_smul_of_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_smul hq ?_
    have hq' := f.isEigen ⟨q, hq.pos⟩ hqN
    simp only [PNat.mk_coe] at hq'
    -- the `Γ₀(N)` Hecke ring is commutative, so `T_q` commutes with `U_p = T_p`
    rw [hG, ← Module.End.mul_apply, ← map_mul,
      HeckeCosetModule.mul_comm_of_antiInvolution ℤ (atkinLehnerAntiInvolution N)
        (atkinLehnerAntiInvolution_onHeckeCoset_eq_self N),
      map_mul, Module.End.mul_apply, hq', map_smul]
  have hc := f.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul G.2 hGeig
  rw [hGcoe] at hc
  -- the scalar is `a_p(f)`: the first coefficient of `U_p f`
  have hc' := (heckeUCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul k hp hpN _).mp hc 1
  rw [mul_one, f.isNorm, mul_one] at hc'
  rw [hc']
  exact hc

/-! ### The full eigenform -/

/-- **A newform is a full Hecke eigenform** (Diamond–Shurman, Theorem 5.8.2; Miyake, Theorem
4.6.13): its good eigensystem, together with the bad-prime eigenvector equations
`U_p f = a_p(f) • f`, makes it an eigenvector of `T_n` at every positive index. This is the
bridge between Miyake's *primitive form*, the definition of `Newform` here, and Diamond–Shurman's
*newform*, defined as a normalised full eigenform in the new subspace. -/
noncomputable def toEigenform (f : Newform N k) : Eigenform N k :=
  f.toEigenformAwayFromLevel.toEigenform fun _ hp hpN ↦
    ⟨_, f.heckeUCuspNat_eq_qExpansion_coeff_smul hp hpN⟩

@[simp]
theorem toEigenform_toCuspForm (f : Newform N k) : f.toEigenform.toCuspForm = f.toCuspForm :=
  EigenformAwayFromLevel.toEigenform_toCuspForm _ _

@[simp]
theorem toEigenform_χ (f : Newform N k) : f.toEigenform.χ = f.χ :=
  EigenformAwayFromLevel.toEigenform_χ _ _

@[simp]
theorem toEigenform_toEigenformAwayFromLevel (f : Newform N k) :
    f.toEigenform.toEigenformAwayFromLevel = f.toEigenformAwayFromLevel :=
  EigenformAwayFromLevel.toEigenform_toEigenformAwayFromLevel _ _

/-- **The Hecke eigenvalues of a newform are its Fourier coefficients, at every positive index**:
`T_n f = a_n(f) • f` for all `n ≥ 1`, the primes dividing the level included. -/
@[simp]
theorem toEigenform_eigenvalue_eq_qExpansion_coeff (f : Newform N k) (n : ℕ+) :
    f.toEigenform.eigenvalue n = (qExpansion 1 f.toCuspForm).coeff n := by
  have h₁ : (qExpansion 1 f.toEigenform.toCuspForm).coeff 1 = 1 := by
    rw [toEigenform_toCuspForm]
    exact f.isNorm
  have h := f.toEigenform.qExpansion_coeff_eq_eigenvalue h₁ n
  rw [toEigenform_toCuspForm] at h
  exact h.symm

/-- **`Tₚ f = aₚ(f) • f` at every prime `p`**, whether or not `p` divides the level: the good
eigensystem of `f` and the bad-prime equation `Newform.heckeUCuspNat_eq_qExpansion_coeff_smul`
(at a prime `p ∣ N` the operator is `U_p`, `heckeUCuspNat_eq_heckeTCuspNat`) in one statement. -/
theorem heckeTCuspNat_eq_qExpansion_coeff_smul (f : Newform N k) {p : ℕ} (hp : p.Prime) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f.toCuspForm =
      (qExpansion 1 f.toCuspForm).coeff p • f.toCuspForm := by
  have h := f.toEigenform.heckeTCuspNat_eq_eigenvalue_smul hp
  rw [toEigenform_toCuspForm] at h
  exact h.trans
    (congrArg (· • f.toCuspForm) (f.toEigenform_eigenvalue_eq_qExpansion_coeff ⟨p, hp.pos⟩))

end HeckeRing.GL2.Newform

end
