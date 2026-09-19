/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.ArithmeticFunction.PrimeRecurrence
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Composite
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence

/-!
# Fourier coefficients of a Hecke-ring eigenvector at the good primes

Let `F ∈ M_k(N, χ)` (or `S_k(N, χ)`) be an eigenvector of the `Γ₀(N)` Hecke-ring generator at a
prime `p ∤ N`, acting through `heckeRingHomCharSpace` (`heckeRingHomCuspCharSpace`), with
eigenvalue `c`. Through the identification of that generator with the classical `T_p`
(`heckeRingHomCharSpace_heckeTGeneratorGamma0`, `heckeRingHomCuspCharSpace_heckeTGeneratorGamma0`)
and the coefficient formula `a_m(T_p F) = a_{pm}(F) + χ(p) p^{k−1} a_{m/p}(F)` of
`HeckeSlash/Recurrence.lean`, the eigenvector equation becomes a recurrence on the Fourier
coefficients of `F` alone:

`a_{pm}(F) = c · a_m(F) − χ(p) p^{k−1} a_{m/p}(F)`, the last term present only when `p ∣ m`.

Running it along the least prime factor shows that a form which is an eigenvector at every
prime outside an auxiliary level `L` (a multiple of `N`; for `L ≠ 0` these are all but finitely
many primes) and has `a₁ = 0` has `a_n = 0` at every nonzero index `n` coprime to `L` — at
`n = 0` as well when it is a cusp form. This is the form
in which strong multiplicity one consumes eigen-ness (Miyake's Theorem 4.6.12 assumes agreement
at the indices prime to such an `L`): the difference of two newforms whose eigenvalues agree
outside `L` has `a₁ = 1 − 1 = 0`, so its coefficients at the indices prime to `L` all vanish,
and the descent argument then places it in the old subspace.

## Main results

* `heckeTNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul`: on `M_k(N, χ)` the recurrence
  **characterises** the eigen-relation `Tₚ F = c • F` — the converse holds too, because a
  modular form is determined by its `q`-expansion. This is the direction Diamond–Shurman's
  Proposition 5.8.5 needs.
* `heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul`: its cusp-form case, the spelling
  `IsEigenformAwayFromLevel` uses.
* `qExpansion_coeff_prime_mul_of_heckeRingHomCharSpace_heckeTCompositeGamma0_eq_smul` and its
  cusp-form counterpart `…_of_heckeRingHomCuspCharSpace_…`: the coefficient recurrence of an
  eigenvector, on `M_k(N, χ)` and on `S_k(N, χ)`; the cusp-form one is the forward half of the
  characterisation above.
* `qExpansion_coeff_eq_zero_of_forall_prime_heckeRingHom_of_one_eq_zero_of_ne_zero_of_coprime` and
  `…_heckeRingHomCuspCharSpace_…`: a form eigen at every prime away from a multiple `L` of `N`,
  with `a₁ = 0`, has `a_n = 0` at every `n` coprime to `L` (and `n ≠ 0` in the modular-form
  case).
* `heckeTNat_eq_smul_of_heckeRingHomCharSpace_heckeTCompositeGamma0_eq_smul` and its cusp-form
  counterpart: a Hecke-ring eigenvector at a good prime is an eigenvector of the classical
  operator `heckeTNat` (resp. `heckeTCuspNat`).

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.3.1 and §5.8 — in particular Proposition 5.8.5, whose engine at a single prime
  is the characterisation stated here.
* [T. Miyake, *Modular forms*][miyake1989], §4.6.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N p : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- **A ring eigenvector at a good prime is an eigenvector of the classical `T_p`**, on
`M_k(N, χ)`: at a prime the Hecke ring's action and `heckeTNat` are the same operator, so the two
eigen-equations are the same statement. -/
theorem heckeTNat_eq_smul_of_heckeRingHomCharSpace_heckeTCompositeGamma0_eq_smul [NeZero p]
    (hp : p.Prime) {F : modFormCharSpace k χ} {c : ℂ}
    (hF : heckeRingHomCharSpace k χ (heckeTCompositeGamma0 N p) F = c • F) :
    heckeTNat k p (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      c • (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  simpa [heckeTCompositeGamma0_prime N hp, heckeRingHomCharSpace_heckeTGeneratorGamma0 k χ hp]
    using congrArg Subtype.val hF

/-- **A ring eigenvector at a good prime is an eigenvector of the classical `T_p`**, on
`S_k(N, χ)`. -/
theorem heckeTCuspNat_eq_smul_of_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_smul
    [NeZero p] (hp : p.Prime) {F : cuspFormCharSpace k χ} {c : ℂ}
    (hF : heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p) F = c • F) :
    heckeTCuspNat k p (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      c • (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  simpa [heckeTCompositeGamma0_prime N hp,
    heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k χ hp] using congrArg Subtype.val hF

/-! ### The recurrence characterises the eigen-relation -/

/-- **The coefficient recurrence characterises the eigen-relation `Tₚ F = c • F` at a good
prime**, on `M_k(N, χ)`. For `F ∈ M_k(N, χ)` and `p ∤ N`, the relation `Tₚ F = c • F` holds
exactly when the Fourier coefficients of `F` satisfy
`a_{pm}(F) = c · a_m(F) − χ(p) p^{k−1} a_{m/p}(F)` at every `m`, the last term present only when
`p ∣ m`.

This is a statement about the equation, not about eigenvectors: `F = 0` satisfies both sides for
every `c`, and a consumer wanting a genuine eigenvector supplies `F ≠ 0` itself. -/
theorem heckeTNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul
    (hp : p.Prime) (hpN : Nat.Coprime p N) {F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hF : F ∈ modFormCharSpace k χ) (c : ℂ) :
    heckeTNat k p (_hn := ⟨hp.ne_zero⟩) F = c • F ↔
      ∀ m : ℕ, (qExpansion 1 F).coeff (p * m) =
        c * (qExpansion 1 F).coeff m -
          if p ∣ m then (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
            (qExpansion 1 F).coeff (m / p) else 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hrec : ∀ m : ℕ, (qExpansion 1 (heckeTNat k p F)).coeff m =
      (qExpansion 1 F).coeff (p * m) +
        if p ∣ m then (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
          (qExpansion 1 F).coeff (m / p) else 0 := fun m ↦ by
    rw [heckeTNat_def]
    exact qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_mem_modFormCharSpace
      k hp hpN χ hF m
  have hsmul : ∀ m : ℕ,
      (qExpansion 1 ((c • F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k))).coeff m =
      c * (qExpansion 1 F).coeff m := fun m ↦ by
    rw [FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _),
      map_smul, smul_eq_mul]
  constructor
  · intro hT m
    have h := hrec m
    rw [hT, hsmul m] at h
    linear_combination -h
  · intro h
    refine (ModularForm.qExpansion_inj one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map _)).1 (PowerSeries.ext fun m ↦ ?_)
    rw [hrec m, hsmul m, h m]
    ring

/-- **The coefficient recurrence characterises the eigen-relation `Tₚ F = c • F` at a good
prime**, on `S_k(N, χ)`: the cusp-form case of
`heckeTNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul`, in the spelling
`IsEigenformAwayFromLevel` uses. -/
theorem heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul
    (hp : p.Prime) (hpN : Nat.Coprime p N) {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hF : F ∈ cuspFormCharSpace k χ) (c : ℂ) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) F = c • F ↔
      ∀ m : ℕ, (qExpansion 1 F).coeff (p * m) =
        c * (qExpansion 1 F).coeff m -
          if p ∣ m then (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
            (qExpansion 1 F).coeff (m / p) else 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [heckeTCuspNat_eq_smul_iff_heckeTNat_eq_smul]
  simpa only [ModularFormClass.coe_modularForm] using
    heckeTNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul hp hpN
      ((coe_mem_modFormCharSpace_iff k χ F).mpr hF) c

/-- **The coefficient recurrence of an eigenvector at a good prime, on `M_k(N, χ)`.** If the ring
generator at `p ∤ N` acts on `F ∈ M_k(N, χ)` by the scalar `c`, then
`a_{pm}(F) = c · a_m(F) − χ(p) p^{k−1} a_{m/p}(F)`, the last term present only when `p ∣ m`. -/
theorem qExpansion_coeff_prime_mul_of_heckeRingHomCharSpace_heckeTCompositeGamma0_eq_smul
    (hp : p.Prime) (hpN : Nat.Coprime p N) {F : modFormCharSpace k χ} {c : ℂ}
    (hF : heckeRingHomCharSpace k χ (heckeTCompositeGamma0 N p) F = c • F) (m : ℕ) :
    (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p * m) =
      c * (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m -
        if p ∣ m then (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
          (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (m / p) else 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hT := heckeTNat_eq_smul_of_heckeRingHomCharSpace_heckeTCompositeGamma0_eq_smul hp hF
  have h := qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_mem_modFormCharSpace
    k hp hpN χ F.2 m
  rw [← heckeTNat_def, hT, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _), map_smul,
    smul_eq_mul] at h
  linear_combination -h

/-- **The coefficient recurrence of an eigenvector at a good prime, on `S_k(N, χ)`.** If the ring
generator at `p ∤ N` acts on `F ∈ S_k(N, χ)` by the scalar `c`, then
`a_{pm}(F) = c · a_m(F) − χ(p) p^{k−1} a_{m/p}(F)`, the last term present only when `p ∣ m`. -/
theorem qExpansion_coeff_prime_mul_of_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_smul
    (hp : p.Prime) (hpN : Nat.Coprime p N) {F : cuspFormCharSpace k χ} {c : ℂ}
    (hF : heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p) F = c • F) (m : ℕ) :
    (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p * m) =
      c * (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m -
        if p ∣ m then (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
          (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (m / p) else 0 :=
  have : NeZero p := ⟨hp.ne_zero⟩
  (heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul hp hpN F.2 c).1
    (heckeTCuspNat_eq_smul_of_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_smul hp hF) m

/-- **Coefficient vanishing from the prime eigenvalues, on `M_k(N, χ)`.** Let `L` be a multiple of
`N`. A form `F ∈ M_k(N, χ)` that is an eigenvector of the ring generator at every prime `p ∤ L`
and has `a₁(F) = 0` has `a_n(F) = 0` at every `n ≠ 0` coprime to `L`.
For `L ≠ 0`, the auxiliary level is the finite slack of strong multiplicity one: eigen-ness is
assumed only away from finitely many primes beyond those dividing `N`. -/
theorem qExpansion_coeff_eq_zero_of_forall_prime_heckeRingHom_of_one_eq_zero_of_ne_zero_of_coprime
    {F : modFormCharSpace k χ} {L : ℕ} (hNL : N ∣ L) (ha : ∀ p : ℕ, p.Prime → Nat.Coprime p L →
      ∃ c : ℂ, heckeRingHomCharSpace k χ (heckeTCompositeGamma0 N p) F = c • F)
    (h1 : (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 = 0) (n : ℕ)
    (hn0 : n ≠ 0) (hn : Nat.Coprime n L) :
    (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n = 0 :=
  TauCeti.eq_zero_of_forall_prime_mul_eq_of_one_eq_zero_of_ne_zero_of_coprime
    (a := fun n ↦ (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n)
    (fun p hp hpL ↦ by
    obtain ⟨c, hc⟩ := ha p hp hpL
    exact ⟨c, _, fun m _ ↦
      qExpansion_coeff_prime_mul_of_heckeRingHomCharSpace_heckeTCompositeGamma0_eq_smul hp
        (hpL.coprime_dvd_right hNL) hc m⟩) h1 n hn0 hn

/-- **Coefficient vanishing from the prime eigenvalues, on `S_k(N, χ)`.** Let `L` be a multiple of
`N`. A cusp form `F ∈ S_k(N, χ)` that is an eigenvector of the ring generator at every prime
`p ∤ L` and has `a₁(F) = 0` has `a_n(F) = 0` at every `n` coprime to `L` — with no `n ≠ 0`
hypothesis, unlike the modular-form version, since a cusp form already has `a₀ = 0`. This is the
form strong multiplicity one consumes. -/
theorem qExpansion_coeff_eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_coprime
    {F : cuspFormCharSpace k χ} {L : ℕ} (hNL : N ∣ L) (ha : ∀ p : ℕ, p.Prime → Nat.Coprime p L →
      ∃ c : ℂ, heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p) F = c • F)
    (h1 : (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 = 0) (n : ℕ)
    (hn : Nat.Coprime n L) :
    (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact CuspFormClass.qExpansion_coeff_zero _ one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N)
  exact TauCeti.eq_zero_of_forall_prime_mul_eq_of_one_eq_zero_of_ne_zero_of_coprime
    (a := fun n ↦ (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n)
    (fun p hp hpL ↦ by
    obtain ⟨c, hc⟩ := ha p hp hpL
    exact ⟨c, _, fun m _ ↦
      qExpansion_coeff_prime_mul_of_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_smul hp
        (hpL.coprime_dvd_right hNL) hc m⟩) h1 n hn0 hn

end HeckeRing.GL2
