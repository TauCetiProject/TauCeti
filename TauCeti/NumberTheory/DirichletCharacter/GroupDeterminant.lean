/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.Primorial
public import Mathlib.RingTheory.Adjoin.Basic
public import TauCeti.NumberTheory.DirichletCharacter.GeneralizedBernoulli
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.Bernoulli.Voronoi
import TauCeti.LinearAlgebra.Matrix.GroupMatrix
import TauCeti.NumberTheory.DirichletCharacter.LFunction.TrivialZeros
import TauCeti.NumberTheory.MulChar.SumUnits

/-!
# Group determinants and a nonzero integer divisible by Bernoulli numbers

For a finite commutative group `G` and a function `g : G → R`, every homomorphism `χ : G →* R`
is an eigenvector of the group matrix `(g(t / s))_{s,t}`, with eigenvalue `∑ᵤ χ(u) g(u)`, and
each such eigenvalue divides the group determinant (`TauCeti.of_div_mulVec`,
`TauCeti.sum_mul_dvd_det_of_div`). For `G = (ZMod N)ˣ` and a domain of characteristic zero with
enough roots of unity, the Dirichlet characters are orthogonal, so the group determinant is
nonzero exactly when no eigenvalue `∑ᵤ χ(u) g(u)` vanishes.

Applied to `g(u) = 2 Pₖ₊₁ Mᵏ Bₖ(⟨u⟩ / M)`, corrected at `u = ±1` so that the eigenvalues of the
characters of the wrong parity are `±2` instead of `0`, this gives one nonzero integer `D`,
depending only on `M` and `k ≥ 2`, that is divisible by `Pₖ₊₁ M Bₖ,ψ` in `ℤ[ψ]` for every Dirichlet
character `ψ` modulo `M` with `ψ(-1) = (-1)ᵏ`, with values in any `ℚ`-algebra. Here
`Pₖ₊₁ = primorial (k + 1)`, and `Bₖ,ψ` is Tau Ceti's `DirichletCharacter.generalizedBernoulli`
at the modulus `M`. That `D ≠ 0` is proved through the complex characters, whose Bernoulli
numbers `Bₖ,ψ` of the right parity are nonzero by `DirichletCharacter.generalizedBernoulli_ne_zero`.

## Main results

* `TauCeti.det_of_div_ne_zero_iff`: the group determinant of `(ZMod N)ˣ` is nonzero
  exactly when every eigenvalue is.
* `TauCeti.exists_ne_zero_forall_eq_primorial_mul_generalizedBernoulli_mul`: the
  nonzero integer `D`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Lemma 5.26 (the group
  determinant).

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), file `src/Lib/Cyclotomic/Voronoi.lean`, declarations
`New.OddPart.det_ne_zero_of_forall_sum_mul_ne_zero` and the determinant step of
`New.OddPart.exists_isStickelbergerBound` (including the correction at `±1`). Here the
nonvanishing criterion is an equivalence, the Bernoulli values are normalised by the primorial
and stated through `DirichletCharacter.generalizedBernoulli`, and the size bound on `D` is not
included.
-/

public section

open Finset Matrix

namespace TauCeti

open DirichletCharacter

variable {N : ℕ}

/-- **Group determinants of `(ZMod N)ˣ`.** Over a domain of characteristic zero with enough roots
of unity, the determinant of the group matrix `(g(t / s))_{s,t}` of `(ZMod N)ˣ` is nonzero
exactly when no eigenvalue `∑ᵤ χ(u) g(u)`, for `χ` a Dirichlet character modulo `N`, vanishes. -/
theorem det_of_div_ne_zero_iff [NeZero N] {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod N)ˣ)] (g : (ZMod N)ˣ → R) :
    (of fun s t : (ZMod N)ˣ ↦ g (t / s)).det ≠ 0 ↔
      ∀ χ : DirichletCharacter R N, ∑ u : (ZMod N)ˣ, χ u * g u ≠ 0 := by
  refine ⟨fun hA χ hχ ↦ hA ?_, fun hg hA ↦ ?_⟩
  · have := sum_mul_dvd_det_of_div g ((χ : ZMod N →* R).comp (Units.coeHom _))
    simp only [MulChar.coe_comp_coeHom_apply] at this
    rwa [hχ, zero_dvd_iff] at this
  -- a vector in the left kernel is orthogonal to every character, hence zero
  obtain ⟨w, hw0, hw⟩ := exists_vecMul_eq_zero_iff.2 hA
  have horth (χ : DirichletCharacter R N) : w ⬝ᵥ (fun t ↦ χ t) = 0 := by
    have h := congrArg (dotProduct w) (of_div_mulVec g ((χ : ZMod N →* R).comp (Units.coeHom _)))
    rw [dotProduct_mulVec, hw, zero_dotProduct, dotProduct_smul, smul_eq_mul] at h
    simp only [MulChar.coe_comp_coeHom_apply] at h
    exact (mul_eq_zero.1 h.symm).resolve_left (hg χ)
  refine hw0 (funext fun a ↦ ?_)
  have hsum : ∑ χ : DirichletCharacter R N, (w ⬝ᵥ fun t ↦ χ t) * χ (a⁻¹ : (ZMod N)ˣ) = 0 := by
    simp [horth]
  simp only [dotProduct, sum_mul, mul_assoc] at hsum
  rw [sum_comm] at hsum
  simp only [← mul_sum, ← map_mul, sum_characters_eq] at hsum
  simp only [mul_ite, mul_zero, Units.mul_inv_eq_one, Units.val_inj, Finset.sum_ite_eq',
    mem_univ, ite_true] at hsum
  exact (mul_eq_zero.1 hsum).resolve_right (by exact_mod_cast (Nat.totient_pos.2
    (Nat.pos_of_ne_zero (NeZero.ne N))).ne')

/-- The Bernoulli eigenvalue: with `β(t) = Pₖ₊₁ Mᵏ Bₖ(⟨t⟩ / M)`, `∑ᵤ ψ(u) β(u) = Pₖ₊₁ M Bₖ,ψ`. -/
private theorem sum_units_mul_eq_primorial_mul_generalizedBernoulli {M : ℕ} [NeZero M] {k : ℕ}
    (hk : 2 ≤ k) {R : Type*} [CommRing R] [Algebra ℚ R] (ψ : DirichletCharacter R M)
    (β : ZMod M → ℤ)
    (hβ : ∀ t : ZMod M, (β t : ℚ) =
      primorial (k + 1) * M ^ k * (Polynomial.bernoulli k).eval ((t.val : ℚ) / M)) :
    ∑ u : (ZMod M)ˣ, ψ u * (β u : R) = primorial (k + 1) * M * ψ.generalizedBernoulli k := by
  rw [generalizedBernoulli_eq_pow_mul_sum_bernoulli_eval _ hk, ψ.sum_mul_eq_sum_units, mul_sum,
    mul_sum]
  refine sum_congr rfl fun u _ ↦ ?_
  have h := congrArg (algebraMap ℚ R) (hβ u)
  simp only [map_intCast, map_mul, map_pow, map_natCast] at h
  rw [show (M : R) ^ k = M ^ (k - 1) * M by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]] at h
  rw [h]
  ring

/-- The Bernoulli entries `2 β(u)` of the group matrix, corrected at `u = ±1` so that the
characters of the wrong parity get the eigenvalue `±2`. -/
private def correctedEntry {M : ℕ} (k : ℕ) (β : ZMod M → ℤ) (u : (ZMod M)ˣ) : ℤ :=
  2 * β u + (if u = 1 then -(-1) ^ k else 0) + if u = -1 then 1 else 0

/-- The eigenvalue of `χ` on the corrected group matrix. -/
private theorem sum_mul_correctedEntry {M : ℕ} [NeZero M] {R : Type*} [CommRing R]
    (χ : (ZMod M)ˣ →* R) (k : ℕ) (β : ZMod M → ℤ) :
    ∑ u, χ u * (correctedEntry k β u : R) = 2 * ∑ u, χ u * (β u : R) - (-1) ^ k + χ (-1) := by
  simp [correctedEntry, mul_add, sum_add_distrib, mul_sum, mul_left_comm, sub_eq_add_neg]

/-- **A nonzero integer divisible by the Bernoulli numbers of all characters of one parity.**
For `M ≥ 1` and `k ≥ 2` there is a nonzero integer `D` such that for every `ℚ`-algebra `R` and
every Dirichlet character `ψ` modulo `M` with values in `R` and `ψ(-1) = (-1)ᵏ`,
`D = Pₖ₊₁ M Bₖ,ψ x` for some `x` in the subring `ℤ[ψ]` generated by the values of `ψ`, where
`Pₖ₊₁ = primorial (k + 1)` and `Bₖ,ψ` is the generalized Bernoulli number at the modulus `M`.
It is the determinant of a group matrix of `(ZMod M)ˣ`. -/
theorem exists_ne_zero_forall_eq_primorial_mul_generalizedBernoulli_mul (M : ℕ) [NeZero M]
    {k : ℕ} (hk : 2 ≤ k) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ (R : Type*) [CommRing R] [Algebra ℚ R] (ψ : DirichletCharacter R M),
      ψ (-1) = (-1) ^ k → ∃ x ∈ Algebra.adjoin ℤ (Set.range ψ),
        (D : R) = primorial (k + 1) * M * ψ.generalizedBernoulli k * x := by
  choose β hβ using fun t : ZMod M ↦
    exists_intCast_eq_primorial_mul_pow_mul_bernoulli_eval k (NeZero.ne M) t.val
  -- the group matrix, corrected at `±1` so that the characters of the wrong parity have
  -- eigenvalue `±2`
  let g := correctedEntry k β
  let A := of fun s t : (ZMod M)ˣ ↦ g (t / s)
  -- the eigenvalue of a character
  refine ⟨A.det, ?_, fun R _ _ ψ hψ ↦ ?_⟩
  · -- over `ℂ`, no eigenvalue vanishes
    have hC : (A.map ((↑) : ℤ → ℂ)).det ≠ 0 := by
      refine (det_of_div_ne_zero_iff (fun u ↦ (g u : ℂ))).2 fun χ ↦ ?_
      have h := sum_mul_correctedEntry ((χ : ZMod M →* ℂ).comp (Units.coeHom (ZMod M))) k β
      simp only [MulChar.coe_comp_coeHom_apply, Units.val_neg, Units.val_one] at h
      rw [h, sum_units_mul_eq_primorial_mul_generalizedBernoulli hk χ β hβ]
      -- same parity: `Bₖ,χ ≠ 0`; opposite parity: `Bₖ,χ = 0` and the eigenvalue is `-2 (-1)ᵏ`
      by_cases hχ : χ (-1) = (-1) ^ k
      · rw [hχ, sub_add_cancel]
        exact mul_ne_zero two_ne_zero (mul_ne_zero (mul_ne_zero (mod_cast primorial_ne_zero _)
          (mod_cast NeZero.ne M)) (generalizedBernoulli_ne_zero hk hχ))
      · have h1 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
        have h2 : χ (-1) * χ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
        have hsq : (χ (-1) - (-1) ^ k) * (χ (-1) + (-1) ^ k) = 0 := by
          linear_combination h2 - h1
        have hneg : χ (-1) = -(-1) ^ k :=
          eq_neg_of_add_eq_zero_left ((mul_eq_zero.1 hsq).resolve_left (sub_ne_zero.2 hχ))
        rw [(generalizedBernoulli_eq_zero_iff hk).2 hneg, hneg]
        simp
    intro h0
    have h := (Int.castRingHom ℂ).map_det A
    rw [h0, map_zero] at h
    exact hC h.symm
  -- in `S = ℤ[ψ]`, the eigenvalue of `ψ` divides the determinant
  set S := Algebra.adjoin ℤ (Set.range ψ)
  let χ : (ZMod M)ˣ →* S := ((ψ : ZMod M →* R).comp (Units.coeHom (ZMod M))).codRestrict
    S.toSubmonoid fun u ↦ Algebra.subset_adjoin ⟨u, rfl⟩
  obtain ⟨y, hy⟩ := sum_mul_dvd_det_of_div (fun u ↦ (g u : S)) χ
  have hdet : (A.det : S) = (of fun s t : (ZMod M)ˣ ↦ (g (t / s) : S)).det := by
    exact (Int.castRingHom S).map_det A
  refine ⟨2 * (y : R), S.mul_mem (S.natCast_mem 2) y.property, ?_⟩
  -- the eigenvalue of `ψ` is `2 Pₖ₊₁ M Bₖ,ψ`
  have h := congrArg S.val (hdet.trans hy)
  rw [map_intCast, map_mul, show ∑ u, χ u * ((g u : ℤ) : S) =
    2 * ∑ u, χ u * (β u : S) - (-1) ^ k + χ (-1) from sum_mul_correctedEntry χ k β] at h
  simp only [map_sum, map_mul, map_sub, map_add, map_pow, map_neg, map_one, map_ofNat,
    map_intCast, Subalgebra.coe_val, χ, MonoidHom.codRestrict_apply,
    MulChar.coe_comp_coeHom_apply, Units.val_neg, Units.val_one] at h
  rw [sum_units_mul_eq_primorial_mul_generalizedBernoulli hk ψ β hβ, hψ] at h
  rw [h]
  ring

end TauCeti
