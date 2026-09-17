/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.CosetMap
public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Normalized
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Gamma0

import TauCeti.NumberTheory.ModularForms.AtkinLehner.DoubleCoset
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Conjugation

/-!
# Atkin–Lehner operators commute with the good Hecke operators

For an exact divisor `Q` of `N`, the Atkin–Lehner operator `W_Q` on `M_k(Γ₀(N))` commutes with
the Hecke operator `[Γ₀(N) α Γ₀(N)]` of every double coset whose determinant is coprime to `Q`,
and so does its normalization `𝒲_Q`; likewise on `S_k(Γ₀(N))`. The classical `Tₙ` with
`gcd(n, Q) = 1` is the sum of the double-coset operators of determinant `n` (Shimura §3.4), so
this is the commutation of the `𝒲_Q` with the Hecke operators away from `Q`, stated coset by
coset; it includes the `U_p` double cosets at the primes `p ∣ N / Q`. It is
the input that lets the good Hecke operators and the `𝒲_Q` be diagonalized simultaneously, which
is how a newform of trivial nebentypus comes to be an eigenvector of each `𝒲_Q`.

The proof is `HeckeRing.GL2.heckeSlashSum_slash_of_mem_normalizer` applied to the Atkin–Lehner
matrix read in `GL(2, ℚ)`: that matrix normalizes `Γ₀(N)`
(`TauCeti.IsAtkinLehnerMatrix.mem_normalizer_map_mapGL`) and fixes each double coset of
determinant coprime to `Q` (`TauCeti.IsAtkinLehnerMatrix.inv_mul_mul_mem_doubleCoset`).

The statements are for every Atkin–Lehner matrix of a divisor `Q ∣ N`, not only the standard one
the operators `Nat.IsExactDivisor.atkinLehnerOperator` are built from.

## Main results

* `TauCeti.commute_atkinLehnerOperator_heckeSlashGamma0ModularFormEnd`,
  `TauCeti.commute_atkinLehnerOperatorCusp_heckeSlashGamma0CuspFormEnd`: the raw operator `W_Q`
  commutes with each Hecke operator of determinant coprime to `Q`.
* In the namespace `TauCeti.Nat.IsExactDivisor`,
  `commute_normalizedAtkinLehnerOperator_heckeSlashGamma0ModularFormEnd` and
  `commute_normalizedAtkinLehnerOperatorCusp_heckeSlashGamma0CuspFormEnd`: so does the normalized
  operator `𝒲_Q`.

## References

* A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*, Math. Ann. 185 (1970), 134–160.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane HeckeRing.GL2

open scoped MatrixGroups ModularForm TauCeti.ExactDivisor

namespace TauCeti

variable {N Q : ℕ} [NeZero N] {M : Matrix (Fin 2) (Fin 2) ℤ} {k : ℤ}
  {D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))}

/-- The slash by an Atkin–Lehner matrix commutes with a slash sum of determinant coprime to `Q`,
on any function invariant under `Γ₀(N)`. -/
private lemma heckeSlashSum_slash_atkinLehnerGL (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (hD : CoprimeDetCoset N Q D) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (Gamma0 N).map (mapGL ℚ), f ∣[k] γ = f) :
    heckeSlashSum k D f ∣[k] atkinLehnerGL hQ h =
      heckeSlashSum k D (f ∣[k] atkinLehnerGL hQ h) := by
  have hdet : (M.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [← Int.cast_det, h.det_eq]
    exact_mod_cast hQ.ne'
  set w := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hw : (w : Matrix (Fin 2) (Fin 2) ℚ) = M.map (Int.cast : ℤ → ℚ) :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ hdet
  have hmap : Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) w = atkinLehnerGL hQ h := by
    ext i j
    simp [hw]
  rw [← HeckeCoset.mk_rep D, coprimeDetCoset_mk, HeckeCoset.rep_def] at hD
  rw [← hmap, ← ModularForm.rat_slash, ← ModularForm.rat_slash]
  have hnorm := h.mem_normalizer_map_mapGL hQ.ne' hQN hw
  obtain ⟨A, hA, -⟩ := (mem_Delta0_iff N).mp (Quotient.out D).2
  exact heckeSlashSum_slash_of_mem_normalizer k D hnorm hnorm
    (h.inv_mul_mul_mem_doubleCoset hQ.ne' hQN hw (Quotient.out D).2 hA (hD A hA)) f hf

/-- **The Atkin–Lehner operator `W_Q` commutes with the Hecke operator of a double coset of
determinant coprime to `Q`**, on `M_k(Γ₀(N))`. -/
theorem commute_atkinLehnerOperator_heckeSlashGamma0ModularFormEnd (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (hD : CoprimeDetCoset N Q D) :
    Commute (atkinLehnerOperator hQ hQN h k) (heckeSlashGamma0ModularFormEnd k D) := by
  refine LinearMap.ext fun f ↦ DFunLike.coe_injective ?_
  simp only [Module.End.mul_apply, coe_atkinLehnerOperator, coe_heckeSlashGamma0ModularFormEnd]
  exact heckeSlashSum_slash_atkinLehnerGL hQ hQN h hD f fun _ hγ ↦
    SlashInvariantFormClass.slash_eq_of_mem_map_mapGL f hγ

/-- **The Atkin–Lehner operator `W_Q` commutes with the Hecke operator of a double coset of
determinant coprime to `Q`**, on `S_k(Γ₀(N))`. -/
theorem commute_atkinLehnerOperatorCusp_heckeSlashGamma0CuspFormEnd (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (hD : CoprimeDetCoset N Q D) :
    Commute (atkinLehnerOperatorCusp hQ hQN h k) (heckeSlashGamma0CuspFormEnd k D) := by
  refine LinearMap.ext fun f ↦ DFunLike.coe_injective ?_
  simp only [Module.End.mul_apply, coe_atkinLehnerOperatorCusp, coe_heckeSlashGamma0CuspFormEnd]
  exact heckeSlashSum_slash_atkinLehnerGL hQ hQN h hD f fun _ hγ ↦
    SlashInvariantFormClass.slash_eq_of_mem_map_mapGL f hγ

namespace Nat.IsExactDivisor

/-- **The normalized Atkin–Lehner operator `𝒲_Q` commutes with the Hecke operator of a double
coset of determinant coprime to `Q`**, on `M_k(Γ₀(N))`. -/
theorem commute_normalizedAtkinLehnerOperator_heckeSlashGamma0ModularFormEnd (h : Q ∥ N)
    (hD : CoprimeDetCoset N Q D) :
    Commute (h.normalizedAtkinLehnerOperator k) (heckeSlashGamma0ModularFormEnd k D) := by
  rw [h.normalizedAtkinLehnerOperator_def k,
    LinearMap.ext (h.atkinLehnerOperator_eq (isAtkinLehnerMatrix_atkinLehnerMatrix h))]
  exact Commute.smul_left
    (commute_atkinLehnerOperator_heckeSlashGamma0ModularFormEnd h.pos h.dvd _ hD) _

/-- **The normalized Atkin–Lehner operator `𝒲_Q` commutes with the Hecke operator of a double
coset of determinant coprime to `Q`**, on `S_k(Γ₀(N))`. -/
theorem commute_normalizedAtkinLehnerOperatorCusp_heckeSlashGamma0CuspFormEnd (h : Q ∥ N)
    (hD : CoprimeDetCoset N Q D) :
    Commute (h.normalizedAtkinLehnerOperatorCusp k) (heckeSlashGamma0CuspFormEnd k D) := by
  rw [h.normalizedAtkinLehnerOperatorCusp_def k,
    LinearMap.ext (h.atkinLehnerOperatorCusp_eq (isAtkinLehnerMatrix_atkinLehnerMatrix h))]
  exact Commute.smul_left
    (commute_atkinLehnerOperatorCusp_heckeSlashGamma0CuspFormEnd h.pos h.dvd _ hD) _

end Nat.IsExactDivisor

end TauCeti
