/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.CosetMap
public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Gamma1
public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Normalized
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Diamond
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Gamma0

import TauCeti.NumberTheory.ModularForms.AtkinLehner.DoubleCoset
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Conjugation

/-!
# Atkin–Lehner operators and Hecke operators

For an exact divisor `Q` of `N`, the Atkin–Lehner operator `W_Q` on `M_k(Γ₀(N))` commutes with
the Hecke operator `[Γ₀(N) α Γ₀(N)]` of every double coset whose determinant is coprime to `Q`,
and so does its normalization `𝒲_Q`; likewise on `S_k(Γ₀(N))`. These results are strictly
coset-by-coset. Once a future identification theorem expresses the classical `Tₙ` and `U_p`
operators as the relevant sums of Γ₀ double-coset slash operators, they will imply the
corresponding commutation statements for those classical operators; that identification is not
proved here.

The proof is `HeckeRing.GL2.heckeSlashSum_slash_of_mem_normalizer` applied to the Atkin–Lehner
matrix read in `GL(2, ℚ)`: that matrix normalizes `Γ₀(N)`
(`TauCeti.IsAtkinLehnerMatrix.mem_normalizer_map_mapGL`) and fixes each double coset of
determinant coprime to `Q` (`TauCeti.IsAtkinLehnerMatrix.inv_mul_mul_mem_doubleCoset`).

The statements are for every Atkin–Lehner matrix of a divisor `Q ∣ N`, not only the standard one
the operators `Nat.IsExactDivisor.atkinLehnerOperator` are built from.

## On `Γ₁(N)`

On `M_k(Γ₁(N))` the operator `W_Q` does not commute with `Tₙ` but twists it by a diamond
operator: for `n` coprime to `N`,

`W_Q (Tₙ f) = ⟨u⟩ (Tₙ (W_Q f))`,   `u ≡ n⁻¹ (mod Q)`,   `u ≡ 1 (mod N / Q)`.

For an Atkin–Lehner matrix `W = !![Q, 1; N z, Q w]` of Atkin and Li's shape this is a matrix
identity `diag(1, n) · W = W · A · diag(1, n) · Tʲ` with `A ∈ Γ₀(N)` of diamond label `u`, read
through the trace description of `Tₙ`: the upper-left entry `Q` of `W` is invertible modulo `n`,
which is what lets the right-hand factor be a power of `T`. Every other Atkin–Lehner matrix for
`Q` is `γ W` with `γ ∈ Γ₀(N)`, and `⟨d_γ⟩` commutes with `Tₙ`
(`HeckeRing.GL2.commute_heckeTNat_diamondOp`), so the identity holds for all of them. At `Q = N`
it is the Fricke relation `W_N Tₙ = ⟨n⟩⁻¹ Tₙ W_N` (`TauCeti.frickeOperator_heckeTNat`).

On a nebentypus space `M_k(N, χ)` with `χ = ψ · φ` split along `N = Q · (N / Q)`, the diamond
twist is the scalar `ψ(n)`: `W_Q (Tₙ f) = ψ(n) Tₙ (W_Q f)`. So `W_Q` carries a good Hecke
eigenform of `S_k(N, ψ φ)` with eigenvalues `λₙ` to a good Hecke eigenform of `S_k(N, ψ⁻¹ φ)`
with eigenvalues `ψ(n)⁻¹ λₙ`, the input to Atkin and Li's pseudo-eigenvalues of newforms.

## Main results

* `TauCeti.commute_atkinLehnerOperator_heckeSlashGamma0ModularFormEnd`,
  `TauCeti.commute_atkinLehnerOperatorCusp_heckeSlashGamma0CuspFormEnd`: the raw operator `W_Q`
  commutes with each Hecke operator of determinant coprime to `Q`.
* In the namespace `TauCeti.Nat.IsExactDivisor`,
  `commute_normalizedAtkinLehnerOperator_heckeSlashGamma0ModularFormEnd` and
  `commute_normalizedAtkinLehnerOperatorCusp_heckeSlashGamma0CuspFormEnd`: so does the normalized
  operator `𝒲_Q`.
* `TauCeti.atkinLehnerOperatorGamma1_heckeTNat`,
  `TauCeti.atkinLehnerOperatorGamma1Cusp_heckeTCuspNat`: on `Γ₁(N)`, `W_Q Tₙ = ⟨u⟩ Tₙ W_Q` for `n`
  coprime to `N`.
* `TauCeti.atkinLehnerOperatorGamma1_heckeTNat_of_mem_modFormCharSpace`,
  `TauCeti.atkinLehnerOperatorGamma1Cusp_heckeTCuspNat_of_mem_cuspFormCharSpace`: on `M_k(N, ψ φ)`
  and `S_k(N, ψ φ)`, `W_Q Tₙ = ψ(n) Tₙ W_Q`.
* `TauCeti.heckeTCuspNat_atkinLehnerOperatorGamma1Cusp_eq_smul_iff_heckeTCuspNat_eq_smul`: `W_Q`
  turns a good Hecke eigenvalue `c` of `f ∈ S_k(N, ψ φ)` into `ψ(n)⁻¹ c`.

## References

* A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*, Math. Ann. 185 (1970), 134–160.
* A. O. L. Atkin and W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of
  `W`-operators*, Invent. Math. **48** (1978), 221–243, §1.
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
  have hnorm := h.mem_normalizer_map_mapGL hQN hw
  obtain ⟨A, hA, -⟩ := (mem_Delta0_iff N).mp (Quotient.out D).2
  exact heckeSlashSum_slash_of_mem_normalizer k D hnorm hnorm
    (h.inv_mul_mul_mem_doubleCoset hQN hw (Quotient.out D).2 hA (hD A hA)) f hf

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

/-! ### The good Hecke operators on `Γ₁(N)` -/

section Gamma1

open DoubleCoset HeckeRing.GLn
open scoped Pointwise

local notation "φ" => Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ ℝ)

variable {n : ℕ} [NeZero n]

omit [NeZero N] in
/-- **`diag(1, n)` moves across an Atkin–Lehner matrix of Atkin–Li shape.** For `n` coprime to
`N` there are an Atkin–Lehner matrix `W` for `Q`, `A ∈ Γ₀(N)` and `B ∈ Γ₁(N)` with
`diag(1, n) · W = W · A · diag(1, n) · B`, where the diamond label of `A` is `n⁻¹` modulo `Q` and
`1` modulo `N / Q`. The matrix `W = !![Q, 1; N z, Q w]` has the shape of Atkin and Li's: its
upper-left entry `Q` is invertible modulo `n`, which lets `B` be a power of `T`. -/
private lemma exists_natDiagGL_mul_atkinLehnerGL_eq (h : Q ∥ N) (hn : n.Coprime N) :
    ∃ M : Matrix (Fin 2) (Fin 2) ℤ, ∃ hM : IsAtkinLehnerMatrix N Q M,
      ∃ A : SL(2, ℤ), ∃ hA : A ∈ Gamma0 N,
        ZMod.unitsMap h.dvd ((Gamma0Map N).toHomUnits ⟨A, hA⟩) =
            (ZMod.unitOfCoprime n (hn.coprime_dvd_right h.dvd))⁻¹ ∧
          ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd) ((Gamma0Map N).toHomUnits ⟨A, hA⟩) = 1 ∧
          ∃ B ∈ Gamma1 N, φ (natDiagGL 2 ![1, n]) * atkinLehnerGL h.pos hM =
            atkinLehnerGL h.pos hM * mapGL ℝ A * φ (natDiagGL 2 ![1, n] * mapGL ℚ B) := by
  set m := N / Q with hm
  have hNm : N = Q * m := (Nat.mul_div_cancel' h.dvd).symm
  have hN : (N : ℤ) = Q * m := by exact_mod_cast hNm
  set a : ℤ := Nat.gcdA Q m
  set b : ℤ := Nat.gcdB Q m
  have hred : (Q : ℤ) * a + m * b = 1 := by
    have := Nat.gcd_eq_gcd_ab Q m
    rw [h.coprime, Nat.cast_one] at this
    exact this.symm
  obtain ⟨j, l, hjl⟩ := Nat.isCoprime_iff_coprime.mpr (hn.coprime_dvd_right h.dvd).symm
  -- the integral matrices of `diag(1, n)`, `W`, `A` and `B = Tʲ`
  set X : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, (n : ℤ)]
  set W : Matrix (Fin 2) (Fin 2) ℤ := !![(Q : ℤ) * 1, 1; (Q : ℤ) * m * -b, (Q : ℤ) * a]
  have hW : IsAtkinLehnerMatrix N Q W :=
    isAtkinLehnerMatrix_of_entries hNm 1 1 (-b) a (by linear_combination hred)
  set Am : Matrix (Fin 2) (Fin 2) ℤ :=
    !![Q * a + n * m * b, a * l - a - j * m * b;
      -((Q : ℤ) * m) * b * (n - 1), Q * a + j * (Q * m) * b + m * b * l]
  set Bm : Matrix (Fin 2) (Fin 2) ℤ := !![1, j; 0, 1]
  have key : X * W = W * Am * X * Bm := by
    simp only [X, W, Am, Bm, Matrix.mul_fin_two]
    congrm !![?_, ?_; ?_, ?_]
    · linear_combination (-(Q : ℤ)) * hred
    · linear_combination (-1 : ℤ) * hred - (Q * a + m * b) * hjl
    · linear_combination ((n : ℤ) * Q * m * b) * hred
    · linear_combination (-((n : ℤ) * Q * a)) * hred
  have hdetAm : Am.det = 1 := by
    have hdet := congrArg Matrix.det key
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, hW.det_eq] at hdet
    have hX : X.det = n := by simp [X, Matrix.det_fin_two_of]
    have hB : Bm.det = 1 := by simp [Bm, Matrix.det_fin_two_of]
    rw [hX, hB] at hdet
    have hQn : (Q : ℤ) * n ≠ 0 :=
      mul_ne_zero (by exact_mod_cast h.pos.ne') (by exact_mod_cast NeZero.ne n)
    exact mul_left_cancel₀ hQn (by linear_combination -hdet)
  let A : SL(2, ℤ) := ⟨Am, hdetAm⟩
  let B : SL(2, ℤ) := ⟨Bm, by simp [Bm, Matrix.det_fin_two_of]⟩
  have hA : A ∈ Gamma0 N := mem_Gamma0_iff_dvd.mpr ⟨-b * (n - 1), by simp [A, Am, hN]; ring⟩
  -- the diamond label of `A` is its lower-right entry
  have hlabel : (((Gamma0Map N).toHomUnits ⟨A, hA⟩ : (ZMod N)ˣ) : ZMod N) =
      ((Q * a + j * (Q * m) * b + m * b * l : ℤ) : ZMod N) := by
    simp [A, Am, Gamma0Map_apply]
  refine ⟨W, hW, A, hA, eq_inv_of_mul_eq_one_left (Units.ext ?_), Units.ext ?_, B,
    mem_Gamma1_of_dvd_lowerRow (by simp [B, Bm]) (by simp [B, Bm]), Units.ext ?_⟩
  · -- modulo `Q`, the label times `n` is `1`
    rw [Units.val_mul, ZMod.unitsMap_val, hlabel, ZMod.cast_intCast h.dvd,
      ZMod.coe_unitOfCoprime, Units.val_one]
    have hmod : (Q * a + j * (Q * m) * b + m * b * l) * (n : ℤ) =
        1 + Q * (n * a + n * j * m * b - n * l * a - j) := by
      linear_combination ((n : ℤ) * l) * hred + hjl
    have := congrArg (Int.cast : ℤ → ZMod Q) hmod
    push_cast [ZMod.natCast_self] at this
    simpa using this
  · -- modulo `N / Q`, the label is `1`
    rw [ZMod.unitsMap_val, hlabel, ZMod.cast_intCast (Nat.div_dvd_of_dvd h.dvd), Units.val_one]
    have hmod : Q * a + j * (Q * m) * b + m * b * l = 1 + m * (b * (j * Q + l - 1)) := by
      linear_combination hred
    rw [hmod]
    push_cast [← hm, ZMod.natCast_self]
    ring
  · -- the matrix identity, read in `GL (Fin 2) ℝ`
    have hX : (↑(φ (natDiagGL 2 ![1, n])) : Matrix (Fin 2) (Fin 2) ℝ) = X.map (↑) := by
      rw [Matrix.GeneralLinearGroup.val_map_apply, coe_map_natDiagGL_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [X]
    have hφB : (↑(φ (natDiagGL 2 ![1, n] * mapGL ℚ B)) : Matrix (Fin 2) (Fin 2) ℝ) =
        (X * Bm).map (↑) := by
      -- `mapGL` of the literal `B = ⟨Bm, _⟩` is `Bm` with its entries cast, by definition
      rw [map_mul, Units.val_mul, hX, Matrix.map_mul_intCast, map_mapGL]
      rfl
    -- likewise for the literal `A = ⟨Am, _⟩`
    have hAm : (↑(mapGL ℝ A) : Matrix (Fin 2) (Fin 2) ℝ) = Am.map (↑) := by
      rw [mapGL_coe_matrix]
      rfl
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hX, hφB, coe_atkinLehnerGL, hAm,
      ← Matrix.map_mul_intCast, ← Matrix.map_mul_intCast, ← Matrix.map_mul_intCast, key]
    simp only [Matrix.mul_assoc]

/-- The trace argument behind `atkinLehnerOperatorGamma1_heckeTNat`: a factorization
`diag(1, n) · W = W · A · diag(1, n) · B` with `A ∈ Γ₀(N)` and `B ∈ Γ₁(N)` gives
`W_Q (Tₙ f) = Tₙ (⟨d_A⟩ (W_Q f))`. -/
private lemma atkinLehnerOperatorGamma1_heckeTNat_of_mul_eq (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) {A : SL(2, ℤ)} (hA : A ∈ Gamma0 N) {B : SL(2, ℤ)}
    (hB : B ∈ Gamma1 N)
    (hmul : φ (natDiagGL 2 ![1, n]) * atkinLehnerGL hQ h =
      atkinLehnerGL hQ h * mapGL ℝ A * φ (natDiagGL 2 ![1, n] * mapGL ℚ B))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    atkinLehnerOperatorGamma1 hQ hQN h k (heckeTNat k n f) =
      heckeTNat k n (diamondOp k ((Gamma0Map N).toHomUnits ⟨A, hA⟩)
        (atkinLehnerOperatorGamma1 hQ hQN h k f)) := by
  have hδ₀ : natDiagGL 2 ![1, n] ∈ doubleCoset ((diagCosetGamma1 N n).out : GL (Fin 2) ℚ)
      ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) := by
    rw [doubleCoset_out_diagCosetGamma1_eq_doubleCoset_natDiagGL]
    exact mem_doubleCoset_self _ _ _
  have hδ : natDiagGL 2 ![1, n] * mapGL ℚ B ∈
      doubleCoset ((diagCosetGamma1 N n).out : GL (Fin 2) ℚ)
        ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) := by
    rw [doubleCoset_out_diagCosetGamma1_eq_doubleCoset_natDiagGL]
    exact mem_doubleCoset.mpr
      ⟨1, one_mem _, mapGL ℚ B, Subgroup.mem_map_of_mem _ hB, by rw [one_mul]⟩
  have := finite_decompQuotient_inv_of_mem_doubleCoset hδ₀
  have : (ConjAct.toConjAct (φ (natDiagGL 2 ![1, n]))⁻¹ •
      (Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma1 N).map (mapGL ℝ)) := by
    rw [← Subgroup.map_mapGL (S := ℚ) (Gamma1 N)]
    exact isFiniteRelIndex_ratCast_conj
  -- the translate by `diag(1, n) · W` has the level of the translate by `diag(1, n) · B`,
  -- because `W` and `A` normalize `Γ₁(N)`
  have hlevel : ConjAct.toConjAct (φ (natDiagGL 2 ![1, n]) * atkinLehnerGL hQ h)⁻¹ •
      (Gamma1 N).map (mapGL ℝ) =
      ConjAct.toConjAct (φ (natDiagGL 2 ![1, n] * mapGL ℚ B))⁻¹ • (Gamma1 N).map (mapGL ℝ) := by
    rw [hmul, mul_assoc, _root_.mul_inv_rev, map_mul, mul_smul,
      Gamma1_map_inv_conjAct_atkinLehnerGL_eq hQ hQN h, conjAct_mapGL_mul_smul_Gamma1 hA]
  have := finite_decompQuotient_inv_of_mem_doubleCoset hδ
  have : (ConjAct.toConjAct (φ (natDiagGL 2 ![1, n] * mapGL ℚ B))⁻¹ •
      (Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma1 N).map (mapGL ℝ)) := by
    rw [← Subgroup.map_mapGL (S := ℚ) (Gamma1 N)]
    exact isFiniteRelIndex_ratCast_conj
  have : (ConjAct.toConjAct (φ (natDiagGL 2 ![1, n]) * atkinLehnerGL hQ h)⁻¹ •
      (Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma1 N).map (mapGL ℝ)) := hlevel ▸ ‹_›
  have hW : atkinLehnerGL hQ h ∈
      Subgroup.normalizer ((Gamma1 N).map (mapGL ℝ) : Set (GL (Fin 2) ℝ)) :=
    (Subgroup.normalizer _).inv_mem_iff.mp
      (Subgroup.conjAct_pointwise_smul_iff.mp (Gamma1_map_inv_conjAct_atkinLehnerGL_eq hQ hQN h))
  apply DFunLike.coe_injective
  rw [coe_atkinLehnerOperatorGamma1, coe_heckeTNat, coe_heckeTNat,
    heckeSlashSum_eq_coe_trace_translate k (diagCosetGamma1 N n) hδ₀
      (Subgroup.map_mapGL (Gamma1 N)) (Subgroup.map_mapGL (Gamma1 N)) f,
    heckeSlashSum_eq_coe_trace_translate k (diagCosetGamma1 N n) hδ
      (Subgroup.map_mapGL (Gamma1 N)) (Subgroup.map_mapGL (Gamma1 N)),
    ← SlashInvariantForm.coe_trace_translate_mul_of_mem_normalizer f _ hW]
  refine congrArg DFunLike.coe (SlashInvariantForm.trace_eq_of_eq_of_coe_eq hlevel ?_)
  rw [_root_.SlashInvariantForm.coe_translate, _root_.SlashInvariantForm.coe_translate,
    coe_diamondOp k _ ⟨A, hA⟩ rfl, coe_atkinLehnerOperatorGamma1, ← SlashAction.slash_mul,
    ← SlashAction.slash_mul, hmul, mul_assoc]

/-- **`W_Q` transports a good `Tₙ` to a diamond twist of `Tₙ`** on `M_k(Γ₁(N))`: for `n` coprime
to `N`, `W_Q (Tₙ f) = ⟨u⟩ (Tₙ (W_Q f))`, where `u ∈ (ZMod N)ˣ` is `n⁻¹` modulo `Q` and `1` modulo
`N / Q`. At `Q = N` this is the Fricke relation `W_N Tₙ = ⟨n⟩⁻¹ Tₙ W_N`; on a nebentypus space
`⟨u⟩` becomes the scalar of `atkinLehnerOperatorGamma1_heckeTNat_of_mem_modFormCharSpace`. -/
theorem atkinLehnerOperatorGamma1_heckeTNat (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (hn : n.Coprime N) {u : (ZMod N)ˣ}
    (hu : ZMod.unitsMap hQN u = (ZMod.unitOfCoprime n (hn.coprime_dvd_right hQN))⁻¹)
    (hu' : ZMod.unitsMap (Nat.div_dvd_of_dvd hQN) u = 1)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    atkinLehnerOperatorGamma1 hQ hQN h k (heckeTNat k n f) =
      diamondOp k u (heckeTNat k n (atkinLehnerOperatorGamma1 hQ hQN h k f)) := by
  have hQN' := h.isExactDivisor hQ.ne' hQN
  obtain ⟨M₀, h₀, A, hA, hAQ, hAm, B, hB, hmul⟩ := exists_natDiagGL_mul_atkinLehnerGL_eq hQN' hn
  have hAu : (Gamma0Map N).toHomUnits ⟨A, hA⟩ = u :=
    hQN'.unitsEquivProd.injective <| Prod.ext
      (by rw [Nat.IsExactDivisor.unitsEquivProd_apply_fst,
        Nat.IsExactDivisor.unitsEquivProd_apply_fst, hAQ, hu])
      (by rw [Nat.IsExactDivisor.unitsEquivProd_apply_snd,
        Nat.IsExactDivisor.unitsEquivProd_apply_snd, hAm, hu'])
  -- every Atkin–Lehner matrix for `Q` is `γ W₀` with `γ ∈ Γ₀(N)`, and `⟨d_γ⟩` commutes with `Tₙ`
  obtain ⟨γ, hγ, rfl⟩ := h₀.exists_mem_Gamma0_eq_mul_left hQ.ne' hQN h
  have hc := fun g ↦ DFunLike.congr_fun
    (commute_heckeTNat_diamondOp k hn ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩)).eq g
  have hc' := DFunLike.congr_fun (commute_heckeTNat_diamondOp k hn u).eq
  simp only [Module.End.mul_apply] at hc hc'
  rw [atkinLehnerOperatorGamma1_mul_left hQ hQN h₀ k hγ, LinearMap.comp_apply,
    LinearMap.comp_apply, ← hc, ← hc', ← hAu]
  exact atkinLehnerOperatorGamma1_heckeTNat_of_mul_eq hQ hQN h₀ hA hB hmul _

/-- **`W_Q` transports a good `Tₙ` to a diamond twist of `Tₙ`** on `S_k(Γ₁(N))`: the cusp-form
counterpart of `atkinLehnerOperatorGamma1_heckeTNat`. -/
theorem atkinLehnerOperatorGamma1Cusp_heckeTCuspNat (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (hn : n.Coprime N) {u : (ZMod N)ˣ}
    (hu : ZMod.unitsMap hQN u = (ZMod.unitOfCoprime n (hn.coprime_dvd_right hQN))⁻¹)
    (hu' : ZMod.unitsMap (Nat.div_dvd_of_dvd hQN) u = 1)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    atkinLehnerOperatorGamma1Cusp hQ hQN h k (heckeTCuspNat k n f) =
      diamondOpCusp k u (heckeTCuspNat k n (atkinLehnerOperatorGamma1Cusp hQ hQN h k f)) := by
  apply CuspForm.toModularFormₗ_injective
  simpa only [CuspForm.toModularFormₗ_eq_coe, atkinLehnerOperatorGamma1_coe_cuspForm,
    heckeTNat_coe_cuspForm, diamondOp_coe_cuspForm] using
    atkinLehnerOperatorGamma1_heckeTNat hQ hQN h hn hu hu'
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)

end Gamma1

/-! ### The good Hecke operators on a nebentypus space -/

section Nebentypus

variable {n : ℕ} [NeZero n] (ψ : (ZMod Q)ˣ →* ℂˣ) (φ : (ZMod (N / Q))ˣ →* ℂˣ)

omit [NeZero N] [NeZero n] in
/-- The unit of `atkinLehnerOperatorGamma1_heckeTNat` exists, and on the image of `W_Q` its
diamond operator is the scalar `ψ(n)`, for a nebentypus `ψ · φ` split along `N = Q · (N / Q)`. -/
private lemma exists_unit_charSpace_eq (hQN : Q ∥ N) (hn : n.Coprime N) :
    ∃ u : (ZMod N)ˣ,
      ZMod.unitsMap hQN.dvd u = (ZMod.unitOfCoprime n (hn.coprime_dvd_right hQN.dvd))⁻¹ ∧
        ZMod.unitsMap (Nat.div_dvd_of_dvd hQN.dvd) u = 1 ∧
        ((ψ.comp (ZMod.unitsMap hQN.dvd) * φ.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hQN.dvd))).comp
          (hQN.unitsInvPart : (ZMod N)ˣ →* (ZMod N)ˣ) u : ℂ) =
          ψ (ZMod.unitOfCoprime n (hn.coprime_dvd_right hQN.dvd)) := by
  set u := hQN.unitsEquivProd.symm ((ZMod.unitOfCoprime n (hn.coprime_dvd_right hQN.dvd))⁻¹, 1)
  have hu : ZMod.unitsMap hQN.dvd u = (ZMod.unitOfCoprime n (hn.coprime_dvd_right hQN.dvd))⁻¹ := by
    rw [← Nat.IsExactDivisor.unitsEquivProd_apply_fst hQN, MulEquiv.apply_symm_apply]
  have hu' : ZMod.unitsMap (Nat.div_dvd_of_dvd hQN.dvd) u = 1 := by
    rw [← Nat.IsExactDivisor.unitsEquivProd_apply_snd hQN, MulEquiv.apply_symm_apply]
  refine ⟨u, hu, hu', ?_⟩
  simp [Nat.IsExactDivisor.unitsMap_unitsInvPart_left,
    Nat.IsExactDivisor.unitsMap_unitsInvPart_right, hu, hu']

/-- **On a nebentypus space, `W_Q` moves a good `Tₙ` past it at the cost of `ψ(n)`**: if
`f ∈ M_k(N, χ)` with `χ = ψ · φ` split along `N = Q · (N / Q)`, then
`W_Q (Tₙ f) = ψ(n) Tₙ (W_Q f)` for `n` coprime to `N`. So if `f` is an eigenform of a good `Tₙ`,
then so is `W_Q f ∈ M_k(N, ψ⁻¹ φ)`, with eigenvalue multiplied by `ψ(n)⁻¹`, as Atkin and Li
compute. At `Q = N` the scalar is `χ(n)`, the Fricke case. -/
theorem atkinLehnerOperatorGamma1_heckeTNat_of_mem_modFormCharSpace (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (hn : n.Coprime N)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k
      (ψ.comp (ZMod.unitsMap hQN) * φ.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hQN)))) :
    atkinLehnerOperatorGamma1 hQ hQN h k (heckeTNat k n f) =
      (ψ (ZMod.unitOfCoprime n (hn.coprime_dvd_right hQN)) : ℂ) •
        heckeTNat k n (atkinLehnerOperatorGamma1 hQ hQN h k f) := by
  obtain ⟨u, hu, hu', hψ⟩ := exists_unit_charSpace_eq ψ φ (h.isExactDivisor hQ.ne' hQN) hn
  have hc := DFunLike.congr_fun (commute_heckeTNat_diamondOp k hn u).eq
    (atkinLehnerOperatorGamma1 hQ hQN h k f)
  simp only [Module.End.mul_apply] at hc
  rw [atkinLehnerOperatorGamma1_heckeTNat hQ hQN h hn hu hu', ← hc,
    diamondOp_apply_of_mem_modFormCharSpace k _ u
      (atkinLehnerOperatorGamma1_mem_modFormCharSpace hQ hQN h hf), map_smul, hψ]

/-- **On a nebentypus space of cusp forms, `W_Q` moves a good `Tₙ` past it at the cost of
`ψ(n)`**: the cusp-form counterpart of
`atkinLehnerOperatorGamma1_heckeTNat_of_mem_modFormCharSpace`. -/
theorem atkinLehnerOperatorGamma1Cusp_heckeTCuspNat_of_mem_cuspFormCharSpace (hQ : 0 < Q)
    (hQN : Q ∣ N) (h : IsAtkinLehnerMatrix N Q M) (hn : n.Coprime N)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k
      (ψ.comp (ZMod.unitsMap hQN) * φ.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hQN)))) :
    atkinLehnerOperatorGamma1Cusp hQ hQN h k (heckeTCuspNat k n f) =
      (ψ (ZMod.unitOfCoprime n (hn.coprime_dvd_right hQN)) : ℂ) •
        heckeTCuspNat k n (atkinLehnerOperatorGamma1Cusp hQ hQN h k f) := by
  obtain ⟨u, hu, hu', hψ⟩ := exists_unit_charSpace_eq ψ φ (h.isExactDivisor hQ.ne' hQN) hn
  have hc := DFunLike.congr_fun (commute_heckeTCuspNat_diamondOpCusp k hn u).eq
    (atkinLehnerOperatorGamma1Cusp hQ hQN h k f)
  simp only [Module.End.mul_apply] at hc
  rw [atkinLehnerOperatorGamma1Cusp_heckeTCuspNat hQ hQN h hn hu hu', ← hc,
    diamondOpCusp_apply_of_mem_cuspFormCharSpace k _ u
      (atkinLehnerOperatorGamma1Cusp_mem_cuspFormCharSpace hQ hQN h hf), map_smul, hψ]

/-- **`W_Q` transports a good Hecke eigenvalue `c` of `f ∈ S_k(N, ψ φ)` to `ψ(n)⁻¹ c`.** The
equivalence includes the zero form and needs no normalization of coefficients. This is the
Hecke-theoretic input to Atkin and Li's pseudo-eigenvalues: if `f` is a simultaneous eigenform
of the good Hecke operators, then so is `W_Q f ∈ S_k(N, ψ⁻¹ φ)`, with the twisted eigenvalues. -/
theorem heckeTCuspNat_atkinLehnerOperatorGamma1Cusp_eq_smul_iff_heckeTCuspNat_eq_smul
   (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (hn : n.Coprime N)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k
      (ψ.comp (ZMod.unitsMap hQN) * φ.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hQN)))) (c : ℂ) :
    heckeTCuspNat k n (atkinLehnerOperatorGamma1Cusp hQ hQN h k f) =
        ((ψ (ZMod.unitOfCoprime n (hn.coprime_dvd_right hQN)) : ℂ)⁻¹ * c) •
          atkinLehnerOperatorGamma1Cusp hQ hQN h k f ↔
      heckeTCuspNat k n f = c • f := by
  have hW := atkinLehnerOperatorGamma1Cusp_heckeTCuspNat_of_mem_cuspFormCharSpace ψ φ hQ hQN h hn hf
  have ha : (ψ (ZMod.unitOfCoprime n (hn.coprime_dvd_right hQN)) : ℂ) ≠ 0 := Units.ne_zero _
  constructor
  · intro hT
    apply atkinLehnerOperatorGamma1Cusp_injective hQ hQN h k
    rw [hW, hT, map_smul, smul_smul, mul_inv_cancel_left₀ ha]
  · intro hT
    rw [hT, map_smul] at hW
    rw [← smul_smul, hW, smul_smul, inv_mul_cancel₀ ha, one_smul]

end Nebentypus

end TauCeti
