/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Trace
public import TauCeti.NumberTheory.ModularForms.Petersson.Trace

/-!
# The Petersson adjoint of the Hecke operators `Tₙ` at indices prime to the level

For `n` coprime to `N`, the Hecke operator `Tₙ` on `S_k(Γ₁(N))` has Petersson adjoint
`Tₙ ⟨n⟩⁻¹`:

```text
⟪Tₙ f, g⟫ = ⟪f, Tₙ (⟨n⟩⁻¹ g)⟫.
```

On the nebentypus space `S_k(N, χ)` the diamond operator `⟨n⟩⁻¹` is the scalar `χ(n)⁻¹`, so
there the formula reads `Tₙ* = χ(n)⁻¹ Tₙ`. This relation is the input to the normality of the
good Hecke operators for the Petersson product, and hence to their simultaneous
diagonalization.

## The argument

`Tₙ` is the double coset operator of `α = diag(1, n)`, the trace of the translate of `f` by
`α` (`TauCeti.heckeTCuspNat_eq_trace_translate`). The Petersson adjoint of such an operator is
the double coset operator of the main involution `α^ι = diag(n, 1)`
(`CuspForm.peterssonInnerCosets_trace_translate`). What remains is arithmetic: identifying
`Γ₁(N) diag(n, 1) Γ₁(N)` with a diamond translate of `Γ₁(N) diag(1, n) Γ₁(N)`. Choosing `u, v`
with `u n + v N = 1`, one checks the matrix identity

```text
diag(n, 1) = !![n, -v; N, u] · diag(1, n) · !![u n, v; -N, 1],
```

whose left factor lies in `Γ₀(N)` with lower-right entry `u ≡ n⁻¹ (mod N)` and whose right
factor lies in `Γ₁(N)`. Since the left factor normalizes `Γ₁(N)`, the operator of `diag(n, 1)`
is `Tₙ` applied after the diamond operator `⟨n⁻¹⟩`.

The composite is `Tₙ ⟨n⟩⁻¹` rather than Diamond–Shurman's `⟨n⟩⁻¹ Tₙ`; the two agree once the
diamond operators are known to commute with `Tₙ`, which this file does not use.

## Main results

* `HeckeRing.GL2.peterssonInnerCosets_heckeTCuspNat`: `⟪Tₙ f, g⟫ = ⟪f, Tₙ (⟨n⟩⁻¹ g)⟫` for
  `n` coprime to `N`.
* `HeckeRing.GL2.peterssonInnerCosets_heckeTCuspNat_of_mem_cuspFormCharSpace`: for `g` in
  `S_k(N, χ)`, `⟪Tₙ f, g⟫ = ⟪f, χ(n)⁻¹ Tₙ g⟫`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.5.3.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.5.4.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
open HeckeRing.GLn
open TauCeti (adjugateGL adjugateGL_val finite_decompQuotient_inv_of_mem_doubleCoset)

open scoped MatrixGroups ModularForm Pointwise

local notation "φ" => Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ ℝ)

namespace HeckeRing.GL2

variable {N n : ℕ} [NeZero N] [NeZero n] (k : ℤ)

/-- The real matrix of `diag(1, n)`. -/
private lemma coe_map_natDiagGL_one :
    ((φ (natDiagGL 2 ![1, n]) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1, 0; 0, (n : ℝ)] := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, coe_natDiagGL_one (Nat.pos_of_neZero n)]
  fin_cases i <;> fin_cases j <;> simp

omit [NeZero N] in
/-- **The main involution of `diag(1, n)` is a diamond translate of a representative of
`Γ₁(N) diag(1, n) Γ₁(N)`.** With `u n + v N = 1`,
`diag(n, 1) = !![n, -v; N, u] · diag(1, n) · !![u n, v; -N, 1]`; the left factor lies in `Γ₀(N)`
with lower-right entry `n⁻¹ (mod N)`, and the right factor lies in `Γ₁(N)`. -/
private lemma exists_adjugateGL_natDiagGL_eq (hn : n.Coprime N) :
    ∃ A : SL(2, ℤ), ∃ hA : A ∈ Gamma0 N,
      (Gamma0Map N).toHomUnits ⟨A, hA⟩ = (ZMod.unitOfCoprime n hn)⁻¹ ∧
      ∃ B ∈ Gamma1 N, adjugateGL (φ (natDiagGL 2 ![1, n])) =
        mapGL ℝ A * φ (natDiagGL 2 ![1, n] * mapGL ℚ B) := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hn
  let A : SL(2, ℤ) :=
    ⟨!![(n : ℤ), -v; (N : ℤ), u], by rw [Matrix.det_fin_two_of]; linear_combination huv⟩
  let B : SL(2, ℤ) :=
    ⟨!![u * n, v; -(N : ℤ), 1], by rw [Matrix.det_fin_two_of]; linear_combination huv⟩
  have hZ := congrArg (Int.cast : ℤ → ZMod N) huv
  push_cast at hZ
  rw [ZMod.natCast_self, mul_zero, add_zero] at hZ
  have hA : A ∈ Gamma0 N := by rw [Gamma0_mem]; simp [A]
  refine ⟨A, hA, ?_, B, ?_, ?_⟩
  · rw [eq_inv_iff_mul_eq_one]
    refine Units.ext ?_
    simpa [A, Gamma0Map] using hZ
  · rw [Gamma1_mem]
    simpa [B] using hZ
  · have hR := congrArg (Int.cast : ℤ → ℝ) huv
    push_cast at hR
    have hA : ((mapGL ℝ A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![(n : ℝ), -v; (N : ℝ), u] := by
      rw [mapGL_coe_matrix, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      ext i j; fin_cases i <;> fin_cases j <;> simp [A]
    have hB : ((mapGL ℝ B : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![(u : ℝ) * n, v; -(N : ℝ), 1] := by
      rw [mapGL_coe_matrix, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      ext i j; fin_cases i <;> fin_cases j <;> simp [B]
    refine Units.ext ?_
    rw [map_mul, map_mapGL, ← mul_assoc, adjugateGL_val, Units.val_mul, Units.val_mul,
      coe_map_natDiagGL_one, hA, hB, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (-(n : ℝ)) * hR
    · ring
    · ring
    · linear_combination -hR

omit [NeZero N] [NeZero n] in
/-- Translating by `A x` with `A ∈ Γ₀(N)` gives the same level as translating by `x`, because
`A` normalizes `Γ₁(N)`. -/
private lemma conjAct_mapGL_mul_smul_Gamma1 {A : SL(2, ℤ)} (hA : A ∈ Gamma0 N)
    (x : GL (Fin 2) ℝ) :
    ConjAct.toConjAct (mapGL ℝ A * x)⁻¹ • (Gamma1 N).map (mapGL ℝ) =
      ConjAct.toConjAct x⁻¹ • (Gamma1 N).map (mapGL ℝ) := by
  rw [_root_.mul_inv_rev, map_mul, mul_smul, Gamma1_map_inv_conjAct_eq ⟨A, hA⟩]

/-- The finite relative index that Mathlib's trace needs for the translate of a level-`Γ₁(N)`
form by the main involution of `diag(1, n)`, when `n` is coprime to `N`. -/
private lemma isFiniteRelIndex_adjugateGL_natDiagGL (hn : n.Coprime N) :
    (ConjAct.toConjAct (adjugateGL (φ (natDiagGL 2 ![1, n])))⁻¹ •
      (Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma1 N).map (mapGL ℝ)) := by
  obtain ⟨A, hA, -, B, hB, hadj⟩ := exists_adjugateGL_natDiagGL_eq hn
  have := finite_decompQuotient_inv_of_mem_doubleCoset
    (g := natDiagGL 2 ![1, n]) (H := (Gamma1 N).map (mapGL ℚ)) (K := (Gamma1 N).map (mapGL ℚ))
    (mem_doubleCoset.mpr ⟨1, one_mem _, mapGL ℚ B, Subgroup.mem_map_of_mem _ hB, by rw [one_mul]⟩)
  rw [hadj, conjAct_mapGL_mul_smul_Gamma1 hA]
  infer_instance

/-- **The double coset operator of `diag(n, 1)` is `Tₙ ⟨n⟩⁻¹`.** For `n` coprime to `N`, the
trace of the translate of `g` by the main involution `diag(n, 1)` of `diag(1, n)` is
`Tₙ (⟨n⁻¹⟩ g)`. -/
private theorem trace_translate_adjugateGL_natDiagGL (hn : n.Coprime N)
    [(ConjAct.toConjAct (adjugateGL (φ (natDiagGL 2 ![1, n])))⁻¹ •
      (Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma1 N).map (mapGL ℝ))]
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm.trace ((Gamma1 N).map (mapGL ℝ))
        (CuspForm.translate g (adjugateGL (φ (natDiagGL 2 ![1, n])))) =
      heckeTCuspNat k n (diamondOpCusp k (ZMod.unitOfCoprime n hn)⁻¹ g) := by
  obtain ⟨A, hA, hAd, B, hB, hadj⟩ := exists_adjugateGL_natDiagGL_eq hn
  have hδ : natDiagGL 2 ![1, n] * mapGL ℚ B ∈
      doubleCoset ((diagCosetGamma1 N n).out : GL (Fin 2) ℚ)
        ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) := by
    rw [doubleCoset_out_diagCosetGamma1_eq_doubleCoset_natDiagGL]
    exact mem_doubleCoset.mpr ⟨1, one_mem _, mapGL ℚ B, Subgroup.mem_map_of_mem _ hB,
      by rw [one_mul]⟩
  have := finite_decompQuotient_inv_of_mem_doubleCoset hδ
  have hG : ((Gamma1 N).map (mapGL ℚ)).map φ = (Gamma1 N).map (mapGL ℝ) := by
    rw [Subgroup.map_map]
    exact congrArg (Subgroup.map · (Gamma1 N)) (MonoidHom.ext fun g ↦ map_mapGL g)
  apply DFunLike.coe_injective
  rw [coe_heckeTCuspNat,
    TauCeti.heckeSlashSum_eq_coe_trace_translate k (diagCosetGamma1 N n) hδ hG hG]
  refine congrArg DFunLike.coe (TauCeti.SlashInvariantForm.trace_eq_of_coe_eq
    (by rw [hadj, conjAct_mapGL_mul_smul_Gamma1 hA]) ?_)
  rw [CuspForm.coe_translate_gl, SlashInvariantForm.coe_translate,
    coe_diamondOpCusp k _ ⟨A, hA⟩ hAd, ← SlashAction.slash_mul, hadj]

/-- **The Petersson adjoint of `Tₙ`** (Diamond–Shurman, Theorem 5.5.3). For `n` coprime to the
level `N` and cusp forms `f`, `g` on `Γ₁(N)`,

`⟪Tₙ f, g⟫ = ⟪f, Tₙ (⟨n⟩⁻¹ g)⟫`,

so the adjoint of `Tₙ` is `Tₙ ⟨n⟩⁻¹`. -/
theorem peterssonInnerCosets_heckeTCuspNat (hn : n.Coprime N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm.peterssonInnerCosets (heckeTCuspNat k n f) g =
      CuspForm.peterssonInnerCosets f
        (heckeTCuspNat k n (diamondOpCusp k (ZMod.unitOfCoprime n hn)⁻¹ g)) := by
  have := isFiniteRelIndex_adjugateGL_natDiagGL hn
  have hdet : 0 < ((φ (natDiagGL 2 ![1, n]) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [coe_map_natDiagGL_one, Matrix.det_fin_two_of]
    simpa using Nat.pos_of_neZero n
  rw [TauCeti.heckeTCuspNat_eq_trace_translate,
    CuspForm.peterssonInnerCosets_trace_translate hdet Iff.rfl,
    trace_translate_adjugateGL_natDiagGL k hn]

/-- **`Tₙ* = χ(n)⁻¹ Tₙ` on `S_k(N, χ)`.** For `n` coprime to `N`, a cusp form `f` on `Γ₁(N)`
and `g` with nebentypus `χ`, `⟪Tₙ f, g⟫ = ⟪f, χ(n)⁻¹ Tₙ g⟫`. -/
theorem peterssonInnerCosets_heckeTCuspNat_of_mem_cuspFormCharSpace
    {χ : (ZMod N)ˣ →* ℂˣ} (hn : n.Coprime N) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hg : g ∈ cuspFormCharSpace k χ) :
    CuspForm.peterssonInnerCosets (heckeTCuspNat k n f) g =
      CuspForm.peterssonInnerCosets f
        ((χ (ZMod.unitOfCoprime n hn) : ℂ)⁻¹ • heckeTCuspNat k n g) := by
  rw [peterssonInnerCosets_heckeTCuspNat k hn,
    diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ _ hg, map_smul, map_inv,
    Units.val_inv_eq_inv_val]

end HeckeRing.GL2
