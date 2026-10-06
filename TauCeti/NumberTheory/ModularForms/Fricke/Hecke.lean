/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Fricke.Normalized
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Diamond
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Fricke transport of the good Hecke operators

At an index `n` coprime to `N`, the Fricke operator intertwines `Tₙ` with
`⟨n⟩⁻¹ Tₙ` on forms for `Γ₁(N)`. On a nebentypus space this gives the scalar
`χ(n)` when `Tₙ` is moved past Fricke from the source to the target character space.
The same identities hold for the Petersson-normalized Fricke operator and for cusp forms.

This relation transports good Hecke eigensystems to the inverse-nebentypus space; it is
the Hecke-theoretic input to the Fricke pseudo-eigenvalue theorem for primitive forms.

## References

* [T. Miyake, *Modular forms*][miyake1989], §4.6, Theorem 4.6.15.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane HeckeRing.GL2
open HeckeRing.GLn
open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

variable {N n : ℕ} [NeZero N] [NeZero n] {k : ℤ}

local notation "φ" => Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ ℝ)

/-- At a good index, Fricke carries `Tₙ` to its inverse-diamond multiple on modular forms. -/
theorem frickeOperator_heckeTNat (hn : n.Coprime N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    frickeOperator k (heckeTNat k n f) =
      diamondOp k (ZMod.unitOfCoprime n hn)⁻¹ (heckeTNat k n (frickeOperator k f)) := by
  -- The proof uses Mathlib's trace construction: `diag(1,n) W = W diag(n,1)` moves Fricke
  -- through the trace, and the existing adjugate-coset identity identifies `diag(n,1)` with
  -- `⟨n⟩⁻¹ Tₙ`. No additional determinant factor is introduced.
  let x := φ (natDiagGL 2 ![1, n])
  let W := frickeGL ℝ N
  -- Fricke exchanges the two diagonal entries, giving the main involution of `x`.
  have hx : (x : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, (n : ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [x, GeneralLinearGroup.map_apply, coe_natDiagGL_one (NeZero.pos n)]
  have hmat : x * W = W * adjugateGL x := by
    apply Units.ext
    simp only [GeneralLinearGroup.coe_mul, adjugateGL_val, hx, W, coe_frickeGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.adjugate_fin_two, mul_comm]
  -- The source levels agree because Fricke normalizes `Γ₁(N)`.
  have hlevel : ConjAct.toConjAct (x * W)⁻¹ • (Gamma1 N).map (mapGL ℝ) =
      ConjAct.toConjAct (adjugateGL x)⁻¹ • (Gamma1 N).map (mapGL ℝ) := by
    rw [hmat, _root_.mul_inv_rev, map_mul, mul_smul]
    rw [Gamma1_map_inv_conjAct_frickeGL_eq]
  have := isFiniteRelIndex_adjugateGL_natDiagGL (N := N) hn
  have : (ConjAct.toConjAct (x * W)⁻¹ • (Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex
      ((Gamma1 N).map (mapGL ℝ)) := hlevel ▸ ‹_›
  have hW : W ∈ Subgroup.normalizer ((Gamma1 N).map (mapGL ℝ) : Set (GL (Fin 2) ℝ)) :=
    (Subgroup.normalizer _).inv_mem_iff.mp
      (Subgroup.conjAct_pointwise_smul_iff.mp Gamma1_map_inv_conjAct_frickeGL_eq)
  -- Move `W` through the trace and compare the two translates at their common level.
  have htrace := SlashInvariantForm.coe_trace_translate_mul_of_mem_normalizer f x hW
  have heq := SlashInvariantForm.trace_eq_of_eq_of_coe_eq hlevel
    (ℋ := (Gamma1 N).map (mapGL ℝ))
    (f₁ := _root_.SlashInvariantForm.translate f (x * W))
    (f₂ := ModularForm.translate (frickeOperator k f) (adjugateGL x)) (by
      rw [_root_.SlashInvariantForm.coe_translate, ModularForm.coe_translate,
        coe_frickeOperator, ← SlashAction.slash_mul, hmat])
  apply DFunLike.coe_injective
  rw [coe_frickeOperator, coe_heckeTNat,
    heckeSlashSum_eq_coe_trace_translate k (diagCosetGamma1 N n)
      (by rw [doubleCoset_out_diagCosetGamma1_eq_doubleCoset_natDiagGL]
          exact DoubleCoset.mem_doubleCoset_self _ _ _)
      (Subgroup.map_mapGL (Gamma1 N)) (Subgroup.map_mapGL (Gamma1 N)), ← htrace, heq]
  have h := congrArg DFunLike.coe
    (trace_translate_adjugateGL_natDiagGL_eq_diamondOp_heckeTNat k hn (frickeOperator k f))
  -- The trace coercion lemmas give the same sum for modular and slash-invariant forms.
  simpa only [ModularForm.coe_trace, _root_.SlashInvariantForm.coe_trace] using h

/-- At a good index, Fricke carries `Tₙ` to its inverse-diamond multiple on cusp forms. -/
theorem frickeOperatorCusp_heckeTCuspNat (hn : n.Coprime N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    frickeOperatorCusp k (heckeTCuspNat k n f) =
      diamondOpCusp k (ZMod.unitOfCoprime n hn)⁻¹
        (heckeTCuspNat k n (frickeOperatorCusp k f)) := by
  apply CuspForm.toModularFormₗ_injective
  simpa only [CuspForm.toModularFormₗ_eq_coe, frickeOperator_coe_cuspForm,
    heckeTNat_coe_cuspForm, diamondOp_coe_cuspForm] using
    frickeOperator_heckeTNat hn (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)

/-- The Petersson normalization leaves the Fricke–Hecke intertwining relation unchanged. -/
theorem normalizedFrickeOperator_heckeTNat (hn : n.Coprime N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    normalizedFrickeOperator k (heckeTNat k n f) =
      diamondOp k (ZMod.unitOfCoprime n hn)⁻¹
        (heckeTNat k n (normalizedFrickeOperator k f)) := by
  simp only [normalizedFrickeOperator_def, LinearMap.smul_apply, map_smul,
    frickeOperator_heckeTNat hn]

/-- The normalized Fricke–Hecke intertwining relation on cusp forms. -/
theorem normalizedFrickeOperatorCusp_heckeTCuspNat (hn : n.Coprime N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    normalizedFrickeOperatorCusp k (heckeTCuspNat k n f) =
      diamondOpCusp k (ZMod.unitOfCoprime n hn)⁻¹
        (heckeTCuspNat k n (normalizedFrickeOperatorCusp k f)) := by
  simp only [normalizedFrickeOperatorCusp_def, LinearMap.smul_apply, map_smul,
    frickeOperatorCusp_heckeTCuspNat hn]

/-- On `M_k(N, χ)`, moving a good `Tₙ` past Fricke introduces `χ(n)`.
The output of Fricke has nebentypus `χ⁻¹`. -/
theorem frickeOperator_heckeTNat_of_mem_modFormCharSpace (hn : n.Coprime N)
    {χ : (ZMod N)ˣ →* ℂˣ} {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    frickeOperator k (heckeTNat k n f) =
      (χ (ZMod.unitOfCoprime n hn) : ℂ) • heckeTNat k n (frickeOperator k f) := by
  have hcomm := DFunLike.congr_fun (commute_heckeTNat_diamondOp_inv k hn).eq
    (frickeOperator k f)
  simp only [Module.End.mul_apply] at hcomm
  rw [frickeOperator_heckeTNat hn, ← hcomm,
    diamondOp_apply_of_mem_modFormCharSpace k χ⁻¹ _
      (frickeOperator_mem_modFormCharSpace k χ hf), map_smul]
  simp

/-- On `S_k(N, χ)`, moving a good `Tₙ` past Fricke introduces `χ(n)`. -/
theorem frickeOperatorCusp_heckeTCuspNat_of_mem_cuspFormCharSpace (hn : n.Coprime N)
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) :
    frickeOperatorCusp k (heckeTCuspNat k n f) =
      (χ (ZMod.unitOfCoprime n hn) : ℂ) • heckeTCuspNat k n (frickeOperatorCusp k f) := by
  apply CuspForm.toModularFormₗ_injective
  rw [map_smul, CuspForm.toModularFormₗ_eq_coe, CuspForm.toModularFormₗ_eq_coe]
  simpa only [frickeOperator_coe_cuspForm, heckeTNat_coe_cuspForm] using
    frickeOperator_heckeTNat_of_mem_modFormCharSpace hn
      ((coe_mem_modFormCharSpace_iff k χ f).mpr hf)

/-- On a nebentypus space, the normalized Fricke operator intertwines `Tₙ` with `χ(n)Tₙ`.
No parity or reality hypothesis on `χ` is needed. -/
theorem normalizedFrickeOperator_heckeTNat_of_mem_modFormCharSpace (hn : n.Coprime N)
    {χ : (ZMod N)ˣ →* ℂˣ} {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    normalizedFrickeOperator k (heckeTNat k n f) =
      (χ (ZMod.unitOfCoprime n hn) : ℂ) • heckeTNat k n (normalizedFrickeOperator k f) := by
  rw [normalizedFrickeOperator_def, LinearMap.smul_apply, LinearMap.smul_apply,
    map_smul, frickeOperator_heckeTNat_of_mem_modFormCharSpace hn hf, smul_comm]

/-- The normalized Fricke–Hecke relation on cusp forms with general nebentypus. -/
theorem normalizedFrickeOperatorCusp_heckeTCuspNat_of_mem_cuspFormCharSpace (hn : n.Coprime N)
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) :
    normalizedFrickeOperatorCusp k (heckeTCuspNat k n f) =
      (χ (ZMod.unitOfCoprime n hn) : ℂ) •
        heckeTCuspNat k n (normalizedFrickeOperatorCusp k f) := by
  rw [normalizedFrickeOperatorCusp_def, LinearMap.smul_apply, LinearMap.smul_apply,
    map_smul, frickeOperatorCusp_heckeTCuspNat_of_mem_cuspFormCharSpace hn hf, smul_comm]

/-- Fricke transports a good Hecke eigenrelation by multiplying its eigenvalue by `χ(n)⁻¹`.
The equivalence includes the zero form and does not require normalization of its coefficients. -/
theorem heckeTCuspNat_normalizedFrickeOperatorCusp_eq_smul_iff_heckeTCuspNat_eq_smul
    (hn : n.Coprime N)
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) (c : ℂ) :
    heckeTCuspNat k n (normalizedFrickeOperatorCusp k f) =
        ((χ (ZMod.unitOfCoprime n hn) : ℂ)⁻¹ * c) • normalizedFrickeOperatorCusp k f ↔
      heckeTCuspNat k n f = c • f := by
  have ha : (χ (ZMod.unitOfCoprime n hn) : ℂ) ≠ 0 := Units.ne_zero _
  constructor
  · intro h
    apply (normalizedFrickeOperatorCuspEquiv (N := N) k).injective
    simp only [normalizedFrickeOperatorCuspEquiv_apply, map_smul]
    rw [normalizedFrickeOperatorCusp_heckeTCuspNat_of_mem_cuspFormCharSpace hn hf, h]
    simp [smul_smul, ha]
  · intro h
    have hW := normalizedFrickeOperatorCusp_heckeTCuspNat_of_mem_cuspFormCharSpace hn hf
    rw [h, map_smul] at hW
    have := congrArg (fun g ↦ (χ (ZMod.unitOfCoprime n hn) : ℂ)⁻¹ • g) hW.symm
    simpa [smul_smul, ha] using this

end TauCeti
