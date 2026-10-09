/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Hecke
public import TauCeti.NumberTheory.ModularForms.Fricke.Normalized

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
open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N n : ℕ} [NeZero N] [NeZero n] {k : ℤ}

/-- At a good index, Fricke carries `Tₙ` to its inverse-diamond multiple on modular forms. This
is the `Q = N` case of `atkinLehnerOperatorGamma1_heckeTNat`, where the twisting unit is `n⁻¹`. -/
theorem frickeOperator_heckeTNat (hn : n.Coprime N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    frickeOperator k (heckeTNat k n f) =
      diamondOp k (ZMod.unitOfCoprime n hn)⁻¹ (heckeTNat k n (frickeOperator k f)) := by
  have : Subsingleton (ZMod (N / N))ˣ := by
    rw [Nat.div_self (NeZero.pos N)]
    infer_instance
  rw [← atkinLehnerOperatorGamma1_fricke]
  exact atkinLehnerOperatorGamma1_heckeTNat (NeZero.pos N) dvd_rfl isAtkinLehnerMatrix_fricke hn
    (by rw [ZMod.unitsMap_self, MonoidHom.id_apply]) (Subsingleton.elim _ _) f

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
  have hcomm := DFunLike.congr_fun (commute_heckeTNat_diamondOp k hn (ZMod.unitOfCoprime n hn)⁻¹).eq
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
