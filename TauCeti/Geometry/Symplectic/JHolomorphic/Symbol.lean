/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import Mathlib.Tactic.Module

/-!
# The real Cauchy–Riemann symbol

For almost complex structures `j`, `J` and a real covector `λ`, the unnormalized real
Cauchy–Riemann symbol sends `q` to `v ↦ λ(j v) q - λ(v) J q`. Its values are complex
antilinear maps. Over a complex line it is bijective onto those maps whenever `λ ≠ 0`.
This is the fiberwise ellipticity statement used for normal operators of pseudoholomorphic
curves, and does not require the operator to be complex linear in its section argument.

The normalization agrees with the defect `du ∘ j - J ∘ du`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1.
-/

public section

namespace TauCeti

variable {U V : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]

/-- The symbol of the unnormalized real Cauchy–Riemann operator at a real covector. -/
def cauchyRiemannSymbol (j : AlmostComplexStructure U) (J : AlmostComplexStructure V)
    (ℓ : U →ₗ[ℝ] ℝ) : V →ₗ[ℝ] (U →ₗ[ℝ] V) where
  toFun q := (ℓ.comp j.toLinearMap).smulRight q - ℓ.smulRight (J q)
  map_add' q r := by ext v; simp [smul_add, sub_add_sub_comm]
  map_smul' c q := by ext v; simp [J.apply_smul, smul_sub, smul_smul, mul_comm]

/-- Evaluation of the real Cauchy–Riemann symbol. -/
@[simp]
theorem cauchyRiemannSymbol_apply (j : AlmostComplexStructure U) (J : AlmostComplexStructure V)
    (ℓ : U →ₗ[ℝ] ℝ) (q : V) (v : U) :
    cauchyRiemannSymbol j J ℓ q v = ℓ (j v) • q - ℓ v • J q := (rfl)

/-- The symbol takes values in the complex-antilinear covectors. -/
theorem isComplexAntilinear_cauchyRiemannSymbol (j : AlmostComplexStructure U)
    (J : AlmostComplexStructure V) (ℓ : U →ₗ[ℝ] ℝ) (q : V) :
    IsComplexAntilinear j.toLinearMap J.toLinearMap (cauchyRiemannSymbol j J ℓ q) := by
  apply isComplexAntilinear_of_apply
  intro v
  simp [J.apply_smul, neg_smul, smul_neg, sub_eq_add_neg]

/-- The real Cauchy–Riemann symbol corestricted to complex-antilinear covectors. -/
def cauchyRiemannSymbolAntilinear (j : AlmostComplexStructure U)
    (J : AlmostComplexStructure V) (ℓ : U →ₗ[ℝ] ℝ) :
    V →ₗ[ℝ] complexAntilinearMaps j.toLinearMap J.toLinearMap :=
  (cauchyRiemannSymbol j J ℓ).codRestrict _ fun q ↦
    mem_complexAntilinearMaps.2 (isComplexAntilinear_cauchyRiemannSymbol j J ℓ q)

/-- Forgetting the corestriction recovers the real Cauchy–Riemann symbol. -/
@[simp]
theorem cauchyRiemannSymbolAntilinear_apply (j : AlmostComplexStructure U)
    (J : AlmostComplexStructure V) (ℓ : U →ₗ[ℝ] ℝ) (q : V) :
    (cauchyRiemannSymbolAntilinear j J ℓ q : U →ₗ[ℝ] V) =
      cauchyRiemannSymbol j J ℓ q := (rfl)

/-- Evaluating the symbol at `v` is invertible whenever the covector is nonzero on the
complex span of `v`. The inverse is `(λ(j v) Id + λ(v) J) / (λ(j v)² + λ(v)²)`. -/
theorem bijective_cauchyRiemannSymbol_apply (j : AlmostComplexStructure U)
    (J : AlmostComplexStructure V) (ℓ : U →ₗ[ℝ] ℝ) (v : U)
    (h : ℓ (j v) ^ 2 + ℓ v ^ 2 ≠ 0) :
    Function.Bijective (fun q ↦ cauchyRiemannSymbol j J ℓ q v) := by
  let a := ℓ (j v)
  let b := ℓ v
  let d := a ^ 2 + b ^ 2
  have hd : d ≠ 0 := h
  refine Function.bijective_iff_has_inverse.2
    ⟨fun q ↦ d⁻¹ • (a • q + b • J q), ?_, ?_⟩
  · intro q
    simp only [cauchyRiemannSymbol_apply, J.apply_sub, J.apply_smul, J.apply_apply]
    have heq : a • (a • q - b • J q) + b • (a • J q - b • -q) = d • q := by
      dsimp [d]
      module
    rw [heq, smul_smul, inv_mul_cancel₀ hd, one_smul]
  · intro q
    simp only [cauchyRiemannSymbol_apply, J.apply_smul, J.apply_add, J.apply_apply]
    calc a • (d⁻¹ • (a • q + b • J q)) - b • (d⁻¹ • (a • J q + b • -q))
        = (d⁻¹ * d) • q := by dsimp [d]; module
      _ = q := by rw [inv_mul_cancel₀ hd, one_smul]

/-- On a complex line the symbol at every nonzero real covector is an isomorphism onto
complex-antilinear covectors. This is ellipticity, stated without a choice of normal frame. -/
theorem bijective_cauchyRiemannSymbolAntilinear (J : AlmostComplexStructure V)
    (ℓ : ℂ →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    Function.Bijective
      (cauchyRiemannSymbolAntilinear (AlmostComplexStructure.ofComplexModule ℂ) J ℓ) := by
  have hpair : ℓ Complex.I ^ 2 + ℓ 1 ^ 2 ≠ 0 := by
    intro h
    have h₁ : ℓ 1 = 0 := by nlinarith [sq_nonneg (ℓ Complex.I)]
    have hI : ℓ Complex.I = 0 := by nlinarith [sq_nonneg (ℓ 1)]
    apply hℓ
    apply Complex.basisOneI.ext
    intro i
    fin_cases i <;> simp [Complex.coe_basisOneI, h₁, hI]
  have hb := bijective_cauchyRiemannSymbol_apply (AlmostComplexStructure.ofComplexModule ℂ)
    J ℓ 1 (by simpa [AlmostComplexStructure.ofComplexModule_apply] using hpair)
  constructor
  · intro q r h
    exact hb.1 (congrArg (fun f : ℂ →ₗ[ℝ] V ↦ f 1) (congrArg Subtype.val h))
  · intro f
    obtain ⟨q, hq⟩ := hb.2 (f.val 1)
    refine ⟨q, Subtype.ext ?_⟩
    -- Antilinear covectors on a complex line are determined by their value at `1`.
    apply Complex.basisOneI.ext
    intro i
    fin_cases i
    · simpa [Complex.coe_basisOneI] using hq
    · have hs := (isComplexAntilinear_cauchyRiemannSymbol
          (AlmostComplexStructure.ofComplexModule ℂ) J ℓ q).apply 1
      have hf := (mem_complexAntilinearMaps.1 f.property).apply 1
      simpa [Complex.coe_basisOneI, AlmostComplexStructure.ofComplexModule_apply] using
        hs.trans ((congrArg (fun q ↦ -J q) hq).trans hf.symm)

/-- The elliptic real Cauchy–Riemann symbol on a complex line as a linear equivalence.
Its inverse recovers the section value from a complex-antilinear covector. -/
noncomputable def cauchyRiemannSymbolEquiv (J : AlmostComplexStructure V)
    (ℓ : ℂ →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    V ≃ₗ[ℝ] complexAntilinearMaps (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
      J.toLinearMap :=
  LinearEquiv.ofBijective
    (cauchyRiemannSymbolAntilinear (AlmostComplexStructure.ofComplexModule ℂ) J ℓ)
    (bijective_cauchyRiemannSymbolAntilinear J ℓ hℓ)

/-- The symbol equivalence has the corestricted symbol as its forward map. -/
@[simp]
theorem cauchyRiemannSymbolEquiv_apply (J : AlmostComplexStructure V)
    (ℓ : ℂ →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (q : V) :
    cauchyRiemannSymbolEquiv J ℓ hℓ q =
      cauchyRiemannSymbolAntilinear (AlmostComplexStructure.ofComplexModule ℂ) J ℓ q := (rfl)

end TauCeti
