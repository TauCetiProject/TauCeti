/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Finrank
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
    : (U →ₗ[ℝ] ℝ) →ₗ[ℝ] V →ₗ[ℝ] (U →ₗ[ℝ] V) where
  toFun ℓ :=
    { toFun q := (ℓ.comp j.toLinearMap).smulRight q - ℓ.smulRight (J q)
      map_add' q r := by ext v; simp [smul_add, sub_add_sub_comm]
      map_smul' c q := by ext v; simp [J.apply_smul, smul_sub, smul_smul, mul_comm] }
  map_add' ℓ m := by ext q v; simp [add_smul]; abel
  map_smul' c ℓ := by ext q v; simp [smul_sub, smul_smul]

/-- Evaluation of the real Cauchy–Riemann symbol. -/
@[simp]
theorem cauchyRiemannSymbol_apply (j : AlmostComplexStructure U) (J : AlmostComplexStructure V)
    (ℓ : U →ₗ[ℝ] ℝ) (q : V) (v : U) :
    cauchyRiemannSymbol j J ℓ q v = ℓ (j v) • q - ℓ v • J q := (rfl)

/-- The symbol as a difference of two rank-one linear maps. -/
theorem cauchyRiemannSymbol_def (j : AlmostComplexStructure U) (J : AlmostComplexStructure V)
    (ℓ : U →ₗ[ℝ] ℝ) (q : V) :
    cauchyRiemannSymbol j J ℓ q =
      (ℓ.comp j.toLinearMap).smulRight q - ℓ.smulRight (J q) := (rfl)

/-- The symbol takes values in the complex-antilinear maps. -/
theorem isComplexAntilinear_cauchyRiemannSymbol (j : AlmostComplexStructure U)
    (J : AlmostComplexStructure V) (ℓ : U →ₗ[ℝ] ℝ) (q : V) :
    IsComplexAntilinear j.toLinearMap J.toLinearMap (cauchyRiemannSymbol j J ℓ q) := by
  apply isComplexAntilinear_of_apply
  intro v
  simp [J.apply_smul, neg_smul, smul_neg, sub_eq_add_neg]

/-- Complex-linear target maps intertwine the Cauchy–Riemann symbols. -/
theorem IsComplexLinearMap.comp_cauchyRiemannSymbol
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {J : AlmostComplexStructure V} {K : AlmostComplexStructure W} {F : V →ₗ[ℝ] W}
    (hF : IsComplexLinearMap J K F) (j : AlmostComplexStructure U)
    (ℓ : U →ₗ[ℝ] ℝ) (q : V) :
    F.comp (cauchyRiemannSymbol j J ℓ q) = cauchyRiemannSymbol j K ℓ (F q) := by
  ext v
  simp [(isComplexLinearMap_iff_apply _ _ _).mp hF]

/-- The symbol is complex-linear in its vector argument. -/
theorem cauchyRiemannSymbol_apply_almostComplexStructure (j : AlmostComplexStructure U)
    (J : AlmostComplexStructure V) (ℓ : U →ₗ[ℝ] ℝ) (q : V) :
    cauchyRiemannSymbol j J ℓ (J q) = J.toLinearMap.comp (cauchyRiemannSymbol j J ℓ q) :=
  (J.isComplexLinearMap_toLinearMap.comp_cauchyRiemannSymbol j ℓ q).symm

/-- Complex-linear source maps pull back Cauchy–Riemann symbols. -/
theorem IsComplexLinearMap.cauchyRiemannSymbol_comp
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {j₁ : AlmostComplexStructure U} {j₂ : AlmostComplexStructure W} {G : U →ₗ[ℝ] W}
    (hG : IsComplexLinearMap j₁ j₂ G) (J : AlmostComplexStructure V)
    (ℓ : W →ₗ[ℝ] ℝ) (q : V) :
    (cauchyRiemannSymbol j₂ J ℓ q).comp G = cauchyRiemannSymbol j₁ J (ℓ.comp G) q := by
  ext v
  simp [(isComplexLinearMap_iff_apply _ _ _).mp hG]

/-- The real Cauchy–Riemann symbol corestricted to complex-antilinear maps. -/
def cauchyRiemannSymbolAntilinear (j : AlmostComplexStructure U)
    (J : AlmostComplexStructure V) :
    (U →ₗ[ℝ] ℝ) →ₗ[ℝ] V →ₗ[ℝ] complexAntilinearMaps j.toLinearMap J.toLinearMap where
  toFun ℓ := (cauchyRiemannSymbol j J ℓ).codRestrict _ fun q ↦
    mem_complexAntilinearMaps.2 (isComplexAntilinear_cauchyRiemannSymbol j J ℓ q)
  map_add' ℓ m := by ext q v; simp [cauchyRiemannSymbol, add_smul]; abel
  map_smul' c ℓ := by ext q v; simp [cauchyRiemannSymbol, smul_sub, smul_smul]

/-- Forgetting the corestriction recovers the real Cauchy–Riemann symbol. -/
@[simp]
theorem cauchyRiemannSymbolAntilinear_apply (j : AlmostComplexStructure U)
    (J : AlmostComplexStructure V) (ℓ : U →ₗ[ℝ] ℝ) (q : V) :
    (cauchyRiemannSymbolAntilinear j J ℓ q : U →ₗ[ℝ] V) =
      cauchyRiemannSymbol j J ℓ q := (rfl)

/-- The inverse of symbol evaluation is a left inverse whenever the covector is nonzero
on the complex span of the evaluation vector. -/
theorem leftInverse_cauchyRiemannSymbol_apply (j : AlmostComplexStructure U)
    (J : AlmostComplexStructure V) (ℓ : U →ₗ[ℝ] ℝ) (v : U)
    (h : ℓ (j v) ^ 2 + ℓ v ^ 2 ≠ 0) :
    Function.LeftInverse
      (fun q ↦ (ℓ (j v) ^ 2 + ℓ v ^ 2)⁻¹ • (ℓ (j v) • q + ℓ v • J q))
      (fun q ↦ cauchyRiemannSymbol j J ℓ q v) := by
  intro q
  simp only [cauchyRiemannSymbol_apply, J.apply_sub, J.apply_smul, J.apply_apply]
  have heq : ℓ (j v) • (ℓ (j v) • q - ℓ v • J q) +
      ℓ v • (ℓ (j v) • J q - ℓ v • -q) = (ℓ (j v) ^ 2 + ℓ v ^ 2) • q := by module
  rw [heq, smul_smul, inv_mul_cancel₀ h, one_smul]

/-- Evaluating the symbol at `v` is invertible whenever the covector is nonzero on the
complex span of `v`. -/
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
  · exact leftInverse_cauchyRiemannSymbol_apply j J ℓ v h
  · intro q
    simp only [cauchyRiemannSymbol_apply, J.apply_smul, J.apply_add, J.apply_apply]
    calc a • (d⁻¹ • (a • q + b • J q)) - b • (d⁻¹ • (a • J q + b • -q))
        = (d⁻¹ * d) • q := by dsimp [d]; module
      _ = q := by rw [inv_mul_cancel₀ hd, one_smul]

/-- A nonzero real covector on a complex line is nonzero on the complex span of every
nonzero vector. -/
theorem cauchyRiemannSymbol_denominator_ne_zero (j : AlmostComplexStructure U)
    (hU : Module.finrank ℝ U = 2) (ℓ : U →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {v : U} (hv : v ≠ 0) : ℓ (j v) ^ 2 + ℓ v ^ 2 ≠ 0 := by
  intro h
  obtain ⟨hjv, hv'⟩ := sq_add_sq_eq_zero.1 h
  apply hℓ
  apply LinearMap.ext_on (j.span_pair_eq_top_of_finrank_eq_two hU hv)
  rintro w (rfl | rfl) <;> simp [hv', hjv]

/-- On a complex line the symbol at every nonzero real covector maps `V` bijectively onto
complex-antilinear maps. This is ellipticity, without a choice of normal frame. -/
theorem bijective_cauchyRiemannSymbolAntilinear (j : AlmostComplexStructure U)
    (hU : Module.finrank ℝ U = 2) (J : AlmostComplexStructure V)
    (ℓ : U →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    Function.Bijective (cauchyRiemannSymbolAntilinear j J ℓ) := by
  have hex : ∃ v, ℓ v ≠ 0 := by
    by_contra! h
    exact hℓ (LinearMap.ext fun v ↦ h v)
  obtain ⟨v, hv⟩ := hex
  have hv₀ : v ≠ 0 := by rintro rfl; simp at hv
  have hb := bijective_cauchyRiemannSymbol_apply j J ℓ v
    (cauchyRiemannSymbol_denominator_ne_zero j hU ℓ hℓ hv₀)
  constructor
  · intro q r h
    apply hb.1
    simpa only [cauchyRiemannSymbolAntilinear_apply] using
      congrArg (fun f : U →ₗ[ℝ] V ↦ f v) (congrArg Subtype.val h)
  · intro f
    obtain ⟨q, hq⟩ := hb.2 (f.val v)
    refine ⟨q, Subtype.ext ?_⟩
    -- Antilinear maps on a complex line are determined at any nonzero vector.
    apply LinearMap.ext_on (j.span_pair_eq_top_of_finrank_eq_two hU hv₀)
    rintro w (rfl | rfl)
    · simpa only [cauchyRiemannSymbolAntilinear_apply] using hq
    · have hs := (isComplexAntilinear_cauchyRiemannSymbol j J ℓ q).apply v
      have hf := (mem_complexAntilinearMaps.1 f.property).apply v
      simpa only [cauchyRiemannSymbolAntilinear_apply] using
        hs.trans ((congrArg (fun q ↦ -J q) hq).trans hf.symm)

/-- The elliptic real Cauchy–Riemann symbol on a complex line as a linear equivalence.
Its inverse recovers the vector in `V` from a complex-antilinear map. -/
noncomputable def cauchyRiemannSymbolEquiv (j : AlmostComplexStructure U)
    (hU : Module.finrank ℝ U = 2) (J : AlmostComplexStructure V)
    (ℓ : U →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    V ≃ₗ[ℝ] complexAntilinearMaps j.toLinearMap J.toLinearMap :=
  LinearEquiv.ofBijective (cauchyRiemannSymbolAntilinear j J ℓ)
    (bijective_cauchyRiemannSymbolAntilinear j hU J ℓ hℓ)

/-- The symbol equivalence has the corestricted symbol as its forward map. -/
@[simp]
theorem cauchyRiemannSymbolEquiv_apply (j : AlmostComplexStructure U)
    (hU : Module.finrank ℝ U = 2) (J : AlmostComplexStructure V)
    (ℓ : U →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (q : V) :
    cauchyRiemannSymbolEquiv j hU J ℓ hℓ q =
      cauchyRiemannSymbolAntilinear j J ℓ q := (rfl)

/-- The inverse symbol recovers the vector in `V` from evaluation at any nonzero vector. -/
theorem cauchyRiemannSymbolEquiv_symm_apply (j : AlmostComplexStructure U)
    (hU : Module.finrank ℝ U = 2) (J : AlmostComplexStructure V)
    (ℓ : U →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (f : complexAntilinearMaps j.toLinearMap J.toLinearMap) {v : U} (hv : v ≠ 0) :
    (cauchyRiemannSymbolEquiv j hU J ℓ hℓ).symm f =
      (ℓ (j v) ^ 2 + ℓ v ^ 2)⁻¹ • (ℓ (j v) • f.val v + ℓ v • J (f.val v)) := by
  have heval := congrArg (fun g : complexAntilinearMaps j.toLinearMap J.toLinearMap ↦ g.val v)
    ((cauchyRiemannSymbolEquiv j hU J ℓ hℓ).apply_symm_apply f)
  simp only [cauchyRiemannSymbolEquiv_apply, cauchyRiemannSymbolAntilinear_apply] at heval
  rw [← heval]
  exact (leftInverse_cauchyRiemannSymbol_apply j J ℓ v
    (cauchyRiemannSymbol_denominator_ne_zero j hU ℓ hℓ hv) _).symm

end TauCeti
