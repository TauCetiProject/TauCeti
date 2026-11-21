/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Plane.Opens
import TauCeti.Analysis.Complex.Wirtinger.OpenSet
import TauCeti.Analysis.Normed.Module.Complexification
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

/-!
# Banach-valued two-form exactness on open subsets of `ℂ`

Combining the planar coordinate calculus on open subsets `U : TopologicalSpace.Opens ℂ`
(`TauCeti.Geometry.Manifold.DifferentialForm.Plane.Opens`) with global `\bar∂` solvability on
arbitrary open subsets of `ℂ` (`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq`)
yields:

* **Form-level closed completion**
  (`TauCeti.exists_contMDiff_mextDeriv_wedgeWith_complexDz_add_eq_zero`): for every `C^n` function
  `f` (`1 ≤ m`, `m + 1 ≤ n`) into a complex Banach space `W`, there is a `C^m` function `g` with
  `d(g dz + f dbar z) = 0`.
* **Explicit `(1, 0)`-primitive for complex Banach-valued two-forms**
  (`TauCeti.exists_contMDiff_mextDeriv_wedgeWith_complexDz_eq`): every `C^n` (`1 ≤ n`) two-form
  `η` on `U` with values in a complex Banach space `W` equals `d(g dz)` for a `C^n` function
  `g : U → W`.
* **Banach-valued two-form exactness**
  (`TauCeti.exists_isSmoothForm_mextDeriv_eq_of_opens_complex`,
  `TauCeti.exists_mextDerivₗ_eq_of_opens_complex`): by passing to the Banach complexification
  `TauCeti.Complexification F` and taking the real part via `TauCeti.RoughForm.mapCoeff`, every
  `C^n` (`1 ≤ n`) two-form on `U` with values in any real Banach space `F` (including `ℝ`, `ℂ`,
  and every complex Banach space) is exact.

No connectedness, simple connectivity, or nonemptiness hypothesis on `U` is assumed.

## References

* A. Rainer, *Advanced Complex Analysis*, §10 and Theorem 12.2.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Chapter I.
-/

public noncomputable section

open Complex Set TopologicalSpace
open scoped ContDiff Manifold ComplexConjugate Topology

namespace TauCeti

/-! ### Closed completion and two-form exactness on open subsets of `ℂ` -/

section Exactness

/-- **Form-level closed completion (Banach-valued).** For any `C^n` function `f : U → W` on an
open subset `U ⊆ ℂ` into a complex Banach space `W`, with `1 ≤ m` and `m + 1 ≤ n`, there exists
a `C^m` function `g : U → W` such that the `W`-valued one-form `g dz + f dbar z` is closed. -/
theorem exists_contMDiff_mextDeriv_wedgeWith_complexDz_add_eq_zero {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {m n : ℕ∞}
    (hm : 1 ≤ m) (hmn : m + 1 ≤ n) {f : U → W}
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) n f) :
    ∃ g : U → W, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) m g ∧
      mextDeriv
        (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
            (RoughForm.ofFunction 𝓘(ℝ, ℂ) g)
            (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
              SmoothForm.complexDz.val) +
          RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
            (RoughForm.ofFunction 𝓘(ℝ, ℂ) f)
            (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
              SmoothForm.complexDzBar.val)) = 0 := by
  let f' : ℂ → W := Subtype.val.extend f 0
  have hf'_eq (z : U) : f' z = f z := Subtype.val_injective.extend_apply f 0 z
  have hf' : ContDiffOn ℝ n f' (U : Set ℂ) :=
    contMDiffOn_iff_contDiffOn.1 (ContMDiffMap.contMDiffOn_extend U ⟨f, hf⟩ 0)
  obtain ⟨g', hg', hsol⟩ :=
    exists_contDiffOn_conjWirtingerDeriv_eq_wirtingerDeriv hm hmn U.isOpen hf'
  let g : U → W := g' ∘ Subtype.val
  have hg : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) m g := hg'.contMDiff_comp_subtypeVal
  refine ⟨g, hg, ?_⟩
  apply planarTwoFormCoeff_injective
  funext z
  have hg1 : IsSmoothForm 𝓘(ℝ, ℂ) 1
      (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
        (RoughForm.ofFunction 𝓘(ℝ, ℂ) g)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDz.val)) :=
    (isSmoothForm_ofFunction_iff.2 (hg.of_le (mod_cast hm))).wedgeWith _
      ((SmoothForm.complexDz.isSmoothForm.mpullback
        (contMDiff_subtypeVal (n := ∞))).of_le (by simp))
  have hf1 : IsSmoothForm 𝓘(ℝ, ℂ) 1
      (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
        (RoughForm.ofFunction 𝓘(ℝ, ℂ) f)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDzBar.val)) :=
    (isSmoothForm_ofFunction_iff.2
        (hf.of_le (mod_cast (hm.trans (le_self_add.trans hmn))))).wedgeWith _
      ((SmoothForm.complexDzBar.isSmoothForm.mpullback
        (contMDiff_subtypeVal (n := ∞))).of_le (by simp))
  have hgd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, W) g z :=
    (hg z).mdifferentiableAt (by exact_mod_cast (zero_lt_one.trans_le hm).ne')
  have hfd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, W) f z :=
    (hf z).mdifferentiableAt (by
      exact_mod_cast (zero_lt_one.trans_le (hm.trans (le_self_add.trans hmn))).ne')
  rw [hg1.mextDeriv_add hf1, planarTwoFormCoeff_add, planarTwoFormCoeff_zero,
    planarTwoFormCoeff_mextDeriv_wedgeWith_complexDz (g := g) (g' := g') (fun _ ↦ rfl) hgd,
    planarTwoFormCoeff_mextDeriv_wedgeWith_complexDzBar hf'_eq hfd, hsol z z.property, ← add_smul]
  simp

/-- **Explicit `(1, 0)`-primitive for complex Banach-valued two-forms on open subsets of `ℂ`.**
Every `C^n` (`1 ≤ n`) two-form `η` on an arbitrary open subset `U ⊆ ℂ` with values in a
complex Banach space `W` equals `d(g dz)` for a `C^n` function `g : U → W`. -/
theorem exists_contMDiff_mextDeriv_wedgeWith_complexDz_eq {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {n : ℕ∞} (hn : 1 ≤ n)
    {η : RoughForm 𝓘(ℝ, ℂ) U W 2} (hη : IsSmoothForm 𝓘(ℝ, ℂ) n η) :
    ∃ g : U → W, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) n g ∧
      mextDeriv
        (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
          (RoughForm.ofFunction 𝓘(ℝ, ℂ) g)
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
            SmoothForm.complexDz.val)) = η := by
  let h : U → W := fun z ↦ (2 * Complex.I)⁻¹ • planarTwoFormCoeff η z
  have hh : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) n h :=
    (contMDiff_iff_contDiff.2
      (((2 * Complex.I)⁻¹ • ContinuousLinearMap.id ℂ W).restrictScalars ℝ).contDiff).comp
      hη.contMDiff_planarTwoFormCoeff
  let h' : ℂ → W := Subtype.val.extend h 0
  have hh'_eq (z : U) : h' z = h z := Subtype.val_injective.extend_apply h 0 z
  have hh' : ContDiffOn ℝ n h' (U : Set ℂ) :=
    contMDiffOn_iff_contDiffOn.1 (ContMDiffMap.contMDiffOn_extend U ⟨h, hh⟩ 0)
  obtain ⟨g', hg', hsol⟩ :=
    exists_contDiffOn_conjWirtingerDeriv_apply_one_eq hn U.isOpen hh'
  let g : U → W := g' ∘ Subtype.val
  have hg : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) n g := hg'.contMDiff_comp_subtypeVal
  refine ⟨g, hg, ?_⟩
  apply planarTwoFormCoeff_injective
  funext z
  have hgd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, W) g z :=
    (hg z).mdifferentiableAt (by exact_mod_cast (zero_lt_one.trans_le hn).ne')
  rw [planarTwoFormCoeff_mextDeriv_wedgeWith_complexDz (g := g) (g' := g') (fun _ ↦ rfl) hgd,
    hsol z z.property, hh'_eq z]
  have hne : (2 * Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  simp only [h, smul_smul, mul_inv_cancel₀ hne, one_smul]

/-- **Banach-valued two-form exactness on open subsets of `ℂ` (`C^n`).** Every `C^n` (`1 ≤ n`)
two-form on an arbitrary open subset `U ⊆ ℂ` with values in any real Banach space `F` (including
`ℝ`, `ℂ`, and every complex Banach space) is the exterior derivative of a `C^n` one-form. -/
theorem exists_isSmoothForm_mextDeriv_eq_of_opens_complex {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {n : ℕ∞} (hn : 1 ≤ n)
    {η : RoughForm 𝓘(ℝ, ℂ) U F 2} (hη : IsSmoothForm 𝓘(ℝ, ℂ) n η) :
    ∃ β : RoughForm 𝓘(ℝ, ℂ) U F 1,
      IsSmoothForm 𝓘(ℝ, ℂ) n β ∧ mextDeriv β = η := by
  obtain ⟨g, hg, hdg⟩ :=
    exists_contMDiff_mextDeriv_wedgeWith_complexDz_eq (W := Complexification F) hn
      (hη.mapCoeff (Complexification.ofRealLI F).toContinuousLinearMap)
  set dz := mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDz.val
  let βℂ : RoughForm 𝓘(ℝ, ℂ) U (Complexification F) 1 :=
    RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
      (RoughForm.ofFunction 𝓘(ℝ, ℂ) g) dz
  have hβℂ : IsSmoothForm 𝓘(ℝ, ℂ) n βℂ := by
    have hdz : IsSmoothForm 𝓘(ℝ, ℂ) n dz :=
      (SmoothForm.complexDz.isSmoothForm.mpullback
        (contMDiff_subtypeVal (n := ∞))).of_le (by simp)
    exact (isSmoothForm_ofFunction_iff.2 hg).wedgeWith _ hdz
  refine ⟨RoughForm.mapCoeff (Complexification.reCLM F) βℂ, hβℂ.mapCoeff _, ?_⟩
  rw [mextDeriv_mapCoeff _ (hβℂ.of_le (by exact_mod_cast hn)), hdg]
  simp

/-- **Banach-valued two-form exactness on open subsets of `ℂ` (bundled smooth forms).** Every
smooth two-form on an arbitrary open subset `U ⊆ ℂ` with values in any real Banach space `F`
(including `ℝ`, `ℂ`, and every complex Banach space) is the exterior derivative of a smooth
one-form. -/
theorem exists_mextDerivₗ_eq_of_opens_complex {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (η : SmoothForm 𝓘(ℝ, ℂ) U F 2) :
    ∃ β : SmoothForm 𝓘(ℝ, ℂ) U F 1, mextDerivₗ 𝓘(ℝ, ℂ) 1 β = η := by
  obtain ⟨β, hβ, hdβ⟩ :=
    exists_isSmoothForm_mextDeriv_eq_of_opens_complex (n := ⊤) le_top η.isSmoothForm
  exact ⟨⟨β, hβ.mem_smoothBundleForms⟩,
    Subtype.ext ((mextDerivₗ_apply 𝓘(ℝ, ℂ) 1 _).trans hdβ)⟩

end Exactness

end TauCeti
