/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Comul
public import TauCeti.NumberTheory.Padics.Distribution.LocallyAnalytic

/-!
# Translation on locally analytic functions

The isometric stage translation
`TauCeti.AnalyticStage.translate S x : LA_h(E) ≃ₗᵢ[S] LA_h(E)` (defined in
`TauCeti.NumberTheory.Padics.Distribution.Comul`) commutes with stage transitions
(`AnalyticStage.transitionLE_translate`), and therefore descends via `Module.DirectLimit.congr` to
the linear equivalence `TauCeti.LocallyAnalytic.translate S x : LA(ℤ_p, E) ≃ₗ[S] LA(ℤ_p, E)`
satisfying `eval S (translate S x f) y = eval S f (x + y)` (`LocallyAnalytic.eval_translate`).

## Main definitions

* `TauCeti.LocallyAnalytic.translate S x`: translation `LA(ℤ_p, E) ≃ₗ[S] LA(ℤ_p, E)` by `x`.

## Main results

* `TauCeti.LocallyAnalytic.translate_ofStage`, `TauCeti.LocallyAnalytic.eval_translate`,
  `TauCeti.LocallyAnalytic.translate_zero`, `TauCeti.LocallyAnalytic.translate_add`,
  `TauCeti.LocallyAnalytic.translate_symm`: stage restriction, evaluation, group law, and inverse
  for translation on `LA(ℤ_p, E)`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
-/

public section

namespace TauCeti.LocallyAnalytic

open AnalyticStage

variable {p : ℕ} [Fact p.Prime]
  {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- **Translation on locally analytic functions.** Translating the argument by `x : ℤ_p` defines a
linear equivalence `LA(ℤ_p, E) ≃ₗ[S] LA(ℤ_p, E)` agreeing with `AnalyticStage.translate S x` on
every stage. -/
noncomputable def translate (x : ℤ_[p]) : LocallyAnalytic p S E ≃ₗ[S] LocallyAnalytic p S E :=
  Module.DirectLimit.congr (fun _ ↦ (AnalyticStage.translate S x).toLinearEquiv)
    (fun _ _ hhk ↦ LinearMap.ext fun c ↦ (transitionLE_translate S hhk x c).symm)

/-- Translation restricts to `AnalyticStage.translate` on every analytic stage. -/
@[simp]
theorem translate_ofStage (x : ℤ_[p]) (h : ℕ) (c : AnalyticStage p h E) :
    translate S x (ofStage S h c) = ofStage S h (AnalyticStage.translate S x c) := by
  rw [translate, ofStage_def, Module.DirectLimit.congr_apply_of,
    LinearIsometryEquiv.coe_toLinearEquiv]

/-- Evaluating the translate of `f` by `x` at `y` gives `eval S f (x + y)`. -/
@[simp]
theorem eval_translate (x : ℤ_[p]) (f : LocallyAnalytic p S E) (y : ℤ_[p]) :
    eval S (translate S x f) y = eval S f (x + y) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, translate_ofStage, eval_ofStage, eval_ofStage, AnalyticStage.eval_translate]

/-- Translating by `0` is the identity. -/
@[simp]
theorem translate_zero (f : LocallyAnalytic p S E) : translate S 0 f = f := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, translate_ofStage, AnalyticStage.translate_zero]

/-- Translations compose by addition. -/
theorem translate_add (x y : ℤ_[p]) (f : LocallyAnalytic p S E) :
    translate S (x + y) f = translate S x (translate S y f) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, translate_ofStage, translate_ofStage, translate_ofStage,
    AnalyticStage.translate_add]

/-- The inverse of translation by `x` is translation by `-x`. -/
@[simp]
theorem translate_symm (x : ℤ_[p]) :
    (translate (p := p) (E := E) S x).symm = translate S (-x) := by
  ext f
  apply (translate S x).injective
  rw [LinearEquiv.apply_symm_apply, ← translate_add, add_neg_cancel, translate_zero]

end TauCeti.LocallyAnalytic
