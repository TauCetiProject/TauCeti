/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.NumberTheory.ModularForms.DirectSum

/-!
# Injectivity of the `q`-expansion on the graded ring of modular forms

Mathlib's `ModularForm.qExpansion_injective` shows that `qExpansion h` is injective on modular forms
of a single weight `k`. On the full graded ring `⨁ k : ℤ, ModularForm Γ k`, the ring homomorphism
`ModularForm.qExpansionRingHom` (and `ℂ`-algebra homomorphism `ModularForm.qExpansionAlgHom` when
`[Γ.HasDetOne]`) sums the `q`-expansions across weights.

For every `x : ⨁ k : ℤ, ModularForm Γ k` and `τ : ℍ`, the power series
`ModularForm.qExpansionRingHom h hh hΓ x` converges at `Function.Periodic.qParam h τ` to the
pointwise sum `ModularForm.evalDirectSum x τ`
(`TauCeti.ModularForm.hasSum_qExpansionRingHom`). Combined with linear independence of modular forms
across weights (`ModularForm.evalDirectSum_injective`), this proves that
`ModularForm.qExpansionRingHom` and `ModularForm.qExpansionAlgHom` are injective whenever
`[Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]`.

## Main results

* `TauCeti.ModularForm.hasSum_qExpansionRingHom`: the `q`-expansion of a mixed-weight sum of
  modular forms converges at `Function.Periodic.qParam h τ` to its pointwise evaluation on `ℍ`.
* `TauCeti.ModularForm.qExpansionRingHom_injective`,
  `TauCeti.ModularForm.qExpansionAlgHom_injective`: `q`-expansion is injective on the graded ring of
  modular forms when `Γ` has finite-index intersection with `SL₂(ℤ)`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII.
* P. Deligne, *Courbes elliptiques : formulaire d'après J. Tate*, in *Modular functions of one
  variable IV*, Lecture Notes in Math. 476, Springer, 1975.
-/

public noncomputable section

open UpperHalfPlane PowerSeries ModularForm
open scoped DirectSum MatrixGroups

namespace TauCeti.ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ}

/-- For a mixed-weight sum `x : ⨁ k : ℤ, ModularForm Γ k`, the `q`-expansion power series
`ModularForm.qExpansionRingHom h hh hΓ x` converges at `Function.Periodic.qParam h τ` to the
pointwise sum `evalDirectSum x τ`. -/
theorem hasSum_qExpansionRingHom [Γ.HasDetPlusMinusOne] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (x : ⨁ k : ℤ, _root_.ModularForm Γ k) (τ : ℍ) :
    HasSum (fun m ↦ (_root_.ModularForm.qExpansionRingHom h hh hΓ x).coeff m *
        Function.Periodic.qParam h τ ^ m)
      (evalDirectSum x τ) := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  induction x using DirectSum.induction_on with
  | zero => simp
  | of k f =>
    simpa only [_root_.ModularForm.qExpansionRingHom_apply, evalDirectSum_of] using
      _root_.ModularForm.hasSum_qExpansion f hh hΓ τ
  | add x y ihx ihy =>
    simpa only [map_add, Pi.add_apply, add_mul] using ihx.add ihy

/-- **Injectivity of `q`-expansion on the graded ring.** When `Γ` has finite-index intersection with
`SL₂(ℤ)`, the ring homomorphism `ModularForm.qExpansionRingHom h hh hΓ` from
`⨁ k : ℤ, ModularForm Γ k` to `ℂ⟦X⟧` is injective. -/
theorem qExpansionRingHom_injective [Γ.HasDetPlusMinusOne] [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    Function.Injective (_root_.ModularForm.qExpansionRingHom h hh hΓ) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  refine (injective_iff_map_eq_zero _).mp evalDirectSum_injective x <| funext fun τ ↦ ?_
  have hsum := hasSum_qExpansionRingHom hh hΓ x τ
  simp only [hx, map_zero, zero_mul] at hsum
  simpa using hsum.unique hasSum_zero

@[simp]
theorem qExpansionRingHom_inj [Γ.HasDetPlusMinusOne] [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {x y : ⨁ k : ℤ, _root_.ModularForm Γ k} :
    _root_.ModularForm.qExpansionRingHom h hh hΓ x =
      _root_.ModularForm.qExpansionRingHom h hh hΓ y ↔ x = y :=
  (qExpansionRingHom_injective hh hΓ).eq_iff

/-- **Injectivity of `q`-expansion on the graded `ℂ`-algebra.** When `Γ` has determinant one and
finite-index intersection with `SL₂(ℤ)`, `ModularForm.qExpansionAlgHom h hh hΓ` is injective. -/
theorem qExpansionAlgHom_injective [Γ.HasDetOne] [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    Function.Injective (_root_.ModularForm.qExpansionAlgHom h hh hΓ) :=
  qExpansionRingHom_injective hh hΓ

@[simp]
theorem qExpansionAlgHom_inj [Γ.HasDetOne] [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {x y : ⨁ k : ℤ, _root_.ModularForm Γ k} :
    _root_.ModularForm.qExpansionAlgHom h hh hΓ x =
      _root_.ModularForm.qExpansionAlgHom h hh hΓ y ↔ x = y :=
  (qExpansionAlgHom_injective hh hΓ).eq_iff

end TauCeti.ModularForm

end
