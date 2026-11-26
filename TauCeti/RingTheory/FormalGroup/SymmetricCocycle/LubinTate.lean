/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.BaseChange
public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.FormalGroup.Deformation.LubinTate
public import TauCeti.RingTheory.FormalGroup.Logarithm.Basic
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Coboundary
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.RingTheory.PowerSeries.CoeffMulMem
import TauCeti.Data.Finsupp.Fin
import TauCeti.RingTheory.FormalGroup.Basic
import TauCeti.RingTheory.FormalGroup.LazardRing.LeadingTerm
import TauCeti.RingTheory.FormalGroup.LazardRing.Polynomial
import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Height
import TauCeti.RingTheory.MvPowerSeries.Derivative
import TauCeti.RingTheory.MvPowerSeries.Ideal
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.MvPowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.Basic

/-!
# Linearised square-zero deformation cocycles and Lubin–Tate cocycles

Let `F(X, Y)` be a commutative formal group law over a commutative ring `A` with normalised
invariant differential `ω = P(T) dT` (`P(T) = F_X(0, T)⁻¹`), and let `I ⊆ A` be an ideal with
`I * I = ⊥`. Following §1 of Lubin and Tate (1966), this file connects deformations of `F` modulo
`I` to symmetric 2-cocycles (`FormalGroup.IsSymmetricCocycle`) and constructs canonical symmetric
2-cocycles with prescribed leading Lazard cocycle over every commutative ring.

## Main definitions and results

* `FormalGroup.deformationCocycle`, `FormalGroup.deformationCocycle_def`,
  `FormalGroup.deformByCocycle`, `FormalGroup.map_deformByCocycle`,
  `FormalGroup.map_deformByCocycle_eq`, `FormalGroup.deformationCocycleEquiv`: Lubin–Tate
  Lemma 1.2, identifying commutative formal group laws congruent to `F` modulo `I` with symmetric
  2-cocycles of `F` without constant term with coefficients in `I`, together with
  `FormalGroup.isSymmetricCocycle_deformationCocycle` and `FormalGroup.deformationCocycle_trans`.
* `FormalGroup.deformationCocycle_smul_eq_homDefect_𝔾ₐ`,
  `FormalGroup.exists_smul_eq_iff_exists_deformationCocycle_eq_homDefect_𝔾ₐ`: Lubin–Tate Lemma 1.1,
  characterising `I`-congruent coordinate equivalence via coboundaries `F.homDefect 𝔾ₐ g`.
* `FormalGroup.lubinTateCocycle`, `TauCeti.lubinTateIndex`,
  `FormalGroup.homogeneousComponent_lubinTateCocycle`,
  `FormalGroup.sum_smul_lubinTateCocycle_eq_homDefect_𝔾ₐ_iff`,
  `FormalGroup.IsSymmetricCocycle.existsUnique_sum_smul_lubinTateCocycle_add_homDefect_𝔾ₐ`:
  Lubin–Tate Lemma 1.3, constructing canonical symmetric 2-cocycles in degree `n + 1` via
  `DualNumber LazardRing` and establishing the Lubin–Tate cocycle basis decomposition.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math.
  France 94 (1966), §1.
* M. Hazewinkel, *Formal Groups and Applications*, Academic Press (1978), §22.
-/

public section

noncomputable section

open MvPowerSeries TauCeti

namespace FormalGroup

/-! ### 1. The linearised deformation cocycle -/

section DeformationCocycle

variable {A B : Type*} [CommRing A] [CommRing B]

/-- **The linearised deformation cocycle** of a pair of formal group laws `F, G` over `A`:
`Φ(X, Y) = P(F(X, Y)) · (G(X, Y) - F(X, Y))`, where `ω = P(T) dT` is the normalised invariant
differential of `F` (`FormalGroup.invariantDifferential`). When `G - F` has coefficients in a
square-zero ideal and `F, G` are commutative, `Φ` is a symmetric 2-cocycle of `F`. -/
noncomputable def deformationCocycle (F G : FormalGroup A) : MvPowerSeries (Fin 2) A :=
  PowerSeries.subst F.toPowerSeries F.invariantDifferential *
    (G.toPowerSeries - F.toPowerSeries)

/-- Unfolding formula for `FormalGroup.deformationCocycle`. -/
theorem deformationCocycle_def (F G : FormalGroup A) :
    F.deformationCocycle G =
      PowerSeries.subst F.toPowerSeries F.invariantDifferential *
        (G.toPowerSeries - F.toPowerSeries) := (rfl)

/-- The deformation cocycle of `F` with itself vanishes. -/
@[simp]
theorem deformationCocycle_self (F : FormalGroup A) : F.deformationCocycle F = 0 := by
  simp [deformationCocycle]

/-- The deformation cocycle has zero constant coefficient. -/
@[simp]
theorem constantCoeff_deformationCocycle (F G : FormalGroup A) :
    constantCoeff (F.deformationCocycle G) = 0 := by
  simp [deformationCocycle, F.zero_constantCoeff, G.zero_constantCoeff]

/-- Over the additive formal group law `𝔾ₐ`, whose invariant differential is `dT`, the deformation
cocycle of `G` is the nonlinear difference `G(X, Y) - (X + Y)`. -/
@[simp]
theorem deformationCocycle_𝔾ₐ (G : FormalGroup A) :
    (𝔾ₐ : FormalGroup A).deformationCocycle G = G.toPowerSeries - (X 0 + X 1) := by
  rw [deformationCocycle, invariantDifferential_𝔾ₐ,
    ← PowerSeries.coe_substAlgHom (.of_constantCoeff_zero 𝔾ₐ.zero_constantCoeff), map_one, one_mul,
    𝔾ₐ_toPowerSeries]

/-- The deformation cocycle commutes with change of coefficient ring. -/
@[simp]
theorem map_deformationCocycle (f : A →+* B) (F G : FormalGroup A) :
    MvPowerSeries.map f (F.deformationCocycle G) =
      (F.map f).deformationCocycle (G.map f) := by
  rw [deformationCocycle, deformationCocycle, map_mul, map_sub,
    PowerSeries.map_subst (.of_constantCoeff_zero F.zero_constantCoeff),
    F.map_invariantDifferential, F.map_toPowerSeries, G.map_toPowerSeries]

/-- Recovering `G - F` from `F.deformationCocycle G` via `F_X(0, F(X, Y))`. -/
private theorem sub_toPowerSeries_eq_mul_deformationCocycle (F G : FormalGroup A) :
    G.toPowerSeries - F.toPowerSeries =
      PowerSeries.subst F.toPowerSeries F.derivZeroX * F.deformationCocycle G := by
  rw [deformationCocycle, ← mul_assoc, mul_comm (PowerSeries.subst _ F.derivZeroX),
    F.subst_invariantDifferential_mul_derivZeroX (.of_constantCoeff_zero F.zero_constantCoeff),
    one_mul]

/-- For a fixed base law `F`, `G ↦ F.deformationCocycle G` is injective over any commutative ring,
since `P(F(X, Y))` is a unit in `A⟦X, Y⟧`. -/
theorem deformationCocycle_injective (F : FormalGroup A) :
    Function.Injective F.deformationCocycle := by
  intro G₁ G₂ h
  have hsub : G₁.toPowerSeries - F.toPowerSeries = G₂.toPowerSeries - F.toPowerSeries := by
    rw [F.sub_toPowerSeries_eq_mul_deformationCocycle G₁,
      F.sub_toPowerSeries_eq_mul_deformationCocycle G₂, h]
  exact FormalGroup.ext (sub_left_inj.mp hsub)

/-- The deformation cocycle `F.deformationCocycle G` has coefficients in an ideal `I` if and only
if `G - F` has coefficients in `I`. -/
theorem coeff_deformationCocycle_mem_iff {F G : FormalGroup A} {I : Ideal A} :
    (∀ d, coeff d (F.deformationCocycle G) ∈ I) ↔
      ∀ d, coeff d (G.toPowerSeries - F.toPowerSeries) ∈ I :=
  ⟨fun h d ↦ F.sub_toPowerSeries_eq_mul_deformationCocycle G ▸ coeff_mul_mem_of_right h d,
    fun h d ↦ coeff_mul_mem_of_right h d⟩

/-- The deformation cocycle vanishes below total degree `2`. -/
theorem two_le_order_deformationCocycle (F G : FormalGroup A) :
    ((2 : ℕ) : ℕ∞) ≤ (F.deformationCocycle G).order := by
  have hord : ((2 : ℕ) : ℕ∞) ≤ (G.toPowerSeries - F.toPowerSeries).order := by
    rw [← G.homDefect_X F]
    exact G.two_le_order_homDefect_X F
  exact le_order_mul_of_le_right hord

/-- **Additivity of the deformation cocycle across square-zero steps.** If `G ≡ F (mod I)` and
`H ≡ G (mod I)` for an ideal `I` with `I * I = ⊥`, then
`F.deformationCocycle H = F.deformationCocycle G + G.deformationCocycle H`. -/
theorem deformationCocycle_trans {F G H : FormalGroup A} {I : Ideal A} (hI : I * I = ⊥)
    (hFG : ∀ d, coeff d (G.toPowerSeries - F.toPowerSeries) ∈ I)
    (hGH : ∀ d, coeff d (H.toPowerSeries - G.toPowerSeries) ∈ I) :
    F.deformationCocycle H = F.deformationCocycle G + G.deformationCocycle H := by
  set π := Ideal.Quotient.mk I
  have hmap : G.map π = F.map π := by
    ext d
    rw [FormalGroup.map_toPowerSeries, FormalGroup.map_toPowerSeries, coeff_map, coeff_map,
      ← sub_eq_zero, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hFG d
  have hzero : (PowerSeries.subst G.toPowerSeries G.invariantDifferential -
      PowerSeries.subst F.toPowerSeries F.invariantDifferential) *
      (H.toPowerSeries - G.toPowerSeries) = 0 :=
    mul_eq_zero_of_coeff_mem hI (fun d ↦ by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, map_sub,
        PowerSeries.map_subst (.of_constantCoeff_zero G.zero_constantCoeff),
        PowerSeries.map_subst (.of_constantCoeff_zero F.zero_constantCoeff),
        G.map_invariantDifferential, F.map_invariantDifferential,
        ← FormalGroup.map_toPowerSeries, ← FormalGroup.map_toPowerSeries, hmap, sub_self, map_zero])
      hGH
  simp only [deformationCocycle]; linear_combination -hzero

/-- Reversing the roles of `F` and `G` negates the deformation cocycle when `G ≡ F (mod I)` and
`I * I = ⊥`. -/
theorem deformationCocycle_symm {F G : FormalGroup A} {I : Ideal A} (hI : I * I = ⊥)
    (hFG : ∀ d, coeff d (G.toPowerSeries - F.toPowerSeries) ∈ I) :
    G.deformationCocycle F = -F.deformationCocycle G := by
  have h := deformationCocycle_trans hI hFG fun d ↦ by
    rw [← neg_sub, map_neg]; exact I.neg_mem (hFG d)
  rw [deformationCocycle_self] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- First-order expansion of `(F + Δ)((F + Δ)(X₀, X₁), X₂) - (F + Δ)(X₀, (F + Δ)(X₁, X₂))` when `Δ`
has coefficients in a square-zero ideal `I`. -/
private theorem assocDefect_add_eq {I : Ideal A} (hI : I * I = ⊥) (F : FormalGroup A)
    (Δ : MvPowerSeries (Fin 2) A) (hΔI : ∀ d, coeff d Δ ∈ I) :
    let S := F.toPowerSeries + Δ
    let F₀₁ := F.toPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1]
    let F₁₂ := F.toPowerSeries.subst ![(X 1 : MvPowerSeries (Fin 3) A), X 2]
    S.subst ![S.subst ![X 0, X 1], X 2] - S.subst ![X 0, S.subst ![X 1, X 2]] =
      Δ.subst ![X 0, X 1] * (pderiv 0 F.toPowerSeries).subst ![F₀₁, X 2] + Δ.subst ![F₀₁, X 2] -
        Δ.subst ![X 0, F₁₂] -
        Δ.subst ![X 1, X 2] * (pderiv 1 F.toPowerSeries).subst ![X 0, F₁₂] := by
  intro S F₀₁ F₁₂
  have haL : HasSubst ![F₀₁, X 2] := .cons_subst_zero_left 0 1 2 F.zero_constantCoeff
  have haR : HasSubst ![X 0, F₁₂] := .cons_subst_zero_right 0 1 2 F.zero_constantCoeff
  set δL : Fin 2 → MvPowerSeries (Fin 3) A := ![Δ.subst ![X 0, X 1], 0]
  set δR : Fin 2 → MvPowerSeries (Fin 3) A := ![0, Δ.subst ![X 1, X 2]]
  have hδLI : ∀ s d, coeff d (δL s) ∈ I
    | 0, d => coeff_subst_mem_of_coeff_mem .X_X hΔI d
    | 1, _ => by simp [δL]
  have hδRI : ∀ s d, coeff d (δR s) ∈ I
    | 0, _ => by simp [δR]
    | 1, d => coeff_subst_mem_of_coeff_mem .X_X hΔI d
  have hhL i j := mul_eq_zero_of_coeff_mem hI (hδLI i) (hδLI j)
  have hhR i j := mul_eq_zero_of_coeff_mem hI (hδRI i) (hδRI j)
  have heqL : (![S.subst ![X 0, X 1], X 2] : Fin 2 → MvPowerSeries (Fin 3) A) = ![F₀₁, X 2] + δL :=
    by funext s; fin_cases s <;> simp [S, F₀₁, δL, subst_add .X_X]
  have heqR : (![X 0, S.subst ![X 1, X 2]] : Fin 2 → MvPowerSeries (Fin 3) A) = ![X 0, F₁₂] + δR :=
    by funext s; fin_cases s <;> simp [S, F₁₂, δR, subst_add .X_X]
  rw [heqL, heqR, subst_add (haL.add (.of_sq_eq_zero fun i ↦ by rw [sq, hhL])),
    subst_add (haR.add (.of_sq_eq_zero fun i ↦ by rw [sq, hhR])),
    subst_add_of_mul_eq_zero haL hhL F.toPowerSeries, subst_add_of_mul_eq_zero haL hhL Δ,
    sum_mul_pderiv_subst_eq_zero hI haL hδLI hΔI,
    subst_add_of_mul_eq_zero haR hhR F.toPowerSeries, subst_add_of_mul_eq_zero haR hhR Δ,
    sum_mul_pderiv_subst_eq_zero hI haR hδRI hΔI, Fin.sum_univ_two, Fin.sum_univ_two, ← F.assoc]
  simp only [δL, δR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    zero_mul, _root_.add_zero]
  ring

/-- Multiplying the associativity defect of `S = F + F_X(0, F) · Φ` by `P(F(F(X₀, X₁), X₂))`
recovers the 2-cocycle defect `Φ(X₀, X₁) + Φ(F(X₀, X₁), X₂) - Φ(X₀, F(X₁, X₂)) - Φ(X₁, X₂)`. -/
private theorem mul_assocDefect_add_eq_cocycle {I : Ideal A} (hI : I * I = ⊥)
    (F : FormalGroup A) [F.IsComm] {Φ : MvPowerSeries (Fin 2) A} (hΦI : ∀ d, coeff d Φ ∈ I) :
    let Δ := PowerSeries.subst F.toPowerSeries F.derivZeroX * Φ
    let S := F.toPowerSeries + Δ
    let F₀₁ := F.toPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1]
    let F₁₂ := F.toPowerSeries.subst ![(X 1 : MvPowerSeries (Fin 3) A), X 2]
    PowerSeries.subst (F.toPowerSeries.subst ![F₀₁, X 2]) F.invariantDifferential *
        (S.subst ![S.subst ![X 0, X 1], X 2] - S.subst ![X 0, S.subst ![X 1, X 2]]) =
      Φ.subst ![X 0, X 1] + Φ.subst ![F₀₁, X 2] - Φ.subst ![X 0, F₁₂] - Φ.subst ![X 1, X 2] := by
  intro Δ S F₀₁ F₁₂
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have haL : HasSubst ![F₀₁, X 2] := .cons_subst_zero_left 0 1 2 F.zero_constantCoeff
  have haR : HasSubst ![X 0, F₁₂] := .cons_subst_zero_right 0 1 2 F.zero_constantCoeff
  have hPΔ : PowerSeries.subst F.toPowerSeries F.invariantDifferential * Δ = Φ := by
    dsimp only [Δ]; rw [← mul_assoc, F.subst_invariantDifferential_mul_derivZeroX hF, one_mul]
  have hPΔ_sub {b : Fin 2 → MvPowerSeries (Fin 3) A} (hb : HasSubst b) :
      PowerSeries.subst (F.toPowerSeries.subst b) F.invariantDifferential * Δ.subst b =
        Φ.subst b := by
    rw [← subst_powerSeriesSubst hb hF, ← subst_mul hb, hPΔ]
  have inv0 := congrArg (subst ![F₀₁, X 2]) F.subst_invariantDifferential_mul_pderiv
  rw [subst_mul haL, subst_powerSeriesSubst haL hF, subst_powerSeriesSubst haL (.X 0),
    subst_X haL, Matrix.cons_val_zero] at inv0
  have inv1 := congrArg (subst ![X 0, F₁₂]) F.subst_invariantDifferential_mul_pderiv_one
  rw [subst_mul haR, subst_powerSeriesSubst haR hF, subst_powerSeriesSubst haR (.X 1),
    subst_X haR, Matrix.cons_val_one, Matrix.cons_val_fin_one, ← F.assoc] at inv1
  have had := assocDefect_add_eq hI F Δ (coeff_mul_mem_of_right hΦI)
  dsimp only at had
  rw [had, ← hPΔ_sub .X_X, ← hPΔ_sub haL, ← hPΔ_sub haR, ← hPΔ_sub .X_X, ← inv0, ← inv1,
    ← F.assoc]
  ring

/-- **Lubin–Tate, Lemma 1.2 (forward direction).** If `F` and `G` are commutative formal group laws
over `A` that agree modulo a square-zero ideal `I` (`I * I = ⊥`), then `F.deformationCocycle G` is
a symmetric 2-cocycle of `F`. -/
theorem isSymmetricCocycle_deformationCocycle (F G : FormalGroup A) [F.IsComm] [G.IsComm]
    {I : Ideal A} (hI : I * I = ⊥)
    (hFG : ∀ d, coeff d (G.toPowerSeries - F.toPowerSeries) ∈ I) :
    F.IsSymmetricCocycle (F.deformationCocycle G) where
  subst_swap := by
    rw [deformationCocycle, subst_mul HasSubst.X_X, subst_sub HasSubst.X_X,
      subst_powerSeriesSubst HasSubst.X_X (.of_constantCoeff_zero F.zero_constantCoeff),
      ← IsComm.comm (F := F), ← IsComm.comm (F := G)]
  subst_add_subst_eq := by
    have hG : G.toPowerSeries = F.toPowerSeries +
        PowerSeries.subst F.toPowerSeries F.derivZeroX * F.deformationCocycle G := by
      rw [← F.sub_toPowerSeries_eq_mul_deformationCocycle G, add_sub_cancel]
    have h := mul_assocDefect_add_eq_cocycle hI F (coeff_deformationCocycle_mem_iff.mpr hFG)
    dsimp only at h; rw [← hG, G.assoc, sub_self, mul_zero] at h; linear_combination -h

private theorem two_le_order_derivZeroX_mul (F : FormalGroup A)
    {Φ : MvPowerSeries (Fin 2) A} (hΦ : F.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0) :
    ((2 : ℕ) : ℕ∞) ≤ (PowerSeries.subst F.toPowerSeries F.derivZeroX * Φ).order :=
  le_order_mul_of_le_right (hΦ.two_le_order hΦ₀)

/-- **Lubin–Tate, Lemma 1.2 (inverse construction).** Given a commutative formal group law `F` over
`A`, an ideal `I` with `I * I = ⊥`, and a symmetric 2-cocycle `Φ` of `F` without constant term whose
coefficients lie in `I`, `F(X, Y) + F_X(0, F(X, Y)) · Φ(X, Y)` is a formal group law over `A`. -/
noncomputable def deformByCocycle (F : FormalGroup A) [F.IsComm] {I : Ideal A} (hI : I * I = ⊥)
    {Φ : MvPowerSeries (Fin 2) A} (hΦ : F.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0)
    (hΦI : ∀ d, coeff d Φ ∈ I) : FormalGroup A where
  toPowerSeries := F.toPowerSeries + PowerSeries.subst F.toPowerSeries F.derivZeroX * Φ
  zero_constantCoeff := by simp [F.zero_constantCoeff, hΦ₀]
  lin_coeff_X := by
    rw [map_add, F.lin_coeff_X, coeff_of_lt_order (lt_of_lt_of_le (by simp)
      (F.two_le_order_derivZeroX_mul hΦ hΦ₀)), _root_.add_zero]
  lin_coeff_Y := by
    rw [map_add, F.lin_coeff_Y, coeff_of_lt_order (lt_of_lt_of_le (by simp)
      (F.two_le_order_derivZeroX_mul hΦ hΦ₀)), _root_.add_zero]
  assoc := by
    have h : _ = (0 : MvPowerSeries (Fin 3) A) :=
      (mul_assocDefect_add_eq_cocycle hI F hΦI).trans (by rw [hΦ.subst_add_subst_eq]; abel)
    have hF3 := F.hasSubst_subst_pair (F.hasSubst_subst_pair
      (PowerSeries.HasSubst.X (τ := Fin 3) (S := A) 0) (.X 1)) (.X 2)
    have hzero := congrArg (PowerSeries.subst (F.toPowerSeries.subst
      ![F.toPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1], X 2])
      F.derivZeroX * ·) h
    rw [mul_zero, ← mul_assoc, mul_comm (PowerSeries.subst _ F.derivZeroX),
      F.subst_invariantDifferential_mul_derivZeroX hF3, one_mul] at hzero
    exact sub_eq_zero.mp hzero

/-- The underlying power series of `F.deformByCocycle hI hΦ hΦ₀ hΦI`. -/
@[simp]
theorem toPowerSeries_deformByCocycle (F : FormalGroup A) [F.IsComm] {I : Ideal A}
    (hI : I * I = ⊥) {Φ : MvPowerSeries (Fin 2) A} (hΦ : F.IsSymmetricCocycle Φ)
    (hΦ₀ : constantCoeff Φ = 0) (hΦI : ∀ d, coeff d Φ ∈ I) :
    (F.deformByCocycle hI hΦ hΦ₀ hΦI).toPowerSeries =
      F.toPowerSeries + PowerSeries.subst F.toPowerSeries F.derivZeroX * Φ := (rfl)

/-- A formal group law constructed from a symmetric 2-cocycle is commutative. -/
instance instIsCommDeformByCocycle (F : FormalGroup A) [F.IsComm] {I : Ideal A} (hI : I * I = ⊥)
    {Φ : MvPowerSeries (Fin 2) A} (hΦ : F.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0)
    (hΦI : ∀ d, coeff d Φ ∈ I) : (F.deformByCocycle hI hΦ hΦ₀ hΦI).IsComm where
  comm := by
    rw [toPowerSeries_deformByCocycle, subst_add HasSubst.X_X, subst_mul HasSubst.X_X,
      subst_powerSeriesSubst HasSubst.X_X (.of_constantCoeff_zero F.zero_constantCoeff),
      ← IsComm.comm (F := F), hΦ.subst_swap]

/-- The deformation cocycle of `F.deformByCocycle hI hΦ hΦ₀ hΦI` relative to `F` is `Φ`. -/
@[simp]
theorem deformationCocycle_deformByCocycle (F : FormalGroup A) [F.IsComm] {I : Ideal A}
    (hI : I * I = ⊥) {Φ : MvPowerSeries (Fin 2) A} (hΦ : F.IsSymmetricCocycle Φ)
    (hΦ₀ : constantCoeff Φ = 0) (hΦI : ∀ d, coeff d Φ ∈ I) :
    F.deformationCocycle (F.deformByCocycle hI hΦ hΦ₀ hΦI) = Φ := by
  rw [deformationCocycle, toPowerSeries_deformByCocycle, add_sub_cancel_left, ← mul_assoc,
    F.subst_invariantDifferential_mul_derivZeroX (.of_constantCoeff_zero F.zero_constantCoeff),
    one_mul]

/-- Deforming `F` by `F.deformationCocycle G` recovers `G`. -/
theorem deformByCocycle_deformationCocycle (F G : FormalGroup A) [F.IsComm] [G.IsComm]
    {I : Ideal A} (hI : I * I = ⊥)
    (hFG : ∀ d, coeff d (G.toPowerSeries - F.toPowerSeries) ∈ I) :
    F.deformByCocycle hI (F.isSymmetricCocycle_deformationCocycle G hI hFG)
      (F.constantCoeff_deformationCocycle G)
      (coeff_deformationCocycle_mem_iff.mpr hFG) = G := by
  ext d
  rw [toPowerSeries_deformByCocycle, ← F.sub_toPowerSeries_eq_mul_deformationCocycle G,
    add_sub_cancel]

/-- Base change along `f : A →+* B` transports `F.deformByCocycle` to `(F.map f).deformByCocycle`
for any square-zero ideal `J` containing `I.map f`. -/
theorem map_deformByCocycle (F : FormalGroup A) [F.IsComm] {I : Ideal A} (hI : I * I = ⊥)
    (f : A →+* B) {J : Ideal B} (hJ : J * J = ⊥) (hIJ : I.map f ≤ J)
    {Φ : MvPowerSeries (Fin 2) A} (hΦ : F.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0)
    (hΦI : ∀ d, coeff d Φ ∈ I) :
    (F.deformByCocycle hI hΦ hΦ₀ hΦI).map f =
      (F.map f).deformByCocycle hJ (hΦ.map f) (by simp [hΦ₀])
        (fun d ↦ hIJ (Ideal.mem_map_of_mem f (hΦI d))) := by
  ext d
  rw [FormalGroup.map_toPowerSeries, toPowerSeries_deformByCocycle,
    toPowerSeries_deformByCocycle, map_add, map_mul,
    PowerSeries.map_subst (.of_constantCoeff_zero F.zero_constantCoeff),
    F.map_derivZeroX, FormalGroup.map_toPowerSeries]

/-- Base change along a homomorphism `f` vanishing on `I` sends `F.deformByCocycle hI hΦ hΦ₀ hΦI`
to `F.map f`. -/
theorem map_deformByCocycle_eq (F : FormalGroup A) [F.IsComm] {I : Ideal A} (hI : I * I = ⊥)
    (f : A →+* B) (hIf : I ≤ RingHom.ker f) {Φ : MvPowerSeries (Fin 2) A}
    (hΦ : F.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0) (hΦI : ∀ d, coeff d Φ ∈ I) :
    (F.deformByCocycle hI hΦ hΦ₀ hΦI).map f = F.map f := by
  ext d
  rw [FormalGroup.map_toPowerSeries, FormalGroup.map_toPowerSeries, coeff_map, coeff_map,
    toPowerSeries_deformByCocycle, map_add, map_add,
    RingHom.mem_ker.mp (hIf (coeff_mul_mem_of_right hΦI d)), _root_.add_zero]

/-- **Lubin–Tate, Lemma 1.2.** Over a ring `A` with a square-zero ideal `I` (`I * I = ⊥`),
commutative formal group laws `G` congruent to `F` modulo `I` correspond bijectively to symmetric
2-cocycles `Φ` of `F` without constant term whose coefficients lie in `I`. -/
noncomputable def deformationCocycleEquiv (F : FormalGroup A) [F.IsComm] {I : Ideal A}
    (hI : I * I = ⊥) :
    {G : FormalGroup A // G.IsComm ∧ ∀ d, coeff d (G.toPowerSeries - F.toPowerSeries) ∈ I} ≃
      {Φ : MvPowerSeries (Fin 2) A //
        F.IsSymmetricCocycle Φ ∧ constantCoeff Φ = 0 ∧ ∀ d, coeff d Φ ∈ I} where
  toFun G :=
    have := G.property.1
    ⟨F.deformationCocycle G.val, F.isSymmetricCocycle_deformationCocycle G.val hI G.property.2,
      F.constantCoeff_deformationCocycle G.val, coeff_deformationCocycle_mem_iff.mpr G.property.2⟩
  invFun Φ :=
    ⟨F.deformByCocycle hI Φ.property.1 Φ.property.2.1 Φ.property.2.2, inferInstance, fun d ↦ by
      rw [toPowerSeries_deformByCocycle, add_sub_cancel_left]
      exact coeff_mul_mem_of_right Φ.property.2.2 d⟩
  left_inv G :=
    have := G.property.1
    Subtype.ext (F.deformByCocycle_deformationCocycle G.val hI G.property.2)
  right_inv Φ :=
    Subtype.ext (F.deformationCocycle_deformByCocycle hI Φ.property.1 Φ.property.2.1 Φ.property.2.2)

/-- Evaluating `deformationCocycleEquiv` on `G` computes `F.deformationCocycle G`. -/
@[simp]
theorem deformationCocycleEquiv_apply_coe (F : FormalGroup A) [F.IsComm] {I : Ideal A}
    (hI : I * I = ⊥)
    (G : {G : FormalGroup A // G.IsComm ∧ ∀ d, coeff d (G.toPowerSeries - F.toPowerSeries) ∈ I}) :
    (F.deformationCocycleEquiv hI G).val = F.deformationCocycle G.val := (rfl)

/-- Evaluating the inverse of `deformationCocycleEquiv` on `Φ` constructs `deformByCocycle`. -/
@[simp]
theorem deformationCocycleEquiv_symm_apply_coe (F : FormalGroup A) [F.IsComm] {I : Ideal A}
    (hI : I * I = ⊥)
    (Φ : {Φ : MvPowerSeries (Fin 2) A //
      F.IsSymmetricCocycle Φ ∧ constantCoeff Φ = 0 ∧ ∀ d, coeff d Φ ∈ I}) :
    ((F.deformationCocycleEquiv hI).symm Φ).val =
      F.deformByCocycle hI Φ.property.1 Φ.property.2.1 Φ.property.2.2 := (rfl)

end DeformationCocycle

/-! ### 2. Infinitesimal coordinate changes and coboundaries -/

section CoordinateChange

variable {A : Type*} [CommRing A]

/-- If `G ≡ F (mod I)` and `g` has coefficients in `I` with `I * I = ⊥`, then the coboundaries of
`g` along `G` and `F` coincide. -/
theorem homDefect_𝔾ₐ_eq_of_coeff_mem {F G : FormalGroup A} {I : Ideal A} (hI : I * I = ⊥)
    (hFG : ∀ d, coeff d (G.toPowerSeries - F.toPowerSeries) ∈ I)
    {g : PowerSeries A} (hgI : ∀ n, PowerSeries.coeff n g ∈ I) :
    G.homDefect 𝔾ₐ g = F.homDefect 𝔾ₐ g := by
  rw [homDefect_𝔾ₐ, homDefect_𝔾ₐ, PowerSeries.subst_def G.toPowerSeries,
    PowerSeries.subst_def F.toPowerSeries,
    subst_eq_subst_of_coeff_mem
      (PowerSeries.HasSubst.of_constantCoeff_zero G.zero_constantCoeff).const
      (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff).const
      (fun _ ↦ hFG) fun e x hx ↦ ?_]
  rw [← Ideal.mem_bot, ← hI]
  exact Ideal.mul_mem_mul (PowerSeries.mvCoeff_mem_of_coeff_mem hgI e) hx

/-- If `φ - X` has coefficients in an ideal `I`, then `(φ • F) - F` also has coefficients in `I`. -/
private theorem coeff_smul_sub_mem {I : Ideal A} (F : FormalGroup A) {φ : FormalCoordinate A}
    (hφ : ∀ n, PowerSeries.coeff n (φ.toPowerSeries - PowerSeries.X) ∈ I)
    (d : Fin 2 →₀ ℕ) : coeff d ((φ • F).toPowerSeries - F.toPowerSeries) ∈ I := by
  set π := Ideal.Quotient.mk I
  have hφ1 : FormalCoordinate.map π φ = 1 :=
    (FormalCoordinate.map_eq_one_iff π φ).mpr fun n ↦ by rw [Ideal.mk_ker]; exact hφ n
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, map_sub, ← FormalGroup.map_toPowerSeries,
    ← FormalGroup.map_toPowerSeries, map_smul, hφ1, one_smul, sub_self, map_zero]

/-- **Lubin–Tate, Lemma 1.1 (coboundary of an infinitesimal coordinate change).** Let `I` be an
ideal of `A` with `I * I = ⊥`, let `F` be a commutative formal group law over `A`, and let `φ` be a
formal coordinate with `φ(T) ≡ T (mod I)`. Then the deformation cocycle of `φ • F` relative to `F`
is the coboundary `F.homDefect 𝔾ₐ (P · (φ - X))`, where `P` is `F.invariantDifferential`. -/
theorem deformationCocycle_smul_eq_homDefect_𝔾ₐ (F : FormalGroup A) [F.IsComm] {I : Ideal A}
    (hI : I * I = ⊥) {φ : FormalCoordinate A}
    (hφ : ∀ n, PowerSeries.coeff n (φ.toPowerSeries - PowerSeries.X) ∈ I) :
    F.deformationCocycle (φ • F) =
      F.homDefect 𝔾ₐ (F.invariantDifferential * (φ.toPowerSeries - PowerSeries.X)) := by
  set δ := φ.toPowerSeries - PowerSeries.X
  set Δ := (φ • F).toPowerSeries - F.toPowerSeries with hΔ
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := A) i
  have hhom := subst_toPowerSeries_eq_subst_smul_toPowerSeries φ F
  have hφeq : φ.toPowerSeries = PowerSeries.X + δ := by simp [δ]
  have hFsmul : (φ • F).toPowerSeries = F.toPowerSeries + Δ := by simp [Δ]
  set δv : Fin 2 → MvPowerSeries (Fin 2) A :=
    ![PowerSeries.subst (X 0) δ, PowerSeries.subst (X 1) δ]
  have hδvI (i : Fin 2) d : coeff d (δv i) ∈ I := by
    fin_cases i <;> exact PowerSeries.coeff_subst_mem_of_coeff_mem (hX _) hφ d
  have hh i j := mul_eq_zero_of_coeff_mem hI (hδvI i) (hδvI j)
  have harg : (![PowerSeries.subst (X 0) φ.toPowerSeries,
      PowerSeries.subst (X 1) φ.toPowerSeries] : Fin 2 → MvPowerSeries (Fin 2) A) = X + δv := by
    funext i; fin_cases i <;>
      simp [hφeq, δv, PowerSeries.subst_add (hX _), PowerSeries.subst_X (hX _)]
  have hΔsub : Δ.subst (X + δv) = Δ := by
    have h0 := sum_mul_pderiv_subst_eq_zero hI HasSubst.X hδvI (F.coeff_smul_sub_mem hφ)
    simp only [subst_self, id_eq] at h0; rw [subst_X_add_of_mul_eq_zero hh, h0, _root_.add_zero]
  rw [harg, hFsmul, hφeq, PowerSeries.subst_add hF, PowerSeries.subst_X hF,
    subst_add (HasSubst.X.add (.of_sq_eq_zero fun i ↦ by rw [sq, hh])),
    subst_X_add_of_mul_eq_zero hh, hΔsub, Fin.sum_univ_two] at hhom
  have hΔeq : Δ = PowerSeries.subst F.toPowerSeries δ -
      PowerSeries.subst (X 0) δ * pderiv 0 F.toPowerSeries -
      PowerSeries.subst (X 1) δ * pderiv 1 F.toPowerSeries := by
    simp only [δv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hhom
    linear_combination -hhom
  rw [deformationCocycle, ← hΔ, hΔeq, homDefect_𝔾ₐ, PowerSeries.subst_mul hF,
    PowerSeries.subst_mul (hX 0), PowerSeries.subst_mul (hX 1),
    ← F.subst_invariantDifferential_mul_pderiv, ← F.subst_invariantDifferential_mul_pderiv_one]
  ring

/-- For an infinitesimal coordinate `φ` (`φ ≡ X (mod I)` with `I * I = ⊥`), `φ • F = G` if and only
if `F.deformationCocycle G` is the coboundary of `F.invariantDifferential * (φ - X)`. -/
theorem smul_eq_iff_deformationCocycle_eq_homDefect_𝔾ₐ (F G : FormalGroup A) [F.IsComm]
    {I : Ideal A} (hI : I * I = ⊥) {φ : FormalCoordinate A}
    (hφ : ∀ n, PowerSeries.coeff n (φ.toPowerSeries - PowerSeries.X) ∈ I) :
    φ • F = G ↔
      F.deformationCocycle G =
        F.homDefect 𝔾ₐ (F.invariantDifferential * (φ.toPowerSeries - PowerSeries.X)) := by
  rw [← F.deformationCocycle_smul_eq_homDefect_𝔾ₐ hI hφ]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ F.deformationCocycle_injective h.symm⟩

/-- **Lubin–Tate, Lemma 1.1.** Over a commutative ring `A` with an ideal `I` satisfying `I * I = ⊥`,
a commutative formal group law `F` and a formal group law `G` are related by a coordinate `φ`
congruent to `X` modulo `I` if and only if `F.deformationCocycle G` is the coboundary of a power
series without constant term whose coefficients lie in `I`. -/
theorem exists_smul_eq_iff_exists_deformationCocycle_eq_homDefect_𝔾ₐ
    (F G : FormalGroup A) [F.IsComm] {I : Ideal A} (hI : I * I = ⊥) :
    (∃ φ : FormalCoordinate A,
        (∀ n, PowerSeries.coeff n (φ.toPowerSeries - PowerSeries.X) ∈ I) ∧ φ • F = G) ↔
      ∃ g : PowerSeries A, PowerSeries.constantCoeff g = 0 ∧
        (∀ n, PowerSeries.coeff n g ∈ I) ∧ F.deformationCocycle G = F.homDefect 𝔾ₐ g := by
  refine ⟨fun ⟨φ, hφI, h⟩ ↦ h ▸ ⟨_, by simp [φ.constantCoeff_toPowerSeries],
    PowerSeries.coeff_mul_mem_ideal_of_coeff_right_mem_ideal' hφI,
    F.deformationCocycle_smul_eq_homDefect_𝔾ₐ hI hφI⟩,
    fun ⟨g, hg₀, hgI, hcoc⟩ ↦ ?_⟩
  set δ := F.derivZeroX * g with hδ
  have hδI := PowerSeries.coeff_mul_mem_ideal_of_coeff_right_mem_ideal'
    (f := F.derivZeroX) hgI
  have hnil : IsNilpotent (PowerSeries.coeff 1 δ) :=
    ⟨2, by rw [pow_two, ← Ideal.mem_bot, ← hI]; exact Ideal.mul_mem_mul (hδI 1) (hδI 1)⟩
  let φ : FormalCoordinate A :=
    ⟨PowerSeries.X + δ, by simp [δ, hg₀], by simpa using hnil.isUnit_one_add⟩
  have hφX : φ.toPowerSeries - PowerSeries.X = δ := by simp [φ]
  have hinv_mul : F.invariantDifferential * δ = g := by
    rw [hδ, ← mul_assoc, F.invariantDifferential_mul_derivZeroX, one_mul]
  refine ⟨φ, fun n ↦ hφX ▸ hδI n, ?_⟩
  rw [F.smul_eq_iff_deformationCocycle_eq_homDefect_𝔾ₐ G hI (fun n ↦ hφX ▸ hδI n), hφX, hinv_mul]
  exact hcoc

end CoordinateChange

/-! ### 3. Canonical Lubin–Tate symmetric 2-cocycles -/

section LubinTateCocycle

open TauCeti.LazardRing

private noncomputable def shiftGeneratorHom (n : ℕ+) : LazardRing →+* DualNumber LazardRing :=
  homEquiv.symm fun m ↦
    algebraMap LazardRing (DualNumber LazardRing) (generator m) +
      if m = n then DualNumber.eps else 0

private theorem shiftGeneratorHom_apply_generator (n m : ℕ+) :
    shiftGeneratorHom n (generator m) =
      algebraMap LazardRing (DualNumber LazardRing) (generator m) +
        if m = n then DualNumber.eps else 0 :=
  homEquiv_symm_apply_generator _ m

private theorem fst_shiftGeneratorHom (n : ℕ+) (x : LazardRing) :
    (shiftGeneratorHom n x).fst = x :=
  RingHom.congr_fun
    (ringHom_ext (φ := (TrivSqZeroExt.fstHom LazardRing LazardRing LazardRing).toRingHom.comp
        (shiftGeneratorHom n)) (ψ := RingHom.id LazardRing) fun m ↦ by
      simp [shiftGeneratorHom_apply_generator, TrivSqZeroExt.algebraMap_eq_inl,
        apply_ite TrivSqZeroExt.fst]) x

private noncomputable def universalShiftSeries (n : ℕ+) : MvPowerSeries (Fin 2) LazardRing :=
  fun d ↦ (shiftGeneratorHom n (coeff d formalGroup.toPowerSeries)).snd

@[simp]
private theorem coeff_universalShiftSeries (n : ℕ+) (d : Fin 2 →₀ ℕ) :
    coeff d (universalShiftSeries n) =
      (shiftGeneratorHom n (coeff d formalGroup.toPowerSeries)).snd := (rfl)

private theorem smul_eps_map_universalShiftSeries (n : ℕ+) :
    (DualNumber.eps : DualNumber LazardRing) •
        MvPowerSeries.map (algebraMap LazardRing (DualNumber LazardRing))
          (universalShiftSeries n) =
      (formalGroup.map (shiftGeneratorHom n)).toPowerSeries -
        (formalGroup.map (algebraMap LazardRing (DualNumber LazardRing))).toPowerSeries :=
  MvPowerSeries.ext fun d ↦ TrivSqZeroExt.ext
    (by simp [FormalGroup.map_toPowerSeries, fst_shiftGeneratorHom,
      TrivSqZeroExt.algebraMap_eq_inl])
    (by simp [FormalGroup.map_toPowerSeries, TrivSqZeroExt.algebraMap_eq_inl])

private theorem le_order_universalShiftSeries (n : ℕ+) :
    (((n : ℕ) + 1 : ℕ) : ℕ∞) ≤ (universalShiftSeries n).order := by
  have hord := succ_le_order_map_sub_map (n := n)
    (φ := shiftGeneratorHom n) (ψ := algebraMap LazardRing (DualNumber LazardRing))
    fun m hm ↦ by simp [shiftGeneratorHom_apply_generator, hm.ne]
  rw [← smul_eps_map_universalShiftSeries] at hord
  refine le_order fun d hd ↦ ?_
  have hd0 := coeff_of_lt_order (hd.trans_le hord)
  simpa [TrivSqZeroExt.algebraMap_eq_inl] using congrArg TrivSqZeroExt.snd hd0

private theorem homogeneousComponent_universalShiftSeries (n : ℕ+) :
    homogeneousComponent ((n : ℕ) + 1) (universalShiftSeries n) =
      ↑(TauCeti.lazardCocycle ((n : ℕ) + 1) LazardRing) := by
  have hcomp := homogeneousComponent_map_sub_map_eq_smul_lazardCocycle (n := n)
    (φ := shiftGeneratorHom n) (ψ := algebraMap LazardRing (DualNumber LazardRing))
    fun m hm ↦ by simp [shiftGeneratorHom_apply_generator, hm.ne]
  rw [← smul_eps_map_universalShiftSeries, shiftGeneratorHom_apply_generator] at hcomp
  simp only [ite_true, add_sub_cancel_left] at hcomp
  ext d
  by_cases hdeg : d.degree = (n : ℕ) + 1
  · have hd := congrArg (TrivSqZeroExt.snd ∘ coeff d) hcomp
    simp only [Function.comp_apply, coeff_homogeneousComponent, hdeg, ↓reduceIte,
      MvPolynomial.coe_smul, coeff_smul, coeff_map, MvPolynomial.coeff_coe,
      ← TauCeti.map_lazardCocycle (algebraMap LazardRing (DualNumber LazardRing)),
      MvPolynomial.coeff_map, smul_eq_mul, TrivSqZeroExt.snd_mul, DualNumber.fst_eps,
      DualNumber.snd_eps, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl] at hd
    simpa [coeff_homogeneousComponent, hdeg] using hd
  · have hdeg' : d 0 + d 1 ≠ (n : ℕ) + 1 := Finsupp.degree_finTwo d ▸ hdeg
    simp [coeff_homogeneousComponent, hdeg, TauCeti.coeff_lazardCocycle, hdeg']

private noncomputable def universalLubinTateCocycle (n : ℕ+) :
    MvPowerSeries (Fin 2) LazardRing :=
  PowerSeries.subst formalGroup.toPowerSeries formalGroup.invariantDifferential *
    universalShiftSeries n

private theorem deformationCocycle_universal_shiftGeneratorHom (n : ℕ+) :
    (formalGroup.map (algebraMap LazardRing (DualNumber LazardRing))).deformationCocycle
        (formalGroup.map (shiftGeneratorHom n)) =
      (DualNumber.eps : DualNumber LazardRing) •
        MvPowerSeries.map (algebraMap LazardRing (DualNumber LazardRing))
          (universalLubinTateCocycle n) := by
  rw [deformationCocycle, ← smul_eps_map_universalShiftSeries, universalLubinTateCocycle, map_mul,
    PowerSeries.map_subst (.of_constantCoeff_zero formalGroup.zero_constantCoeff),
    formalGroup.map_invariantDifferential, ← FormalGroup.map_toPowerSeries, mul_smul_comm]

private theorem isSymmetricCocycle_universalLubinTateCocycle (n : ℕ+) :
    formalGroup.IsSymmetricCocycle (universalLubinTateCocycle n) := by
  let inlR := algebraMap LazardRing (DualNumber LazardRing)
  have hcoc := (formalGroup.map inlR).isSymmetricCocycle_deformationCocycle
    (formalGroup.map (shiftGeneratorHom n))
    ((pow_two _).symm.trans (TrivSqZeroExt.kerIdeal_sq LazardRing LazardRing)) fun d ↦ by
      simp only [TrivSqZeroExt.kerIdeal, RingHom.mem_ker, TrivSqZeroExt.fstHom_apply]
      simp [inlR, FormalGroup.map_toPowerSeries, fst_shiftGeneratorHom,
        TrivSqZeroExt.algebraMap_eq_inl]
  rw [deformationCocycle_universal_shiftGeneratorHom] at hcoc
  exact hcoc.of_smul_map_injective fun r₁ r₂ heq ↦ by
    simpa [inlR, TrivSqZeroExt.algebraMap_eq_inl] using congrArg TrivSqZeroExt.snd heq

private theorem homogeneousComponent_universalLubinTateCocycle (n : ℕ+) :
    homogeneousComponent ((n : ℕ) + 1) (universalLubinTateCocycle n) =
      ↑(TauCeti.lazardCocycle ((n : ℕ) + 1) LazardRing) := by
  rw [universalLubinTateCocycle, ← _root_.zero_add ((n : ℕ) + 1),
    homogeneousComponent_mul_of_le_order zero_le (le_order_universalShiftSeries n)]
  simp [homogeneousComponent_zero,
    PowerSeries.constantCoeff_subst_of_constantCoeff_zero formalGroup.zero_constantCoeff,
    homogeneousComponent_universalShiftSeries]

/-- **Lubin–Tate, Lemma 1.3 (canonical symmetric 2-cocycle in degree `n + 1`).** For every
commutative formal group law `F` over a commutative ring `R` and every `n : ℕ+`,
`F.lubinTateCocycle n` is a symmetric 2-cocycle of `F` without constant term, vanishing below total
degree `n + 1`, with degree-`(n + 1)` homogeneous part equal to the Lazard cocycle `C_(n + 1)`. -/
noncomputable def lubinTateCocycle {R : Type*} [CommRing R] (F : FormalGroup R) [F.IsComm]
    (n : ℕ+) : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.map (LazardRing.lift ⟨F, inferInstance⟩) (universalLubinTateCocycle n)

/-- `FormalGroup.lubinTateCocycle` depends only on the formal group law, not on the proof of
commutativity. -/
theorem lubinTateCocycle_congr {R : Type*} [CommRing R] {F G : FormalGroup R}
    [F.IsComm] [G.IsComm] (h : F = G) (n : ℕ+) :
    F.lubinTateCocycle n = G.lubinTateCocycle n := by
  subst h; rfl

/-- `F.lubinTateCocycle n` is a symmetric 2-cocycle of `F`. -/
theorem isSymmetricCocycle_lubinTateCocycle {R : Type*} [CommRing R] (F : FormalGroup R)
    [F.IsComm] (n : ℕ+) : F.IsSymmetricCocycle (F.lubinTateCocycle n) := by
  simpa [lubinTateCocycle, LazardRing.map_lift] using
    (isSymmetricCocycle_universalLubinTateCocycle n).map (LazardRing.lift ⟨F, inferInstance⟩)

/-- `F.lubinTateCocycle n` vanishes below total degree `n + 1`. -/
theorem le_order_lubinTateCocycle {R : Type*} [CommRing R] (F : FormalGroup R) [F.IsComm]
    (n : ℕ+) : (((n : ℕ) + 1 : ℕ) : ℕ∞) ≤ (F.lubinTateCocycle n).order :=
  (le_order_mul_of_le_right (le_order_universalShiftSeries n)).trans (MvPowerSeries.le_order_map _)

/-- `F.lubinTateCocycle n` has zero constant coefficient. -/
@[simp]
theorem constantCoeff_lubinTateCocycle {R : Type*} [CommRing R] (F : FormalGroup R) [F.IsComm]
    (n : ℕ+) : constantCoeff (F.lubinTateCocycle n) = 0 :=
  one_le_order_iff_constCoeff_eq_zero.mp <|
    (by simp : (1 : ℕ∞) ≤ (((n : ℕ) + 1 : ℕ) : ℕ∞)).trans (F.le_order_lubinTateCocycle n)

/-- The degree-`(n + 1)` homogeneous component of `F.lubinTateCocycle n` is the Lazard cocycle
`C_(n + 1)`. -/
@[simp]
theorem homogeneousComponent_lubinTateCocycle {R : Type*} [CommRing R] (F : FormalGroup R)
    [F.IsComm] (n : ℕ+) :
    homogeneousComponent ((n : ℕ) + 1) (F.lubinTateCocycle n) =
      ↑(TauCeti.lazardCocycle ((n : ℕ) + 1) R) := by
  ext d; rw [coeff_homogeneousComponent, lubinTateCocycle, coeff_map, MvPolynomial.coeff_coe]
  have hd := congrArg (coeff d) (homogeneousComponent_universalLubinTateCocycle n)
  rw [coeff_homogeneousComponent, MvPolynomial.coeff_coe] at hd
  by_cases hdeg : d.degree = (n : ℕ) + 1
  · rw [ite_eq_left hdeg] at hd ⊢
    rw [hd, ← TauCeti.map_lazardCocycle (LazardRing.lift ⟨F, inferInstance⟩),
      MvPolynomial.coeff_map]
  · have : d 0 + d 1 ≠ (n : ℕ) + 1 := Finsupp.degree_finTwo d ▸ hdeg
    rw [ite_eq_right hdeg, TauCeti.coeff_lazardCocycle, ite_eq_right (by tauto)]

/-- `FormalGroup.lubinTateCocycle` commutes with base change of the coefficient ring. -/
@[simp]
theorem map_lubinTateCocycle {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (F : FormalGroup R) [F.IsComm] (n : ℕ+) :
    MvPowerSeries.map f (F.lubinTateCocycle n) = (F.map f).lubinTateCocycle n := by
  rw [lubinTateCocycle, lubinTateCocycle, ← RingHom.comp_apply, ← MvPowerSeries.map_comp,
    LazardRing.lift_map]

private theorem le_order_lubinTateCocycle_index {R : Type*} [CommRing R] (F : FormalGroup R)
    [F.IsComm] {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ((p ^ (j + 1) : ℕ) : ℕ∞) ≤ (F.lubinTateCocycle (lubinTateIndex hp.one_lt j)).order := by
  simpa [coe_lubinTateIndex_add_one] using F.le_order_lubinTateCocycle (lubinTateIndex hp.one_lt j)

private theorem homogeneousComponent_lubinTateCocycle_index {R : Type*} [CommRing R]
    (F : FormalGroup R) [F.IsComm] {p : ℕ} (hp : p.Prime) (j : ℕ) :
    homogeneousComponent (p ^ (j + 1)) (F.lubinTateCocycle (lubinTateIndex hp.one_lt j)) =
      ↑((1 : R) • TauCeti.lazardCocycle (p ^ (j + 1)) R) := by
  simpa [coe_lubinTateIndex_add_one] using
    F.homogeneousComponent_lubinTateCocycle (lubinTateIndex hp.one_lt j)

/-- **Linear independence of the canonical Lubin–Tate cocycles modulo coboundaries.** Let `p` be
a prime and let `[p]_F` have order at least `pʰ`. A linear combination
`∑ j : Fin (h - 1), c j • F.lubinTateCocycle (TauCeti.lubinTateIndex hp.one_lt j.val)` is a
coboundary `F.homDefect 𝔾ₐ g` if and only if `c = 0`. -/
theorem sum_smul_lubinTateCocycle_eq_homDefect_𝔾ₐ_iff
    {R : Type*} [CommRing R] {F : FormalGroup R} [F.IsComm] {p h : ℕ} (hp : p.Prime)
    (hF : ((p ^ h : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order) {c : Fin (h - 1) → R} :
    (∃ g : PowerSeries R,
      ∑ j : Fin (h - 1), c j • F.lubinTateCocycle (lubinTateIndex hp.one_lt j.val) =
        F.homDefect 𝔾ₐ g) ↔ c = 0 :=
  F.sum_smul_eq_homDefect_𝔾ₐ_iff hp hF (u := fun _ ↦ 1)
    (fun j ↦ F.le_order_lubinTateCocycle_index hp j.val)
    (fun j ↦ F.homogeneousComponent_lubinTateCocycle_index hp j.val)
    (fun _ ↦ isUnit_one)

/-- **Canonical Lubin–Tate decomposition of symmetric 2-cocycles.** Let `p` be a prime with `p = 0`
in `R`, and let `F` be a commutative formal group law over `R` whose `p`-series has order at least
`pʰ` and a unit coefficient of `X^(pʰ)`. Then every symmetric 2-cocycle `Φ` of `F` without constant
term decomposes as
`∑ j : Fin (h - 1), c j • F.lubinTateCocycle (TauCeti.lubinTateIndex hp.one_lt j.val) +`
`F.homDefect 𝔾ₐ g`
for a *unique* tuple `c : Fin (h - 1) → R` and some power series `g` without constant term. -/
theorem IsSymmetricCocycle.existsUnique_sum_smul_lubinTateCocycle_add_homDefect_𝔾ₐ
    {R : Type*} [CommRing R] {F : FormalGroup R} [F.IsComm] {p h : ℕ} (hp : p.Prime)
    (hpR : (p : R) = 0) (hF : ((p ^ h : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order)
    (hv : IsUnit (PowerSeries.coeff (p ^ h) (F.nsmulSeries p)))
    {Φ : MvPowerSeries (Fin 2) R} (hΦ : F.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0) :
    ∃! c : Fin (h - 1) → R, ∃ g : PowerSeries R, PowerSeries.constantCoeff g = 0 ∧
      Φ = ∑ j : Fin (h - 1), c j • F.lubinTateCocycle (lubinTateIndex hp.one_lt j.val) +
        F.homDefect 𝔾ₐ g :=
  hΦ.existsUnique_sum_smul_add_homDefect_𝔾ₐ hp hpR hF hv (u := fun _ ↦ 1)
    (fun j ↦ F.isSymmetricCocycle_lubinTateCocycle (lubinTateIndex hp.one_lt j.val))
    (fun j ↦ F.le_order_lubinTateCocycle_index hp j.val)
    (fun j ↦ F.homogeneousComponent_lubinTateCocycle_index hp j.val)
    (fun _ ↦ isUnit_one) hΦ₀

end LubinTateCocycle

end FormalGroup
