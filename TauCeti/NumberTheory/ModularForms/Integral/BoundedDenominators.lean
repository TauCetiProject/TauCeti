/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
public import TauCeti.NumberTheory.ModularForms.SturmBound
public import Mathlib.FieldTheory.AlgebraicClosure

import TauCeti.LinearAlgebra.Span.IntegralDescent
import TauCeti.NumberTheory.ModularForms.Degeneracy
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion
import TauCeti.NumberTheory.ModularForms.Newforms.NumberField
import TauCeti.RingTheory.PowerSeries.SubringCoeff
import Mathlib.RingTheory.Algebraic.Denominator

/-!
# Bounded denominators for cusp forms with algebraic `q`-expansion

A cusp form on `Γ₁(N)` whose `q`-expansion coefficients at `∞` are algebraic numbers has
*bounded denominators*: a single positive integer `D` makes every `D aₙ(f)` an algebraic integer
(`CuspForm.exists_integral_multiple_qExpansion_coeff`). If the coefficients are rational, every
`D aₙ(f)` is then an integer (`CuspForm.exists_nsmul_qExpansion_coeff_eq_intCast`). This holds in
every weight, including weight one.

For an arbitrary power series, algebraic coefficients do not bound the denominators; for cusp
forms the bound comes from a spanning set with algebraic-integer coefficients. The engine is
`ModularForm.exists_integral_multiple_qExpansion_coeff_of_mem_span`: on any finite-index subgroup,
a modular form with algebraic coefficients in the `ℂ`-span of forms with algebraic-integer
coefficients is an algebraic combination of finitely many of them, so clearing the denominators
of these finitely many scalars clears those of all its coefficients. The first coefficients up to
the Sturm bound determine a modular form, and a vector of algebraic numbers in the `ℂ`-span of
algebraic vectors is in their span over the algebraic numbers
(`TauCeti.mem_span_of_mem_span_of_forall_apply_mem_range`).

In weight `k ≥ 2` the forms `g(dτ)`, with `g` a newform of level `M` and `d M ∣ N`, span
`S_k(Γ₁(N))` and have algebraic-integer coefficients. Weight one has no such spanning set to
start with; there multiplication by the discriminant `Δ = q + ⋯`, which has integer coefficients,
embeds `S_k(Γ₁(N))` into `S_{k+12}(Γ₁(N))`, and dividing by `Δ` keeps one denominator bound.

These are the denominator bounds of Deligne–Serre's lattice of weight-one forms: a
`ℚ`-structure on `S₁(Γ₁(N))` given by forms with rational coefficients spans a lattice of forms
with integral coefficients once its finitely many basis forms are cleared of denominators.

## Main results

* `ModularForm.exists_integral_multiple_qExpansion_coeff_of_mem_span`: a modular form with algebraic
  coefficients in the span of forms with algebraic-integer coefficients has bounded denominators.
* `CuspForm.exists_integral_multiple_qExpansion_coeff`: a cusp form on `Γ₁(N)` of any weight
  with algebraic coefficients has bounded denominators.
* `CuspForm.exists_nsmul_qExpansion_coeff_eq_intCast`: a cusp form on `Γ₁(N)` with rational
  coefficients has a nonzero integer multiple with integer coefficients.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530, Proposition 2.7 and Remarque 2.8.
-/

public section

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane TauCeti
open scoped MatrixGroups

namespace ModularForm

section Span

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.HasDetOne] [𝒢.IsFiniteRelIndex 𝒮ℒ]
  [DiscreteTopology 𝒢.strictPeriods] {k : ℤ}

/-- **Bounded denominators from an integral spanning set.** On a subgroup of finite index in
`SL₂(ℤ)`, let `f` be a modular form in the `ℂ`-span of forms whose `q`-expansion coefficients are
algebraic integers. If the coefficients of `f` are algebraic numbers, then one positive integer
`D` makes all the coefficients `D aₙ(f)` algebraic integers. -/
theorem exists_integral_multiple_qExpansion_coeff_of_mem_span (f : ModularForm 𝒢 k)
    {S : Set (ModularForm 𝒢 k)}
    (hS : ∀ g ∈ S, ∀ n, IsIntegral ℤ ((qExpansion 𝒢.strictWidthInfty g).coeff n))
    (hfS : f ∈ Submodule.span ℂ S)
    (hf : ∀ n, IsAlgebraic ℚ ((qExpansion 𝒢.strictWidthInfty f).coeff n)) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ n, IsIntegral ℤ (D • (qExpansion 𝒢.strictWidthInfty f).coeff n) := by
  set h := 𝒢.strictWidthInfty
  let A := algebraicClosure ℚ ℂ
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  -- the `q`-expansion coefficients, and those up to the Sturm bound, as linear maps
  let Q (n : ℕ) : ModularForm 𝒢 k →ₗ[ℂ] ℂ := (PowerSeries.coeff n).comp
    (TauCeti.ModularForm.qExpansionLinearMap
      TauCeti.Subgroup.strictWidthInfty_pos_of_finiteRelIndex
      𝒢.strictWidthInfty_mem_strictPeriods k)
  have hQ (n : ℕ) (F : ModularForm 𝒢 k) : Q n F = (qExpansion h F).coeff n := by
    simp [Q, h]
  let T : ModularForm 𝒢 k →ₗ[ℂ] Fin (ModularForm.sturmLength 𝒢 k) → ℂ :=
    sturmCoeffsₗ k
  -- the truncated expansion of `f` is an algebraic combination of those of the spanning forms
  have hA {x : ℂ} (hx : IsAlgebraic ℚ x) : x ∈ (algebraMap A ℂ).range :=
    ⟨⟨x, mem_algebraicClosure_iff.mpr hx⟩, rfl⟩
  have hTf : T f ∈ Submodule.span A (T '' S) := by
    refine mem_span_of_mem_span_of_forall_apply_mem_range ?_
      (fun i ↦ sturmCoeffsₗ_apply f i ▸ hA (hf i))
      (Submodule.apply_mem_span_image_of_mem_span T hfS)
    rintro _ ⟨g, hg, rfl⟩ i
    exact sturmCoeffsₗ_apply g i ▸ hA (hS g hg i).tower_top.isAlgebraic
  -- along the combination, denominators are cleared by the product of finitely many
  -- denominators of algebraic numbers
  have key : ∀ v ∈ Submodule.span A (T '' S), ∃ F : ModularForm 𝒢 k, T F = v ∧
      ∃ D : ℕ, D ≠ 0 ∧ ∀ n, IsIntegral ℤ (D • (qExpansion h F).coeff n) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g, hg, rfl⟩ := hv
      exact ⟨g, rfl, 1, one_ne_zero, by simpa using hS g hg⟩
    | zero =>
      refine ⟨0, map_zero T, 1, one_ne_zero, fun n ↦ ?_⟩
      rw [← hQ, map_zero, smul_zero]
      exact isIntegral_zero
    | add v w _ _ hv hw =>
      obtain ⟨F, rfl, D, hD, hF⟩ := hv
      obtain ⟨G, rfl, D', hD', hG⟩ := hw
      refine ⟨F + G, map_add T F G, D * D', mul_ne_zero hD hD', fun n ↦ ?_⟩
      rw [← hQ, map_add, hQ, hQ, smul_add]
      refine IsIntegral.add ?_ ?_
      · rw [mul_comm, mul_smul]
        exact (hF n).nsmul D'
      · rw [mul_smul]
        exact (hG n).nsmul D
    | smul c v _ hv =>
      obtain ⟨F, rfl, D, hD, hF⟩ := hv
      have hc : IsAlgebraic ℤ (algebraMap A ℂ c) :=
        (mem_algebraicClosure_iff.mp c.2).restrictScalars ℤ
      refine ⟨algebraMap A ℂ c • F, by rw [map_smul, algebraMap_smul],
        Algebra.natDenominator (algebraMap A ℂ c) * D, mul_ne_zero hc.natDenominator_ne_zero hD,
        fun n ↦ ?_⟩
      rw [← hQ, map_smul, hQ, smul_eq_mul, ← smul_mul_smul_comm]
      exact (Algebra.isIntegral_natDenominator_smul _).mul (hF n)
  obtain ⟨F, hF, D, hD, hint⟩ := key _ hTf
  exact ⟨D, hD, sturmCoeffsₗ_injective hF ▸ hint⟩

end Span

end ModularForm

namespace CuspForm

section Gamma1

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- In weight `k ≥ 2`, the level-raised newforms span `S_k(Γ₁(N))` and have algebraic-integer
coefficients, so a cusp form with algebraic coefficients has bounded denominators. -/
private theorem exists_integral_multiple_qExpansion_coeff_of_two_le (hk : 2 ≤ k)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : ∀ n, IsAlgebraic ℚ ((qExpansion 1 f).coeff n)) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ n, IsIntegral ℤ (D • (qExpansion 1 f).coeff n) := by
  have hw : ((Gamma1 N).map (mapGL ℝ)).strictWidthInfty = 1 := strictWidthInfty_Gamma1 N
  have hcoe (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : ⇑(toModularFormₗ g) = g :=
    funext (toModularFormₗ_apply g)
  rw [← hw] at hf ⊢
  refine ModularForm.exists_integral_multiple_qExpansion_coeff_of_mem_span (toModularFormₗ f) ?_
    (Submodule.apply_mem_span_image_of_mem_span toModularFormₗ
      ((HeckeRing.GL2.Newform.span_levelRaise_eq_top N k).symm ▸ Submodule.mem_top)) hf
  rintro _ ⟨_, ⟨M, d, _, _, h, g, rfl⟩, rfl⟩ n
  rw [hcoe, hw, CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map M)]
  split_ifs
  · exact g.isIntegral_qExpansion_coeff hk _
  · exact isIntegral_zero

/-- **Bounded denominators on `Γ₁(N)`.** If every `q`-expansion coefficient of a cusp form `f`
on `Γ₁(N)` is an algebraic number, then one positive integer `D` makes all the coefficients
`D aₙ(f)` algebraic integers. This holds in every weight `k`, including weight one. -/
theorem exists_integral_multiple_qExpansion_coeff (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : ∀ n, IsAlgebraic ℚ ((qExpansion 1 f).coeff n)) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ n, IsIntegral ℤ (D • (qExpansion 1 f).coeff n) := by
  -- multiply by `Δ` until the weight is at least `2`
  suffices H : ∀ m : ℕ, ∀ k : ℤ, 2 ≤ k + 12 * m → ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ n, IsAlgebraic ℚ ((qExpansion 1 f).coeff n)) →
        ∃ D : ℕ, D ≠ 0 ∧ ∀ n, IsIntegral ℤ (D • (qExpansion 1 f).coeff n) from
    H (2 - k).toNat k (by omega) f hf
  intro m
  induction m with
  | zero => exact fun k hk ↦ exists_integral_multiple_qExpansion_coeff_of_two_le (by simpa using hk)
  | succ m ih =>
    intro k hk f hf
    let Δ : ModularForm ((Gamma1 N).map (mapGL ℝ)) 12 :=
      ModularForm.restrict (Subgroup.map_le_range _ _) (toModularFormₗ CuspForm.discriminant)
    have hΔ : qExpansion 1 (f.mulModularForm Δ) =
        qExpansion 1 f * qExpansion 1 ModularForm.discriminant := by
      have hcoe : ⇑Δ = ModularForm.discriminant := by
        ext τ
        simp [Δ, ModularForm.coe_restrict, coe_discriminant]
      rw [coe_mulModularForm, ModularForm.qExpansion_mul_coe one_pos
        (one_mem_strictPeriods_Gamma1_map N) f Δ, hcoe]
    have hΔℤ (i : ℕ) : ∃ z : ℤ, (qExpansion 1 ModularForm.discriminant).coeff i = z :=
      TauCeti.ModularForm.exists_discriminant_qExpansion_coeff_eq_intCast i
    obtain ⟨D, hD, hint⟩ := ih (k + 12) (by push_cast at hk; omega) (f.mulModularForm Δ)
      fun n ↦ by
        rw [← mem_algebraicClosure_iff, hΔ, PowerSeries.coeff_mul]
        refine sum_mem fun i _ ↦ mul_mem (mem_algebraicClosure_iff.mpr (hf i.1)) ?_
        obtain ⟨z, hz⟩ := hΔℤ i.2
        exact hz ▸ intCast_mem _ z
    -- dividing by `Δ = q + ⋯` keeps the coefficients of `D f` integral
    refine ⟨D, hD, fun n ↦ ?_⟩
    have hR (i : ℕ) :
        (qExpansion 1 ModularForm.discriminant).coeff i ∈ (integralClosure ℤ ℂ).toSubring := by
      obtain ⟨z, hz⟩ := hΔℤ i
      exact hz ▸ intCast_mem _ z
    have := PowerSeries.coeff_mem_of_coeff_mul_mem (F := D • qExpansion 1 f) (m := 1)
      (fun i hi ↦ by
        simpa [Nat.lt_one_iff.mp hi] using TauCeti.ModularForm.discriminant_qExpansion_coeff_zero)
      ModularForm.discriminant_qExpansion_coeff_one hR
      (fun n ↦ by rw [smul_mul_assoc, ← hΔ, map_nsmul]; exact hint n) n
    rwa [map_nsmul] at this

/-- **Rational coefficients have bounded denominators.** If every `q`-expansion coefficient of a
cusp form `f` on `Γ₁(N)` is rational, then one positive integer `D` makes all the coefficients
`D aₙ(f)` integers. This holds in every weight `k`, including weight one. -/
theorem exists_nsmul_qExpansion_coeff_eq_intCast (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : ∀ n, ∃ r : ℚ, (qExpansion 1 f).coeff n = r) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ n, ∃ z : ℤ, D • (qExpansion 1 f).coeff n = z := by
  obtain ⟨D, hD, hint⟩ := exists_integral_multiple_qExpansion_coeff f fun n ↦ by
    obtain ⟨r, hr⟩ := hf n
    exact hr ▸ isAlgebraic_algebraMap r
  refine ⟨D, hD, fun n ↦ ?_⟩
  obtain ⟨r, hr⟩ := hf n
  -- a rational number that is an algebraic integer is an integer
  have hDr : IsIntegral ℤ (D • r) := by
    refine (isIntegral_algHom_iff ((Algebra.ofId ℚ ℂ).restrictScalars ℤ)
      (algebraMap ℚ ℂ).injective).mp ?_
    simpa [hr] using hint n
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hDr
  refine ⟨z, ?_⟩
  rw [hr]
  simpa [nsmul_eq_mul] using congrArg (fun x : ℚ ↦ (x : ℂ)) hz.symm

end Gamma1

end CuspForm
