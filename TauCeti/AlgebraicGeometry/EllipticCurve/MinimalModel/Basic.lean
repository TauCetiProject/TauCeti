/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.AlgebraicGeometry.EllipticCurve.NodePolynomial

/-!
# Minimal models: a criterion, their comparison, and what transfers between them

Mathlib defines `WeierstrassCurve.IsMinimal` by a maximality property — the valuation of the
discriminant is maximal among all integral models isomorphic to the given one — and derives
minimality only from that property or from a class that already extends it. Establishing it for a
*given* equation therefore means quantifying over every change of variables, which is not something
a caller can discharge by hand.

This file supplies the cheapest sufficient conditions — an integral Weierstrass equation whose `c₄`
or whose discriminant is a **unit** at the place is already minimal — and then the comparison any
two minimal models admit: they have the same discriminant valuation, so a change of variables
between them has a scaling factor of valuation `1`, and they have the same `c₄` valuation too.

## Main results

* `WeierstrassCurve.isMinimal_of_valuation_c₄_eq_one`: over the fraction field of a discrete
  valuation ring, an integral Weierstrass equation with `v (c₄) = 1` is minimal.
* `WeierstrassCurve.isMinimal_of_valuation_Δ_eq_one`: so is one with `v (Δ) = 1`.
* `WeierstrassCurve.exists_smul_eq_minimal`: Mathlib's chosen minimal equation is obtained by a
  change of variables.
* `WeierstrassCurve.exists_smul_minimal_eq_minimal`: chosen minimal equations of isomorphic
  equations are related by a change of variables.
* `WeierstrassCurve.valuation_Δ_le_of_isMinimal_smul`: no integral model in the orbit of a minimal
  model has larger `v (Δ)`.
* `WeierstrassCurve.valuation_Δ_eq_of_isMinimal_smul`: two minimal models related by a change of
  variables have equal `v (Δ)`.
* `WeierstrassCurve.isMinimal_of_valuation_Δ_eq_of_isMinimal_smul`: conversely, an integral model
  attaining that valuation is minimal.
* `WeierstrassCurve.isMinimal_baseChange_smul`: a change of variables defined over `R` carries a
  minimal model to a minimal model.
* `WeierstrassCurve.valuation_u_eq_one_of_isMinimal_smul`: for an elliptic curve, the scaling
  factor of such a change of variables satisfies `v (u) = 1`.
* `WeierstrassCurve.valuation_c₄_eq_of_isMinimal_smul`: hence the two minimal models have equal
  `v (c₄)`.
* `WeierstrassCurve.VariableChange.exists_unit_algebraMap_eq_u_of_isMinimal_smul`: the scaling
  factor is the image of a unit of the discrete valuation ring.
* `VariableChange.exists_baseChange_eq_and_smul_integralModel_eq_of_isMinimal_smul`: so the
  change of variables is defined over `R` and relates the two integral models.
* `WeierstrassCurve.exists_smul_reduction_eq_of_isMinimal_smul`: the reductions of two minimal
  models are related by a change of variables over the residue field.
* `WeierstrassCurve.valuation_Δ_minimal_smul` and
  `WeierstrassCurve.valuation_c₄_minimal_smul`: the chosen minimal equations of isomorphic curves
  have the same discriminant and `c₄` valuations.
* `WeierstrassCurve.hasGoodReduction_minimal_smul_iff` and
  `WeierstrassCurve.HasGoodReduction.hasGoodReduction_minimal`: good reduction of the chosen
  minimal equation is a property of the curve, and holds whenever some equation has good
  reduction.
* `WeierstrassCurve.hasGoodReduction_iff_isUnit_integralModel_Δ`: an integral equation has good
  reduction exactly when its integral discriminant is a unit, and then it is elliptic
  (`WeierstrassCurve.HasGoodReduction.isElliptic`).
* `WeierstrassCurve.HasGoodReduction.baseChange` and `WeierstrassCurve.reduction_baseChange`:
  good reduction is preserved by base change along a map of discrete valuation rings, and the
  reduction of the base change is the base change of the reduction.
* `WeierstrassCurve.HasSplitMultiplicativeReduction.of_isMinimal_smul`: split multiplicative
  reduction transfers along such a change of variables.

`valuation_u_eq_one_of_isMinimal_smul` and
`VariableChange.exists_unit_algebraMap_eq_u_of_isMinimal_smul` supply the unit needed for descent.
Turning that into a change of variables actually *defined* over `R` is the job of
`WeierstrassCurve.VariableChange.exists_baseChange_eq_of_smul_eq`, which also consumes integrality
of both models. A change of variables defined over `R` is one the reduction can see, and that is
what carries split multiplicativity across.

## Why this is the useful form

The hypothesis is stated through the adic valuation of `W.c₄ : K`, matching how Mathlib phrases
`WeierstrassCurve.HasMultiplicativeReduction`, whose `multiplicativeReduction` field is exactly
`valuation K (maximalIdeal R) W.c₄ = 1`. That class *extends* `IsMinimal`, so the implication is
not needed to go from multiplicative reduction to minimality — it is needed in the other
direction, to **construct** `HasMultiplicativeReduction` for an equation one has only computed
`c₄` and `Δ` for. That is the shape a quadratic twist arrives in: twisting by a discriminant that
is a unit scales `c₄` by a unit square, so the twist's `c₄` valuation is again `1`, and this
criterion is what turns that computation into minimality of the twisted model.

## Mathematical content

It is the unit-`c₄` case of the Kraus–Laska criterion — the special case "`v (c₄) < 4` or
`v (Δ) < 12` implies minimal" of Silverman, *The Arithmetic of Elliptic Curves*,
Remark VII.1.1, restricted to `v (c₄) = 0`. The proof is direct: a change of variables scales
`c₄` by `u⁻⁴` and `Δ` by `u⁻¹²`, and integrality of the transformed model bounds `v (u⁻⁴)` by
`1`, hence `v (u⁻¹²) ≤ 1`, so no change of variables can raise the discriminant's valuation.
The unit-`Δ` case, `isMinimal_of_valuation_Δ_eq_one`, is immediate, since every integral model
has `v (Δ) ≤ 1`.

## Provenance

⚠ *mathlib-track*: this is a statement about Mathlib's own `IsMinimal`, with no Tau Ceti
definitions involved, and belongs upstream once its consumers are in place.

Ported from FLT, https://github.com/ImperialCollegeLondon/FLT
@ `bc2fe8ff7396469a16c2a6d51d6117f5825d93a0` (Apache-2.0), file
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`, by Kevin Buzzard — the source commit
is FLT PR #1088, "Quadratic twist to split multiplicative reduction". Five declarations are taken
from it:

* `isMinimal_of_valuation_c₄_eq_one`;
* `valuation_Δ_aux_smul_le`, here `valuation_Δ_le_of_isMinimal_smul`;
* `valuation_Δ_eq_of_isMinimal_smul`;
* `valuation_u_eq_one_of_isMinimal_smul`;
* `HasSplitMultiplicativeReduction.of_isMinimal_smul`.

The source declaration `HasSplitMultiplicativeReduction.of_isMinimal_smul` no longer exists at
FLT's current head (`9deae05a`), which drops that development entirely; the pinned revision above
is the record of it. It is absent from Mathlib too, whose `IsMinimal` API stops at the pairwise
exclusion of the reduction types and never compares two minimal models.

`valuation_Δ_le_of_isMinimal_smul` compares the discriminant valuations of two models related by
a change of variables. `of_isMinimal_smul` drops the source's `[IsMinimal R W₁]`, which its `h₁`
already implies, since `HasSplitMultiplicativeReduction` extends `HasMultiplicativeReduction`
extends `IsMinimal`. The other statements are unchanged. The converse
`isMinimal_of_valuation_Δ_eq_of_isMinimal_smul` is not in the source.
-/

public section

namespace WeierstrassCurve

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **An integral Weierstrass equation whose `c₄` is a unit at the place is minimal.** No change of
variables can increase the valuation of the discriminant: it scales `Δ` by `u⁻¹²` while scaling
`c₄` by `u⁻⁴`, and integrality of the transformed equation forces `v (u⁻⁴) ≤ 1`.

This is the unit-`c₄` case of the Kraus–Laska criterion (Silverman, *AEC*, Remark VII.1.1). The
hypothesis is phrased through the adic valuation of `W.c₄ : K` to match
`WeierstrassCurve.HasMultiplicativeReduction`, so that a curve for which only `c₄` has been
computed can be given its `IsMinimal` field. -/
theorem isMinimal_of_valuation_c₄_eq_one (W : WeierstrassCurve K) [IsIntegral R W]
    (hc₄ : valuation K (maximalIdeal R) W.c₄ = 1) : IsMinimal R W := by
  refine ⟨⟨by simpa using ‹IsIntegral R W›, ?_⟩⟩
  intro C hC _
  simp only [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral R (C • W),
    valuation_Δ_aux_eq_of_isIntegral R W]
  have hint : valuation K (maximalIdeal R) (C • W).c₄ ≤ 1 := by
    simpa [← integralModel_c₄_eq R (C • W)] using valuation_le_one _ _
  rw [variableChange_c₄, map_mul, map_pow, hc₄, mul_one] at hint
  simpa [variableChange_Δ, map_mul, map_pow] using mul_le_of_le_one_left'
    (pow_le_one' ((pow_le_one_iff (by norm_num)).mp hint) 12)

/-- **An integral Weierstrass equation whose discriminant is a unit at the place is minimal.** The
discriminant of every integral model has valuation at most `1`, which a unit discriminant already
attains. This is the `v (Δ) = 0` case of Silverman, *AEC*, Remark VII.1.1. -/
theorem isMinimal_of_valuation_Δ_eq_one (W : WeierstrassCurve K) [IsIntegral R W]
    (hΔ : valuation K (maximalIdeal R) W.Δ = 1) : IsMinimal R W := by
  refine ⟨⟨by simpa using ‹IsIntegral R W›, ?_⟩⟩
  intro C hC _
  simp only [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral R (C • W),
    valuation_Δ_aux_eq_of_isIntegral R W, hΔ]
  simpa [← integralModel_Δ_eq R (C • W)] using valuation_le_one _ _

/-- **Mathlib's chosen minimal equation lies in the variable-change orbit.** The equation
`W.minimal R` is obtained from `W` by a change of variables. -/
theorem exists_smul_eq_minimal (W : WeierstrassCurve K) :
    ∃ C : VariableChange K, C • W = W.minimal R :=
  ⟨_, rfl⟩

/-- The chosen minimal equations of two equations related by a change of variables are themselves
related by a change of variables. -/
theorem exists_smul_minimal_eq_minimal (D : VariableChange K) (W : WeierstrassCurve K) :
    ∃ C : VariableChange K, C • W.minimal R = (D • W).minimal R := by
  obtain ⟨C₁, hC₁⟩ := W.exists_smul_eq_minimal R
  obtain ⟨C₂, hC₂⟩ := (D • W).exists_smul_eq_minimal R
  refine ⟨C₂ * D * C₁⁻¹, ?_⟩
  rw [mul_smul, mul_smul, ← hC₁, inv_smul_smul, hC₂]

/-! ### Comparing two minimal models

`IsMinimal` says the discriminant valuation is maximal among integral models. Two minimal models of
the same curve therefore pin each other: each is at least as good as the other, so their
valuations agree, and the change of variables between them can only scale `Δ` by a unit. -/

/-- **A minimal model maximises the discriminant valuation in its orbit**: every integral model
obtained from it by a change of variables has discriminant of at most that valuation. This is the
`valuation`-level reading of Mathlib's `IsMinimal`, whose `MaximalFor` phrasing speaks of
`valuation_Δ_aux` and of the orbit of a fixed equation. -/
theorem valuation_Δ_le_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [hm : IsMinimal R W₁]
    [IsIntegral R W₂] (D : VariableChange K) (hD : D • W₁ = W₂) :
    valuation K (maximalIdeal R) W₂.Δ ≤ valuation K (maximalIdeal R) W₁.Δ := by
  have hint : IsIntegral R (D • W₁) := by rw [hD]; infer_instance
  have h : valuation_Δ_aux R (D • W₁) ≤ valuation_Δ_aux R ((1 : VariableChange K) • W₁) :=
    (le_total (valuation_Δ_aux R ((1 : VariableChange K) • W₁)) (valuation_Δ_aux R (D • W₁))).elim
      (hm.val_Δ_maximal.2 hint) id
  rw [hD, one_smul] at h
  rw [← valuation_Δ_aux_eq_of_isIntegral R W₂, ← valuation_Δ_aux_eq_of_isIntegral R W₁,
    Subtype.coe_le_coe]
  exact h

/-- **Two minimal models related by a change of variables have the same discriminant valuation.**
So `v (Δ)` is an invariant of the curve at this place rather than of the chosen model: any two
minimal models of the same curve agree on it, and a consumer may read it off whichever model it
holds. -/
theorem valuation_Δ_eq_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₁]
    [IsMinimal R W₂] (D : VariableChange K) (hD : D • W₁ = W₂) :
    valuation K (maximalIdeal R) W₂.Δ = valuation K (maximalIdeal R) W₁.Δ :=
  -- Antisymmetry: `D` carries `W₁` to `W₂` and `D⁻¹` carries `W₂` back, and by minimality neither
  -- direction can increase the valuation.
  le_antisymm (valuation_Δ_le_of_isMinimal_smul R D hD)
    (valuation_Δ_le_of_isMinimal_smul R D⁻¹ (by rw [← hD, inv_smul_smul]))

/-- **An integral model whose discriminant valuation matches that of a minimal model in its orbit
is itself minimal.** Together with `valuation_Δ_le_of_isMinimal_smul` this makes the discriminant
valuation a complete test for minimality among integral models of one curve. -/
theorem isMinimal_of_valuation_Δ_eq_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K}
    [IsMinimal R W₁] [IsIntegral R W₂] (D : VariableChange K) (hD : D • W₁ = W₂)
    (h : valuation K (maximalIdeal R) W₂.Δ = valuation K (maximalIdeal R) W₁.Δ) :
    IsMinimal R W₂ := by
  refine ⟨⟨by simpa using ‹IsIntegral R W₂›, fun {C} hC _ => ?_⟩⟩
  dsimp only at hC ⊢
  have hint : IsIntegral R (C • W₂) := hC
  have hCD : (C * D) • W₁ = C • W₂ := by rw [mul_smul, hD]
  rw [← Subtype.coe_le_coe, one_smul, valuation_Δ_aux_eq_of_isIntegral R (C • W₂),
    valuation_Δ_aux_eq_of_isIntegral R W₂, h]
  exact valuation_Δ_le_of_isMinimal_smul R (C * D) hCD

/-- **A change of variables defined over `R` preserves minimality**: if `W` is minimal over `R`
and `C` is a change of variables with coefficients in `R`, then `C • W` is minimal over `R`. With
`valuation_u_eq_one_of_isMinimal_smul` and
`VariableChange.exists_baseChange_eq_of_smul_eq` in the other direction, the changes of variables
between minimal models of an elliptic curve are exactly those defined over `R`. -/
theorem isMinimal_baseChange_smul (W : WeierstrassCurve K) [IsMinimal R W]
    (C : VariableChange R) : IsMinimal R (C.baseChange K • W) := by
  have hW : (C • W.integralModel R).baseChange K = C.baseChange K • W := by
    rw [baseChange, ← map_variableChange, ← baseChange, baseChange_integralModel_eq R W]
    rfl
  have : IsIntegral R (C.baseChange K • W) := ⟨⟨C • W.integralModel R, hW.symm⟩⟩
  refine isMinimal_of_valuation_Δ_eq_of_isMinimal_smul R (C.baseChange K) rfl ?_
  have hu : valuation K (maximalIdeal R) (algebraMap R K ↑C.u) = 1 := by
    rw [valuation_of_algebraMap, intValuation_eq_one_iff_mem_primeCompl]
    exact (IsLocalRing.notMem_maximalIdeal).2 (Units.isUnit _)
  rw [variableChange_Δ, map_mul, map_pow]
  simp [VariableChange.baseChange, hu]

/-- **The scaling factor of a change of variables between two minimal models of an elliptic curve
has valuation `1`.** Over a discrete valuation ring that says `u` is a **unit**: it and its inverse
are both integral, so such a change of variables is as integral as its coordinates allow. This is
the hypothesis `VariableChange.exists_baseChange_eq_of_smul_eq` asks for, and hence the step by
which a property of the reduction transfers between two minimal models of one curve. -/
theorem valuation_u_eq_one_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₁]
    [IsMinimal R W₂] [W₁.IsElliptic] (D : VariableChange K) (hD : D • W₁ = W₂) :
    valuation K (maximalIdeal R) ↑D.u = 1 := by
  -- A change of variables scales `Δ` by `u⁻¹²`. The two discriminant valuations agree and are
  -- nonzero, so `v (u)¹² = 1`, and the value group is torsion-free.
  have hΔ0 : valuation K (maximalIdeal R) W₁.Δ ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr W₁.isUnit_Δ.ne_zero
  have h12 : valuation K (maximalIdeal R) ↑D.u ^ 12 = 1 := by
    have key : valuation K (maximalIdeal R) W₁.Δ
        = (valuation K (maximalIdeal R) ↑D.u)⁻¹ ^ 12 * valuation K (maximalIdeal R) W₁.Δ := by
      conv_lhs => rw [← valuation_Δ_eq_of_isMinimal_smul R D hD, ← hD, variableChange_Δ]
      rw [map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀]
    have h1 : (valuation K (maximalIdeal R) ↑D.u)⁻¹ ^ 12 = 1 :=
      mul_right_cancel₀ hΔ0 (key.symm.trans (one_mul _).symm)
    rw [inv_pow] at h1
    exact inv_eq_one.mp h1
  exact (pow_eq_one_iff_of_nonneg zero_le (by norm_num)).mp h12

/-- **Two minimal models of an elliptic curve related by a change of variables have the same `c₄`
valuation**, since the change of variables scales `c₄` by `u⁻⁴` with `v (u) = 1`. -/
theorem valuation_c₄_eq_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₁]
    [IsMinimal R W₂] [W₁.IsElliptic] (D : VariableChange K) (hD : D • W₁ = W₂) :
    valuation K (maximalIdeal R) W₂.c₄ = valuation K (maximalIdeal R) W₁.c₄ := by
  rw [← hD, variableChange_c₄, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀,
    valuation_u_eq_one_of_isMinimal_smul R D hD]
  simp

namespace VariableChange

/-- The scaling factor between two minimal elliptic equations is the image of a unit of the
discrete valuation ring. -/
theorem exists_unit_algebraMap_eq_u_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K}
    [IsMinimal R W₁] [IsMinimal R W₂] [W₁.IsElliptic] (D : VariableChange K)
    (hD : D • W₁ = W₂) : ∃ u₀ : Rˣ, algebraMap R K u₀ = D.u := by
  obtain ⟨u₀, hau⟩ := associated_of_valuation_eq (A := R) 1 (↑D.u : K)
    (by rw [map_one]; exact (valuation_u_eq_one_of_isMinimal_smul R D hD).symm)
  rw [Units.smul_def, Algebra.smul_def, mul_one] at hau
  exact ⟨u₀, hau⟩

/-- **A change of variables between two minimal elliptic equations is defined over `R`, and it
carries one integral model to the other.** Its scaling factor is the image of a unit, so it
descends to a change of variables `C` over `R`, and since `R → K` is injective `C` relates the
integral models themselves. A property of integral models that is invariant under changes of
variables over `R`, such as one read off the reduction, is therefore shared by all minimal models
of an elliptic curve (Silverman, *AEC*, Proposition VII.1.3(b)). -/
theorem exists_baseChange_eq_and_smul_integralModel_eq_of_isMinimal_smul
    {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₁] [IsMinimal R W₂] [W₁.IsElliptic]
    (D : VariableChange K) (hD : D • W₁ = W₂) :
    ∃ C : VariableChange R, C.baseChange K = D ∧ C • W₁.integralModel R = W₂.integralModel R := by
  obtain ⟨u₀, hau⟩ := exists_unit_algebraMap_eq_u_of_isMinimal_smul R D hD
  obtain ⟨C, hC⟩ := exists_baseChange_eq_of_smul_eq R D hD u₀ hau
  refine ⟨C, hC, (integralModel_eq_of_baseChange_eq ?_).symm⟩
  rw [WeierstrassCurve.baseChange, ← map_variableChange]
  exact (congrArg₂ (· • ·) hC (baseChange_integralModel_eq R W₁)).trans hD

end VariableChange

/-- **The reductions of two minimal models of an elliptic curve are related by a change of
variables over the residue field**, namely the reduction of the integral change of variables
between their integral models. So every property of the reduction that is invariant under changes
of variables, such as being elliptic, ordinary or supersingular, depends only on the curve. -/
theorem exists_smul_reduction_eq_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K}
    [IsMinimal R W₁] [IsMinimal R W₂] [W₁.IsElliptic] (D : VariableChange K) (hD : D • W₁ = W₂) :
    ∃ C : VariableChange (IsLocalRing.ResidueField R), C • W₁.reduction R = W₂.reduction R := by
  obtain ⟨C, -, hC⟩ :=
    VariableChange.exists_baseChange_eq_and_smul_integralModel_eq_of_isMinimal_smul R D hD
  exact ⟨C.map (IsLocalRing.residue R), by rw [reduction, reduction, ← hC, map_variableChange]⟩

/-- The discriminants of the chosen minimal equations have the same valuation after a change of
variables. -/
@[simp]
theorem valuation_Δ_minimal_smul (D : VariableChange K) (W : WeierstrassCurve K) :
    valuation K (maximalIdeal R) ((D • W).minimal R).Δ =
      valuation K (maximalIdeal R) (W.minimal R).Δ := by
  obtain ⟨C, hC⟩ := exists_smul_minimal_eq_minimal R D W
  exact valuation_Δ_eq_of_isMinimal_smul R C hC

/-- The `c₄` invariants of the chosen minimal equations have the same valuation after a change of
variables. -/
@[simp]
theorem valuation_c₄_minimal_smul (D : VariableChange K) (W : WeierstrassCurve K)
    [W.IsElliptic] :
    valuation K (maximalIdeal R) ((D • W).minimal R).c₄ =
      valuation K (maximalIdeal R) (W.minimal R).c₄ := by
  obtain ⟨C₀, hC₀⟩ := W.exists_smul_eq_minimal R
  have : (W.minimal R).IsElliptic := hC₀ ▸ inferInstance
  obtain ⟨C, hC⟩ := exists_smul_minimal_eq_minimal R D W
  exact valuation_c₄_eq_of_isMinimal_smul R C hC

/-- The chosen minimal equation has good reduction exactly when its discriminant is a unit at the
place. -/
theorem hasGoodReduction_minimal_iff (W : WeierstrassCurve K) :
    (W.minimal R).HasGoodReduction R ↔ valuation K (maximalIdeal R) (W.minimal R).Δ = 1 :=
  ⟨fun h ↦ h.goodReduction, fun h ↦ ⟨h⟩⟩

/-- **Good reduction is a property of the curve**: the chosen minimal equations of two equations
related by a change of variables have good reduction together. -/
@[simp]
theorem hasGoodReduction_minimal_smul_iff (D : VariableChange K) (W : WeierstrassCurve K) :
    ((D • W).minimal R).HasGoodReduction R ↔ (W.minimal R).HasGoodReduction R := by
  rw [hasGoodReduction_minimal_iff, hasGoodReduction_minimal_iff, valuation_Δ_minimal_smul]

/-- An equation with good reduction has a chosen minimal equation with good reduction. -/
theorem HasGoodReduction.hasGoodReduction_minimal {W : WeierstrassCurve K}
    (h : W.HasGoodReduction R) : (W.minimal R).HasGoodReduction R := by
  have := h.toIsMinimal
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal R
  rw [hasGoodReduction_minimal_iff, valuation_Δ_eq_of_isMinimal_smul R C hC]
  exact h.goodReduction

/-- **An integral equation has good reduction exactly when the discriminant of its integral model
is a unit.** Such an equation is automatically minimal, so no minimality hypothesis appears. -/
theorem hasGoodReduction_iff_isUnit_integralModel_Δ (W : WeierstrassCurve K) [IsIntegral R W] :
    W.HasGoodReduction R ↔ IsUnit (W.integralModel R).Δ := by
  have hval : valuation K (maximalIdeal R) W.Δ = 1 ↔ IsUnit (W.integralModel R).Δ := by
    rw [← integralModel_Δ_eq R W]
    exact (maximalIdeal R).valuation_eq_one_iff_notMem.trans IsLocalRing.notMem_maximalIdeal
  rw [← hval]
  exact ⟨fun h ↦ h.goodReduction,
    fun h ↦ { toIsMinimal := isMinimal_of_valuation_Δ_eq_one R W h, goodReduction := h }⟩

/-- **An equation with good reduction is elliptic**: its discriminant has valuation `1`, so it is
nonzero. -/
theorem HasGoodReduction.isElliptic {W : WeierstrassCurve K} (h : W.HasGoodReduction R) :
    W.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr fun h0 ↦ by simpa [h0] using h.goodReduction⟩

section BaseChange

variable (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R S]

/-- **Good reduction is preserved by base change.** Let `S` be a discrete valuation ring with
fraction field `L`, receiving `R` compatibly with `K → L`. If an equation has good reduction over
`R`, then its base change to `L` has good reduction over `S`: the unit discriminant of its integral
model stays a unit. No ramification hypothesis is needed, and the base-changed equation is again
minimal (Silverman, *AEC*, VII.5.4(b)). -/
theorem HasGoodReduction.baseChange
    (hRS : (algebraMap S L).comp (algebraMap R S) = (algebraMap K L).comp (algebraMap R K))
    {W : WeierstrassCurve K} (h : W.HasGoodReduction R) : (W.baseChange L).HasGoodReduction S := by
  have := h.toIsMinimal
  have := IsIntegral.baseChange hRS W
  rw [hasGoodReduction_iff_isUnit_integralModel_Δ, integralModel_baseChange hRS, map_Δ]
  exact ((hasGoodReduction_iff_isUnit_integralModel_Δ R W).mp h).map _

/-- **Reduction commutes with base change.** If `R → S` is a local homomorphism of discrete
valuation rings compatible with `K → L`, and an equation is minimal over `R` with base change
minimal over `S`, then its reduction over `S` is the base change of its reduction over `R` along
the extension of residue fields. -/
theorem reduction_baseChange [IsLocalHom (algebraMap R S)]
    (hRS : (algebraMap S L).comp (algebraMap R S) = (algebraMap K L).comp (algebraMap R K))
    (W : WeierstrassCurve K) [IsMinimal R W] [IsMinimal S (W.baseChange L)] :
    (W.baseChange L).reduction S = (W.reduction R).baseChange (IsLocalRing.ResidueField S) := by
  rw [reduction, reduction, integralModel_baseChange hRS, baseChange, map_map, map_map]
  exact congrArg _ (RingHom.ext fun x ↦ (IsLocalRing.ResidueField.algebraMap_residue x).symm)

end BaseChange

/-- **Split multiplicative reduction is an isomorphism invariant of minimal models.** If two
minimal Weierstrass models of an elliptic curve over `K` are related by a change of variables
(`D • W₁ = W₂`), and `W₁` has split multiplicative reduction, then so does `W₂`.

This is what makes split multiplicative reduction a property of the curve at the place rather than
of the equation presenting it. Mathlib's class is stated through a *chosen* integral model, so the
transfer is not definitional: it needs `D` to be defined over `R`. Two results combine to give
that — `valuation_u_eq_one_of_isMinimal_smul` supplies the unit scaling factor, and
`VariableChange.exists_baseChange_eq_of_smul_eq` turns that unit, with integrality of both models,
into the descent. A form of Silverman, *The Arithmetic of Elliptic Curves*, Remark VII.1.3(b), on
the uniqueness of minimal models over a discrete valuation ring. -/
theorem HasSplitMultiplicativeReduction.of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K}
    [IsMinimal R W₂] [W₁.IsElliptic] (D : VariableChange K) (hD : D • W₁ = W₂)
    (h₁ : W₁.HasSplitMultiplicativeReduction R) : W₂.HasSplitMultiplicativeReduction R := by
  -- `W₁` is minimal because it has multiplicative reduction, so that is not a hypothesis.
  have hm₁ := h₁.toHasMultiplicativeReduction
  have : IsMinimal R W₁ := hm₁.toIsMinimal
  -- `W₂` is again multiplicative, since `v (u) = 1` fixes the valuations of both `Δ` and `c₄`.
  have hmult₂ : W₂.HasMultiplicativeReduction R :=
    { badReduction := by rw [valuation_Δ_eq_of_isMinimal_smul R D hD]; exact hm₁.badReduction
      multiplicativeReduction := by
        rw [valuation_c₄_eq_of_isMinimal_smul R D hD]; exact hm₁.multiplicativeReduction }
  -- `D` descends to some `C₀` over `R` carrying the integral model of `W₁` to that of `W₂`, so
  -- their node polynomials split together.
  refine { hmult₂ with splitMultiplicativeReduction := ?_ }
  obtain ⟨C₀, -, hint₂⟩ :=
    VariableChange.exists_baseChange_eq_and_smul_integralModel_eq_of_isMinimal_smul R D hD
  rw [← hint₂, ← nodePolynomial_def]
  exact (splits_variableChange_nodePolynomial_map_iff
    (algebraMap R (IsLocalRing.ResidueField R)) (W₁.integralModel R) C₀).mpr
      (by rw [nodePolynomial_def]; exact h₁.splitMultiplicativeReduction)

end WeierstrassCurve

end
