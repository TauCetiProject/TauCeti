/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel.ValuativeExtension
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Valuation
public import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass
public import TauCeti.NumberTheory.LocalField.Unramified.Basic
-- Proof-only: an equation on which Tate's algorithm stops is minimal.
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Invariance
-- Proof-only: base change commutes with changes of variables.
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic
-- Proof-only: the additive valuation of `𝒪[K]` scales by the ramification index in `𝒪[L]`.
import TauCeti.NumberTheory.LocalField.RamificationIndex

/-!
# Minimal equations over an unramified extension

Let `L/K` be an unramified extension of nonarchimedean local fields, and let `W` be an elliptic
curve over `K` given by a minimal equation. This file proves that the base change of `W` to `L`
is again minimal, and that its reduction type, its reduction and the valuation of its minimal
discriminant do not change (Silverman, *The Arithmetic of Elliptic Curves*, VII.5.4(a)).
The base change is minimal because Tate's algorithm stops at the same symbol over `𝒪[L]` as over
`𝒪[K]`. Once both equations are minimal:

* the reduction over `L` is the base change of the reduction over `K`, by
  `WeierstrassCurve.reduction_baseChange`, which applies through the instance
  `WeierstrassCurve.isMinimal_baseChange_of_isUnramified`;
* good and multiplicative reduction, which do not change under any base change of an integral
  equation (`WeierstrassCurve.hasGoodReduction_baseChange_iff`,
  `WeierstrassCurve.hasMultiplicativeReduction_baseChange_iff`), leave additive reduction as the
  only remaining type on both sides;
* the discriminant of the integral model has the same additive valuation in `𝒪[L]` as in `𝒪[K]`,
  the ramification index being `1`.

Over a ramified extension the base change of a minimal equation need not be minimal, and additive
reduction can become good or multiplicative.

Since the valuation of the minimal discriminant bounds the index of the subgroup `E₀` of points
with nonsingular reduction, this gives a bound on `[E(L) : E₀(L)]` independent of the unramified
extension `L`; that bound is proved in
`TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Unramified`.

## Main results

* `WeierstrassCurve.isMinimal_baseChange_of_isUnramified`: a minimal equation stays minimal over
  an unramified extension.
* `WeierstrassCurve.hasAdditiveReduction_baseChange_iff_of_isUnramified`: additive reduction does
  not change.
* `WeierstrassCurve.localMinimalDiscriminantValuation_baseChange_of_isUnramified`: the valuation
  of the minimal discriminant does not change.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.4.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open ValuativeRel IsLocalRing TauCeti

namespace WeierstrassCurve

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

variable [IsUnramified K L] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **A minimal equation stays minimal over an unramified extension** (Silverman AEC VII.5.4(a)).
If `L/K` is an unramified extension of nonarchimedean local fields and `W` is an elliptic curve
given by an equation minimal over `𝒪[K]`, then its base change to `L` is minimal over `𝒪[L]`. -/
instance isMinimal_baseChange_of_isUnramified [IsMinimal 𝒪[K] W] : IsMinimal 𝒪[L] (W⁄L) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set Wo := integralModel 𝒪[K] W
  have : IsMinimal 𝒪[K] (Wo.baseChange K) := by
    rw [baseChange_integralModel_eq]
    infer_instance
  have hΔ : Wo.Δ ≠ 0 := fun h ↦ W.isUnit_Δ.ne_zero <| by
    rw [← integralModel_Δ_eq 𝒪[K] W, h, map_zero]
  -- Tate's algorithm stops on `C • Wo` at some symbol `s`, for a change of variables `C`. Its
  -- stopping tests are divisibilities by powers of `ϖ`, which `𝒪[K] → 𝒪[L]` reflects, and `ϖ` is
  -- still a uniformiser of `L` since `L/K` is unramified. So the algorithm stops at `s` on the
  -- image of `C • Wo` over `𝒪[L]`, and an equation on which it stops is minimal.
  obtain ⟨C, s, hs⟩ := exists_isTateTerminal (K := K) hϖ Wo hΔ
  set f := algebraMap 𝒪[K] 𝒪[L]
  -- `𝒪[K] → 𝒪[L]` reflects divisibility
  have hf (n : ℕ) (x : 𝒪[K]) : f ϖ ^ n ∣ f x ↔ ϖ ^ n ∣ x := by
    rw [← map_pow]
    exact algebraMap_integerRing_dvd_iff
  -- so the algorithm stops at `s` on the image of `C • Wo` over `𝒪[L]`, which is minimal
  have hsL : ((C • Wo).map f).IsTateTerminal (f ϖ) s := (isTateTerminal_map_iff f hf).2 hs
  have := hsL.isMinimal_baseChange (K := L) (IsUnramified.irreducible_algebraMap hϖ)
  -- and its base change to `L` is that of `W` transformed by a change of variables over `𝒪[L]`
  have hWL : ((C • Wo).map f).baseChange L = (C.map f).baseChange L • W⁄L := by
    rw [← map_variableChange, ← baseChange_smul_baseChange,
      baseChange_map_integralModel algebraMap_comp_algebraMap_integerRing]
  rw [hWL] at this
  have h := isMinimal_baseChange_smul 𝒪[L] ((C.map f).baseChange L • W⁄L) (C.map f)⁻¹
  have e : (C.map f)⁻¹.baseChange L = ((C.map f).baseChange L)⁻¹ :=
    map_inv (VariableChange.mapHom (algebraMap 𝒪[L] L)) (C.map f)
  rwa [e, inv_smul_smul] at h

variable [IsMinimal 𝒪[K] W]

/-- **Additive reduction does not change under an unramified base change** (Silverman AEC
VII.5.4(a)): a minimal equation over `𝒪[K]` has additive reduction exactly when its base change to
an unramified extension `L` has additive reduction over `𝒪[L]`. Good and multiplicative reduction
do not change under any base change (`WeierstrassCurve.hasGoodReduction_baseChange_iff`,
`WeierstrassCurve.hasMultiplicativeReduction_baseChange_iff`); over a ramified extension the base
change of an equation with additive reduction need not be minimal. -/
@[simp]
theorem hasAdditiveReduction_baseChange_iff_of_isUnramified :
    (W⁄L).HasAdditiveReduction 𝒪[L] ↔ W.HasAdditiveReduction 𝒪[K] := by
  have hg := hasGoodReduction_baseChange_iff 𝒪[K] 𝒪[L] algebraMap_comp_algebraMap_integerRing W
  have hm :=
    hasMultiplicativeReduction_baseChange_iff 𝒪[K] 𝒪[L] algebraMap_comp_algebraMap_integerRing W
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction (R := 𝒪[K])
      (W := W) with h' | h' | h'
    · exact absurd (hg.2 h') h.not_hasGoodReduction
    · exact absurd (hm.2 h') h.not_hasMultiplicativeReduction
    · exact h'
  · rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction (R := 𝒪[L])
      (W := W⁄L) with h' | h' | h'
    · exact absurd (hg.1 h') h.not_hasGoodReduction
    · exact absurd (hm.1 h') h.not_hasMultiplicativeReduction
    · exact h'

omit [IsMinimal 𝒪[K] W] in
/-- **The valuation of the minimal discriminant does not change under an unramified base change**:
`v_L(Δ_min(E/L)) = v_K(Δ_min(E/K))`. -/
@[simp]
theorem localMinimalDiscriminantValuation_baseChange_of_isUnramified :
    (W⁄L).localMinimalDiscriminantValuation 𝒪[L] = W.localMinimalDiscriminantValuation 𝒪[K] := by
  -- compute both sides on the chosen minimal equation `M = C • W` over `K` and its base change
  set M := W.minimal 𝒪[K]
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal 𝒪[K]
  have := IsIntegral.baseChange (algebraMap_comp_algebraMap_integerRing (K := K) (L := L)) M
  have hCL : C.baseChange L • W⁄L = M⁄L := by
    rw [baseChange_smul_baseChange, hC]
  have h := (W⁄L).localMinimalDiscriminantValuation_eq_addVal_of_isMinimal_smul 𝒪[L] _ hCL
  rw [integralModel_baseChange algebraMap_comp_algebraMap_integerRing, map_Δ, addVal_algebraMap,
    IsUnramified.ramificationIndex_eq_one, one_smul,
    ← W.localMinimalDiscriminantValuation_eq_addVal_of_isMinimal_smul 𝒪[K] C hC] at h
  exact_mod_cast h

end WeierstrassCurve
