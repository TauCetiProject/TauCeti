/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Bound
public import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel.ValuativeExtension
public import TauCeti.NumberTheory.LocalField.Unramified.Basic
-- Proof-only: an equation on which Tate's algorithm stops is minimal.
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Invariance
-- Proof-only: the additive valuation of `𝒪[K]` scales by the ramification index in `𝒪[L]`.
import TauCeti.NumberTheory.LocalField.RamificationIndex
-- Proof-only: `𝒪[L]` is Henselian.
import TauCeti.NumberTheory.LocalField.Henselian

/-!
# Minimal equations over an unramified extension

Let `L/K` be an unramified extension of nonarchimedean local fields, and let `W` be an elliptic
curve over `K` given by a minimal equation. This file proves that the base change of `W` to `L`
is again minimal, and that its reduction type, its reduction and the valuation of its minimal
discriminant do not change (Silverman, *The Arithmetic of Elliptic Curves*, VII.5.4(a)).

Minimality is the substantial step. Tate's algorithm, run on the integral model of `W` with a
uniformiser `ϖ` of `K`, stops after a change of variables over `𝒪[K]` at some symbol `s`. Its
stopping tests are divisibilities by powers of `ϖ`, which the inclusion `𝒪[K] → 𝒪[L]` reflects
(`TauCeti.algebraMap_integerRing_dvd_iff`), and `ϖ` is still a uniformiser of `L` since `L/K` is
unramified. So the algorithm stops at `s` on the image of that equation over `𝒪[L]`
(`WeierstrassCurve.isTateTerminal_map_iff`), and an equation on which it stops is minimal
(`WeierstrassCurve.IsTateTerminal.isMinimal_baseChange`). Once both equations are minimal:

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

The valuation of the minimal discriminant bounds the index of the subgroup `E₀` of points with
nonsingular reduction: it is `v(Δ_min)` at split multiplicative reduction and at most `4`
otherwise (Kodaira, Néron; `WeierstrassCurve.Affine.index_nonsingularReduction_le_four`). Read
over `L`, this gives a bound on `[E(L) : E₀(L)]` that is independent of the unramified extension
`L`, so torsion of `E(L)` of prime order beyond that bound has nonsingular reduction, whatever the
degree of `L`. Over unramified extensions of growing degree this is what puts prescribed torsion
points into `E₀(L)`.

## Main results

* `WeierstrassCurve.isMinimal_baseChange_of_isUnramified`: a minimal equation stays minimal over
  an unramified extension.
* `WeierstrassCurve.hasAdditiveReduction_baseChange_iff_of_isUnramified`: additive reduction does
  not change.
* `WeierstrassCurve.localMinimalDiscriminantValuation_baseChange_of_isUnramified`: the valuation
  of the minimal discriminant does not change.
* `WeierstrassCurve.Affine.index_nonsingularReduction_baseChange_le_of_isUnramified`: the index
  `[E(L) : E₀(L)]` is at most `max 4 v(Δ_min)`, with `v(Δ_min)` computed over `K`.
* `WeierstrassCurve.Affine.Point.mem_nonsingularReduction_baseChange_of_isUnramified`: points of
  `W(L)` of prime order `ℓ > max 4 v(Δ_min)` have nonsingular reduction.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.4 and VII.6.1.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open ValuativeRel IsLocalRing TauCeti

namespace WeierstrassCurve

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] in
/-- The square from `𝒪[K]` to `L` through `𝒪[L]` and through `K` commutes. -/
private theorem algebraMap_comp_algebraMap_integerRing :
    (algebraMap 𝒪[L] L).comp (algebraMap 𝒪[K] 𝒪[L]) =
      (algebraMap K L).comp (algebraMap 𝒪[K] K) := by
  rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

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
  -- Tate's algorithm stops on `C • Wo` at some symbol `s`, for a change of variables `C`
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

/-- Over an unramified extension, `E₀(L)` has positive index at most `max 4 v(Δ_min)`. -/
private theorem index_nonsingularReduction_baseChange_pos_and_le [DecidableEq L] :
    0 < ((W⁄L).toAffine.nonsingularReduction (valuation L)).index ∧
      ((W⁄L).toAffine.nonsingularReduction (valuation L)).index ≤
        max 4 (W.localMinimalDiscriminantValuation 𝒪[K]) := by
  -- the results over a Henselian discrete valuation ring are stated for the valuation subring
  have : IsMinimal (valuation L).valuationSubring (W⁄L) :=
    inferInstanceAs (IsMinimal 𝒪[L] (W⁄L))
  have : IsDiscreteValuationRing (valuation L).valuationSubring :=
    inferInstanceAs (IsDiscreteValuationRing 𝒪[L])
  have : HenselianLocalRing (valuation L).valuationSubring :=
    inferInstanceAs (HenselianLocalRing 𝒪[L])
  have : PerfectField (ResidueField (valuation L).valuationSubring) :=
    inferInstanceAs (PerfectField 𝓀[L])
  refine ⟨Nat.pos_of_ne_zero (AddSubgroup.FiniteIndex.index_ne_zero), ?_⟩
  by_cases h : (W⁄L).HasSplitMultiplicativeReduction (valuation L).valuationSubring
  · rw [Affine.index_nonsingularReduction_eq_localMinimalDiscriminantValuation (valuation L) (W⁄L)]
    exact (localMinimalDiscriminantValuation_baseChange_of_isUnramified W).le.trans
      (le_max_right _ _)
  · exact (Affine.index_nonsingularReduction_le_four (valuation L) (W⁄L) h).trans
      (le_max_left _ _)

/-- **The index of `E₀` is bounded uniformly over unramified extensions** (Kodaira, Néron;
Silverman AEC VII.6.1). Let `W` be an elliptic curve over `K` given by a minimal equation, and let
`L/K` be unramified. Then the subgroup `E₀(L)` of points of `W(L)` with nonsingular reduction has
index at most `max 4 v(Δ_min)`, where `v(Δ_min)` is the valuation of the minimal discriminant of
`W` over `K`: the index is `v(Δ_min)` where the reduction over `L` is split multiplicative and at
most `4` otherwise. -/
theorem Affine.index_nonsingularReduction_baseChange_le_of_isUnramified [DecidableEq L] :
    ((W⁄L).toAffine.nonsingularReduction (valuation L)).index ≤
      max 4 (W.localMinimalDiscriminantValuation 𝒪[K]) :=
  (index_nonsingularReduction_baseChange_pos_and_le W).2

/-- **Torsion of large prime order has nonsingular reduction over unramified extensions.** Let `W`
be an elliptic curve over `K` given by a minimal equation, let `L/K` be unramified, and let `ℓ` be
a prime larger than `4` and than the valuation of the minimal discriminant of `W` over `K`. Then
every point of `W(L)` killed by `ℓ` lies in the subgroup `E₀(L)` of points with nonsingular
reduction, since `ℓ` is prime to the index of `E₀(L)`. -/
theorem Affine.Point.mem_nonsingularReduction_baseChange_of_isUnramified [DecidableEq L] {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hlt : max 4 (W.localMinimalDiscriminantValuation 𝒪[K]) < ℓ)
    {P : (W⁄L).toAffine.Point} (hP : ℓ • P = 0) :
    P ∈ (W⁄L).toAffine.nonsingularReduction (valuation L) := by
  set H := (W⁄L).toAffine.nonsingularReduction (valuation L)
  obtain ⟨hc₀, hc⟩ := index_nonsingularReduction_baseChange_pos_and_le (L := L) W
  -- `ℓ` and the index `c` are coprime, and both `ℓ • P = 0` and `c • P` lie in `H`
  have hcop := Nat.coprime_of_lt_prime hc₀.ne' (hc.trans_lt hlt) hℓ
  have hcP : H.index • P ∈ H := AddSubgroup.nsmul_index_mem H P
  have key : P = Nat.gcdA ℓ H.index • ℓ • P + Nat.gcdB ℓ H.index • H.index • P := by
    rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, mul_comm _ (ℓ : ℤ),
      mul_comm _ (H.index : ℤ), ← Nat.gcd_eq_gcd_ab, hcop, Nat.cast_one, one_smul]
  rw [key, hP, smul_zero, zero_add]
  exact H.zsmul_mem hcP _

end WeierstrassCurve
