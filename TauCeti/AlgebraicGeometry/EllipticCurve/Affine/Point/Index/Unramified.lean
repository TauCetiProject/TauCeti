/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Bound
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Unramified
-- Proof-only: Bézout coefficients for coprime multiples.
import TauCeti.Algebra.Group.Coprime
-- Proof-only: `𝒪[L]` is Henselian.
import TauCeti.NumberTheory.LocalField.Henselian

/-!
# The index of `E₀` over an unramified extension

Let `L/K` be an unramified extension of nonarchimedean local fields, and let `W` be an elliptic
curve over `K` given by a minimal equation. The valuation of the minimal discriminant bounds the
index of the subgroup `E₀` of points with nonsingular reduction: it is `v(Δ_min)` at split
multiplicative reduction and at most `4` otherwise (Kodaira, Néron;
`WeierstrassCurve.Affine.index_nonsingularReduction_le_four`). Since the base change of `W` to `L`
stays minimal with the same `v(Δ_min)`
(`WeierstrassCurve.localMinimalDiscriminantValuation_baseChange_of_isUnramified`), this gives a
bound on `[E(L) : E₀(L)]` that is independent of the unramified extension `L`, so torsion of
`E(L)` of prime order beyond that bound has nonsingular reduction, whatever the degree of `L`.
Over unramified extensions of growing degree this is what puts prescribed torsion points into
`E₀(L)`.

## Main results

* `WeierstrassCurve.Affine.index_nonsingularReduction_baseChange_le_of_isUnramified`: the index
  `[E(L) : E₀(L)]` is at most `max 4 v(Δ_min)`, with `v(Δ_min)` computed over `K`.
* `WeierstrassCurve.Affine.Point.mem_nonsingularReduction_baseChange_of_isUnramified`: points of
  `W(L)` of prime order `ℓ > max 4 v(Δ_min)` have nonsingular reduction.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.4 and VII.6.1.
-/

public section

open ValuativeRel IsLocalRing TauCeti

namespace WeierstrassCurve

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [IsUnramified K L]
  (W : WeierstrassCurve K) [W.IsElliptic] [IsMinimal 𝒪[K] W]

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
  obtain ⟨i, j, hij⟩ := exists_zsmul_add_zsmul_eq_of_coprime (G := (W⁄L).toAffine.Point) hcop
  rw [← hij P, hP, smul_zero, zero_add]
  exact H.zsmul_mem hcP _

end WeierstrassCurve
