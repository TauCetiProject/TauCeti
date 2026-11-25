/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.MultiplicativeDomain
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
public import TauCeti.Analysis.InnerProductSpace.Compression

/-!
# The multiplicative domain of a compression

For a linear isometry `V : H →ₗᵢ[ℂ] K` between complex Hilbert spaces, the compression
`φ(T) = V† T V` from `B(K)` to `B(H)` is a unital completely positive map
(`ContinuousLinearMap.conjAdjoint`); it is the compression `T ↦ PTP` onto the corner `PB(K)P`
for the projection `P = V V†`, read on `B(H) ≅ PB(K)P`. Its multiplicative domain consists of the
operators commuting with `P` (`mem_multiplicativeDomain_conjAdjoint_iff`). The Schwarz defect is
`φ(T†T) - φ(T)†φ(T) = ((1 - P) T V)† ((1 - P) T V)`, so the Schwarz equality at `T` says exactly
that `(1 - P) T P = 0`. Using one Schwarz equality only would give this set of operators leaving the
range of `P` invariant, which is not closed under adjoints in general.
-/

public section

open ContinuousLinearMap

namespace TauCeti.CompressionMultiplicativeDomainExample

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (V : H →ₗᵢ[ℂ] K)

/-- The adjoint of the isometry `V` cancels it on the left of a composite: `V† ∘L (V ∘L X) = X`. -/
private theorem adjoint_comp_comp_cancel {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] (X : G →L[ℂ] H) :
    V.toContinuousLinearMap.adjoint ∘L (V.toContinuousLinearMap ∘L X) = X := by
  rw [← comp_assoc, V.adjoint_comp_self, one_def, id_comp]

/-- The Schwarz defect of the compression by an isometry `V` at `T` is
`((1 - P) T V)† ((1 - P) T V)` for the projection `P = V V†`. -/
private theorem schwarz_defect (T : K →L[ℂ] K) :
    (T.adjoint ∘L T).compression V.toContinuousLinearMap -
        (T.compression V.toContinuousLinearMap).adjoint ∘L T.compression V.toContinuousLinearMap =
      ((1 - V.toContinuousLinearMap ∘L V.toContinuousLinearMap.adjoint) ∘L T ∘L
          V.toContinuousLinearMap).adjoint ∘L
        ((1 - V.toContinuousLinearMap ∘L V.toContinuousLinearMap.adjoint) ∘L T ∘L
          V.toContinuousLinearMap) := by
  simp only [compression_def, comp_assoc, sub_comp, comp_sub, one_def, id_comp, adjoint_comp,
    adjoint_adjoint, map_sub, adjoint_comp_comp_cancel V]
  abel

/-- For an isometry `V`, the Schwarz equality `φ(T†T) = φ(T)†φ(T)` of the compression holds
exactly when `(1 - P) T P = 0` for `P = V V†`. -/
theorem conjAdjoint_star_mul_self_eq_iff (T : K →L[ℂ] K) :
    V.toContinuousLinearMap.conjAdjoint (star T * T) =
        star (V.toContinuousLinearMap.conjAdjoint T) * V.toContinuousLinearMap.conjAdjoint T ↔
      (1 - V.toContinuousLinearMap ∘L V.toContinuousLinearMap.adjoint) ∘L T ∘L
        (V.toContinuousLinearMap ∘L V.toContinuousLinearMap.adjoint) = 0 := by
  simp only [conjAdjoint_apply, ← compression_def, star_eq_adjoint, mul_def]
  rw [← sub_eq_zero, schwarz_defect V, ← norm_eq_zero, norm_adjoint_comp_self,
    mul_self_eq_zero, norm_eq_zero]
  constructor
  · intro h
    simp only [← comp_assoc] at h ⊢
    rw [h, zero_comp]
  · intro h
    have := congrArg (· ∘L V.toContinuousLinearMap) h
    simpa only [comp_assoc, LinearIsometry.adjoint_comp_self, one_def, comp_id, zero_comp]
      using this

/-- **The multiplicative domain of a compression.** For an isometry `V`, an operator `T` lies in
the multiplicative domain of the compression `T ↦ V† T V` exactly when it commutes with the
projection `P = V V†`. -/
theorem mem_multiplicativeDomain_conjAdjoint_iff (T : K →L[ℂ] K) :
    T ∈ ((V.toContinuousLinearMap.conjAdjoint).isNPositive 2).multiplicativeDomain
        (by rw [CompletelyPositiveMap.coe_toLinearMap, conjAdjoint_apply, ← compression_def,
          compression_one]) ↔
      T ∘L (V.toContinuousLinearMap ∘L V.toContinuousLinearMap.adjoint) =
        (V.toContinuousLinearMap ∘L V.toContinuousLinearMap.adjoint) ∘L T := by
  have h2 : V.toContinuousLinearMap.conjAdjoint (T * star T) =
        V.toContinuousLinearMap.conjAdjoint T * star (V.toContinuousLinearMap.conjAdjoint T) ↔
      (1 - V.toContinuousLinearMap ∘L V.toContinuousLinearMap.adjoint) ∘L star T ∘L
        (V.toContinuousLinearMap ∘L V.toContinuousLinearMap.adjoint) = 0 := by
    rw [← conjAdjoint_star_mul_self_eq_iff V (star T), star_star,
      CompletelyPositiveMap.map_star, star_star]
  rw [IsNPositive.mem_multiplicativeDomain, CompletelyPositiveMap.coe_toLinearMap,
    conjAdjoint_star_mul_self_eq_iff V, h2]
  simp only [star_eq_adjoint, comp_assoc, sub_comp, one_def, id_comp, sub_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩
    have h2' := congrArg adjoint h2
    simp only [adjoint_comp, adjoint_adjoint, comp_assoc] at h2'
    rw [h1, h2']
  · intro h
    refine ⟨?_, ?_⟩
    · rw [h, adjoint_comp_comp_cancel V]
    · have ha := congrArg adjoint h
      simp only [adjoint_comp, adjoint_adjoint, comp_assoc] at ha
      rw [← ha, adjoint_comp_comp_cancel V]

end TauCeti.CompressionMultiplicativeDomainExample
