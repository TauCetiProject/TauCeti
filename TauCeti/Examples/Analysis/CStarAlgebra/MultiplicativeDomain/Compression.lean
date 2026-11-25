/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.MultiplicativeDomain
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order

/-!
# The multiplicative domain of a compression

For an isometry `V : H →L[ℂ] K` between complex Hilbert spaces, the compression
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
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {V : H →L[ℂ] K}

/-- The Schwarz defect of the compression by an isometry `V` at `T` is
`((1 - P) T V)† ((1 - P) T V)` for the projection `P = V V†`. -/
private theorem schwarz_defect (hV : V.adjoint ∘L V = 1) (T : K →L[ℂ] K) :
    V.adjoint ∘L (T.adjoint ∘L T) ∘L V - (V.adjoint ∘L T ∘L V).adjoint ∘L (V.adjoint ∘L T ∘L V) =
      ((1 - V ∘L V.adjoint) ∘L T ∘L V).adjoint ∘L ((1 - V ∘L V.adjoint) ∘L T ∘L V) := by
  have hX (X : H →L[ℂ] H) : V.adjoint ∘L (V ∘L X) = X := by
    rw [← comp_assoc, hV, one_def, id_comp]
  simp only [comp_assoc, sub_comp, comp_sub, one_def, id_comp, adjoint_comp, adjoint_adjoint,
    map_sub, hX]
  abel

/-- For an isometry `V`, the Schwarz equality `φ(T†T) = φ(T)†φ(T)` of the compression holds
exactly when `(1 - P) T P = 0` for `P = V V†`. -/
theorem conjAdjoint_star_mul_self_eq_iff (hV : V.adjoint ∘L V = 1) (T : K →L[ℂ] K) :
    V.conjAdjoint (star T * T) = star (V.conjAdjoint T) * V.conjAdjoint T ↔
      (1 - V ∘L V.adjoint) ∘L T ∘L (V ∘L V.adjoint) = 0 := by
  simp only [conjAdjoint_apply, star_eq_adjoint, mul_def]
  rw [← sub_eq_zero, schwarz_defect hV, ← norm_eq_zero, norm_adjoint_comp_self,
    mul_self_eq_zero, norm_eq_zero]
  constructor
  · intro h
    rw [show (1 - V ∘L V.adjoint) ∘L T ∘L V ∘L V.adjoint =
      ((1 - V ∘L V.adjoint) ∘L T ∘L V) ∘L V.adjoint by simp only [comp_assoc], h, zero_comp]
  · intro h
    have := congrArg (· ∘L V) h
    simpa only [comp_assoc, hV, one_def, comp_id, zero_comp] using this

/-- **The multiplicative domain of a compression.** For an isometry `V`, an operator `T` lies in
the multiplicative domain of the compression `T ↦ V† T V` exactly when it commutes with the
projection `P = V V†`. -/
theorem mem_multiplicativeDomain_conjAdjoint_iff (hV : V.adjoint ∘L V = 1) (T : K →L[ℂ] K) :
    T ∈ ((V.conjAdjoint).isNPositive 2).multiplicativeDomain (V.conjAdjoint_one hV) ↔
      T ∘L (V ∘L V.adjoint) = (V ∘L V.adjoint) ∘L T := by
  have hs : ∀ S, V.conjAdjoint (star S) = star (V.conjAdjoint S) :=
    ((V.conjAdjoint).isNPositive 2).map_star two_pos
  have h2 : V.conjAdjoint (T * star T) = V.conjAdjoint T * star (V.conjAdjoint T) ↔
      (1 - V ∘L V.adjoint) ∘L star T ∘L (V ∘L V.adjoint) = 0 := by
    rw [← conjAdjoint_star_mul_self_eq_iff hV (star T), star_star, hs, star_star]
  rw [IsNPositive.mem_multiplicativeDomain, CompletelyPositiveMap.coe_toLinearMap,
    conjAdjoint_star_mul_self_eq_iff hV, h2]
  simp only [star_eq_adjoint, comp_assoc, sub_comp, one_def, id_comp, sub_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩
    have h2' := congrArg adjoint h2
    simp only [adjoint_comp, adjoint_adjoint, comp_assoc] at h2'
    rw [h1, h2']
  · intro h
    refine ⟨?_, ?_⟩
    · rw [h, ← comp_assoc V.adjoint V, hV, one_def, id_comp]
    · have ha := congrArg adjoint h
      simp only [adjoint_comp, adjoint_adjoint, comp_assoc] at ha
      rw [← ha, ← comp_assoc V.adjoint V, hV, one_def, id_comp]

end TauCeti.CompressionMultiplicativeDomainExample
