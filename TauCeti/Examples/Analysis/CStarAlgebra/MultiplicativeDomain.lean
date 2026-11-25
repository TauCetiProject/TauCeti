/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.MultiplicativeDomain
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
public import TauCeti.Analysis.InnerProductSpace.Positive.VectorFunctional
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace

/-!
# The multiplicative domains of a vector state and of the normalized trace

For a unit vector `ξ` of a complex Hilbert space `H`, the vector state `ω_ξ(a) = ⟪ξ, a ξ⟫` on
`H →L[ℂ] H` is a unital completely positive functional. Its multiplicative domain consists of the
operators `a` for which both `a ξ` and `a⋆ ξ` are multiples of `ξ`
(`mem_multiplicativeDomain_vectorFunctional_iff`).

The computation rests on the identity
`ω_ξ(a⋆a) - conj (ω_ξ a) ω_ξ(a) = ‖a ξ - ω_ξ(a) ξ‖²`, so the Schwarz equality at `a` says exactly
that `a ξ` is the multiple `ω_ξ(a) ξ` of `ξ`.

The normalized trace `tr_n` on `M_n`, `n ≥ 1`, has multiplicative domain `ℂ·1`
(`multiplicativeDomain_traceFunctional`): its Schwarz defect at `a` is
`tr_n(b⋆b)` for `b = a - tr_n(a)·1`, and `tr_n` is faithful.
-/

public section

open scoped InnerProductSpace ComplexOrder CStarAlgebra

namespace TauCeti.MultiplicativeDomainExample

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The vector functional `a ↦ ⟪ξ, a ξ⟫` on the bounded operators on `H`, completely positive
since it is a positive functional. It is a state when `‖ξ‖ = 1`. -/
noncomputable def vectorFunctional (ξ : H) : (H →L[ℂ] H) →CP ℂ :=
  (ContinuousLinearMap.innerPositiveLinearMap ℂ ξ).toCompletelyPositiveMap

@[simp]
theorem vectorFunctional_apply (ξ : H) (a : H →L[ℂ] H) : vectorFunctional ξ a = ⟪ξ, a ξ⟫_ℂ := by
  simp [vectorFunctional]

/-- The vector functional of a unit vector is unital, so it is a state. -/
theorem vectorFunctional_one {ξ : H} (hξ : ‖ξ‖ = 1) :
    (vectorFunctional ξ).toLinearMap 1 = 1 := by
  simp [vectorFunctional, hξ]

/-- The Schwarz defect of a vector functional is a squared norm:
`ω_ξ(a⋆a) - conj (ω_ξ a) ω_ξ(a) = ‖a ξ - ω_ξ(a) ξ‖²` for a unit vector `ξ`. -/
private theorem vectorFunctional_star_mul_self_sub {ξ : H} (hξ : ‖ξ‖ = 1) (a : H →L[ℂ] H) :
    vectorFunctional ξ (star a * a) - star (vectorFunctional ξ a) * vectorFunctional ξ a =
      ⟪a ξ - ⟪ξ, a ξ⟫_ℂ • ξ, a ξ - ⟪ξ, a ξ⟫_ℂ • ξ⟫_ℂ := by
  simp only [vectorFunctional_apply, ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp,
    ContinuousLinearMap.adjoint_inner_right, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, inner_self_eq_one_of_norm_eq_one hξ, Complex.star_def,
    ← inner_conj_symm (a ξ) ξ]
  ring

/-- The Schwarz equality `ω_ξ(a⋆a) = conj (ω_ξ a) ω_ξ(a)` holds for a unit vector `ξ` exactly
when `a ξ` is a multiple of `ξ`. -/
private theorem vectorFunctional_star_mul_self_eq_iff {ξ : H} (hξ : ‖ξ‖ = 1) (a : H →L[ℂ] H) :
    vectorFunctional ξ (star a * a) = star (vectorFunctional ξ a) * vectorFunctional ξ a ↔
      ∃ c : ℂ, a ξ = c • ξ := by
  rw [← sub_eq_zero, vectorFunctional_star_mul_self_sub hξ, inner_self_eq_zero, sub_eq_zero]
  refine ⟨fun h => ⟨_, h⟩, fun ⟨c, hc⟩ => ?_⟩
  rw [hc, inner_smul_right, inner_self_eq_one_of_norm_eq_one hξ, mul_one]

/-- **The multiplicative domain of a vector state.** For a unit vector `ξ`, an operator `a` lies in
the multiplicative domain of `ω_ξ` exactly when `a ξ` and `a⋆ ξ` are both multiples of `ξ`. -/
theorem mem_multiplicativeDomain_vectorFunctional_iff {ξ : H} (hξ : ‖ξ‖ = 1) (a : H →L[ℂ] H) :
    a ∈ ((vectorFunctional ξ).isNPositive 2).multiplicativeDomain (vectorFunctional_one hξ) ↔
      (∃ c : ℂ, a ξ = c • ξ) ∧ ∃ c : ℂ, star a ξ = c • ξ := by
  have hstar : ∀ b : H →L[ℂ] H, vectorFunctional ξ (star b) = star (vectorFunctional ξ b) :=
    ((vectorFunctional ξ).isNPositive 2).map_star two_pos
  -- The Schwarz equality for `a⋆` is the second condition `ω_ξ(aa⋆) = ω_ξ(a) ω_ξ(a)⋆`.
  have h2 : vectorFunctional ξ (a * star a) = vectorFunctional ξ a * star (vectorFunctional ξ a) ↔
      ∃ c : ℂ, star a ξ = c • ξ := by
    simpa [hstar, mul_comm] using vectorFunctional_star_mul_self_eq_iff hξ (star a)
  rw [IsNPositive.mem_multiplicativeDomain]
  exact and_congr (vectorFunctional_star_mul_self_eq_iff hξ a) h2

section Trace

variable (n : Type*) [Fintype n]

/-- The normalized trace `tr_n` on `M_n`, completely positive since it is a positive functional.
It is a faithful tracial state when `n` is nonempty. -/
noncomputable def traceFunctional : CStarMatrix n n ℂ →CP ℂ :=
  (CStarMatrix.normalizedTraceMap n).toPositiveLinearMap.toCompletelyPositiveMap

variable {n}

@[simp]
theorem traceFunctional_apply (a : CStarMatrix n n ℂ) :
    traceFunctional n a = CStarMatrix.normalizedTrace a := by
  simp [traceFunctional]

theorem traceFunctional_one [DecidableEq n] [Nonempty n] :
    (traceFunctional n).toLinearMap 1 = 1 := by
  simp

/-- The Schwarz defect of the normalized trace at `a` is `tr_n(b⋆b)` for `b = a - tr_n(a)·1`. -/
private theorem normalizedTrace_star_mul_self_sub [DecidableEq n] [Nonempty n]
    (a : CStarMatrix n n ℂ) :
    CStarMatrix.normalizedTrace (star a * a) -
        star (CStarMatrix.normalizedTrace a) * CStarMatrix.normalizedTrace a =
      CStarMatrix.normalizedTrace (star (a - CStarMatrix.normalizedTrace a • 1) *
        (a - CStarMatrix.normalizedTrace a • 1)) := by
  simp only [star_sub, star_smul, star_one, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, CStarMatrix.normalizedTrace_sub,
    CStarMatrix.normalizedTrace_smul, CStarMatrix.normalizedTrace_star,
    CStarMatrix.normalizedTrace_one]
  ring

/-- **The multiplicative domain of the normalized trace** on `M_n`, `n ≥ 1`, is `ℂ·1`: the
Schwarz equality `tr_n(a⋆a) = |tr_n(a)|²` forces `a = tr_n(a)·1`, since `tr_n` is faithful. -/
theorem multiplicativeDomain_traceFunctional [DecidableEq n] [Nonempty n] :
    ((traceFunctional n).isNPositive 2).multiplicativeDomain traceFunctional_one = ⊥ := by
  refine eq_bot_iff.mpr fun a ha ↦ ?_
  have h := ((IsNPositive.mem_multiplicativeDomain _ _).mp ha).1
  simp only [CompletelyPositiveMap.coe_toLinearMap, traceFunctional_apply] at h
  have hb : a - CStarMatrix.normalizedTrace a • 1 = 0 := by
    rw [← CStarMatrix.normalizedTrace_star_mul_self_eq_zero_iff,
      ← normalizedTrace_star_mul_self_sub, h, sub_self]
  rw [sub_eq_zero] at hb
  rw [hb, Algebra.smul_def, mul_one]
  exact StarSubalgebra.algebraMap_mem _ _

end Trace

end TauCeti.MultiplicativeDomainExample
