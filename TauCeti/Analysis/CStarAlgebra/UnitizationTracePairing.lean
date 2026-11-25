/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.TracePairing
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.TracePairing

/-!
# The pairing of positive tracial functionals with the nonunital `K₀`-group

Let `τ` be a positive tracial functional on a possibly nonunital C⋆-algebra `A`, and
`K₀(A) = ker (K₀(A⁺) → K₀(ℂ))` the operator `K₀`-group (`TauCeti.UnitizationKZero ℂ A`). Extend
`τ` to the unitization by `τ⁺(a + λ) = τ(a) + λ`; it is tracial, though in general neither
positive nor bounded by `1`. The **trace pairing** `τ_* : K₀(A) →+ ℝ`
(`TauCeti.PositiveTracialFunctional.unitizationKZeroPairing`) is the real part of the unnormalized
matrix trace of `τ⁺` on `K₀(A⁺)`, restricted to `K₀(A)`. On a class `[e] − [p_n]`, where the
scalar part of the projection `e` over `A⁺` is the scalar projection `p_n`, it is the trace
`∑ i, τ ((e − p_n) i i)` of a matrix over `A`
(`TauCeti.PositiveTracialFunctional.unitizationKZeroPairing_of_mk_sub_of_mk`), so neither
positivity of `τ⁺` nor a bound on `‖τ‖` enters. It is natural for star homomorphisms
(`TauCeti.PositiveTracialFunctional.unitizationKZeroPairing_comp`). The unital pairing
`TauCeti.PositiveTracialFunctional.kZeroPairing` is the same construction on `K₀(A)` itself
(`TauCeti.PositiveTracialFunctional.kZeroPairing_eq_re_tracePairing`).

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §6.9.
-/

public section

noncomputable section

open Matrix Algebra

namespace TauCeti

namespace PositiveTracialFunctional

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τ : PositiveTracialFunctional A) {m : Type*} [Fintype m]

/-- The unital trace pairing `TauCeti.PositiveTracialFunctional.kZeroPairing` is the real part of
the trace pairing `TauCeti.ProjectionKZero.tracePairing` of `τ` as a tracial additive map. -/
theorem kZeroPairing_eq_re_tracePairing :
    τ.kZeroPairing =
      Complex.reAddGroupHom.comp (ProjectionKZero.tracePairing (τ : A →+ ℂ) τ.map_mul_comm) := by
  refine GrothendieckAddGroup.addHom_ext fun x ↦ ?_
  induction x using ProjectionMonoid.ind with
  | mk k p hp =>
    rw [AddMonoidHom.comp_apply, kZeroPairing_of_mk, ProjectionKZero.tracePairing_of_mk]
    rfl

/-- The **trace pairing** `τ_* : K₀(A) →+ ℝ` of a positive tracial functional with the operator
`K₀`-group of a possibly nonunital C⋆-algebra: the real part of the unnormalized matrix trace of
`τ⁺(a + λ) = τ(a) + λ` on `K₀(A⁺)`, restricted to `K₀(A)`. -/
def unitizationKZeroPairing : UnitizationKZero ℂ A →+ ℝ :=
  Complex.reAddGroupHom.comp
    (UnitizationKZero.tracePairing (AddMonoidHom.id ℂ) (τ : A →+ ℂ) τ.map_mul_comm)

/-- Unfolding `TauCeti.PositiveTracialFunctional.unitizationKZeroPairing`. -/
theorem unitizationKZeroPairing_apply (x : UnitizationKZero ℂ A) :
    τ.unitizationKZeroPairing x =
      (UnitizationKZero.tracePairing (AddMonoidHom.id ℂ) (τ : A →+ ℂ) τ.map_mul_comm x).re :=
  (rfl)

/-- **The pairing on a representative.** For a projection `e` over `A⁺` with scalar part the
projection `p` over `ℂ`, the class `[e] − [p]` pairs to the real part of `∑ i, τ ((e i i).snd)`,
the trace of `e − p`. -/
theorem unitizationKZeroPairing_of_mk_sub_of_mk {e : Matrix m m (Unitization ℂ A)}
    (he : IsStarProjection e) {p : Matrix m m ℂ} (hp : IsStarProjection p)
    (hep : e.map (fun x ↦ x.fst) = p) :
    τ.unitizationKZeroPairing
        ⟨_, UnitizationKZero.of_mk_sub_inl_of_mk_mem he hp hep⟩ =
      (∑ i, τ ((e i i).snd)).re := by
  rw [unitizationKZeroPairing_apply, UnitizationKZero.tracePairing_of_mk_sub_of_mk _ _ _ he hp hep]
  rfl

/-- **Naturality.** For a star homomorphism `φ : A → B` and a positive tracial functional `τ` on
`B`, the pairing of `τ ∘ φ` is the pairing of `τ` composed with `φ_* : K₀(A) → K₀(B)`. -/
theorem unitizationKZeroPairing_comp (τ : PositiveTracialFunctional B) (φ : A →⋆ₙₐ[ℂ] B) :
    (τ.comp φ).unitizationKZeroPairing =
      τ.unitizationKZeroPairing.comp (UnitizationKZero.map φ) := by
  have h := UnitizationKZero.tracePairing_comp_map φ (AddMonoidHom.id ℂ) (τ : B →+ ℂ)
    τ.map_mul_comm
  ext x
  rw [AddMonoidHom.comp_apply, unitizationKZeroPairing_apply, unitizationKZeroPairing_apply,
    ← AddMonoidHom.comp_apply, ← h]
  have key : ∀ (f f' : A →+ ℂ), f = f' → ∀ hf hf',
      UnitizationKZero.tracePairing (AddMonoidHom.id ℂ) f hf =
        UnitizationKZero.tracePairing (AddMonoidHom.id ℂ) f' hf' := by
    rintro f _ rfl _ _
    rfl
  exact congrArg (fun y ↦ (y x).re) (key ((τ.comp φ : PositiveTracialFunctional A) : A →+ ℂ)
    ((τ : B →+ ℂ).comp φ.toNonUnitalAlgHom.toAddMonoidHom) (AddMonoidHom.ext fun a ↦ by simp) _ _)

end PositiveTracialFunctional

end TauCeti
