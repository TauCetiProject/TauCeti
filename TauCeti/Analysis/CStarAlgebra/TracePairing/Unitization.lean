/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.TracePairing.Basic
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Unitization.UnitalTracePairing

/-!
# The pairing of positive tracial functionals with the nonunital `K₀`-group

Let `τ` be a positive tracial functional on a possibly nonunital C⋆-algebra `A`, and
`K₀(A) = ker (K₀(A⁺) → K₀(ℂ))` the operator `K₀`-group (`TauCeti.UnitizationKZero ℂ A`). Extend
`τ` to the unitization by `τ⁺(a + λ) = τ(a) + λ`; it is tracial, though in general neither
positive nor bounded by `1`. The **trace pairing** `τ_* : K₀(A) →+ ℝ`
(`TauCeti.PositiveTracialFunctional.unitizationKZeroPairing`) is the real part of the unnormalized
matrix trace of `τ⁺` on `K₀(A⁺)`, restricted to `K₀(A)`; the value of `τ⁺` on the scalars does
not matter there (`TauCeti.UnitizationKZero.tracePairing_traceExtension`). On a class `[e] − [p]`
of `K₀(A)`, for projections `e` over `A⁺` and `p` over `ℂ`, it is the real part of
`∑ i, τ ((e i i).snd)`; when `p` is the scalar part of `e`, this is the trace of the matrix
`e − p` over `A`
(`TauCeti.PositiveTracialFunctional.unitizationKZeroPairing_of_mk_sub_inl_of_mk`), so neither
positivity of `τ⁺` nor a bound on `‖τ‖` enters. It is natural for star homomorphisms
(`TauCeti.PositiveTracialFunctional.unitizationKZeroPairing_comp`). For unital `A`, it is the
pairing `TauCeti.PositiveTracialFunctional.kZeroPairing` with the projection `K₀`-group under
the isomorphism `K₀(A) ≃+ K₀ᵖ(A)` of `TauCeti.UnitizationKZero.unitalEquiv`
(`TauCeti.PositiveTracialFunctional.kZeroPairing_unitalEquiv`).

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §6.9.
-/

public section

noncomputable section

open Matrix Algebra

namespace TauCeti

namespace PositiveTracialFunctional

section NonUnital

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τ : PositiveTracialFunctional A) {m : Type*} [Fintype m]

/-- The **trace pairing** `τ_* : K₀(A) →+ ℝ` of a positive tracial functional with the operator
`K₀`-group of a possibly nonunital C⋆-algebra: the real part of the unnormalized matrix trace of
`τ⁺(a + λ) = τ(a) + λ` on `K₀(A⁺)`, restricted to `K₀(A)`
(`TauCeti.UnitizationKZero.tracePairing_traceExtension`). -/
def unitizationKZeroPairing : UnitizationKZero ℂ A →+ ℝ :=
  Complex.reAddGroupHom.comp (UnitizationKZero.tracePairing (τ : A →+ ℂ) τ.map_mul_comm)

/-- Unfolding `TauCeti.PositiveTracialFunctional.unitizationKZeroPairing`. -/
theorem unitizationKZeroPairing_apply (x : UnitizationKZero ℂ A) :
    τ.unitizationKZeroPairing x =
      (UnitizationKZero.tracePairing (τ : A →+ ℂ) τ.map_mul_comm x).re :=
  (rfl)

/-- **The pairing on a representative.** Let `e` be a projection over `A⁺` and `p` a projection
over `ℂ`. If `[e] − [p]` lies in `K₀(A)`, it pairs to the real part of `∑ i, τ ((e i i).snd)`.
When `p` is the scalar part of `e` (`TauCeti.UnitizationKZero.of_mk_sub_inl_of_mk_mem`), this is
the trace of `e − p`. -/
theorem unitizationKZeroPairing_of_mk_sub_inl_of_mk {e : Matrix m m (Unitization ℂ A)}
    (he : IsStarProjection e) {p : Matrix m m ℂ} (hp : IsStarProjection p)
    (hx : GrothendieckAddGroup.of (ProjectionMonoid.mk e he) -
      UnitizationKZero.inl ℂ A (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp)) ∈
        UnitizationKZero ℂ A) :
    τ.unitizationKZeroPairing ⟨_, hx⟩ = (∑ i, τ ((e i i).snd)).re := by
  rw [unitizationKZeroPairing_apply, UnitizationKZero.tracePairing_of_mk_sub_inl_of_mk]
  simp

/-- **Naturality.** For a star homomorphism `φ : A → B` and a positive tracial functional `τ` on
`B`, the pairing of `τ ∘ φ` is the pairing of `τ` composed with `φ_* : K₀(A) → K₀(B)`. -/
theorem unitizationKZeroPairing_comp (τ : PositiveTracialFunctional B) (φ : A →⋆ₙₐ[ℂ] B) :
    (τ.comp φ).unitizationKZeroPairing =
      τ.unitizationKZeroPairing.comp (UnitizationKZero.map φ) := by
  rw [unitizationKZeroPairing, unitizationKZeroPairing, AddMonoidHom.comp_assoc,
    ← UnitizationKZero.tracePairing_comp_map]
  congr 1
  exact UnitizationKZero.tracePairing_congr (AddMonoidHom.ext fun a ↦ by simp) _ _

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : PositiveTracialFunctional A)

/-- **Agreement with the operator `K₀`-group.** For unital `A`, the pairing of `τ` with
`K₀(A) = ker (K₀(A⁺) → K₀(ℂ))` is `τ_*` composed with `K₀(A) ≃+ K₀ᵖ(A)`. -/
theorem kZeroPairing_unitalEquiv (x : UnitizationKZero ℂ A) :
    τ.kZeroPairing (UnitizationKZero.unitalEquiv ℂ A x) = τ.unitizationKZeroPairing x := by
  rw [kZeroPairing_apply, unitizationKZeroPairing_apply,
    UnitizationKZero.tracePairing_unitalEquiv]

end Unital

end PositiveTracialFunctional

end TauCeti
