/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.UnitalComparison
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Unitization.TracePairing

/-!
# Trace pairings on unital algebras

For a unital `A`, the nonunital `K₀`-group `K₀(A)`, the kernel of `K₀(A⁺) → K₀(R)`, is the
projection `K₀`-group of `A` (`TauCeti.UnitizationKZero.unitalEquiv`), and the two trace pairings
of a tracial `f : A →+ M` agree under this isomorphism
(`TauCeti.UnitizationKZero.tracePairing_unitalEquiv`). The isomorphism is induced by `A⁺ → A`,
`(r, a) ↦ r • 1 + a` (`TauCeti.UnitizationKZero.unitalEquiv_apply_eq_map`), along which `f` pulls
back to the extension `f⁺ (r, a) = f (r • 1) + f a`, and the scalar values of an extension do not
change the nonunital pairing (`TauCeti.UnitizationKZero.tracePairing_traceExtension`).

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §6.9.
-/

public section

namespace TauCeti

namespace UnitizationKZero

variable {R A M : Type*} [CommSemiring R] [StarRing R] [Ring A] [StarRing A] [Algebra R A]
  [StarModule R A] [AddCommGroup M]

/-- **The trace pairings of a unital algebra agree.** For a unital `A` and a tracial
`f : A →+ M`, the pairing of `f` on the projection `K₀`-group, applied to the image of
`x ∈ K₀(A)` under `K₀(A) ≃+ K₀ᵖ(A)`, is the nonunital trace pairing of `f` at `x`. -/
theorem tracePairing_unitalEquiv (f : A →+ M) (hf : ∀ a b, f (a * b) = f (b * a))
    (x : UnitizationKZero R A) :
    ProjectionKZero.tracePairing f hf (unitalEquiv R A x) = tracePairing f hf x := by
  -- `f` pulled back along `A⁺ → A` is the extension of `f` with the scalar values `r ↦ f (r • 1)`.
  let g : R →+ M := f.comp (algebraMap R A).toAddMonoidHom
  have hfg : f.comp (NonUnitalStarRingHom.ofClass
      (Unitization.starLift (NonUnitalStarAlgHom.id R A))).toNonUnitalRingHom.toAddMonoidHom =
      Unitization.traceExtension g f :=
    AddMonoidHom.ext fun y ↦ by simp [g]
  rw [unitalEquiv_apply_eq_map, ← AddMonoidHom.comp_apply (ProjectionKZero.tracePairing f hf),
    ← ProjectionKZero.tracePairing_comp_map,
    ProjectionKZero.tracePairing_congr hfg _ (Unitization.traceExtension_mul_comm g hf)]
  exact tracePairing_traceExtension g f hf x

end UnitizationKZero

end TauCeti
