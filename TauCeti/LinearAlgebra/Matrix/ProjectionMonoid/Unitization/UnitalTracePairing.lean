/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Prod
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.UnitalComparison
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Unitization.TracePairing

/-!
# Trace pairings on products and on unital algebras

Two comparisons for the trace pairings of tracial additive maps on `K₀`:

* **Products.** For a tracial `f : R × S →+ M`, the trace pairing on `K₀(R × S)` is computed
  summand by summand: it is the pairing of `f ∘ inl` on `K₀(R)` applied to the first component
  plus the pairing of `f ∘ inr` on `K₀(S)` applied to the second
  (`TauCeti.ProjectionKZero.tracePairing_prod`). This is the decomposition
  `x = inl_* (fst_* x) + inr_* (snd_* x)` of `K₀(R × S) ≃+ K₀(R) × K₀(S)` together with the
  naturality of the pairing.
* **Unital algebras.** For a unital `A`, the nonunital `K₀`-group `K₀(A)`, the kernel of
  `K₀(A⁺) → K₀(R)`, is the projection `K₀`-group of `A` (`TauCeti.UnitizationKZero.unitalEquiv`),
  and the two trace pairings of a tracial `f : A →+ M` agree under this isomorphism
  (`TauCeti.UnitizationKZero.tracePairing_unitalEquiv`). The isomorphism is induced by
  `A⁺ → A`, `(r, a) ↦ r • 1 + a`, along which `f` pulls back to the extension
  `f⁺ (r, a) = f (r • 1) + f a`, and the scalar values of an extension do not change the
  nonunital pairing (`TauCeti.UnitizationKZero.tracePairing_traceExtension`).

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §6.9.
-/

public section

namespace TauCeti

namespace ProjectionKZero

variable {R S M : Type*} [NonUnitalSemiring R] [StarRing R] [NonUnitalSemiring S] [StarRing S]
  [AddCommGroup M]

/-- **The trace pairing of a product is computed summand by summand**: for a tracial
`f : R × S →+ M`, `f_* x = (f ∘ inl)_* (fst_* x) + (f ∘ inr)_* (snd_* x)`. -/
theorem tracePairing_prod (f : R × S →+ M) (hf : ∀ a b, f (a * b) = f (b * a))
    (x : ProjectionKZero (R × S)) :
    tracePairing f hf x =
      tracePairing (f.comp (NonUnitalStarRingHom.inl R S).toNonUnitalRingHom.toAddMonoidHom)
          (fun a b ↦ by simpa using hf (a, 0) (b, 0))
          (map (NonUnitalStarRingHom.fst R S) x) +
        tracePairing (f.comp (NonUnitalStarRingHom.inr R S).toNonUnitalRingHom.toAddMonoidHom)
          (fun a b ↦ by simpa using hf (0, a) (0, b))
          (map (NonUnitalStarRingHom.snd R S) x) := by
  conv_lhs => rw [← (prodEquiv R S).symm_apply_apply x]
  rw [prodEquiv_symm_apply, prodEquiv_apply, map_add, tracePairing_comp_map,
    tracePairing_comp_map]
  rfl

end ProjectionKZero

namespace UnitizationKZero

variable {R A M : Type*} [CommSemiring R] [StarRing R] [Ring A] [StarRing A] [Algebra R A]
  [StarModule R A] [AddCommGroup M]

/-- **The trace pairings of a unital algebra agree.** For a unital `A` and a tracial
`f : A →+ M`, the pairing of `f` on the projection `K₀`-group, applied to the image of
`x ∈ K₀(A)` under `K₀(A) ≃+ K₀ᵖ(A)`, is the nonunital trace pairing of `f` at `x`. -/
theorem tracePairing_unitalEquiv (f : A →+ M) (hf : ∀ a b, f (a * b) = f (b * a))
    (x : UnitizationKZero R A) :
    ProjectionKZero.tracePairing f hf (unitalEquiv R A x) = tracePairing f hf x := by
  set ψ : _root_.Unitization R A →⋆ₙ+* A :=
    (NonUnitalStarRingHom.fst A R).comp (Unitization.prodStarAlgEquiv R A).toStarRingEquiv
  have hψ (y : _root_.Unitization R A) : ψ y = algebraMap R A y.fst + y.snd := by
    rw [NonUnitalStarRingHom.comp_apply, NonUnitalStarRingHom.fst_apply]
    exact congrArg Prod.fst (Unitization.prodStarAlgEquiv_apply R A y)
  -- `f ∘ ψ` is the extension of `f` with the scalar values `r ↦ f (r • 1)`.
  let g : R →+ M := f.comp (algebraMap R A).toAddMonoidHom
  have hfg : f.comp ψ.toNonUnitalRingHom.toAddMonoidHom = Unitization.traceExtension g f :=
    AddMonoidHom.ext fun y ↦ by simp [hψ, g]
  rw [unitalEquiv_apply, unitalProdEquiv_apply, ProjectionKZero.prodEquiv_apply,
    ← AddMonoidHom.comp_apply (ProjectionKZero.map _), ← ProjectionKZero.map_comp,
    ← AddMonoidHom.comp_apply (ProjectionKZero.tracePairing f hf),
    ← ProjectionKZero.tracePairing_comp_map,
    ProjectionKZero.tracePairing_congr hfg _ (Unitization.traceExtension_mul_comm g hf)]
  exact tracePairing_traceExtension g f hf x

end UnitizationKZero

end TauCeti
