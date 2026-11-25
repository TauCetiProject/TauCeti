/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.KZero

/-!
# Trace pairings on projection `K₀`-groups

Let `R` be a star ring and `f : R →+ M` an additive map into an abelian group with
`f (a * b) = f (b * a)`, a *tracial* map. Its unnormalized matrix trace `f_m(p) = ∑ i, f (p i i)`
takes the same value on Murray–von Neumann equivalent matrix projections of any sizes and is
additive under block sum, so it induces the **trace pairing**
`f_* : K₀(R) →+ M` on the projection `K₀`-group (`TauCeti.ProjectionKZero.tracePairing`), natural
under star ring homomorphisms (`TauCeti.ProjectionKZero.tracePairing_comp_map`). Neither
positivity nor linearity enters.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §6.9.
-/

public section

noncomputable section

open Matrix Algebra

namespace TauCeti

namespace ProjectionKZero

variable {R S M : Type*} [NonUnitalSemiring R] [StarRing R] [NonUnitalSemiring S] [StarRing S]
  [AddCommGroup M] {m : Type*} [Fintype m]

/-- The unnormalized matrix trace of a tracial additive map, as a function on `V(R)`. -/
private def traceFun (f : R →+ M) (hf : ∀ a b, f (a * b) = f (b * a)) : ProjectionMonoid R → M :=
  ProjectionMonoid.lift (fun p _ ↦ ∑ i, f (p i i)) fun _ _ h ↦ h.sum_map_eq f hf

private theorem traceFun_mk (f : R →+ M) (hf : ∀ a b, f (a * b) = f (b * a)) {p : Matrix m m R}
    (hp : IsStarProjection p) : traceFun f hf (ProjectionMonoid.mk p hp) = ∑ i, f (p i i) := by
  rw [traceFun, ProjectionMonoid.lift_mk_of_equiv _ _ hp (Fintype.equivFin m)]
  exact ((hp.isMurrayVonNeumannEquivalent_reindex _).sum_map_eq f hf).symm

/-- The unnormalized matrix trace on `V(R)`, as an additive monoid homomorphism. -/
private def traceMonoidHom (f : R →+ M) (hf : ∀ a b, f (a * b) = f (b * a)) :
    ProjectionMonoid R →+ M where
  toFun := traceFun f hf
  map_zero' := by
    rw [← ProjectionMonoid.mk_zero (m := Fin 0), traceFun_mk]
    simp
  map_add' x y := by
    induction x using ProjectionMonoid.ind with | mk k p hp => ?_
    induction y using ProjectionMonoid.ind with | mk l q hq => ?_
    rw [← ProjectionMonoid.mk_fromBlocks, traceFun_mk, traceFun_mk, traceFun_mk]
    simp [Fintype.sum_sum_type]

/-- The **trace pairing** `f_* : K₀(R) →+ M` of a tracial additive map `f : R →+ M`, induced by
the unnormalized matrix trace `f_m(p) = ∑ i, f (p i i)`. -/
def tracePairing (f : R →+ M) (hf : ∀ a b, f (a * b) = f (b * a)) : ProjectionKZero R →+ M :=
  GrothendieckAddGroup.lift (traceMonoidHom f hf)

/-- The trace pairing sends the class of `p` to `∑ i, f (p i i)`. -/
theorem tracePairing_of_mk (f : R →+ M) (hf : ∀ a b, f (a * b) = f (b * a)) {p : Matrix m m R}
    (hp : IsStarProjection p) :
    tracePairing f hf (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp)) = ∑ i, f (p i i) :=
  (GrothendieckAddGroup.lift_apply_of _ _).trans (traceFun_mk f hf hp)

/-- **Naturality.** For a star ring homomorphism `φ : R → S` and a tracial `f : S →+ M`, the
pairing of `f ∘ φ` is the pairing of `f` composed with `φ_* : K₀(R) → K₀(S)`. -/
theorem tracePairing_comp_map (φ : R →⋆ₙ+* S) (f : S →+ M) (hf : ∀ a b, f (a * b) = f (b * a)) :
    tracePairing (f.comp φ.toNonUnitalRingHom.toAddMonoidHom)
        (fun a b ↦ by simpa using hf (φ a) (φ b)) =
      (tracePairing f hf).comp (map φ) := by
  refine GrothendieckAddGroup.addHom_ext fun x ↦ ?_
  induction x using ProjectionMonoid.ind with
  | mk k p hp =>
    rw [AddMonoidHom.comp_apply, map_of_mk, tracePairing_of_mk, tracePairing_of_mk]
    simp

/-- The trace pairing depends only on the map `f`. -/
theorem tracePairing_congr {f f' : R →+ M} (h : f = f') (hf : ∀ a b, f (a * b) = f (b * a))
    (hf' : ∀ a b, f' (a * b) = f' (b * a)) : tracePairing f hf = tracePairing f' hf' := by
  subst h
  rfl

end ProjectionKZero

end TauCeti
