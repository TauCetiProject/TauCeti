/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Comap
public import TauCeti.Analysis.CStarAlgebra.Quotient

/-!
# Covariant representations of quotient systems

Let `φ : Hom α β` be a surjective equivariant homomorphism of C⋆-dynamical systems, for instance
the projection of `A` onto its quotient by a closed invariant ideal. A covariant pair `P` of `α`
is a pullback `Q.comap φ` of a covariant pair `Q` of `β` exactly when its coefficient
representation vanishes on the kernel of `φ`; the pair `Q` is then unique. This identifies the
covariant pairs of the quotient system with the covariant pairs of `α` that vanish on the ideal.

The descended pair `P.descend φ hφ h` keeps the group representation of `P`, and its coefficient
representation is obtained from `P.coefficient` through the C⋆-isomorphism `A ⧸ ker φ ≃ B`.
No unitality, separability or local compactness is assumed.

## Main declarations

* `TauCeti.CStarAction.CovariantRepresentation.descend`: the covariant pair of `β` induced by a
  covariant pair of `α` whose coefficient representation vanishes on `ker φ`.
* `TauCeti.CStarAction.CovariantRepresentation.comap_descend` and
  `TauCeti.CStarAction.CovariantRepresentation.eq_descend_iff`: `P.descend φ hφ h` is the unique
  covariant pair pulling back to `P`.
* `TauCeti.CStarAction.CovariantRepresentation.exists_comap_eq_iff`: a covariant pair of `α` is a
  pullback along `φ` precisely when its coefficient representation vanishes on `ker φ`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Proposition 3.19, where covariant pairs of the
  quotient system are identified with covariant pairs vanishing on the ideal.
-/

public section

noncomputable section

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G A B H : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {β : CStarAction G B}
  (P : CovariantRepresentation α H) (φ : Hom α β) (hφ : Function.Surjective φ)
  (h : ∀ a, φ a = 0 → P.coefficient a = 0)

/-- The coefficient representation of `P` descended along the surjection `φ`. -/
private def descendCoefficient : B →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  (TwoSidedIdeal.Quotient.liftStarAlgHom (TwoSidedIdeal.ker φ.toNonUnitalStarAlgHom)
      P.coefficient fun a ha => h a ((TwoSidedIdeal.mem_ker _).1 ha)).comp
    (NonUnitalStarAlgHom.quotientKerEquivOfSurjective
      (φ := φ.toNonUnitalStarAlgHom) hφ).symm.toNonUnitalStarAlgHom

private theorem descendCoefficient_apply (a : A) :
    descendCoefficient P φ hφ h (φ a) = P.coefficient a := by
  have hmk : (NonUnitalStarAlgHom.quotientKerEquivOfSurjective
      (φ := φ.toNonUnitalStarAlgHom) hφ).symm (φ a) =
      TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker φ.toNonUnitalStarAlgHom) a := by
    rw [StarAlgEquiv.symm_apply_eq, NonUnitalStarAlgHom.quotientKerEquivOfSurjective_mk,
      Hom.coe_toNonUnitalStarAlgHom]
  simp only [descendCoefficient, NonUnitalStarAlgHom.comp_apply,
    StarAlgEquiv.toNonUnitalStarAlgHom_apply, hmk, TwoSidedIdeal.Quotient.liftStarAlgHom_mk]

/-- Descend a covariant pair of `α` along a surjective equivariant homomorphism `φ : Hom α β`,
when its coefficient representation vanishes on the kernel of `φ`. The group representation is
unchanged, and the coefficient representation sends `φ a` to `P.coefficient a`. -/
def descend : CovariantRepresentation β H where
  coefficient := descendCoefficient P φ hφ h
  group := P.group
  isUnitary := P.isUnitary
  continuous_orbit := P.continuous_orbit
  covariance g b v := by
    obtain ⟨a, rfl⟩ := hφ b
    rw [← φ.map_action, descendCoefficient_apply, descendCoefficient_apply]
    exact P.covariance g a v

@[simp]
theorem descend_coefficient_apply (a : A) :
    (P.descend φ hφ h).coefficient (φ a) = P.coefficient a :=
  descendCoefficient_apply P φ hφ h a

@[simp]
theorem descend_group : (P.descend φ hφ h).group = P.group :=
  (rfl)

/-- Pulling the descended pair back along `φ` recovers `P`. -/
@[simp]
theorem comap_descend : (P.descend φ hφ h).comap φ = P :=
  CovariantRepresentation.ext (NonUnitalStarAlgHom.ext fun a => by simp) (by simp)

/-- The descended pair is the unique covariant pair of `β` pulling back to `P` along `φ`. -/
theorem eq_descend_iff {Q : CovariantRepresentation β H} :
    Q = P.descend φ hφ h ↔ Q.comap φ = P := by
  refine ⟨fun hQ => hQ ▸ P.comap_descend φ hφ h, fun hQ => ?_⟩
  subst hQ
  refine CovariantRepresentation.ext (NonUnitalStarAlgHom.ext fun b => ?_) (by simp)
  obtain ⟨a, rfl⟩ := hφ b
  simp

/-- Descending a pulled-back pair recovers the original pair. -/
@[simp]
theorem descend_comap (Q : CovariantRepresentation β H)
    (h : ∀ a, φ a = 0 → (Q.comap φ).coefficient a = 0) :
    (Q.comap φ).descend φ hφ h = Q :=
  ((Q.comap φ).eq_descend_iff φ hφ h).2 rfl |>.symm

include hφ in
omit h in
/-- A covariant pair of `α` is pulled back along a surjective equivariant homomorphism `φ`
precisely when its coefficient representation vanishes on the kernel of `φ`. -/
theorem exists_comap_eq_iff :
    (∃ Q : CovariantRepresentation β H, Q.comap φ = P) ↔
      ∀ a, φ a = 0 → P.coefficient a = 0 := by
  refine ⟨?_, fun h => ⟨P.descend φ hφ h, P.comap_descend φ hφ h⟩⟩
  rintro ⟨Q, rfl⟩ a ha
  simp [ha]

end TauCeti.CStarAction.CovariantRepresentation
