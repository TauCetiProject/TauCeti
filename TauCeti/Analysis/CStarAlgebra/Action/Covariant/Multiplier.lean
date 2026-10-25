/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Basic
public import TauCeti.Analysis.CStarAlgebra.Action.Multiplier
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate

/-!
# Covariance on multiplier algebras

A nondegenerate covariant pair remains covariant after extending its coefficient representation
to the multiplier algebra. Thus the same unitary group implements both the original action and
its canonical multiplier extension. The multiplier covariance identity is characterized by its
restriction to the coefficient algebra. An operator implements an action on the multiplier
extension of a nondegenerate representation exactly when it does so on the coefficient algebra,
`CStarAction.mul_multiplierExtension_iff`.

Conversely, a strictly continuous homomorphism into the unitary multipliers that implements a
C⋆-action gives a covariant pair in every nondegenerate representation of the coefficient algebra.
Only continuity of left multiplication on each coefficient is needed: unitary multipliers are
uniformly bounded, so the multiplier extension sends their orbits to strongly continuous operator
orbits. These constructions allow covariant representations to be specified by canonical multiplier
maps, as in the universal property of a crossed product.

The extension and continuity arguments reuse `NonUnitalStarAlgHom.multiplierExtension` and
`NonUnitalStarAlgHom.continuous_multiplierExtension_apply`.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, for covariant representations
and their multiplier-algebra formulation.
-/

public section

noncomputable section

open scoped MultiplierAlgebra

namespace TauCeti.CStarAction

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]

/-- An operator implements an action automorphism on the multiplier extension of a nondegenerate
representation exactly when it implements it on the coefficient algebra. -/
theorem mul_multiplierExtension_iff {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (α : CStarAction G A)
    {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : π.IsNondegenerate) (g : G) (T : H →L[ℂ] H) :
    (∀ m : 𝓜(ℂ, A), T * π.multiplierExtension hπ m =
      π.multiplierExtension hπ (α.multiplier g m) * T) ↔
      ∀ a : A, T * π a = π (α g a) * T := by
  constructor
  · intro h a
    simpa using h (a : 𝓜(ℂ, A))
  · intro h m
    apply hπ.ext
    intro a
    simp only [mul_assoc, NonUnitalStarAlgHom.multiplierExtension_mul_eq_fst, h]
    rw [← mul_assoc, NonUnitalStarAlgHom.multiplierExtension_mul_eq_fst]
    simp

namespace CovariantRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)
  (hπ : P.coefficient.IsNondegenerate)

/-- Covariance extends from the coefficient algebra to its multiplier algebra. -/
@[simp]
theorem group_mul_multiplierExtension (g : G) (m : 𝓜(ℂ, A)) :
    P.group g * P.coefficient.multiplierExtension hπ m =
      P.coefficient.multiplierExtension hπ (α.multiplier g m) * P.group g :=
  (α.mul_multiplierExtension_iff hπ g (P.group g)).mpr (P.group_mul_coefficient g) m

/-- The extended coefficient at a transformed multiplier is its unitary conjugate. -/
theorem multiplierExtension_action (g : G) (m : 𝓜(ℂ, A)) :
    P.coefficient.multiplierExtension hπ (α.multiplier g m) =
      P.group g * P.coefficient.multiplierExtension hπ m * P.group g⁻¹ := by
  rw [P.group_mul_multiplierExtension hπ, mul_assoc, ← map_mul]
  simp

variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : π.IsNondegenerate)
  (u : G →* unitary (𝓜(ℂ, A)))
  (hu : ∀ a : A, Continuous fun g => (u g : 𝓜(ℂ, A)).fst a)
  (hcov : ∀ (g : G) (a : A),
    (u g : 𝓜(ℂ, A)) * (a : 𝓜(ℂ, A)) = (α g a : 𝓜(ℂ, A)) * (u g : 𝓜(ℂ, A)))

/-- A strictly continuous unitary multiplier implementation of an action gives a covariant pair
in every nondegenerate coefficient representation. The coefficient representation may act on
the zero Hilbert space, and the coefficient algebra need not have an identity. -/
def ofUnitaryMultiplier : CovariantRepresentation α H where
  coefficient := π
  group := .ofMonoidHom <| (π.multiplierExtension hπ).toMonoidHom.comp
    ((unitary (𝓜(ℂ, A))).subtype.comp u)
  isUnitary := (ContRepresentation.isUnitary_iff_mem_unitary _).mpr fun g =>
    Unitary.map_mem (π.multiplierExtension hπ) (u g).property
  continuous_orbit ξ := π.continuous_multiplierExtension_apply hπ hu
    (C := ‖(1 : 𝓜(ℂ, A))‖)
    (fun g => by simpa using (CStarRing.norm_coe_unitary_mul (u g) (1 : 𝓜(ℂ, A))).le) ξ
  covariance g a ξ := by
    have h := congrArg (π.multiplierExtension hπ) (hcov g a)
    simp only [map_mul, NonUnitalStarAlgHom.multiplierExtension_coe] at h
    exact congr($(h) ξ)

@[simp]
theorem ofUnitaryMultiplier_coefficient :
    (ofUnitaryMultiplier π hπ u hu hcov).coefficient = π :=
  (rfl)

/-- The group operators are the images of the unitary multipliers under the multiplier extension.
-/
@[simp]
theorem ofUnitaryMultiplier_group (g : G) :
    (ofUnitaryMultiplier π hπ u hu hcov).group g =
      π.multiplierExtension hπ (u g : 𝓜(ℂ, A)) :=
  (rfl)

end CovariantRepresentation

end TauCeti.CStarAction
