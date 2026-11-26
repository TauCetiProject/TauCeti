/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commensurable
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.NumberTheory.Quaternion.Fuchsian.RealSplitting
public import TauCeti.NumberTheory.Quaternion.Order.NormOne

/-!
# Projective norm-one images of quaternion orders

A real splitting carries the reduced-norm-one group of a quaternion order into `SL(2, ℝ)`.
Its image in `PSL(2, ℝ)` is `RealSplitting.normOneImage`, the group conventionally denoted
`Γ¹(Λ)`. The construction is monotone in the order, and changing the order gives groups of
finite relative index in each other. Thus for a smaller order its projective image has finite
index in that of the larger order.

## References

* J. Voight, *Quaternion algebras*, §38.1.5 and §38.3.1.
-/

public section

open scoped Quaternion MatrixGroups

namespace TauCeti.RealSplitting

variable {R k : Type*} [CommRing R] [Field k] [Algebra R k]
  [IsFractionRing R k] [IsIntegrallyClosed R] {a b : k}
  [alg : Algebra R ℍ[k,a,b]] [@IsScalarTower R k ℍ[k,a,b] _ _ alg.toSMul]
  (S : RealSplitting k a b) {Λ Γ : Subalgebra R ℍ[k,a,b]}

/-- The projective image of the reduced-norm-one group of a quaternion order under a real
splitting. This is the group `Γ¹(Λ)` used to define arithmetic Fuchsian groups. -/
def normOneImage (hΛ : IntegralOrder.IsOrder k Λ) : Subgroup (PSL(2, ℝ)) :=
  hΛ.normOne.map ((QuotientGroup.mk' (Subgroup.center (SL(2, ℝ)))).comp
    S.unitaryToSpecialLinear)

/-- An element of `PSL(2, ℝ)` belongs to the projective norm-one image exactly when it has a
norm-one quaternion representative belonging to the order. -/
theorem mem_normOneImage (hΛ : IntegralOrder.IsOrder k Λ) {g : PSL(2, ℝ)} :
    g ∈ S.normOneImage hΛ ↔ ∃ x : unitary ℍ[k,a,b], (x : ℍ[k,a,b]) ∈ Λ ∧
      QuotientGroup.mk (S.unitaryToSpecialLinear x) = g := by
  simp only [normOneImage, Subgroup.mem_map, IntegralOrder.IsOrder.mem_normOne]
  rfl

/-- Inclusion of quaternion orders induces inclusion of their projective norm-one images. -/
theorem normOneImage_mono (hΛ : IntegralOrder.IsOrder k Λ) (hΓ : IntegralOrder.IsOrder k Γ)
    (h : Λ ≤ Γ) : S.normOneImage hΛ ≤ S.normOneImage hΓ :=
  Subgroup.map_mono (hΛ.normOne_mono hΓ h)

/-- The projective norm-one images of any two orders have finite relative index. In particular,
for nested orders this is the finiteness of the index of the smaller image in the larger one. -/
theorem normOneImage_isFiniteRelIndex [Ring.HasFiniteQuotients R]
    (hΛ : IntegralOrder.IsOrder k Λ) (hΓ : IntegralOrder.IsOrder k Γ) :
    (S.normOneImage hΛ).IsFiniteRelIndex (S.normOneImage hΓ) :=
  (hΛ.normOne_isFiniteRelIndex hΓ).map _

/-- Changing the quaternion order preserves the commensurability class of its projective
norm-one image. -/
theorem normOneImage_commensurable [Ring.HasFiniteQuotients R]
    (hΛ : IntegralOrder.IsOrder k Λ) (hΓ : IntegralOrder.IsOrder k Γ) :
    (S.normOneImage hΛ).Commensurable (S.normOneImage hΓ) :=
  ⟨S.normOneImage_isFiniteRelIndex hΛ hΓ, S.normOneImage_isFiniteRelIndex hΓ hΛ⟩

end TauCeti.RealSplitting
