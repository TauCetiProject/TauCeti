/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Unitization
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The left action of the minimal unitization

The canonical left action of `Unitization 𝕜 A` on `A` is Mathlib's
`Unitization.lift (NonUnitalAlgHom.Lmul 𝕜 A)`. It sends `(z, a)` to `z • id + L_a`.
If `A` has no left identity (or is a star ring with no two-sided identity), the scalar
coordinate is bounded by the operator norm of this action. When `A` is a regular normed
algebra, the action is therefore isometric
for the minimal unitization norm and has closed image. In particular, this applies to
complex C⋆-algebras without a two-sided identity, with their C⋆-unitization norm.

The absence of an identity is essential: for an already unital algebra, the external
unitization acts through `(z, a) ↦ z • 1 + a` and is not faithful.

The norm comparison uses the Neumann-series criterion: if the scalar part had larger
norm than the left action, a left multiplication operator would be invertible, forcing
a left identity. In a star ring a left identity supplies a two-sided identity.

## References

* B. Blackadar, *Operator Algebras*, Section II.1.2 (unitization).
* The minimal norm and the algebra homomorphism used here are Mathlib's
  `Unitization.norm_eq_sup` and `Unitization.lift`.
-/

public section

open ContinuousLinearMap

namespace Unitization

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
  [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A]
  [SMulCommClass 𝕜 A A] [CompleteSpace A]

/-- For a complete normed algebra without a left identity, the scalar coordinate is bounded
by the operator norm of the left action. -/
theorem norm_fst_le_norm_lift_Lmul_of_no_left_identity
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b) (u : Unitization 𝕜 A) :
    ‖u.fst‖ ≤ ‖lift (NonUnitalAlgHom.Lmul 𝕜 A) u‖ := by
  by_contra! h
  have hz : u.fst ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt h)
  let a : A := -u.fst⁻¹ • u.snd
  have hid : 1 - u.fst⁻¹ • lift (NonUnitalAlgHom.Lmul 𝕜 A) u = mul 𝕜 A a := by
    ext b
    simp [a, smul_add, smul_smul, hz]
  have hn : ‖u.fst⁻¹ • lift (NonUnitalAlgHom.Lmul 𝕜 A) u‖ < 1 := by
    rw [norm_smul, norm_inv, inv_mul_lt_iff₀ (norm_pos_iff.mpr hz), mul_one]
    exact h
  have hu := isUnit_one_sub_of_norm_lt_one hn
  rw [hid] at hu
  -- Invertibility of L_a supplies an identity inside A, not merely its unitization.
  obtain ⟨hinj, hsurj⟩ := ContinuousLinearMap.isUnit_iff_bijective.mp hu
  obtain ⟨e, he⟩ := hsurj a
  have hae : a * e = a := by simpa only [mul_apply'] using he
  have hleft (b : A) : e * b = b := by
    apply hinj
    simp only [mul_apply', ← mul_assoc, hae]
  exact hA ⟨e, hleft⟩

variable [StarRing A]

/-- For a complete star algebra without a two-sided identity, the scalar coordinate is bounded
by the operator norm of the left action. No C⋆-identity is needed for this inequality. -/
theorem norm_fst_le_norm_lift_Lmul
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (u : Unitization 𝕜 A) :
    ‖u.fst‖ ≤ ‖lift (NonUnitalAlgHom.Lmul 𝕜 A) u‖ := by
  apply norm_fst_le_norm_lift_Lmul_of_no_left_identity (u := u)
  rintro ⟨e, hleft⟩
  have hright (b : A) : b * star e = b := by
    simpa only [star_mul, star_star] using congrArg star (hleft (star b))
  have heStar : e = star e := (hright e).symm.trans (hleft (star e))
  exact hA ⟨e, fun b => ⟨hleft b, heStar ▸ hright b⟩⟩

variable [RegularNormedAlgebra 𝕜 A]

/-- The minimal unitization norm equals the norm of the left action when the complete regular
normed star algebra has no two-sided identity. This includes nonunital C⋆-algebras. -/
theorem norm_lift_Lmul
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (u : Unitization 𝕜 A) :
    ‖lift (NonUnitalAlgHom.Lmul 𝕜 A) u‖ = ‖u‖ := by
  rw [norm_eq_sup]
  exact (max_eq_right (norm_fst_le_norm_lift_Lmul hA u)).symm

/-- When `A` has no two-sided identity, the left action embeds the minimal unitization
isometrically into the bounded operators on `A`. -/
theorem isometry_lift_Lmul
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) :
    Isometry (lift (NonUnitalAlgHom.Lmul 𝕜 A)) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_lift_Lmul hA)

variable [CompleteSpace 𝕜]

/-- The left-action image of the minimal unitization of an algebra without identity is closed. -/
theorem isClosed_range_lift_Lmul
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) :
    IsClosed (Set.range (lift (NonUnitalAlgHom.Lmul 𝕜 A))) :=
  (isometry_lift_Lmul hA).isClosedEmbedding.isClosed_range

end Unitization
