/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Unitization
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.SpecificLimits.Normed
public import TauCeti.Algebra.Algebra.Unitization
public import TauCeti.Algebra.Star.Basic
public import TauCeti.Analysis.Normed.Operator.Mul

/-!
# The left and right actions of the minimal unitization

The canonical left action of `Unitization 𝕜 A` on `A` is Mathlib's
`Unitization.lift (NonUnitalAlgHom.Lmul 𝕜 A)`, sending `(z, a)` to `z • id + L_a`; symmetrically,
`(z, a)` acts on the right as `z • id + R_a`. If a complete normed algebra `A` has no left
(respectively, right) identity—or has an antimultiplicative involution and no two-sided
identity—the scalar coordinate is bounded by the operator norm of the corresponding action. When
`A` is a regular normed algebra, left multiplication is faithful, so any left identity is already
two-sided without assuming an involution; consequently, the left action is faithful if and only if
`A` has no identity, embeds `Unitization 𝕜 A` isometrically when `A` is complete and has no
identity, and always has closed image in `A →L[𝕜] A` when `𝕜` and `A` are complete.

The absence of an identity is essential for faithfulness and isometry:
* for an already unital algebra `A`, the external unitization acts through `(z, a) ↦ z • 1 + a`,
  so its image is `(AlgHom.Lmul 𝕜 A).range` and its kernel is `{(z, -z • 1)}`;
* for a subsingleton (zero) algebra `A`, `Unitization 𝕜 A` is isometrically isomorphic to `𝕜`
  with norm `‖u‖ = ‖u.fst‖`, while the left-action image is `{0}`.

The norm comparison uses the Neumann-series criterion: if the scalar part had larger norm than the
action, a multiplication operator would be invertible, forcing a one-sided identity inside `A`.

## References

* B. Blackadar, *Operator Algebras*, Section II.1.2 (unitization).
* The minimal norm and the algebra homomorphism used here are Mathlib's
  `Unitization.norm_eq_sup` and `Unitization.lift`.
-/

public section

open ContinuousLinearMap

namespace Unitization

section Seminormed

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalSeminormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- When `A` has a left identity `e`, the scalar term `z • id` equals `L_{z • e}`, so the image
of `Unitization.lift (NonUnitalAlgHom.Lmul 𝕜 A)` coincides with the range of left multiplication. -/
theorem range_lift_Lmul_of_left_identity {e : A} (he : ∀ b : A, e * b = b) :
    Set.range (lift (NonUnitalAlgHom.Lmul 𝕜 A)) = Set.range (mul 𝕜 A) := by
  ext T
  refine ⟨?_, ?_⟩
  · rintro ⟨u, rfl⟩
    refine ⟨u.fst • e + u.snd, ?_⟩
    ext b
    simp [Algebra.algebraMap_eq_smul_one, he b]
  · rintro ⟨a, rfl⟩
    exact ⟨a, by simp⟩

/-- When `A` has a right identity `e`, the scalar term `z • id` equals `R_{z • e}`, so the image
of `(z, a) ↦ z • id + R_a` coincides with the range of right multiplication. -/
theorem range_rightAction_of_right_identity {e : A} (he : ∀ b : A, b * e = b) :
    (Set.range fun u : Unitization 𝕜 A ↦
      u.fst • ContinuousLinearMap.id 𝕜 A + (mul 𝕜 A).flip u.snd) =
      Set.range (mul 𝕜 A).flip := by
  ext T
  refine ⟨?_, ?_⟩
  · rintro ⟨u, rfl⟩
    refine ⟨u.fst • e + u.snd, ?_⟩
    ext b
    simp [he b]
  · rintro ⟨a, rfl⟩
    exact ⟨a, by simp⟩

end Seminormed

section Normed

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
  [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

section Injectivity

variable [RegularNormedAlgebra 𝕜 A]

/-- In a regular normed algebra, the left action of `Unitization 𝕜 A` is injective if and only if
`A` has no left identity; completeness is not needed. -/
theorem injective_lift_Lmul_iff_no_left_identity :
    Function.Injective (lift (NonUnitalAlgHom.Lmul 𝕜 A)) ↔ ¬ ∃ e : A, ∀ b : A, e * b = b := by
  rw [injective_iff_map_eq_zero]
  refine ⟨fun hinj ⟨e, he⟩ ↦ ?_, fun hA u hu ↦ ?_⟩
  · have h0 : lift (NonUnitalAlgHom.Lmul 𝕜 A) (inl (1 : 𝕜) - (e : Unitization 𝕜 A)) = 0 := by
      ext b
      simp [he b]
    have h1 : (1 : 𝕜) = 0 := by simpa using congrArg (·.fst) (hinj _ h0)
    exact one_ne_zero h1
  · by_cases hz : u.fst = 0
    · have hsnd : mul 𝕜 A u.snd = 0 := by simpa [hz] using hu
      exact Unitization.ext hz ((isometry_mul 𝕜 A).injective (by simpa using hsnd))
    · refine (hA ⟨-u.fst⁻¹ • u.snd, fun b ↦ ?_⟩).elim
      have hb : u.fst • b + u.snd * b = 0 := by
        simpa [Algebra.algebraMap_eq_smul_one] using DFunLike.congr_fun hu b
      have hmul : u.snd * b = -(u.fst • b) := eq_neg_of_add_eq_zero_right hb
      simp [smul_mul_assoc, hmul, smul_smul, hz]

/-- In a regular normed algebra, the left action of `Unitization 𝕜 A` is injective if and only if
`A` has no two-sided identity; neither completeness nor an involution is needed. -/
theorem injective_lift_Lmul_iff :
    Function.Injective (lift (NonUnitalAlgHom.Lmul 𝕜 A)) ↔
      ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b := by
  rw [injective_lift_Lmul_iff_no_left_identity, RegularNormedAlgebra.exists_left_identity_iff 𝕜]

end Injectivity

section Complete

variable [CompleteSpace A]

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

/-- For a complete algebra with an antimultiplicative involution and no two-sided identity, the
scalar coordinate is bounded by the operator norm of the left action. No C⋆-identity is needed
for this inequality. -/
theorem norm_fst_le_norm_lift_Lmul [StarMul A]
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (u : Unitization 𝕜 A) :
    ‖u.fst‖ ≤ ‖lift (NonUnitalAlgHom.Lmul 𝕜 A) u‖ :=
  norm_fst_le_norm_lift_Lmul_of_no_left_identity (mt TauCeti.exists_left_identity_iff.mp hA) u

/-- For a complete normed algebra without a right identity, the scalar coordinate is bounded by
the operator norm of the right action `u.fst • id + R_{u.snd}`. -/
theorem norm_fst_le_norm_rightAction_of_no_right_identity
    (hA : ¬ ∃ e : A, ∀ b : A, b * e = b) (u : Unitization 𝕜 A) :
    ‖u.fst‖ ≤ ‖u.fst • ContinuousLinearMap.id 𝕜 A + (mul 𝕜 A).flip u.snd‖ := by
  by_contra! h
  have hz : u.fst ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt h)
  let a : A := -u.fst⁻¹ • u.snd
  let T : A →L[𝕜] A := u.fst • ContinuousLinearMap.id 𝕜 A + (mul 𝕜 A).flip u.snd
  have hid : 1 - u.fst⁻¹ • T = (mul 𝕜 A).flip a := by
    ext b
    simp [T, a, smul_add, smul_smul, hz]
  have hn : ‖u.fst⁻¹ • T‖ < 1 := by
    rw [norm_smul, norm_inv, inv_mul_lt_iff₀ (norm_pos_iff.mpr hz), mul_one]
    exact h
  have hu := isUnit_one_sub_of_norm_lt_one hn
  rw [hid] at hu
  obtain ⟨hinj, hsurj⟩ := ContinuousLinearMap.isUnit_iff_bijective.mp hu
  obtain ⟨e, he⟩ := hsurj a
  have hea : e * a = a := by simpa only [flip_apply, mul_apply'] using he
  have hright (b : A) : b * e = b := by
    apply hinj
    simp only [flip_apply, mul_apply', mul_assoc, hea]
  exact hA ⟨e, hright⟩

/-- For a complete normed algebra with an antimultiplicative involution and no two-sided identity,
the scalar coordinate is bounded by the operator norm of `u.fst • id + R_{u.snd}`. -/
theorem norm_fst_le_norm_rightAction [StarMul A]
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (u : Unitization 𝕜 A) :
    ‖u.fst‖ ≤ ‖u.fst • ContinuousLinearMap.id 𝕜 A + (mul 𝕜 A).flip u.snd‖ :=
  norm_fst_le_norm_rightAction_of_no_right_identity (mt TauCeti.exists_right_identity_iff.mp hA) u

variable [RegularNormedAlgebra 𝕜 A]

/-- The minimal unitization norm equals the norm of the left action when a complete regular
normed algebra has no left identity. -/
theorem norm_lift_Lmul_of_no_left_identity
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b) (u : Unitization 𝕜 A) :
    ‖lift (NonUnitalAlgHom.Lmul 𝕜 A) u‖ = ‖u‖ := by
  rw [norm_eq_sup]
  exact (max_eq_right (norm_fst_le_norm_lift_Lmul_of_no_left_identity hA u)).symm

/-- When `A` has no left identity, the left action embeds the minimal unitization isometrically
into the bounded operators on `A`. -/
theorem isometry_lift_Lmul_of_no_left_identity
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b) :
    Isometry (lift (NonUnitalAlgHom.Lmul 𝕜 A)) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_lift_Lmul_of_no_left_identity hA)

/-- The minimal unitization norm equals the norm of the left action when the complete regular
normed algebra has no two-sided identity. This includes nonunital C⋆-algebras. -/
theorem norm_lift_Lmul
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (u : Unitization 𝕜 A) :
    ‖lift (NonUnitalAlgHom.Lmul 𝕜 A) u‖ = ‖u‖ :=
  norm_lift_Lmul_of_no_left_identity
    (mt (RegularNormedAlgebra.exists_left_identity_iff 𝕜).mp hA) u

/-- When `A` has no two-sided identity, the left action embeds the minimal unitization
isometrically into the bounded operators on `A`. -/
theorem isometry_lift_Lmul
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) :
    Isometry (lift (NonUnitalAlgHom.Lmul 𝕜 A)) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_lift_Lmul hA)

/-- For any complete regular normed algebra over a complete field, the left-action image of
`Unitization 𝕜 A` in `A →L[𝕜] A` is closed: if `A` has a left identity it equals the isometric
image of `mul 𝕜 A`, and otherwise `lift (NonUnitalAlgHom.Lmul 𝕜 A)` is itself an isometry. -/
theorem isClosed_range_lift_Lmul [CompleteSpace 𝕜] :
    IsClosed (Set.range (lift (NonUnitalAlgHom.Lmul 𝕜 A))) := by
  by_cases hA : ∃ e : A, ∀ b : A, e * b = b
  · obtain ⟨e, he⟩ := hA
    rw [range_lift_Lmul_of_left_identity he]
    exact (isometry_mul 𝕜 A).isClosedEmbedding.isClosed_range
  · exact (isometry_lift_Lmul_of_no_left_identity hA).isClosedEmbedding.isClosed_range

end Complete

end Normed

section Unital

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [SeminormedRing A] [NormedAlgebra 𝕜 A]

/-- On an already unital algebra `A`, the left action of `Unitization 𝕜 A` factors as the
collapsing map `(z, a) ↦ z • 1 + a` followed by the unital left regular representation
`AlgHom.Lmul 𝕜 A`. -/
theorem lift_Lmul_eq_Lmul_comp :
    lift (NonUnitalAlgHom.Lmul 𝕜 A) = (AlgHom.Lmul 𝕜 A).comp (lift (NonUnitalAlgHom.id 𝕜 A)) :=
  algHom_ext'' fun a ↦ by ext b; simp

/-- On an already unital algebra `A`, the left-action subalgebra of `Unitization 𝕜 A` coincides
with the left regular representation `(AlgHom.Lmul 𝕜 A).range`. -/
theorem range_lift_Lmul_eq_range_Lmul :
    (lift (NonUnitalAlgHom.Lmul 𝕜 A)).range = (AlgHom.Lmul 𝕜 A).range := by
  ext T
  refine ⟨?_, ?_⟩
  · rintro ⟨u, rfl⟩
    rw [lift_Lmul_eq_Lmul_comp]
    exact ⟨_, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by simp⟩

/-- On an already unital algebra `A`, an element `(z, a)` of `Unitization 𝕜 A` acts as zero on the
left if and only if `a = -algebraMap 𝕜 A z`. -/
theorem mem_ker_lift_Lmul_iff (u : Unitization 𝕜 A) :
    u ∈ RingHom.ker (lift (NonUnitalAlgHom.Lmul 𝕜 A)) ↔ u.snd = -algebraMap 𝕜 A u.fst := by
  rw [RingHom.mem_ker, lift_Lmul_eq_Lmul_comp, AlgHom.comp_apply,
    ← map_zero (AlgHom.Lmul 𝕜 A), (AlgHom.Lmul_injective 𝕜 A).eq_iff]
  exact ⟨fun h ↦ eq_neg_of_add_eq_zero_right (by simpa using h), fun h ↦ by simp [h]⟩

/-- On an already unital algebra `A`, the kernel of the left action of `Unitization 𝕜 A` is
`{(z, -z • 1) : z ∈ 𝕜}`. -/
theorem ker_lift_Lmul_eq_range :
    (RingHom.ker (lift (NonUnitalAlgHom.Lmul 𝕜 A)) : Set (Unitization 𝕜 A)) =
      Set.range fun c : 𝕜 ↦ (inl c : Unitization 𝕜 A) - (algebraMap 𝕜 A c : Unitization 𝕜 A) := by
  ext u
  rw [SetLike.mem_coe, mem_ker_lift_Lmul_iff, Set.mem_range]
  refine ⟨fun hu ↦ ⟨u.fst, ?_⟩, ?_⟩
  · ext
    · simp
    · simp [hu]
  · rintro ⟨c, rfl⟩
    simp

end Unital

section Subsingleton

section SeminormedSubsingleton

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalSeminormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [Subsingleton A]

/-- On a subsingleton algebra, every element of `Unitization 𝕜 A` acts as the zero operator. -/
theorem lift_Lmul_apply_eq_zero (u : Unitization 𝕜 A) :
    lift (NonUnitalAlgHom.Lmul 𝕜 A) u = 0 :=
  Subsingleton.elim _ _

/-- On a subsingleton algebra, the left-action image of `Unitization 𝕜 A` is `{0}`. -/
theorem range_lift_Lmul_eq_singleton_zero :
    Set.range (lift (NonUnitalAlgHom.Lmul 𝕜 A)) = {0} := by
  ext T
  simp only [Set.mem_range, Set.mem_singleton_iff, Subsingleton.elim T 0]
  exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- On a subsingleton algebra over a nontrivially normed field, the left action of
`Unitization 𝕜 A` is not injective. -/
theorem not_injective_lift_Lmul :
    ¬ Function.Injective (lift (NonUnitalAlgHom.Lmul 𝕜 A)) := by
  intro hinj
  have h : (inl 1 : Unitization 𝕜 A) = 0 := hinj (Subsingleton.elim _ _)
  exact one_ne_zero (congrArg (·.fst) h)

end SeminormedSubsingleton

section NormedSubsingleton

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [Subsingleton A]

/-- On a subsingleton normed algebra, the minimal unitization norm is the norm of the scalar
coordinate. -/
@[simp]
theorem norm_eq_norm_fst (u : Unitization 𝕜 A) : ‖u‖ = ‖u.fst‖ := by
  rw [norm_eq_sup, Subsingleton.elim (algebraMap 𝕜 (A →L[𝕜] A) u.fst + mul 𝕜 A u.snd) 0,
    norm_zero, max_eq_left (norm_nonneg _)]

/-- On a subsingleton normed algebra, the augmentation `Unitization.fstHom` is an isometry. -/
theorem isometry_fstHom : Isometry (fstHom 𝕜 A) :=
  AddMonoidHomClass.isometry_of_norm _ fun u ↦ (norm_eq_norm_fst u).symm

/-- On a subsingleton normed algebra, `Unitization.fstAlgEquiv` is an isometry. -/
theorem isometry_fstAlgEquiv : Isometry (fstAlgEquiv 𝕜 A) :=
  AddMonoidHomClass.isometry_of_norm _ fun u ↦ by simp

/-- On a subsingleton normed star algebra, `Unitization.fstStarAlgEquiv` is an isometry. -/
theorem isometry_fstStarAlgEquiv [Star 𝕜] [Star A] : Isometry (fstStarAlgEquiv 𝕜 A) :=
  AddMonoidHomClass.isometry_of_norm _ fun u ↦ by simp

end NormedSubsingleton

end Subsingleton

end Unitization
