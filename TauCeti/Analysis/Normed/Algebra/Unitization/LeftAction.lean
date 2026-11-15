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
`Unitization.rightAction 𝕜 A` is the `𝕜`-linear antimultiplicative map sending `(z, a)` to
`z • id + R_a`. If a complete normed algebra `A` has no left (respectively, right) identity—or has
an antimultiplicative involution and no two-sided identity—the scalar coordinate is bounded by the
operator norm of the corresponding action, with the right-handed statements deduced from `Aᵐᵒᵖ`.
When `A` is a regular normed algebra, left multiplication is faithful, so any left identity is
already two-sided without assuming an involution; consequently, the left action is faithful if and
only if `A` has no identity (without assuming completeness), embeds `Unitization 𝕜 A` isometrically
when `A` is complete and has no identity, and has closed image in `A →L[𝕜] A` when both `𝕜` and
`A` are complete.

The absence of an identity is essential for faithfulness and isometry:
* for an already unital algebra `A`, the external unitization acts through `(z, a) ↦ z • 1 + a`,
  so its image is `(AlgHom.Lmul 𝕜 A).range` and its kernel is `{(z, -z • 1)}`;
* for a subsingleton (zero) algebra `A`, `Unitization 𝕜 A` is isometrically isomorphic to `𝕜`
  with norm `‖u‖ = ‖u.fst‖`, while the left-action image is `{0}`.

For any normed algebra `A`, `Unitization.LeftAction 𝕜 A` is the subtype of the unital subalgebra
`(Unitization.lift (NonUnitalAlgHom.Lmul 𝕜 A)).range` of `A →L[𝕜] A`, inheriting its normed algebra
structure from `A →L[𝕜] A`, commutative when `A` is commutative, and complete when `𝕜` and `A` are
complete and `A` is regular. Although `A →L[𝕜] A` carries no ambient adjoint in general, every
operator `z • id + L_a` and its formal conjugate `star z • id + L_{star a}` satisfy the `A`-valued
adjoint identity `star ((z • id + L_a) x) * y = star x * ((star z • id + L_{star a}) y)`. When `A`
has a proper involution (`IsProperStar A`), this adjoint is uniquely determined by the operator
itself—even when `A` is unital or zero—equipping `Unitization.LeftAction 𝕜 A` with `StarRing` and
`StarModule` structures and the nonunital `⋆`-homomorphism `Unitization.LeftAction.Lmul` (which is
isometric when `A` is regular). When `A` is regular with proper involution and no two-sided
identity, `Unitization.starLift` of `Lmul` upgrades to `Unitization.starAlgEquivLeftAction :
Unitization 𝕜 A ≃⋆ₐ[𝕜] Unitization.LeftAction 𝕜 A`, which is isometric when `A` is complete.

## References

* B. Blackadar, *Operator Algebras*, Section II.1.2 (unitization).
* The minimal norm and the algebra lifts used here are Mathlib's `Unitization.norm_eq_sup`,
  `Unitization.lift`, and `Unitization.starLift`.
-/

public section

open ContinuousLinearMap

namespace Unitization

section Seminormed

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalSeminormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

variable (𝕜 A) in
/-- The right action of `Unitization 𝕜 A` on `A` by bounded linear operators, sending `(z, a)` to
`z • id + R_a`. It is `𝕜`-linear and antimultiplicative (`Unitization.rightAction_mul`). -/
noncomputable def rightAction : Unitization 𝕜 A →ₗ[𝕜] A →L[𝕜] A where
  toFun u := u.fst • ContinuousLinearMap.id 𝕜 A + (mul 𝕜 A).flip u.snd
  map_add' u v := by simp [add_smul, add_add_add_comm]
  map_smul' c u := by simp [mul_smul, smul_add]

@[simp]
theorem rightAction_apply (u : Unitization 𝕜 A) :
    rightAction 𝕜 A u = u.fst • ContinuousLinearMap.id 𝕜 A + (mul 𝕜 A).flip u.snd := (rfl)

/-- The right action of `Unitization 𝕜 A` reverses multiplication order:
`rightAction 𝕜 A (u * v) = rightAction 𝕜 A v * rightAction 𝕜 A u`. -/
theorem rightAction_mul (u v : Unitization 𝕜 A) :
    rightAction 𝕜 A (u * v) = rightAction 𝕜 A v * rightAction 𝕜 A u := by
  ext b
  simp [mul_smul, smul_add, mul_add, add_mul, mul_assoc]
  abel

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
of `Unitization.rightAction 𝕜 A` coincides with the range of right multiplication. -/
theorem range_rightAction_of_right_identity {e : A} (he : ∀ b : A, b * e = b) :
    Set.range (rightAction 𝕜 A) = Set.range (mul 𝕜 A).flip := by
  have he' (b : Aᵐᵒᵖ) : MulOpposite.op e * b = b :=
    MulOpposite.unop_injective (he b.unop)
  ext T
  refine ⟨?_, fun ⟨a, ha⟩ ↦ ⟨a, by simpa using ha⟩⟩
  rintro ⟨u, rfl⟩
  have hmem : lift (NonUnitalAlgHom.Lmul 𝕜 Aᵐᵒᵖ) (inl u.fst + inr (MulOpposite.op u.snd)) ∈
      Set.range (mul 𝕜 Aᵐᵒᵖ) := by
    rw [← range_lift_Lmul_of_left_identity he']
    exact ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := hmem
  refine ⟨a.unop, ?_⟩
  ext b
  have hb := congrArg MulOpposite.unop (DFunLike.congr_fun ha (MulOpposite.op b))
  simpa [Algebra.algebraMap_eq_smul_one] using hb

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
the operator norm of `Unitization.rightAction 𝕜 A u`. -/
theorem norm_fst_le_norm_rightAction_of_no_right_identity
    (hA : ¬ ∃ e : A, ∀ b : A, b * e = b) (u : Unitization 𝕜 A) :
    ‖u.fst‖ ≤ ‖rightAction 𝕜 A u‖ := by
  have hA' : ¬ ∃ e : Aᵐᵒᵖ, ∀ b : Aᵐᵒᵖ, e * b = b := fun ⟨e, he⟩ ↦
    hA ⟨e.unop, fun b ↦ MulOpposite.op_injective (he (MulOpposite.op b))⟩
  let u' : Unitization 𝕜 Aᵐᵒᵖ := inl u.fst + inr (MulOpposite.op u.snd)
  let T' : Aᵐᵒᵖ →L[𝕜] Aᵐᵒᵖ := lift (NonUnitalAlgHom.Lmul 𝕜 Aᵐᵒᵖ) u'
  have hfst : ‖u.fst‖ ≤ ‖T'‖ := by
    simpa [T', u'] using norm_fst_le_norm_lift_Lmul_of_no_left_identity hA' u'
  refine hfst.trans (opNorm_le_bound _ (norm_nonneg _) fun y ↦ ?_)
  have hy : T' y = MulOpposite.op (rightAction 𝕜 A u y.unop) := by
    simp [T', u', Algebra.algebraMap_eq_smul_one]
  rw [hy, MulOpposite.norm_op]
  simpa [MulOpposite.norm_unop] using (rightAction 𝕜 A u).le_opNorm y.unop

/-- For a complete normed algebra with an antimultiplicative involution and no two-sided identity,
the scalar coordinate is bounded by the operator norm of `Unitization.rightAction 𝕜 A u`. -/
theorem norm_fst_le_norm_rightAction [StarMul A]
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (u : Unitization 𝕜 A) :
    ‖u.fst‖ ≤ ‖rightAction 𝕜 A u‖ :=
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
theorem lift_Lmul_eq_zero (u : Unitization 𝕜 A) :
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

section Adjoint

/-- Every left-action operator `lift (NonUnitalAlgHom.Lmul 𝕜 A) u` and its formal conjugate at
`star u` are mutually adjoint with respect to `(x, y) ↦ star x * y`. -/
theorem star_lift_Lmul_apply_mul {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜]
    [NonUnitalSeminormedRing A] [StarRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A]
    [SMulCommClass 𝕜 A A] [StarModule 𝕜 A] (u : Unitization 𝕜 A) (x y : A) :
    star (lift (NonUnitalAlgHom.Lmul 𝕜 A) u x) * y =
      star x * lift (NonUnitalAlgHom.Lmul 𝕜 A) (star u) y := by
  simp [Algebra.algebraMap_eq_smul_one, star_add, star_smul, star_mul, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, mul_assoc]

/-- When `A` has a proper involution, the left action of `star u` depends only on the operator
`lift (NonUnitalAlgHom.Lmul 𝕜 A) u`, without assuming completeness or absence of an identity. -/
theorem lift_Lmul_star_eq_of_eq {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜]
    [NonUnitalNormedRing A] [StarRing A] [IsProperStar A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [StarModule 𝕜 A] {u v : Unitization 𝕜 A}
    (h : lift (NonUnitalAlgHom.Lmul 𝕜 A) u = lift (NonUnitalAlgHom.Lmul 𝕜 A) v) :
    lift (NonUnitalAlgHom.Lmul 𝕜 A) (star u) = lift (NonUnitalAlgHom.Lmul 𝕜 A) (star v) := by
  ext y
  refine MulOpposite.op_injective (FaithfulSMul.eq_of_smul_eq_smul (α := A) fun c ↦ ?_)
  rw [MulOpposite.smul_eq_mul_unop, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    MulOpposite.unop_op, ← star_star c, ← star_lift_Lmul_apply_mul,
    ← star_lift_Lmul_apply_mul, h]

end Adjoint

/-- The unital operator-norm subalgebra `{z • id + L_a : z ∈ 𝕜, a ∈ A}` of `A →L[𝕜] A` generated
by the identity and left multiplications, realized as the subtype of
`(Unitization.lift (NonUnitalAlgHom.Lmul 𝕜 A)).range`. Its `Ring`, `Module`, `Algebra`,
`NormedRing`, and `NormedAlgebra` structures are inherited from `Subalgebra`. -/
abbrev LeftAction (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
    [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] : Type _ :=
  (lift (NonUnitalAlgHom.Lmul 𝕜 A)).range

namespace LeftAction

section Normed

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- When `𝕜` and `A` are complete and `A` is regular, `LeftAction 𝕜 A` is complete in the
inherited operator norm because its carrier in `A →L[𝕜] A` is closed
(`isClosed_range_lift_Lmul`). -/
instance instCompleteSpace [CompleteSpace 𝕜] [RegularNormedAlgebra 𝕜 A] [CompleteSpace A] :
    CompleteSpace (LeftAction 𝕜 A) :=
  ((AlgHom.coe_range (lift (NonUnitalAlgHom.Lmul 𝕜 A))).symm ▸
    isClosed_range_lift_Lmul).completeSpace_coe

end Normed

section CommNormed

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedCommRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- When `A` is commutative, `LeftAction 𝕜 A` is a commutative normed ring even though the ambient
endomorphism ring `A →L[𝕜] A` need not be commutative. -/
noncomputable instance instNormedCommRing : NormedCommRing (LeftAction 𝕜 A) :=
  { (inferInstance : NormedRing (LeftAction 𝕜 A)) with
    mul_comm := fun S T ↦ by
      obtain ⟨u, hu⟩ := (AlgHom.mem_range _).mp S.2
      obtain ⟨v, hv⟩ := (AlgHom.mem_range _).mp T.2
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_mul, ← hu, ← hv, ← map_mul, mul_comm u v, map_mul] }

end CommNormed

section Star

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NonUnitalNormedRing A]
  [StarRing A] [IsProperStar A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A]
  [SMulCommClass 𝕜 A A] [StarModule 𝕜 A]

/-- On an algebra with proper involution, `star` on `LeftAction 𝕜 A` is transported along the
surjection `lift (NonUnitalAlgHom.Lmul 𝕜 A)` (`lift_Lmul_star_eq_of_eq`). -/
noncomputable instance instStar : Star (LeftAction 𝕜 A) where
  star T := ⟨lift (NonUnitalAlgHom.Lmul 𝕜 A) (star ((AlgHom.mem_range _).mp T.2).choose),
    (lift (NonUnitalAlgHom.Lmul 𝕜 A)).mem_range_self _⟩

/-- For any preimage `u` of `T` under `lift (NonUnitalAlgHom.Lmul 𝕜 A)`, the transported
involution on `LeftAction 𝕜 A` evaluates in `A →L[𝕜] A` as the left action of `star u`. -/
theorem coe_star_of_eq {T : LeftAction 𝕜 A} {u : Unitization 𝕜 A}
    (hu : lift (NonUnitalAlgHom.Lmul 𝕜 A) u = (T : A →L[𝕜] A)) :
    ((star T : LeftAction 𝕜 A) : A →L[𝕜] A) = lift (NonUnitalAlgHom.Lmul 𝕜 A) (star u) :=
  -- `instStar` above defines `↑(star T)` as the left action of `star` of the chosen preimage.
  lift_Lmul_star_eq_of_eq (((AlgHom.mem_range _).mp T.2).choose_spec.trans hu.symm)

noncomputable instance instStarRing : StarRing (LeftAction 𝕜 A) where
  star_involutive T := by
    obtain ⟨u, hu⟩ := (AlgHom.mem_range _).mp T.2
    apply Subtype.ext
    have hs : lift (NonUnitalAlgHom.Lmul 𝕜 A) (star u) =
        ((star T : LeftAction 𝕜 A) : A →L[𝕜] A) :=
      (coe_star_of_eq hu).symm
    rw [coe_star_of_eq hs, star_star, hu]
  star_mul S T := by
    obtain ⟨u, hu⟩ := (AlgHom.mem_range _).mp S.2
    obtain ⟨v, hv⟩ := (AlgHom.mem_range _).mp T.2
    apply Subtype.ext
    have huv : lift (NonUnitalAlgHom.Lmul 𝕜 A) (u * v) =
        ((S * T : LeftAction 𝕜 A) : A →L[𝕜] A) := by
      rw [map_mul, hu, hv, Subalgebra.coe_mul]
    rw [coe_star_of_eq huv, StarMul.star_mul u v, map_mul, Subalgebra.coe_mul,
      coe_star_of_eq hv, coe_star_of_eq hu]
  star_add S T := by
    obtain ⟨u, hu⟩ := (AlgHom.mem_range _).mp S.2
    obtain ⟨v, hv⟩ := (AlgHom.mem_range _).mp T.2
    apply Subtype.ext
    have huv : lift (NonUnitalAlgHom.Lmul 𝕜 A) (u + v) =
        ((S + T : LeftAction 𝕜 A) : A →L[𝕜] A) := by
      rw [map_add, hu, hv, Subalgebra.coe_add]
    rw [coe_star_of_eq huv, StarAddMonoid.star_add u v, map_add, Subalgebra.coe_add,
      coe_star_of_eq hu, coe_star_of_eq hv]

/-- Every operator in `LeftAction 𝕜 A` and its involution are mutually adjoint for
`(x, y) ↦ star x * y`. -/
theorem star_apply_mul (T : LeftAction 𝕜 A) (x y : A) :
    star ((T : A →L[𝕜] A) x) * y = star x * ((star T : LeftAction 𝕜 A) : A →L[𝕜] A) y := by
  obtain ⟨u, hu⟩ := (AlgHom.mem_range _).mp T.2
  rw [coe_star_of_eq hu, ← hu]
  exact star_lift_Lmul_apply_mul u x y

instance instStarModule : StarModule 𝕜 (LeftAction 𝕜 A) where
  star_smul c T := by
    obtain ⟨u, hu⟩ := (AlgHom.mem_range _).mp T.2
    apply Subtype.ext
    have hcu : lift (NonUnitalAlgHom.Lmul 𝕜 A) (c • u) =
        ((c • T : LeftAction 𝕜 A) : A →L[𝕜] A) := by
      rw [map_smul, hu, SetLike.val_smul]
    rw [coe_star_of_eq hcu, StarModule.star_smul, map_smul, SetLike.val_smul, coe_star_of_eq hu]

variable (𝕜 A) in
/-- Left multiplication as a nonunital `⋆`-algebra homomorphism into `LeftAction 𝕜 A`. -/
noncomputable def Lmul : A →⋆ₙₐ[𝕜] LeftAction 𝕜 A where
  toFun a := ⟨mul 𝕜 A a, (AlgHom.mem_range _).mpr ⟨a, by simp⟩⟩
  map_smul' c a := Subtype.ext (map_smul (NonUnitalAlgHom.Lmul 𝕜 A) c a)
  map_zero' := Subtype.ext (map_zero (NonUnitalAlgHom.Lmul 𝕜 A))
  map_add' a b := Subtype.ext (map_add (NonUnitalAlgHom.Lmul 𝕜 A) a b)
  map_mul' a b := Subtype.ext (map_mul (NonUnitalAlgHom.Lmul 𝕜 A) a b)
  map_star' a := by
    apply Subtype.ext
    have ha : lift (NonUnitalAlgHom.Lmul 𝕜 A) (a : Unitization 𝕜 A) = mul 𝕜 A a := by simp
    simpa [← inr_star] using
      (coe_star_of_eq (T := ⟨mul 𝕜 A a, (AlgHom.mem_range _).mpr ⟨a, by simp⟩⟩) ha).symm

@[simp]
theorem coe_Lmul (a : A) : ((Lmul 𝕜 A a : LeftAction 𝕜 A) : A →L[𝕜] A) = mul 𝕜 A a := (rfl)

/-- Left multiplication into `LeftAction 𝕜 A` preserves norms in any regular normed algebra
(including `a = 0`). -/
theorem norm_Lmul [RegularNormedAlgebra 𝕜 A] (a : A) :
    ‖Lmul 𝕜 A a‖ = ‖a‖ := by
  simp

/-- Left multiplication into `LeftAction 𝕜 A` is an isometry in any regular normed algebra. -/
theorem isometry_Lmul [RegularNormedAlgebra 𝕜 A] :
    Isometry (Lmul 𝕜 A) :=
  AddMonoidHomClass.isometry_of_norm (Lmul 𝕜 A).toNonUnitalAlgHom norm_Lmul

/-- By uniqueness of lifts from `Unitization 𝕜 A`, the underlying algebra homomorphism of
`Unitization.starLift (LeftAction.Lmul 𝕜 A)` equals
`(lift (NonUnitalAlgHom.Lmul 𝕜 A)).rangeRestrict`. -/
theorem toAlgHom_starLift_Lmul :
    (starLift (Lmul 𝕜 A)).toAlgHom = (lift (NonUnitalAlgHom.Lmul 𝕜 A)).rangeRestrict :=
  algHom_ext'' fun a ↦ Subtype.ext (by simp)

/-- Evaluating `Unitization.starLift (LeftAction.Lmul 𝕜 A)` in `A →L[𝕜] A` produces
`u.fst • id + L_{u.snd}`. -/
theorem coe_starLift_Lmul (u : Unitization 𝕜 A) :
    ((starLift (Lmul 𝕜 A) u : LeftAction 𝕜 A) : A →L[𝕜] A) =
      u.fst • ContinuousLinearMap.id 𝕜 A + mul 𝕜 A u.snd := by
  have h : ((starLift (Lmul 𝕜 A) u : LeftAction 𝕜 A) : A →L[𝕜] A) =
      lift (NonUnitalAlgHom.Lmul 𝕜 A) u := by
    simpa only [← StarAlgHom.coe_toAlgHom, AlgHom.coe_codRestrict] using
      congrArg (fun φ : Unitization 𝕜 A →ₐ[𝕜] LeftAction 𝕜 A ↦ (φ u : A →L[𝕜] A))
        toAlgHom_starLift_Lmul
  rw [h, lift_apply, NonUnitalAlgHom.toAlgHom_apply, Algebra.algebraMap_eq_smul_one,
    ContinuousLinearMap.one_def, NonUnitalAlgHom.coe_Lmul]

/-- The `⋆`-lift of `LeftAction.Lmul 𝕜 A` maps `Unitization 𝕜 A` surjectively onto
`LeftAction 𝕜 A`. -/
theorem starLift_Lmul_surjective :
    Function.Surjective (starLift (Lmul 𝕜 A)) := by
  intro T
  obtain ⟨u, hu⟩ := (lift (NonUnitalAlgHom.Lmul 𝕜 A)).rangeRestrict_surjective T
  refine ⟨u, ?_⟩
  rw [← StarAlgHom.coe_toAlgHom, toAlgHom_starLift_Lmul, hu]

end Star

end LeftAction

section Equiv

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NonUnitalNormedRing A]
  [StarRing A] [IsProperStar A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A]
  [SMulCommClass 𝕜 A A] [StarModule 𝕜 A] [RegularNormedAlgebra 𝕜 A]

/-- When `A` is a regular normed star algebra with proper involution and no two-sided identity,
`Unitization.starLift (LeftAction.Lmul 𝕜 A)` is a `⋆`-algebra equivalence onto `LeftAction 𝕜 A`. -/
noncomputable def starAlgEquivLeftAction
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) :
    Unitization 𝕜 A ≃⋆ₐ[𝕜] LeftAction 𝕜 A :=
  StarAlgEquiv.ofBijective (starLift (LeftAction.Lmul 𝕜 A))
    ⟨fun u v huv ↦ (injective_lift_Lmul_iff.mpr hA) <| by
      have h := congrArg (fun T : LeftAction 𝕜 A ↦ (T : A →L[𝕜] A)) huv
      simpa only [← StarAlgHom.coe_toAlgHom, LeftAction.toAlgHom_starLift_Lmul,
        AlgHom.coe_codRestrict] using h,
    LeftAction.starLift_Lmul_surjective⟩

@[simp]
theorem toStarAlgHom_starAlgEquivLeftAction
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) :
    (starAlgEquivLeftAction (𝕜 := 𝕜) hA).toStarAlgHom = starLift (LeftAction.Lmul 𝕜 A) := (rfl)

@[simp]
theorem coe_starAlgEquivLeftAction
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (u : Unitization 𝕜 A) :
    ((starAlgEquivLeftAction (𝕜 := 𝕜) hA u : LeftAction 𝕜 A) : A →L[𝕜] A) =
      u.fst • ContinuousLinearMap.id 𝕜 A + mul 𝕜 A u.snd :=
  LeftAction.coe_starLift_Lmul u

@[simp]
theorem starAlgEquivLeftAction_inr
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (a : A) :
    starAlgEquivLeftAction (𝕜 := 𝕜) hA (a : Unitization 𝕜 A) = LeftAction.Lmul 𝕜 A a :=
  Subtype.ext (by simp)

@[simp]
theorem starAlgEquivLeftAction_symm_Lmul
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (a : A) :
    (starAlgEquivLeftAction (𝕜 := 𝕜) hA).symm (LeftAction.Lmul 𝕜 A a) = (a : Unitization 𝕜 A) :=
  (starAlgEquivLeftAction (𝕜 := 𝕜) hA).symm_apply_eq.mpr (starAlgEquivLeftAction_inr hA a).symm

/-- When `A` is complete and has no two-sided identity, `Unitization.starAlgEquivLeftAction`
preserves norms. -/
theorem norm_starAlgEquivLeftAction [CompleteSpace A]
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (u : Unitization 𝕜 A) :
    ‖starAlgEquivLeftAction (𝕜 := 𝕜) hA u‖ = ‖u‖ := by
  rw [AddSubgroupClass.coe_norm, coe_starAlgEquivLeftAction, ← ContinuousLinearMap.one_def,
    ← Algebra.algebraMap_eq_smul_one, ← NonUnitalAlgHom.coe_Lmul,
    ← NonUnitalAlgHom.toAlgHom_apply, ← lift_apply, norm_lift_Lmul hA u]

/-- When `A` is complete and has no two-sided identity, `Unitization.starAlgEquivLeftAction` is
an isometry. -/
theorem isometry_starAlgEquivLeftAction [CompleteSpace A]
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) :
    Isometry (starAlgEquivLeftAction (𝕜 := 𝕜) hA) :=
  AddMonoidHomClass.isometry_of_norm (starAlgEquivLeftAction (𝕜 := 𝕜) hA).toStarAlgHom.toAlgHom
    (norm_starAlgEquivLeftAction hA)

end Equiv

end Unitization
