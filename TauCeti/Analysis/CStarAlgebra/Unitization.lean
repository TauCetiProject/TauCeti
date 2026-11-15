/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Algebra.Star.Basic
public import TauCeti.Analysis.Normed.Algebra.Unitization.LeftAction

/-!
# C⋆-algebra structure of the left-action unitization

For a nonunital normed algebra `A` over `𝕜`, `Unitization.LeftAction 𝕜 A` is the unital
subalgebra `{z • id + L_a : z ∈ 𝕜, a ∈ A}` of `A →L[𝕜] A`, equipped with the inherited operator
norm. Although `A →L[𝕜] A` carries no ambient Hilbert-space adjoint in general, every operator
`z • id + L_a` and its formal conjugate `star z • id + L_{star a}` satisfy the `A`-valued
adjoint identity

`star ((z • id + L_a) x) * y = star x * ((star z • id + L_{star a}) y)`.

When `A` has a proper involution (`IsProperStar A`, in particular for every C⋆-ring), this
adjoint is uniquely determined by the operator itself—even when `A` is unital or zero and the
representation of `Unitization 𝕜 A` is not faithful. Transporting `star` along the surjection
`Unitization.lift (NonUnitalAlgHom.Lmul 𝕜 A)` therefore equips `Unitization.LeftAction 𝕜 A`
unconditionally with `StarRing` and `StarModule` structures, a C⋆-norm (via
`Unitization.norm_splitMul_snd_sq`), and, over `ℂ`, a `CStarAlgebra` structure.

Left multiplication bundles as an isometric nonunital `⋆`-homomorphism
`Unitization.LeftAction.Lmul : A →⋆ₙₐ[𝕜] Unitization.LeftAction 𝕜 A`. By the universal property
`Unitization.starAlgHom_ext`, `Unitization.starLift` of `Lmul` sends `(z, a)` to `z • id + L_a`.
When `A` has no two-sided identity, this lift upgrades to an isometric `⋆`-algebra equivalence
`Unitization.starAlgEquivLeftAction`. Conjugating by an isometric involution also expresses the
unitization norm in terms of the right action `z • id + R_a` and shows that the right-action image
in `A →L[𝕜] A` is closed.

## References

* B. Blackadar, *Operator Algebras*, Section II.1.2.
-/

public section

open ContinuousLinearMap

namespace Unitization

section RightAction

/-- Conjugating by an isometric involution identifies the operator norm of the right action
`c • id + R_a` with that of `star c • id + L_{star a}`. -/
theorem norm_smul_id_add_mul_flip {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [Star 𝕜]
    [NonUnitalSeminormedRing A] [StarRing A] [NormedStarGroup A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [StarModule 𝕜 A] (c : 𝕜) (a : A) :
    ‖c • ContinuousLinearMap.id 𝕜 A + (mul 𝕜 A).flip a‖ =
      ‖star c • ContinuousLinearMap.id 𝕜 A + mul 𝕜 A (star a)‖ := by
  have hconj (x : A) :
      star ((c • ContinuousLinearMap.id 𝕜 A + (mul 𝕜 A).flip a) (star x)) =
        (star c • ContinuousLinearMap.id 𝕜 A + mul 𝕜 A (star a)) x := by
    simp [star_add, star_smul, star_mul]
  refine le_antisymm ?_ ?_
  · refine opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    have hx := hconj (star x)
    rw [star_star] at hx
    rw [← norm_star, hx]
    simpa [norm_star] using
      (star c • ContinuousLinearMap.id 𝕜 A + mul 𝕜 A (star a)).le_opNorm (star x)
  · refine opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    rw [← hconj x, norm_star]
    simpa [norm_star] using
      (c • ContinuousLinearMap.id 𝕜 A + (mul 𝕜 A).flip a).le_opNorm (star x)

/-- For any C⋆-algebra `A` (with or without identity or completeness), the C⋆-norm on
`Unitization 𝕜 A` is the supremum of `‖u.fst‖` and the operator norm of the right action
`u.fst • id + R_{u.snd}`. -/
theorem norm_eq_sup_rightAction {𝕜 A : Type*} [DenselyNormedField 𝕜] [StarRing 𝕜] [CStarRing 𝕜]
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [StarModule 𝕜 A] (u : Unitization 𝕜 A) :
    ‖u‖ = ‖u.fst‖ ⊔ ‖u.fst • ContinuousLinearMap.id 𝕜 A + (mul 𝕜 A).flip u.snd‖ := by
  have hL : algebraMap 𝕜 (A →L[𝕜] A) (star u.fst) + mul 𝕜 A (star u.snd) =
      star u.fst • ContinuousLinearMap.id 𝕜 A + mul 𝕜 A (star u.snd) := by
    rw [Algebra.algebraMap_eq_smul_one]
    rfl
  rw [← norm_star u, norm_eq_sup, fst_star, norm_star, snd_star, hL,
    ← norm_smul_id_add_mul_flip]

/-- In a complete C⋆-algebra without a two-sided identity, the C⋆-norm of `u : Unitization 𝕜 A`
equals the operator norm of its right action `u.fst • id + R_{u.snd}`. -/
theorem norm_rightAction_eq_norm {𝕜 A : Type*} [DenselyNormedField 𝕜] [StarRing 𝕜] [CStarRing 𝕜]
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [StarModule 𝕜 A] [CompleteSpace A]
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (u : Unitization 𝕜 A) :
    ‖u.fst • ContinuousLinearMap.id 𝕜 A + (mul 𝕜 A).flip u.snd‖ = ‖u‖ := by
  rw [norm_eq_sup_rightAction]
  exact (max_eq_right (norm_fst_le_norm_rightAction hA u)).symm

/-- When a complete C⋆-algebra `A` has no two-sided identity, the right action
`u ↦ u.fst • id + R_{u.snd}` is an isometry from `Unitization 𝕜 A` into `A →L[𝕜] A`. -/
theorem isometry_rightAction {𝕜 A : Type*} [DenselyNormedField 𝕜] [StarRing 𝕜] [CStarRing 𝕜]
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [StarModule 𝕜 A] [CompleteSpace A]
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) :
    Isometry (fun u : Unitization 𝕜 A ↦
      u.fst • ContinuousLinearMap.id 𝕜 A + (mul 𝕜 A).flip u.snd) := by
  refine Isometry.of_dist_eq fun u v ↦ ?_
  have hsub : (u.fst • ContinuousLinearMap.id 𝕜 A + (mul 𝕜 A).flip u.snd) -
      (v.fst • ContinuousLinearMap.id 𝕜 A + (mul 𝕜 A).flip v.snd) =
      (u - v).fst • ContinuousLinearMap.id 𝕜 A + (mul 𝕜 A).flip (u - v).snd := by
    simp [sub_smul, sub_add_sub_comm]
  rw [dist_eq_norm, dist_eq_norm, hsub, norm_rightAction_eq_norm hA (u - v)]

/-- For any complete C⋆-algebra over a complete densely normed C⋆-field, the right-action image of
`Unitization 𝕜 A` in `A →L[𝕜] A` is closed, whether or not `A` has an identity. -/
theorem isClosed_range_rightAction {𝕜 A : Type*} [DenselyNormedField 𝕜] [StarRing 𝕜]
    [CStarRing 𝕜] [CompleteSpace 𝕜] [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [StarModule 𝕜 A]
    [CompleteSpace A] :
    IsClosed (Set.range fun u : Unitization 𝕜 A ↦
      u.fst • ContinuousLinearMap.id 𝕜 A + (mul 𝕜 A).flip u.snd) := by
  by_cases hA : ∃ e : A, ∀ b : A, b * e = b
  · obtain ⟨e, he⟩ := hA
    rw [range_rightAction_of_right_identity he]
    exact (isometry_mul_flip 𝕜 A).isClosedEmbedding.isClosed_range
  · exact (isometry_rightAction
      (mt TauCeti.exists_right_identity_iff.mpr hA)).isClosedEmbedding.isClosed_range

end RightAction

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
by the identity and left multiplications, realized as the range of
`Unitization.lift (NonUnitalAlgHom.Lmul 𝕜 A)`. -/
structure LeftAction (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
    [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] where
  /-- The underlying bounded linear operator on `A`. -/
  toContinuousLinearMap : A →L[𝕜] A
  /-- Membership in the range of `Unitization.lift (NonUnitalAlgHom.Lmul 𝕜 A)`. -/
  mem_range' : toContinuousLinearMap ∈ (lift (NonUnitalAlgHom.Lmul 𝕜 A)).range

attribute [coe] LeftAction.toContinuousLinearMap

namespace LeftAction

section Normed

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

instance instCoeOut : CoeOut (LeftAction 𝕜 A) (A →L[𝕜] A) := ⟨toContinuousLinearMap⟩

theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap : LeftAction 𝕜 A → A →L[𝕜] A) := by
  rintro ⟨_, _⟩ ⟨_, _⟩ rfl
  rfl

instance instFunLike : FunLike (LeftAction 𝕜 A) A A where
  coe T := (T : A →L[𝕜] A)
  coe_injective _ _ h := toContinuousLinearMap_injective (DFunLike.ext _ _ (congrFun h))

instance instContinuousLinearMapClass : ContinuousLinearMapClass (LeftAction 𝕜 A) 𝕜 A A where
  map_add T x y := map_add (T : A →L[𝕜] A) x y
  map_smulₛₗ T c x := map_smul (T : A →L[𝕜] A) c x
  map_continuous T := (T : A →L[𝕜] A).continuous

@[ext]
theorem ext {S T : LeftAction 𝕜 A} (h : ∀ a, S a = T a) : S = T :=
  DFunLike.ext S T h

@[simp]
theorem coe_toContinuousLinearMap (T : LeftAction 𝕜 A) (a : A) :
    (T : A →L[𝕜] A) a = T a := (rfl)

@[simp]
theorem mk_apply (T : A →L[𝕜] A) (hT : T ∈ (lift (NonUnitalAlgHom.Lmul 𝕜 A)).range) (a : A) :
    (⟨T, hT⟩ : LeftAction 𝕜 A) a = T a := (rfl)

/-- Every operator in `LeftAction 𝕜 A` arises from `Unitization.lift (NonUnitalAlgHom.Lmul 𝕜 A)`. -/
theorem exists_lift_Lmul_eq (T : LeftAction 𝕜 A) :
    ∃ u : Unitization 𝕜 A, lift (NonUnitalAlgHom.Lmul 𝕜 A) u = (T : A →L[𝕜] A) :=
  T.mem_range'

instance instZero : Zero (LeftAction 𝕜 A) := ⟨⟨0, zero_mem _⟩⟩
instance instOne : One (LeftAction 𝕜 A) := ⟨⟨1, one_mem _⟩⟩
instance instAdd : Add (LeftAction 𝕜 A) := ⟨fun S T ↦ ⟨S.1 + T.1, add_mem S.2 T.2⟩⟩
instance instNeg : Neg (LeftAction 𝕜 A) := ⟨fun T ↦ ⟨-T.1, neg_mem T.2⟩⟩
instance instSub : Sub (LeftAction 𝕜 A) := ⟨fun S T ↦ ⟨S.1 - T.1, sub_mem S.2 T.2⟩⟩
instance instMul : Mul (LeftAction 𝕜 A) := ⟨fun S T ↦ ⟨S.1 * T.1, mul_mem S.2 T.2⟩⟩
instance instPowNat : Pow (LeftAction 𝕜 A) ℕ := ⟨fun T n ↦ ⟨T.1 ^ n, pow_mem T.2 n⟩⟩
instance instNatCast : NatCast (LeftAction 𝕜 A) := ⟨fun n ↦ ⟨n, natCast_mem _ n⟩⟩
instance instIntCast : IntCast (LeftAction 𝕜 A) := ⟨fun n ↦ ⟨n, intCast_mem _ n⟩⟩
instance instSMulNat : SMul ℕ (LeftAction 𝕜 A) := ⟨fun n T ↦ ⟨n • T.1, nsmul_mem T.2 n⟩⟩
instance instSMulInt : SMul ℤ (LeftAction 𝕜 A) := ⟨fun n T ↦ ⟨n • T.1, zsmul_mem T.2 n⟩⟩
instance instSMul : SMul 𝕜 (LeftAction 𝕜 A) := ⟨fun c T ↦ ⟨c • T.1, Subalgebra.smul_mem _ T.2 c⟩⟩

instance instInhabited : Inhabited (LeftAction 𝕜 A) := ⟨0⟩

instance instSubsingleton [Subsingleton A] : Subsingleton (LeftAction 𝕜 A) :=
  toContinuousLinearMap_injective.subsingleton

instance instRing : Ring (LeftAction 𝕜 A) :=
  toContinuousLinearMap_injective.ring toContinuousLinearMap rfl rfl (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

instance instModule : Module 𝕜 (LeftAction 𝕜 A) :=
  Function.Injective.module 𝕜 ⟨⟨toContinuousLinearMap, rfl⟩, fun _ _ ↦ rfl⟩
    toContinuousLinearMap_injective (fun _ _ ↦ rfl)

instance instAlgebra : Algebra 𝕜 (LeftAction 𝕜 A) where
  algebraMap :=
    { toFun := fun c ↦ ⟨algebraMap 𝕜 (A →L[𝕜] A) c, algebraMap_mem _ c⟩
      map_one' := toContinuousLinearMap_injective (map_one _)
      map_mul' := fun x y ↦ toContinuousLinearMap_injective (map_mul _ x y)
      map_zero' := toContinuousLinearMap_injective (map_zero _)
      map_add' := fun x y ↦ toContinuousLinearMap_injective (map_add _ x y) }
  commutes' c T := toContinuousLinearMap_injective (Algebra.commutes c T.1)
  smul_def' c T := toContinuousLinearMap_injective (Algebra.smul_def c T.1)

/-- The canonical unital algebra embedding `LeftAction 𝕜 A →ₐ[𝕜] (A →L[𝕜] A)`. -/
def valAlgHom : LeftAction 𝕜 A →ₐ[𝕜] A →L[𝕜] A where
  toFun := toContinuousLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem coe_valAlgHom : ⇑(valAlgHom (𝕜 := 𝕜) (A := A)) = toContinuousLinearMap := (rfl)

theorem valAlgHom_injective : Function.Injective (valAlgHom (𝕜 := 𝕜) (A := A)) :=
  toContinuousLinearMap_injective

noncomputable instance instNormedRing : NormedRing (LeftAction 𝕜 A) :=
  NormedRing.induced (LeftAction 𝕜 A) (A →L[𝕜] A) valAlgHom valAlgHom_injective

@[simp]
theorem norm_toContinuousLinearMap (T : LeftAction 𝕜 A) :
    ‖(T : A →L[𝕜] A)‖ = ‖T‖ := (rfl)

@[simp, norm_cast]
theorem toContinuousLinearMap_zero : ((0 : LeftAction 𝕜 A) : A →L[𝕜] A) = 0 := (rfl)

@[simp, norm_cast]
theorem toContinuousLinearMap_one :
    ((1 : LeftAction 𝕜 A) : A →L[𝕜] A) = ContinuousLinearMap.id 𝕜 A := (rfl)

@[simp, norm_cast]
theorem toContinuousLinearMap_add (S T : LeftAction 𝕜 A) :
    ((S + T : LeftAction 𝕜 A) : A →L[𝕜] A) = (S : A →L[𝕜] A) + (T : A →L[𝕜] A) := (rfl)

@[simp, norm_cast]
theorem toContinuousLinearMap_neg (T : LeftAction 𝕜 A) :
    ((-T : LeftAction 𝕜 A) : A →L[𝕜] A) = -(T : A →L[𝕜] A) := (rfl)

@[simp, norm_cast]
theorem toContinuousLinearMap_sub (S T : LeftAction 𝕜 A) :
    ((S - T : LeftAction 𝕜 A) : A →L[𝕜] A) = (S : A →L[𝕜] A) - (T : A →L[𝕜] A) := (rfl)

@[simp, norm_cast]
theorem toContinuousLinearMap_mul (S T : LeftAction 𝕜 A) :
    ((S * T : LeftAction 𝕜 A) : A →L[𝕜] A) = (S : A →L[𝕜] A) * (T : A →L[𝕜] A) := (rfl)

@[simp, norm_cast]
theorem toContinuousLinearMap_smul (c : 𝕜) (T : LeftAction 𝕜 A) :
    ((c • T : LeftAction 𝕜 A) : A →L[𝕜] A) = c • (T : A →L[𝕜] A) := (rfl)

@[simp]
theorem zero_apply (a : A) : (0 : LeftAction 𝕜 A) a = 0 := (rfl)

@[simp]
theorem one_apply (a : A) : (1 : LeftAction 𝕜 A) a = a := (rfl)

@[simp]
theorem add_apply (S T : LeftAction 𝕜 A) (a : A) : (S + T) a = S a + T a := (rfl)

@[simp]
theorem neg_apply (T : LeftAction 𝕜 A) (a : A) : (-T) a = -T a := (rfl)

@[simp]
theorem sub_apply (S T : LeftAction 𝕜 A) (a : A) : (S - T) a = S a - T a := (rfl)

@[simp]
theorem mul_apply (S T : LeftAction 𝕜 A) (a : A) : (S * T) a = S (T a) := (rfl)

@[simp]
theorem smul_apply (c : 𝕜) (T : LeftAction 𝕜 A) (a : A) : (c • T) a = c • T a := (rfl)

@[simp]
theorem algebraMap_apply (c : 𝕜) (a : A) : (algebraMap 𝕜 (LeftAction 𝕜 A) c) a = c • a := (rfl)

instance instNormedAlgebra : NormedAlgebra 𝕜 (LeftAction 𝕜 A) where
  norm_smul_le c T := by
    rw [← norm_toContinuousLinearMap, ← norm_toContinuousLinearMap, toContinuousLinearMap_smul]
    exact norm_smul_le c (T : A →L[𝕜] A)

theorem isometry_toContinuousLinearMap :
    Isometry (toContinuousLinearMap : LeftAction 𝕜 A → A →L[𝕜] A) :=
  AddMonoidHomClass.isometry_of_norm valAlgHom norm_toContinuousLinearMap

theorem range_toContinuousLinearMap :
    Set.range (toContinuousLinearMap : LeftAction 𝕜 A → A →L[𝕜] A) =
      Set.range (lift (NonUnitalAlgHom.Lmul 𝕜 A)) := by
  ext f
  exact ⟨fun ⟨T, hT⟩ ↦ hT ▸ T.mem_range', fun hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩

instance instCompleteSpace [CompleteSpace 𝕜] [RegularNormedAlgebra 𝕜 A] [CompleteSpace A] :
    CompleteSpace (LeftAction 𝕜 A) := by
  rw [completeSpace_iff_isComplete_range isometry_toContinuousLinearMap.isUniformInducing,
    range_toContinuousLinearMap]
  exact isClosed_range_lift_Lmul.isComplete

end Normed

section CommNormed

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedCommRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

noncomputable instance instNormedCommRing : NormedCommRing (LeftAction 𝕜 A) :=
  { instNormedRing (𝕜 := 𝕜) (A := A) with
    mul_comm := fun S T ↦ by
      obtain ⟨u, hu⟩ := S.exists_lift_Lmul_eq
      obtain ⟨v, hv⟩ := T.exists_lift_Lmul_eq
      apply toContinuousLinearMap_injective
      rw [toContinuousLinearMap_mul, toContinuousLinearMap_mul, ← hu, ← hv, ← map_mul,
        mul_comm u v, map_mul] }

end CommNormed

section Star

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NonUnitalNormedRing A]
  [StarRing A] [IsProperStar A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A]
  [SMulCommClass 𝕜 A A] [StarModule 𝕜 A]

private theorem lift_Lmul_star_choose_eq {T : LeftAction 𝕜 A} {u : Unitization 𝕜 A}
    (hu : lift (NonUnitalAlgHom.Lmul 𝕜 A) u = (T : A →L[𝕜] A)) :
    lift (NonUnitalAlgHom.Lmul 𝕜 A) (star T.exists_lift_Lmul_eq.choose) =
      lift (NonUnitalAlgHom.Lmul 𝕜 A) (star u) :=
  lift_Lmul_star_eq_of_eq (T.exists_lift_Lmul_eq.choose_spec.trans hu.symm)

noncomputable instance instStarRing : StarRing (LeftAction 𝕜 A) where
  star T :=
    ⟨lift (NonUnitalAlgHom.Lmul 𝕜 A) (star T.exists_lift_Lmul_eq.choose),
      ⟨star T.exists_lift_Lmul_eq.choose, rfl⟩⟩
  star_involutive T := by
    obtain ⟨u, hu⟩ := T.exists_lift_Lmul_eq
    apply toContinuousLinearMap_injective
    dsimp only
    have hs : lift (NonUnitalAlgHom.Lmul 𝕜 A) (star T.exists_lift_Lmul_eq.choose) =
        lift (NonUnitalAlgHom.Lmul 𝕜 A) (star u) :=
      lift_Lmul_star_choose_eq hu
    let T' : LeftAction 𝕜 A :=
      ⟨lift (NonUnitalAlgHom.Lmul 𝕜 A) (star T.exists_lift_Lmul_eq.choose),
        ⟨star T.exists_lift_Lmul_eq.choose, rfl⟩⟩
    rw [lift_Lmul_star_choose_eq (T := T') hs.symm, InvolutiveStar.star_involutive u, hu]
  star_mul S T := by
    obtain ⟨u, hu⟩ := S.exists_lift_Lmul_eq
    obtain ⟨v, hv⟩ := T.exists_lift_Lmul_eq
    apply toContinuousLinearMap_injective
    have huv : lift (NonUnitalAlgHom.Lmul 𝕜 A) (u * v) =
        ((S * T : LeftAction 𝕜 A) : A →L[𝕜] A) := by
      rw [map_mul, hu, hv, toContinuousLinearMap_mul]
    change lift (NonUnitalAlgHom.Lmul 𝕜 A) (star (S * T).exists_lift_Lmul_eq.choose) =
      lift (NonUnitalAlgHom.Lmul 𝕜 A) (star T.exists_lift_Lmul_eq.choose) *
        lift (NonUnitalAlgHom.Lmul 𝕜 A) (star S.exists_lift_Lmul_eq.choose)
    rw [lift_Lmul_star_choose_eq huv, StarMul.star_mul u v, map_mul, lift_Lmul_star_choose_eq hv,
      lift_Lmul_star_choose_eq hu]
  star_add S T := by
    obtain ⟨u, hu⟩ := S.exists_lift_Lmul_eq
    obtain ⟨v, hv⟩ := T.exists_lift_Lmul_eq
    apply toContinuousLinearMap_injective
    have huv : lift (NonUnitalAlgHom.Lmul 𝕜 A) (u + v) =
        ((S + T : LeftAction 𝕜 A) : A →L[𝕜] A) := by
      rw [map_add, hu, hv, toContinuousLinearMap_add]
    change lift (NonUnitalAlgHom.Lmul 𝕜 A) (star (S + T).exists_lift_Lmul_eq.choose) =
      lift (NonUnitalAlgHom.Lmul 𝕜 A) (star S.exists_lift_Lmul_eq.choose) +
        lift (NonUnitalAlgHom.Lmul 𝕜 A) (star T.exists_lift_Lmul_eq.choose)
    rw [lift_Lmul_star_choose_eq huv, StarAddMonoid.star_add u v, map_add,
      lift_Lmul_star_choose_eq hu, lift_Lmul_star_choose_eq hv]

/-- For any preimage `u` of `T` under `lift (NonUnitalAlgHom.Lmul 𝕜 A)`, the transported
involution on `LeftAction 𝕜 A` evaluates as the left action of `star u`. -/
theorem toContinuousLinearMap_star_of_eq {T : LeftAction 𝕜 A} {u : Unitization 𝕜 A}
    (hu : lift (NonUnitalAlgHom.Lmul 𝕜 A) u = (T : A →L[𝕜] A)) :
    ((star T : LeftAction 𝕜 A) : A →L[𝕜] A) = lift (NonUnitalAlgHom.Lmul 𝕜 A) (star u) := by
  exact lift_Lmul_star_choose_eq hu

/-- Every operator in `LeftAction 𝕜 A` and its involution are mutually adjoint for
`(x, y) ↦ star x * y`. -/
theorem star_apply_mul (T : LeftAction 𝕜 A) (x y : A) :
    star (T x) * y = star x * (star T : LeftAction 𝕜 A) y := by
  obtain ⟨u, hu⟩ := T.exists_lift_Lmul_eq
  rw [← coe_toContinuousLinearMap T, ← coe_toContinuousLinearMap (star T),
    toContinuousLinearMap_star_of_eq hu, ← hu]
  exact star_lift_Lmul_apply_mul u x y

instance instStarModule : StarModule 𝕜 (LeftAction 𝕜 A) where
  star_smul c T := by
    obtain ⟨u, hu⟩ := T.exists_lift_Lmul_eq
    apply toContinuousLinearMap_injective
    have hcu : lift (NonUnitalAlgHom.Lmul 𝕜 A) (c • u) =
        ((c • T : LeftAction 𝕜 A) : A →L[𝕜] A) := by
      rw [map_smul, hu, toContinuousLinearMap_smul]
    rw [toContinuousLinearMap_star_of_eq hcu, star_smul, map_smul, toContinuousLinearMap_smul,
      toContinuousLinearMap_star_of_eq hu]

/-- Left multiplication as a nonunital `⋆`-algebra homomorphism into `LeftAction 𝕜 A`. -/
noncomputable def Lmul : A →⋆ₙₐ[𝕜] LeftAction 𝕜 A where
  toNonUnitalAlgHom :=
    { toFun := fun a ↦ ⟨mul 𝕜 A a, ⟨a, by simp⟩⟩
      map_smul' := fun c a ↦ toContinuousLinearMap_injective (map_smul (mul 𝕜 A) c a)
      map_zero' := toContinuousLinearMap_injective (map_zero (mul 𝕜 A))
      map_add' := fun a b ↦ toContinuousLinearMap_injective (map_add (mul 𝕜 A) a b)
      map_mul' := fun a b ↦
        toContinuousLinearMap_injective (map_mul (NonUnitalAlgHom.Lmul 𝕜 A) a b) }
  map_star' a := by
    apply toContinuousLinearMap_injective
    have ha : lift (NonUnitalAlgHom.Lmul 𝕜 A) (a : Unitization 𝕜 A) = mul 𝕜 A a := by simp
    have hstar : ((star (⟨mul 𝕜 A a, ⟨a, ha⟩⟩ : LeftAction 𝕜 A) : LeftAction 𝕜 A) : A →L[𝕜] A) =
        lift (NonUnitalAlgHom.Lmul 𝕜 A) (star (a : Unitization 𝕜 A)) :=
      toContinuousLinearMap_star_of_eq ha
    simpa [← inr_star] using hstar.symm

@[simp]
theorem toContinuousLinearMap_Lmul (a : A) :
    ((Lmul a : LeftAction 𝕜 A) : A →L[𝕜] A) = mul 𝕜 A a := (rfl)

@[simp]
theorem Lmul_apply (a b : A) : (Lmul a : LeftAction 𝕜 A) b = a * b := (rfl)

/-- Left multiplication into `LeftAction 𝕜 A` preserves norms in any regular normed algebra
(including `a = 0`). -/
@[simp]
theorem norm_Lmul [RegularNormedAlgebra 𝕜 A] (a : A) :
    ‖(Lmul a : LeftAction 𝕜 A)‖ = ‖a‖ := by
  rw [← norm_toContinuousLinearMap, toContinuousLinearMap_Lmul, opNorm_mul_apply]

/-- Left multiplication into `LeftAction 𝕜 A` is an isometry in any regular normed algebra. -/
theorem isometry_Lmul [RegularNormedAlgebra 𝕜 A] :
    Isometry (Lmul (𝕜 := 𝕜) (A := A)) :=
  AddMonoidHomClass.isometry_of_norm (Lmul (𝕜 := 𝕜) (A := A)).toNonUnitalAlgHom norm_Lmul

/-- The unital `⋆`-homomorphism `Unitization 𝕜 A →⋆ₐ[𝕜] LeftAction 𝕜 A` obtained directly from
`Unitization.lift (NonUnitalAlgHom.Lmul 𝕜 A)`. -/
noncomputable def ofLift : Unitization 𝕜 A →⋆ₐ[𝕜] LeftAction 𝕜 A where
  toFun u := ⟨lift (NonUnitalAlgHom.Lmul 𝕜 A) u, ⟨u, rfl⟩⟩
  map_one' := toContinuousLinearMap_injective (map_one _)
  map_mul' u v := toContinuousLinearMap_injective (map_mul _ u v)
  map_zero' := toContinuousLinearMap_injective (map_zero _)
  map_add' u v := toContinuousLinearMap_injective (map_add _ u v)
  commutes' c := toContinuousLinearMap_injective ((lift (NonUnitalAlgHom.Lmul 𝕜 A)).commutes c)
  map_star' _ := (toContinuousLinearMap_injective (toContinuousLinearMap_star_of_eq rfl)).symm

@[simp]
theorem toContinuousLinearMap_ofLift (u : Unitization 𝕜 A) :
    ((ofLift u : LeftAction 𝕜 A) : A →L[𝕜] A) = lift (NonUnitalAlgHom.Lmul 𝕜 A) u := (rfl)

/-- By uniqueness of `Unitization.starLift` (`Unitization.starAlgHom_ext`), lifting `a ↦ L_a`
gives `LeftAction.ofLift`, i.e., `(z, a) ↦ z • id + L_a`. -/
theorem starLift_Lmul_eq_ofLift :
    starLift (Lmul (𝕜 := 𝕜) (A := A)) = ofLift := by
  rw [← starLift.eq_symm_apply]
  refine NonUnitalStarAlgHom.ext fun a ↦ toContinuousLinearMap_injective ?_
  simp

/-- Evaluating `Unitization.starLift LeftAction.Lmul` in `A →L[𝕜] A` produces
`u.fst • id + L_{u.snd}`. -/
theorem toContinuousLinearMap_starLift_Lmul (u : Unitization 𝕜 A) :
    ((starLift (Lmul (𝕜 := 𝕜) (A := A)) u : LeftAction 𝕜 A) : A →L[𝕜] A) =
      u.fst • ContinuousLinearMap.id 𝕜 A + mul 𝕜 A u.snd := by
  rw [starLift_Lmul_eq_ofLift, toContinuousLinearMap_ofLift]
  simp [Algebra.algebraMap_eq_smul_one]
  rfl

/-- The `⋆`-lift of `LeftAction.Lmul` maps `Unitization 𝕜 A` surjectively onto `LeftAction 𝕜 A`. -/
theorem starLift_Lmul_surjective :
    Function.Surjective (starLift (Lmul (𝕜 := 𝕜) (A := A))) := by
  rw [starLift_Lmul_eq_ofLift]
  rintro ⟨_, u, rfl⟩
  exact ⟨u, rfl⟩

end Star

section CStar

/-- For any C⋆-algebra `A` over a densely normed star field `𝕜`, the operator-norm subalgebra
`LeftAction 𝕜 A` satisfies the C⋆-identity. -/
instance instCStarRing {𝕜 A : Type*} [DenselyNormedField 𝕜] [StarRing 𝕜]
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [StarModule 𝕜 A] :
    CStarRing (LeftAction 𝕜 A) where
  norm_mul_self_le T := by
    obtain ⟨u, hu⟩ := T.exists_lift_Lmul_eq
    have hmul : lift (NonUnitalAlgHom.Lmul 𝕜 A) (star u * u) =
        ((star T * T : LeftAction 𝕜 A) : A →L[𝕜] A) := by
      rw [map_mul, toContinuousLinearMap_mul, ← toContinuousLinearMap_star_of_eq hu, hu]
    simpa [← sq, ← norm_toContinuousLinearMap, ← hu, ← hmul, splitMul_apply] using
      norm_splitMul_snd_sq 𝕜 u

noncomputable instance instCStarAlgebra {A : Type*} [NonUnitalCStarAlgebra A] :
    CStarAlgebra (LeftAction ℂ A) where

noncomputable instance instCommCStarAlgebra {A : Type*} [NonUnitalCommCStarAlgebra A] :
    CommCStarAlgebra (LeftAction ℂ A) where

end CStar

end LeftAction

section Equiv

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NonUnitalNormedRing A]
  [StarRing A] [IsProperStar A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A]
  [SMulCommClass 𝕜 A A] [StarModule 𝕜 A] [RegularNormedAlgebra 𝕜 A]

/-- When `A` is a regular normed star algebra with proper involution and no two-sided identity,
`Unitization.starLift LeftAction.Lmul` is a `⋆`-algebra equivalence onto `LeftAction 𝕜 A`. -/
noncomputable def starAlgEquivLeftAction
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) :
    Unitization 𝕜 A ≃⋆ₐ[𝕜] LeftAction 𝕜 A :=
  StarAlgEquiv.ofBijective (starLift (LeftAction.Lmul (𝕜 := 𝕜) (A := A)))
    ⟨fun u v huv ↦ (injective_lift_Lmul_iff.mpr hA) <| by
      have h := congrArg LeftAction.toContinuousLinearMap huv
      rwa [LeftAction.starLift_Lmul_eq_ofLift, LeftAction.toContinuousLinearMap_ofLift,
        LeftAction.toContinuousLinearMap_ofLift] at h,
    LeftAction.starLift_Lmul_surjective⟩

@[simp]
theorem toStarAlgHom_starAlgEquivLeftAction
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) :
    (starAlgEquivLeftAction (𝕜 := 𝕜) hA).toStarAlgHom =
      starLift (LeftAction.Lmul (𝕜 := 𝕜) (A := A)) := (rfl)

@[simp]
theorem toContinuousLinearMap_starAlgEquivLeftAction
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (u : Unitization 𝕜 A) :
    ((starAlgEquivLeftAction (𝕜 := 𝕜) hA u : LeftAction 𝕜 A) : A →L[𝕜] A) =
      u.fst • ContinuousLinearMap.id 𝕜 A + mul 𝕜 A u.snd :=
  LeftAction.toContinuousLinearMap_starLift_Lmul u

@[simp]
theorem starAlgEquivLeftAction_inr
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (a : A) :
    starAlgEquivLeftAction (𝕜 := 𝕜) hA (a : Unitization 𝕜 A) = LeftAction.Lmul a :=
  LeftAction.toContinuousLinearMap_injective (by simp)

@[simp]
theorem starAlgEquivLeftAction_symm_Lmul
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (a : A) :
    (starAlgEquivLeftAction (𝕜 := 𝕜) hA).symm (LeftAction.Lmul a) = (a : Unitization 𝕜 A) :=
  (starAlgEquivLeftAction (𝕜 := 𝕜) hA).symm_apply_eq.mpr (starAlgEquivLeftAction_inr hA a).symm

/-- When `A` is complete and has no two-sided identity, `Unitization.starAlgEquivLeftAction`
preserves norms. -/
@[simp]
theorem norm_starAlgEquivLeftAction [CompleteSpace A]
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (u : Unitization 𝕜 A) :
    ‖starAlgEquivLeftAction (𝕜 := 𝕜) hA u‖ = ‖u‖ := by
  have h : ((starAlgEquivLeftAction (𝕜 := 𝕜) hA u : LeftAction 𝕜 A) : A →L[𝕜] A) =
      lift (NonUnitalAlgHom.Lmul 𝕜 A) u := by
    change ((starLift (LeftAction.Lmul (𝕜 := 𝕜) (A := A)) u : LeftAction 𝕜 A) : A →L[𝕜] A) = _
    rw [LeftAction.starLift_Lmul_eq_ofLift, LeftAction.toContinuousLinearMap_ofLift]
  rw [← LeftAction.norm_toContinuousLinearMap, h, norm_lift_Lmul hA u]

/-- When `A` is complete and has no two-sided identity, `Unitization.starAlgEquivLeftAction` is
an isometry. -/
theorem isometry_starAlgEquivLeftAction [CompleteSpace A]
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) :
    Isometry (starAlgEquivLeftAction (𝕜 := 𝕜) hA) :=
  AddMonoidHomClass.isometry_of_norm (starAlgEquivLeftAction (𝕜 := 𝕜) hA).toStarAlgHom.toAlgHom
    (norm_starAlgEquivLeftAction hA)

end Equiv

end Unitization
