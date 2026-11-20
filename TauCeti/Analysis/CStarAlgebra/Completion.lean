/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import TauCeti.Analysis.Normed.Ring.Completion
public import TauCeti.Topology.Algebra.Star.Completion
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Isometric star operations and C⋆-completions

The norm of the completion of a seminormed additive group extends the norm of the group by
continuity, and the star operation extends through `UniformSpace.Completion.map`. An isometric
star operation therefore stays isometric on the completion. Together with
`UniformSpace.Completion.instNonUnitalNormedRing` and `UniformSpace.Completion.instStarRing`, this
makes the completion of a nonunital seminormed ⋆-ring with isometric star, such as an `L¹`
convolution algebra on compactly supported functions, a nonunital Banach ⋆-algebra.

The C⋆-identity `‖x⋆ * x‖ = ‖x‖ * ‖x‖` also extends by continuity. Completing a complex ⋆-algebra
`A` in a C⋆-seminorm `p : TauCeti.CStarSeminorm A` (a submultiplicative complex seminorm satisfying
`p x * p x ≤ p (star x * x)`) therefore produces a nonunital C⋆-algebra `p.Completion`, and a
unital C⋆-algebra when `A` is unital. This shared construction underlies both the full crossed
product of a C⋆-dynamical system and the full unital C⋆-free product.

## Main definitions

* `TauCeti.CStarSeminorm`: a submultiplicative complex seminorm on a ⋆-ring satisfying the
  C⋆-inequality `p x * p x ≤ p (star x * x)`.
* `TauCeti.CStarSeminorm.WithSeminorm`: type synonym equipping `A` with the seminorm `p`.
* `TauCeti.CStarSeminorm.Completion`: the Hausdorff C⋆-completion of `A` with respect to `p`,
  carrying `NonUnitalCStarAlgebra` (and `CStarAlgebra` when `A` is unital).
* `TauCeti.CStarSeminorm.ofNonUnital` and `TauCeti.CStarSeminorm.of`: the canonical dense
  nonunital and unital ⋆-homomorphisms `A → p.Completion`.
* `TauCeti.CStarSeminorm.liftCLM`, `TauCeti.CStarSeminorm.liftNonUnital`, and
  `TauCeti.CStarSeminorm.lift`: continuous extensions of `p`-bounded linear maps and nonunital or
  unital ⋆-homomorphisms to `p.Completion`.

## Main results

* `UniformSpace.Completion.instNormedStarGroup`: an isometric star operation stays isometric on
  the completion.
* `UniformSpace.Completion.cstarRing`: the completion of a seminormed ⋆-ring whose seminorm
  satisfies the C⋆-identity is a C⋆-ring.
* `TauCeti.CStarSeminorm.map_star` and `TauCeti.CStarSeminorm.map_star_mul_self`: star-invariance
  and the C⋆-identity follow automatically from submultiplicativity and the C⋆-inequality.
* `TauCeti.CStarSeminorm.norm_ofNonUnital`, `TauCeti.CStarSeminorm.norm_of`,
  `TauCeti.CStarSeminorm.denseRange_ofNonUnital`, `TauCeti.CStarSeminorm.denseRange_of`,
  `TauCeti.CStarSeminorm.induction_on`, `TauCeti.CStarSeminorm.continuousLinearMap_ext`,
  `TauCeti.CStarSeminorm.nonUnitalStarAlgHom_ext`, `TauCeti.CStarSeminorm.starAlgHom_ext`, and
  `TauCeti.CStarSeminorm.normOneClass_completion`: norm, density, induction, extensionality, and
  norm-one properties of the C⋆-completion.
-/

public section

open UniformSpace

/-- **An isometric star operation on a seminormed group stays isometric on its completion.** -/
instance UniformSpace.Completion.instNormedStarGroup {E : Type*} [SeminormedAddCommGroup E]
    [StarAddMonoid E] [NormedStarGroup E] : NormedStarGroup (Completion E) where
  norm_star_le x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih a => rw [← Completion.coe_star, Completion.norm_coe, Completion.norm_coe, norm_star]

/-- **The completion of a seminormed ⋆-ring satisfying the C⋆-identity is a C⋆-ring.** The
inequality `‖x‖ * ‖x‖ ≤ ‖x⋆ * x‖` on `E` passes to the completion by continuity. This is not an
instance because `CStarRing` is only defined for normed rings, so the hypothesis cannot be stated
as a class on the seminormed ring `E`. -/
theorem UniformSpace.Completion.cstarRing {E : Type*} [NonUnitalSeminormedRing E] [StarRing E]
    [NormedStarGroup E] (h : ∀ x : E, ‖x‖ * ‖x‖ ≤ ‖star x * x‖) : CStarRing (Completion E) where
  norm_mul_self_le x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih a =>
      simpa only [← Completion.coe_star, ← Completion.coe_mul', Completion.norm_coe] using h a

namespace TauCeti

/-- A C⋆-seminorm on a complex ⋆-ring `A`: a complex seminorm `p` that is submultiplicative
(`p (x * y) ≤ p x * p y`) and satisfies the C⋆-inequality `p x * p x ≤ p (star x * x)`.
Invariance under `star` and the C⋆-identity `p (star x * x) = p x * p x` follow automatically. -/
structure CStarSeminorm (A : Type*) [NonUnitalRing A] [Module ℂ A] [StarRing A] extends
    Seminorm ℂ A where
  /-- Submultiplicativity of the seminorm: `p (x * y) ≤ p x * p y`. -/
  map_mul_le' : ∀ x y : A, toFun (x * y) ≤ toFun x * toFun y
  /-- The C⋆-inequality `p x * p x ≤ p (star x * x)`. -/
  mul_self_le_star_mul_self' : ∀ x : A, toFun x * toFun x ≤ toFun (star x * x)

namespace CStarSeminorm

section Basic

variable {A : Type*} [NonUnitalRing A] [Module ℂ A] [StarRing A]

instance : FunLike (CStarSeminorm A) A ℝ where
  coe p := p.toFun
  coe_injective p q h := by
    cases p
    cases q
    congr
    exact DFunLike.coe_injective h

instance : SeminormClass (CStarSeminorm A) ℂ A where
  map_add_le_add p := p.add_le'
  map_zero p := p.map_zero'
  map_neg_eq_map p := p.neg'
  map_smul_eq_mul p := p.smul'

@[ext]
theorem ext {p q : CStarSeminorm A} (h : ∀ x, p x = q x) : p = q :=
  DFunLike.ext p q h

@[simp]
theorem toSeminorm_apply (p : CStarSeminorm A) (x : A) : p.toSeminorm x = p x :=
  (rfl)

/-- A C⋆-seminorm is submultiplicative. -/
theorem map_mul_le (p : CStarSeminorm A) (x y : A) : p (x * y) ≤ p x * p y :=
  p.map_mul_le' x y

/-- A C⋆-seminorm satisfies `p x * p x ≤ p (star x * x)`. -/
theorem mul_self_le_star_mul_self (p : CStarSeminorm A) (x : A) :
    p x * p x ≤ p (star x * x) :=
  p.mul_self_le_star_mul_self' x

/-- Every C⋆-seminorm is invariant under `star`. -/
@[simp]
theorem map_star (p : CStarSeminorm A) (x : A) : p (star x) = p x := by
  have hle (y : A) : p y ≤ p (star y) := by
    rcases (apply_nonneg p y).eq_or_lt with h0 | hpos
    · exact h0 ▸ apply_nonneg p (star y)
    · exact le_of_mul_le_mul_right
        ((p.mul_self_le_star_mul_self y).trans (p.map_mul_le (star y) y)) hpos
  exact le_antisymm (by simpa using hle (star x)) (hle x)

/-- Every C⋆-seminorm satisfies the C⋆-identity `p (star x * x) = p x * p x`. -/
theorem map_star_mul_self (p : CStarSeminorm A) (x : A) :
    p (star x * x) = p x * p x :=
  le_antisymm ((p.map_mul_le (star x) x).trans_eq (by rw [p.map_star]))
    (p.mul_self_le_star_mul_self x)

end Basic

/-! ### Type synonym equipped with a C⋆-seminorm -/

section WithSeminorm

variable {A : Type*} [NonUnitalRing A] [Module ℂ A] [StarRing A]

/-- Type synonym of `A` equipped with the seminorm given by `p : CStarSeminorm A`. -/
@[expose] def WithSeminorm (_ : CStarSeminorm A) : Type _ :=
  A

/-- View an element of `A` as an element of `p.WithSeminorm`. -/
def toWithSeminorm (p : CStarSeminorm A) : A ≃ p.WithSeminorm :=
  Equiv.refl _

/-- Extract the underlying element of `A` from `p.WithSeminorm`. -/
def ofWithSeminorm (p : CStarSeminorm A) : p.WithSeminorm ≃ A :=
  Equiv.refl _

@[simp]
theorem toWithSeminorm_symm (p : CStarSeminorm A) :
    p.toWithSeminorm.symm = p.ofWithSeminorm :=
  (rfl)

@[simp]
theorem ofWithSeminorm_symm (p : CStarSeminorm A) :
    p.ofWithSeminorm.symm = p.toWithSeminorm :=
  (rfl)

@[simp]
theorem ofWithSeminorm_toWithSeminorm (p : CStarSeminorm A) (x : A) :
    p.ofWithSeminorm (p.toWithSeminorm x) = x :=
  (rfl)

@[simp]
theorem toWithSeminorm_ofWithSeminorm (p : CStarSeminorm A) (x : p.WithSeminorm) :
    p.toWithSeminorm (p.ofWithSeminorm x) = x :=
  (rfl)

instance instNonUnitalRingWithSeminorm (p : CStarSeminorm A) : NonUnitalRing p.WithSeminorm :=
  inferInstanceAs (NonUnitalRing A)

instance instModuleWithSeminorm (p : CStarSeminorm A) : Module ℂ p.WithSeminorm :=
  inferInstanceAs (Module ℂ A)

instance instIsScalarTowerWithSeminorm [IsScalarTower ℂ A A] (p : CStarSeminorm A) :
    IsScalarTower ℂ p.WithSeminorm p.WithSeminorm :=
  inferInstanceAs (IsScalarTower ℂ A A)

instance instSMulCommClassWithSeminorm [SMulCommClass ℂ A A] (p : CStarSeminorm A) :
    SMulCommClass ℂ p.WithSeminorm p.WithSeminorm :=
  inferInstanceAs (SMulCommClass ℂ A A)

instance instStarRingWithSeminorm (p : CStarSeminorm A) : StarRing p.WithSeminorm :=
  inferInstanceAs (StarRing A)

instance instStarModuleWithSeminorm [StarModule ℂ A] (p : CStarSeminorm A) :
    StarModule ℂ p.WithSeminorm :=
  inferInstanceAs (StarModule ℂ A)

@[simp]
theorem toWithSeminorm_zero (p : CStarSeminorm A) : p.toWithSeminorm 0 = 0 :=
  (rfl)

@[simp]
theorem toWithSeminorm_add (p : CStarSeminorm A) (x y : A) :
    p.toWithSeminorm (x + y) = p.toWithSeminorm x + p.toWithSeminorm y :=
  (rfl)

@[simp]
theorem toWithSeminorm_neg (p : CStarSeminorm A) (x : A) :
    p.toWithSeminorm (-x) = -p.toWithSeminorm x :=
  (rfl)

@[simp]
theorem toWithSeminorm_sub (p : CStarSeminorm A) (x y : A) :
    p.toWithSeminorm (x - y) = p.toWithSeminorm x - p.toWithSeminorm y :=
  (rfl)

@[simp]
theorem toWithSeminorm_mul (p : CStarSeminorm A) (x y : A) :
    p.toWithSeminorm (x * y) = p.toWithSeminorm x * p.toWithSeminorm y :=
  (rfl)

@[simp]
theorem toWithSeminorm_smul (p : CStarSeminorm A) (c : ℂ) (x : A) :
    p.toWithSeminorm (c • x) = c • p.toWithSeminorm x :=
  (rfl)

@[simp]
theorem toWithSeminorm_star (p : CStarSeminorm A) (x : A) :
    p.toWithSeminorm (star x) = star (p.toWithSeminorm x) :=
  (rfl)

@[simp]
theorem ofWithSeminorm_zero (p : CStarSeminorm A) : p.ofWithSeminorm 0 = 0 :=
  (rfl)

@[simp]
theorem ofWithSeminorm_add (p : CStarSeminorm A) (x y : p.WithSeminorm) :
    p.ofWithSeminorm (x + y) = p.ofWithSeminorm x + p.ofWithSeminorm y :=
  (rfl)

@[simp]
theorem ofWithSeminorm_neg (p : CStarSeminorm A) (x : p.WithSeminorm) :
    p.ofWithSeminorm (-x) = -p.ofWithSeminorm x :=
  (rfl)

@[simp]
theorem ofWithSeminorm_sub (p : CStarSeminorm A) (x y : p.WithSeminorm) :
    p.ofWithSeminorm (x - y) = p.ofWithSeminorm x - p.ofWithSeminorm y :=
  (rfl)

@[simp]
theorem ofWithSeminorm_mul (p : CStarSeminorm A) (x y : p.WithSeminorm) :
    p.ofWithSeminorm (x * y) = p.ofWithSeminorm x * p.ofWithSeminorm y :=
  (rfl)

@[simp]
theorem ofWithSeminorm_smul (p : CStarSeminorm A) (c : ℂ) (x : p.WithSeminorm) :
    p.ofWithSeminorm (c • x) = c • p.ofWithSeminorm x :=
  (rfl)

@[simp]
theorem ofWithSeminorm_star (p : CStarSeminorm A) (x : p.WithSeminorm) :
    p.ofWithSeminorm (star x) = star (p.ofWithSeminorm x) :=
  (rfl)

/-- `p.WithSeminorm` carries the seminormed additive group structure induced by `p`. -/
instance instSeminormedAddCommGroupWithSeminorm (p : CStarSeminorm A) :
    SeminormedAddCommGroup p.WithSeminorm :=
  @AddGroupSeminorm.toSeminormedAddCommGroup p.WithSeminorm _ p.toAddGroupSeminorm

@[simp]
theorem norm_toWithSeminorm (p : CStarSeminorm A) (x : A) :
    ‖p.toWithSeminorm x‖ = p x :=
  (rfl)

/-- The norm on `p.WithSeminorm` is `p` applied to the underlying element of `A`. -/
theorem norm_withSeminorm (p : CStarSeminorm A) (x : p.WithSeminorm) :
    ‖x‖ = p (p.ofWithSeminorm x) :=
  (rfl)

instance instNormedSpaceWithSeminorm (p : CStarSeminorm A) : NormedSpace ℂ p.WithSeminorm where
  __ := instModuleWithSeminorm p
  norm_smul_le c x := by
    simp only [norm_withSeminorm, ofWithSeminorm_smul]
    exact (map_smul_eq_mul p c (p.ofWithSeminorm x)).le

instance instNonUnitalSeminormedRingWithSeminorm (p : CStarSeminorm A) :
    NonUnitalSeminormedRing p.WithSeminorm where
  __ := instSeminormedAddCommGroupWithSeminorm p
  __ := instNonUnitalRingWithSeminorm p
  norm_mul_le x y := by
    simpa only [norm_withSeminorm, ofWithSeminorm_mul] using
      p.map_mul_le (p.ofWithSeminorm x) (p.ofWithSeminorm y)

instance instNormedStarGroupWithSeminorm (p : CStarSeminorm A) :
    NormedStarGroup p.WithSeminorm where
  norm_star_le x := by
    simp only [norm_withSeminorm, ofWithSeminorm_star, map_star, le_refl]

/-- The C⋆-identity on `p.WithSeminorm`. -/
theorem norm_star_mul_self_withSeminorm (p : CStarSeminorm A) (x : p.WithSeminorm) :
    ‖star x * x‖ = ‖x‖ * ‖x‖ := by
  simpa only [norm_withSeminorm, ofWithSeminorm_mul, ofWithSeminorm_star] using
    p.map_star_mul_self (p.ofWithSeminorm x)

end WithSeminorm

/-! ### Hausdorff C⋆-completion of a C⋆-seminorm -/

section CompletionNonUnital

variable {A : Type*} [NonUnitalRing A] [Module ℂ A] [StarRing A]

/-- The Hausdorff C⋆-completion of `A` with respect to a C⋆-seminorm `p : CStarSeminorm A`. -/
@[expose] def Completion (p : CStarSeminorm A) : Type _ :=
  UniformSpace.Completion p.WithSeminorm

variable [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]

/-- The completion of a complex ⋆-algebra in a C⋆-seminorm is a nonunital C⋆-algebra. -/
noncomputable instance (priority := 50) instNonUnitalCStarAlgebra (p : CStarSeminorm A) :
    NonUnitalCStarAlgebra p.Completion :=
  ({ toCStarRing :=
        UniformSpace.Completion.cstarRing fun x => (p.norm_star_mul_self_withSeminorm x).ge } :
    NonUnitalCStarAlgebra (UniformSpace.Completion p.WithSeminorm))

/-- The canonical nonunital ⋆-homomorphism from `A` into its C⋆-completion `p.Completion`, with
dense range and `‖p.ofNonUnital x‖ = p x`. -/
noncomputable def ofNonUnital (p : CStarSeminorm A) : A →⋆ₙₐ[ℂ] p.Completion where
  toFun x := (p.toWithSeminorm x : UniformSpace.Completion p.WithSeminorm)
  map_smul' c x := UniformSpace.Completion.coe_smul c (p.toWithSeminorm x)
  map_zero' := UniformSpace.Completion.coe_zero
  map_add' x y := UniformSpace.Completion.coe_add (p.toWithSeminorm x) (p.toWithSeminorm y)
  map_mul' x y := UniformSpace.Completion.coe_mul' (p.toWithSeminorm x) (p.toWithSeminorm y)
  map_star' x := UniformSpace.Completion.coe_star (p.toWithSeminorm x)

/-- The norm of `p.ofNonUnital x` in `p.Completion` equals `p x`. -/
@[simp]
theorem norm_ofNonUnital (p : CStarSeminorm A) (x : A) :
    ‖p.ofNonUnital x‖ = p x :=
  UniformSpace.Completion.norm_coe (p.toWithSeminorm x)

/-- The image of `p.ofNonUnital` is dense in `p.Completion`. -/
theorem denseRange_ofNonUnital (p : CStarSeminorm A) : DenseRange p.ofNonUnital :=
  UniformSpace.Completion.denseRange_coe.comp p.toWithSeminorm.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

/-- To prove a closed property of every element of `p.Completion`, it suffices to prove it on the
dense image `p.ofNonUnital`. -/
@[elab_as_elim]
theorem induction_on {p : CStarSeminorm A} {P : p.Completion → Prop} (x : p.Completion)
    (hP : IsClosed {x | P x}) (ih : ∀ a : A, P (p.ofNonUnital a)) : P x :=
  UniformSpace.Completion.induction_on (p := P) x hP fun a => ih (p.ofWithSeminorm a)

/-- Continuous linear maps out of `p.Completion` into a Hausdorff space are determined on
`p.ofNonUnital`. -/
@[ext]
theorem continuousLinearMap_ext {p : CStarSeminorm A} {E : Type*} [TopologicalSpace E] [T2Space E]
    [AddCommMonoid E] [Module ℂ E] {S T : p.Completion →L[ℂ] E}
    (h : ∀ a, S (p.ofNonUnital a) = T (p.ofNonUnital a)) : S = T :=
  ContinuousLinearMap.ext fun x => induction_on x (isClosed_eq S.continuous T.continuous) h

open scoped _root_.CStarAlgebra in
/-- Nonunital ⋆-homomorphisms from `p.Completion` into a nonunital C⋆-algebra are determined on
`p.ofNonUnital`. -/
@[ext]
theorem nonUnitalStarAlgHom_ext {p : CStarSeminorm A} {B : Type*} [NonUnitalCStarAlgebra B]
    {φ ψ : p.Completion →⋆ₙₐ[ℂ] B} (h : φ.comp p.ofNonUnital = ψ.comp p.ofNonUnital) :
    φ = ψ :=
  NonUnitalStarAlgHom.ext fun x =>
    induction_on x (isClosed_eq (map_continuous φ) (map_continuous ψ)) fun a => congr($h a)

/-- Extend a linear map `T : A →ₗ[ℂ] E` bounded by `C * p x` to a continuous linear map
`p.Completion →L[ℂ] E`. -/
noncomputable def liftCLM (p : CStarSeminorm A) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (T : A →ₗ[ℂ] E) (C : ℝ)
    (hT : ∀ x, ‖T x‖ ≤ C * p x) : p.Completion →L[ℂ] E :=
  let toLin : p.WithSeminorm →ₗ[ℂ] A :=
    { toFun := p.ofWithSeminorm
      map_add' := p.ofWithSeminorm_add
      map_smul' := p.ofWithSeminorm_smul }
  ((T.comp toLin).mkContinuous C fun x => hT (p.ofWithSeminorm x)).fromCompletion

@[simp]
theorem liftCLM_ofNonUnital (p : CStarSeminorm A) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (T : A →ₗ[ℂ] E) (C : ℝ)
    (hT : ∀ x, ‖T x‖ ≤ C * p x) (x : A) :
    p.liftCLM T C hT (p.ofNonUnital x) = T x :=
  (ContinuousLinearMap.fromCompletion_apply_coe _ (p.toWithSeminorm x)).trans (rfl)

/-- Extend a nonunital ⋆-homomorphism bounded by `p` to a nonunital ⋆-homomorphism on
`p.Completion`. -/
noncomputable def liftNonUnital (p : CStarSeminorm A) {B : Type*} [NonUnitalNormedRing B]
    [StarRing B] [ContinuousStar B] [CompleteSpace B] [NormedSpace ℂ B]
    (ρ : A →⋆ₙₐ[ℂ] B) (hρ : ∀ x, ‖ρ x‖ ≤ p x) : p.Completion →⋆ₙₐ[ℂ] B where
  toFun := p.liftCLM (ρ : A →ₗ[ℂ] B) 1 fun x => by rw [one_mul]; exact hρ x
  map_smul' := map_smul _
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x using induction_on with
    | hP => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih a =>
      induction y using induction_on with
      | hP => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih b =>
        rw [← map_mul p.ofNonUnital, liftCLM_ofNonUnital, liftCLM_ofNonUnital,
          liftCLM_ofNonUnital]
        exact map_mul ρ a b
  map_star' x := by
    induction x using induction_on with
    | hP => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih a =>
      rw [← StarHomClass.map_star p.ofNonUnital, liftCLM_ofNonUnital, liftCLM_ofNonUnital]
      exact StarHomClass.map_star ρ a

@[simp]
theorem liftNonUnital_ofNonUnital (p : CStarSeminorm A) {B : Type*} [NonUnitalNormedRing B]
    [StarRing B] [ContinuousStar B] [CompleteSpace B] [NormedSpace ℂ B]
    (ρ : A →⋆ₙₐ[ℂ] B) (hρ : ∀ x, ‖ρ x‖ ≤ p x) (x : A) :
    p.liftNonUnital ρ hρ (p.ofNonUnital x) = ρ x :=
  p.liftCLM_ofNonUnital (ρ : A →ₗ[ℂ] B) 1 (fun y => by rw [one_mul]; exact hρ y) x

@[simp]
theorem liftNonUnital_comp_ofNonUnital (p : CStarSeminorm A) {B : Type*} [NonUnitalNormedRing B]
    [StarRing B] [ContinuousStar B] [CompleteSpace B] [NormedSpace ℂ B]
    (ρ : A →⋆ₙₐ[ℂ] B) (hρ : ∀ x, ‖ρ x‖ ≤ p x) :
    (p.liftNonUnital ρ hρ).comp p.ofNonUnital = ρ :=
  NonUnitalStarAlgHom.ext (p.liftNonUnital_ofNonUnital ρ hρ)

end CompletionNonUnital

section CompletionUnital

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

/-- The completion of a unital complex ⋆-algebra in a C⋆-seminorm is a unital C⋆-algebra.
Built directly over `instNonUnitalCStarAlgebra` so that `CStarAlgebra.toNonUnitalCStarAlgebra`
agrees definitionally with `instNonUnitalCStarAlgebra`. -/
noncomputable instance instCStarAlgebra (p : CStarSeminorm A) :
    CStarAlgebra p.Completion :=
  letI ringInst : Ring p.Completion :=
    { (instNonUnitalCStarAlgebra p).toNonUnitalRing with
      one := p.ofNonUnital 1
      one_mul x := by
        induction x using induction_on with
        | hP => exact isClosed_eq (by fun_prop) continuous_id
        | ih a =>
          exact (map_mul p.ofNonUnital 1 a).symm.trans (by rw [one_mul])
      mul_one x := by
        induction x using induction_on with
        | hP => exact isClosed_eq (by fun_prop) continuous_id
        | ih a =>
          exact (map_mul p.ofNonUnital a 1).symm.trans (by rw [mul_one]) }
  letI algInst : Algebra ℂ p.Completion :=
    { (instNonUnitalCStarAlgebra p).toSMul with
      algebraMap :=
        { toFun c := p.ofNonUnital (algebraMap ℂ A c)
          map_one' := by rw [map_one]; rfl
          map_mul' c d := by rw [map_mul, map_mul]
          map_zero' := by rw [map_zero, map_zero]
          map_add' c d := by rw [map_add, map_add] }
      commutes' c x := by
        induction x using induction_on with
        | hP => exact isClosed_eq (by fun_prop) (by fun_prop)
        | ih a =>
          exact (map_mul p.ofNonUnital (algebraMap ℂ A c) a).symm.trans <|
            (congrArg p.ofNonUnital (Algebra.commutes c a)).trans
              (map_mul p.ofNonUnital a (algebraMap ℂ A c))
      smul_def' c x := by
        induction x using induction_on with
        | hP => exact isClosed_eq (by fun_prop) (by fun_prop)
        | ih a =>
          exact (map_smul p.ofNonUnital c a).symm.trans <|
            (congrArg p.ofNonUnital (Algebra.smul_def c a)).trans
              (map_mul p.ofNonUnital (algebraMap ℂ A c) a) }
  { (instNonUnitalCStarAlgebra p).toNonUnitalNormedRing, ringInst,
    (instNonUnitalCStarAlgebra p).toStarRing, (instNonUnitalCStarAlgebra p).toCompleteSpace,
    (instNonUnitalCStarAlgebra p).toCStarRing, algInst,
    (instNonUnitalCStarAlgebra p).toStarModule with
    norm_smul_le := (instNonUnitalCStarAlgebra p).norm_smul_le }

/-- The canonical unital ⋆-homomorphism from a unital complex ⋆-algebra `A` into its C⋆-completion
`p.Completion`, with dense range and `‖p.of x‖ = p x`. -/
@[expose] noncomputable def of (p : CStarSeminorm A) : A →⋆ₐ[ℂ] p.Completion where
  __ := p.ofNonUnital
  map_one' := rfl
  commutes' _ := rfl

@[simp]
theorem toNonUnitalStarAlgHom_of (p : CStarSeminorm A) :
    p.of.toNonUnitalStarAlgHom = p.ofNonUnital :=
  (rfl)

/-- The norm of `p.of x` in `p.Completion` equals `p x`. -/
@[simp]
theorem norm_of (p : CStarSeminorm A) (x : A) : ‖p.of x‖ = p x :=
  p.norm_ofNonUnital x

/-- The image of `p.of` is dense in `p.Completion`. -/
theorem denseRange_of (p : CStarSeminorm A) : DenseRange p.of :=
  p.denseRange_ofNonUnital

/-- If `p 1 = 1`, then the unit of `p.Completion` has norm `1`. -/
theorem normOneClass_completion (p : CStarSeminorm A) (h1 : p 1 = 1) :
    NormOneClass p.Completion where
  norm_one := by
    rw [← map_one p.of, p.norm_of, h1]

open scoped _root_.CStarAlgebra in
/-- Unital ⋆-homomorphisms from `p.Completion` into a unital C⋆-algebra are determined on `p.of`. -/
@[ext]
theorem starAlgHom_ext {p : CStarSeminorm A} {B : Type*} [CStarAlgebra B]
    {φ ψ : p.Completion →⋆ₐ[ℂ] B} (h : φ.comp p.of = ψ.comp p.of) : φ = ψ :=
  StarAlgHom.ext fun x =>
    induction_on x (isClosed_eq (map_continuous φ) (map_continuous ψ)) fun a => congr($h a)

@[simp]
theorem liftCLM_of (p : CStarSeminorm A) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (T : A →ₗ[ℂ] E) (C : ℝ)
    (hT : ∀ x, ‖T x‖ ≤ C * p x) (x : A) :
    p.liftCLM T C hT (p.of x) = T x :=
  p.liftCLM_ofNonUnital T C hT x

/-- Extend a unital ⋆-homomorphism bounded by `p` to a unital ⋆-homomorphism on `p.Completion`. -/
noncomputable def lift (p : CStarSeminorm A) {B : Type*} [NormedRing B] [StarRing B]
    [ContinuousStar B] [CompleteSpace B] [NormedAlgebra ℂ B]
    (ρ : A →⋆ₐ[ℂ] B) (hρ : ∀ x, ‖ρ x‖ ≤ p x) : p.Completion →⋆ₐ[ℂ] B where
  __ := p.liftNonUnital ρ.toNonUnitalStarAlgHom hρ
  map_one' := (p.liftNonUnital_ofNonUnital ρ.toNonUnitalStarAlgHom hρ 1).trans (map_one ρ)
  commutes' c :=
    (p.liftNonUnital_ofNonUnital ρ.toNonUnitalStarAlgHom hρ (algebraMap ℂ A c)).trans
      (AlgHomClass.commutes ρ c)

@[simp]
theorem toNonUnitalStarAlgHom_lift (p : CStarSeminorm A) {B : Type*} [NormedRing B] [StarRing B]
    [ContinuousStar B] [CompleteSpace B] [NormedAlgebra ℂ B]
    (ρ : A →⋆ₐ[ℂ] B) (hρ : ∀ x, ‖ρ x‖ ≤ p x) :
    (p.lift ρ hρ).toNonUnitalStarAlgHom = p.liftNonUnital ρ.toNonUnitalStarAlgHom hρ :=
  (rfl)

@[simp]
theorem lift_of (p : CStarSeminorm A) {B : Type*} [NormedRing B] [StarRing B]
    [ContinuousStar B] [CompleteSpace B] [NormedAlgebra ℂ B]
    (ρ : A →⋆ₐ[ℂ] B) (hρ : ∀ x, ‖ρ x‖ ≤ p x) (x : A) :
    p.lift ρ hρ (p.of x) = ρ x :=
  p.liftNonUnital_ofNonUnital ρ.toNonUnitalStarAlgHom hρ x

@[simp]
theorem lift_comp_of (p : CStarSeminorm A) {B : Type*} [NormedRing B] [StarRing B]
    [ContinuousStar B] [CompleteSpace B] [NormedAlgebra ℂ B]
    (ρ : A →⋆ₐ[ℂ] B) (hρ : ∀ x, ‖ρ x‖ ≤ p x) :
    (p.lift ρ hρ).comp p.of = ρ :=
  StarAlgHom.ext (p.lift_of ρ hρ)

end CompletionUnital

end CStarSeminorm

end TauCeti
