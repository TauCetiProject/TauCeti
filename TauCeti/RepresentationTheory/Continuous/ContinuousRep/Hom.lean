/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Basic

/-!
# Morphisms of jointly continuous representations

A morphism between two jointly continuous representations `ρ : ContinuousRep Γ A M` and
`σ : ContinuousRep Γ A N` is an `A`-linear continuous map `M → N` that intertwines the actions of
`Γ`. Joint continuity is a condition on the objects `ρ` and `σ`, not an extra condition on maps
between them, so when `A` is a ring and `M`, `N` are topological additive groups, morphisms of
`ContinuousRep` agree with Mathlib's `ContIntertwiningMap` on the underlying `ContRepresentation`s.

When `M` carries its `A`-module topology (`IsModuleTopology A M`) and `N` is a topological
`A`-module (`ContinuousAdd N`, `ContinuousSMul A N`), every `A`-linear map `M →ₗ[A] N` is
automatically continuous. Forgetting continuity therefore identifies `ContinuousRep.Hom ρ σ` with
the algebraic intertwiner space
`Representation.IntertwiningMap ρ.toRepresentation σ.toRepresentation`
(`Hom.intertwiningMapAddEquiv`, `Hom.intertwiningMapEquiv`).

## Main definitions

* `TauCeti.ContinuousRep.Hom ρ σ`: equivariant continuous `A`-linear maps from `ρ` to `σ`, with
  identity `Hom.id`, composition `Hom.comp`, and additive, module, and endomorphism-ring instances.
* `TauCeti.ContinuousRep.Hom.ofContinuousLinearMap`: builds a morphism from a continuous linear map
  and pointwise equivariance.
* `TauCeti.ContinuousRep.Hom.ofIntertwiningMap`: automatic continuity of algebraic intertwining maps
  out of a module carrying its module topology.
* `TauCeti.ContinuousRep.Hom.intertwiningMapAddEquiv` and
  `TauCeti.ContinuousRep.Hom.intertwiningMapEquiv`: additive and `A`-linear equivalences between
  `Hom ρ σ` and `Representation.IntertwiningMap ρ.toRepresentation σ.toRepresentation`.
* `TauCeti.ContinuousRep.Hom.equivContIntertwiningMap`: additive equivalence with
  `ContIntertwiningMap ρ.toContRepresentation σ.toContRepresentation`.
* `TauCeti.ContinuousRep.Iso.toHom` and `TauCeti.ContinuousRep.Iso.ofHomInv`: conversion between
  isomorphisms and mutually inverse morphisms.
* `TauCeti.ContinuousRep.Hom.baseChange`: scalar extension of a morphism along a continuous
  coefficient map.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1.
* G. Böckle, M. Harris, C. Khare and J. A. Thorne, *Potential automorphy of `G`-local systems*, §2.
-/

public section

open scoped TensorProduct

namespace TauCeti.ContinuousRep

section Basic

variable {Γ A M N P Q : Type*} [Monoid Γ] [TopologicalSpace Γ] [Semiring A]
  [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [AddCommMonoid N] [Module A N] [TopologicalSpace N]
  [AddCommMonoid P] [Module A P] [TopologicalSpace P]
  [AddCommMonoid Q] [Module A Q] [TopologicalSpace Q]

/-- **A morphism of continuous representations**: an equivariant continuous `A`-linear map. -/
structure Hom (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) extends
    toIntertwiningMap : ρ.toRepresentation.IntertwiningMap σ.toRepresentation,
    toContinuousLinearMap : M →L[A] N

/-- The algebraic intertwining map underlying a morphism of continuous representations. -/
add_decl_doc Hom.toIntertwiningMap

/-- The continuous linear map underlying a morphism of continuous representations. -/
add_decl_doc Hom.toContinuousLinearMap

namespace Hom

variable {ρ : ContinuousRep Γ A M} {σ : ContinuousRep Γ A N} {τ : ContinuousRep Γ A P}
  {υ : ContinuousRep Γ A Q}

/-- Two morphisms with the same underlying continuous linear map are equal. -/
theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap : Hom ρ σ → M →L[A] N) := by
  rintro ⟨⟨f, hf⟩, cf⟩ ⟨⟨g, hg⟩, cg⟩ h
  have hfg : f = g := congrArg ContinuousLinearMap.toLinearMap h
  subst hfg
  rfl

/-- Two morphisms with the same underlying algebraic intertwining map are equal. -/
theorem toIntertwiningMap_injective :
    Function.Injective (toIntertwiningMap : Hom ρ σ → _) := by
  rintro ⟨f, _⟩ ⟨g, _⟩ h
  subst h
  rfl

/-- Two morphisms with the same underlying linear map are equal. -/
theorem toLinearMap_injective :
    Function.Injective (fun f : Hom ρ σ => f.toLinearMap) :=
  fun _ _ h => toIntertwiningMap_injective (Representation.IntertwiningMap.ext h)

instance : FunLike (Hom ρ σ) M N where
  coe f := f.toFun
  coe_injective _ _ h :=
    toIntertwiningMap_injective (DFunLike.coe_injective h)

instance : ContinuousLinearMapClass (Hom ρ σ) A M N where
  map_add f := f.map_add'
  map_smulₛₗ f := f.map_smul'
  map_continuous f := f.cont

/-- Forgetting continuity does not change the underlying function of a morphism. -/
@[simp]
theorem coe_toIntertwiningMap (f : Hom ρ σ) : ⇑f.toIntertwiningMap = f :=
  (rfl)

/-- Forgetting equivariance does not change the underlying function of a morphism. -/
theorem coe_toContinuousLinearMap (f : Hom ρ σ) : ⇑f.toContinuousLinearMap = f :=
  (rfl)

/-- Evaluating the underlying algebraic intertwining map agrees with evaluating the morphism. -/
theorem toIntertwiningMap_apply (f : Hom ρ σ) (x : M) : f.toIntertwiningMap x = f x :=
  (rfl)

/-- Evaluating the underlying continuous linear map agrees with evaluating the morphism. -/
theorem toContinuousLinearMap_apply (f : Hom ρ σ) (x : M) : f.toContinuousLinearMap x = f x :=
  (rfl)

/-- **Extensionality of morphisms.** Two morphisms agreeing on every vector are equal. -/
@[ext]
theorem ext {f g : Hom ρ σ} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- **A morphism of continuous representations is equivariant.** -/
theorem isIntertwining (f : Hom ρ σ) (g : Γ) (x : M) : f (ρ g x) = σ g (f x) :=
  f.toIntertwiningMap.isIntertwining _ _ g x

/-- Equivariance of a morphism at the level of underlying continuous linear maps. -/
theorem toContinuousLinearMap_comp_eq_comp (f : Hom ρ σ) (g : Γ) :
    f.toContinuousLinearMap.comp ⟨ρ g, ρ.continuous_apply g⟩ =
      (⟨σ g, σ.continuous_apply g⟩ : N →L[A] N).comp f.toContinuousLinearMap := by
  ext x
  exact f.isIntertwining g x

/-- Builds a morphism of continuous representations from a continuous linear map and pointwise
equivariance. -/
def ofContinuousLinearMap (f : M →L[A] N) (hf : ∀ g x, f (ρ g x) = σ g (f x)) : Hom ρ σ where
  toIntertwiningMap := f.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ hf
  cont := f.cont

/-- Evaluating `ofContinuousLinearMap` evaluates the given continuous linear map. -/
@[simp]
theorem ofContinuousLinearMap_apply (f : M →L[A] N) (hf : ∀ g x, f (ρ g x) = σ g (f x)) (x : M) :
    ofContinuousLinearMap f hf x = f x :=
  (rfl)

/-- The continuous linear map underlying `ofContinuousLinearMap` is the original map. -/
@[simp]
theorem toContinuousLinearMap_ofContinuousLinearMap (f : M →L[A] N)
    (hf : ∀ g x, f (ρ g x) = σ g (f x)) :
    (ofContinuousLinearMap f hf).toContinuousLinearMap = f :=
  (rfl)

/-- Re-bundling a morphism through `ofContinuousLinearMap` returns the original morphism. -/
@[simp]
theorem ofContinuousLinearMap_toContinuousLinearMap (f : Hom ρ σ) :
    ofContinuousLinearMap f.toContinuousLinearMap f.isIntertwining = f :=
  (rfl)

variable (ρ) in
/-- The identity morphism of a continuous representation. -/
def id : Hom ρ ρ where
  toIntertwiningMap := .id ρ.toRepresentation
  cont := continuous_id

/-- The composite of two morphisms of continuous representations. -/
def comp (f : Hom σ τ) (g : Hom ρ σ) : Hom ρ τ where
  toIntertwiningMap := f.toIntertwiningMap.comp g.toIntertwiningMap
  cont := f.cont.comp g.cont

/-- The identity morphism acts as the identity on vectors. -/
@[simp]
theorem id_apply (x : M) : id ρ x = x :=
  (rfl)

/-- A composite morphism acts by composing the underlying functions. -/
@[simp]
theorem comp_apply (f : Hom σ τ) (g : Hom ρ σ) (x : M) : f.comp g x = f (g x) :=
  (rfl)

/-- Left composition with the identity leaves a morphism unchanged. -/
@[simp]
theorem id_comp (f : Hom ρ σ) : (id σ).comp f = f := by
  ext
  rfl

/-- Right composition with the identity leaves a morphism unchanged. -/
@[simp]
theorem comp_id (f : Hom ρ σ) : f.comp (id ρ) = f := by
  ext
  rfl

/-- Composition of morphisms is associative. -/
theorem comp_assoc (f : Hom τ υ) (g : Hom σ τ) (h : Hom ρ σ) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  ext
  rfl

/-- Forgetting continuity sends the identity morphism to the identity intertwining map. -/
@[simp]
theorem toIntertwiningMap_id :
    (id ρ).toIntertwiningMap = .id ρ.toRepresentation :=
  (rfl)

/-- Forgetting continuity commutes with composition. -/
@[simp]
theorem toIntertwiningMap_comp (f : Hom σ τ) (g : Hom ρ σ) :
    (f.comp g).toIntertwiningMap = f.toIntertwiningMap.comp g.toIntertwiningMap :=
  (rfl)

/-- Forgetting equivariance sends the identity morphism to `ContinuousLinearMap.id`. -/
@[simp]
theorem toContinuousLinearMap_id :
    (id ρ).toContinuousLinearMap = ContinuousLinearMap.id A M :=
  (rfl)

/-- Forgetting equivariance commutes with composition. -/
@[simp]
theorem toContinuousLinearMap_comp (f : Hom σ τ) (g : Hom ρ σ) :
    (f.comp g).toContinuousLinearMap =
      f.toContinuousLinearMap.comp g.toContinuousLinearMap :=
  (rfl)

/-! ### Algebraic structure on morphisms -/

instance : Zero (Hom ρ σ) where
  zero :=
    { toIntertwiningMap := 0
      cont := continuous_const }

instance : IsZeroApply (Hom ρ σ) where

/-- Forgetting continuity preserves the zero morphism. -/
@[simp]
theorem toIntertwiningMap_zero : (0 : Hom ρ σ).toIntertwiningMap = 0 :=
  (rfl)

/-- Forgetting equivariance preserves the zero morphism. -/
@[simp]
theorem toContinuousLinearMap_zero : (0 : Hom ρ σ).toContinuousLinearMap = 0 :=
  (rfl)

instance : Inhabited (Hom ρ σ) := ⟨0⟩

/-- Composing with zero on the right yields zero. -/
@[simp]
theorem comp_zero (f : Hom σ τ) : f.comp (0 : Hom ρ σ) = 0 := by
  ext
  simp

/-- Composing with zero on the left yields zero. -/
@[simp]
theorem zero_comp (f : Hom ρ σ) : (0 : Hom σ τ).comp f = 0 := by
  ext
  simp

instance : One (Hom ρ ρ) where
  one := id ρ

instance : IsOneApplyEqSelf (Hom ρ ρ) where

instance : Mul (Hom ρ ρ) where
  mul := comp

instance : IsMulApplyEqComp (Hom ρ ρ) where

/-- The multiplicative identity of the endomorphism monoid is `Hom.id`. -/
theorem one_def : (1 : Hom ρ ρ) = id ρ :=
  (rfl)

/-- Multiplication in the endomorphism monoid is composition. -/
theorem mul_def (f g : Hom ρ ρ) : f * g = f.comp g :=
  (rfl)

/-- Forgetting equivariance preserves `1`. -/
@[simp]
theorem toContinuousLinearMap_one : (1 : Hom ρ ρ).toContinuousLinearMap = 1 :=
  (rfl)

/-- Forgetting equivariance preserves multiplication of endomorphisms. -/
@[simp]
theorem toContinuousLinearMap_mul (f g : Hom ρ ρ) :
    (f * g).toContinuousLinearMap = f.toContinuousLinearMap * g.toContinuousLinearMap :=
  (rfl)

instance : NPow (Hom ρ ρ) where
  npow := npowRec

instance : IsNPowApplyEqIterate (Hom ρ ρ) where
  pow_apply_eq_iterate f n x := by
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (f x)

instance : MonoidWithZero (Hom ρ ρ) :=
  FunLike.compMonoidWithZero

section ContinuousAdd

section Codomain

variable [ContinuousAdd N]

instance : Add (Hom ρ σ) where
  add f g :=
    { toIntertwiningMap := f.toIntertwiningMap + g.toIntertwiningMap
      cont := f.cont.add g.cont }

instance : IsAddApply (Hom ρ σ) where

/-- Forgetting continuity preserves addition of morphisms. -/
@[simp]
theorem toIntertwiningMap_add (f g : Hom ρ σ) :
    (f + g).toIntertwiningMap = f.toIntertwiningMap + g.toIntertwiningMap :=
  (rfl)

/-- Forgetting equivariance preserves addition of morphisms. -/
@[simp]
theorem toContinuousLinearMap_add (f g : Hom ρ σ) :
    (f + g).toContinuousLinearMap = f.toContinuousLinearMap + g.toContinuousLinearMap :=
  (rfl)

instance : SMul ℕ (Hom ρ σ) where
  smul n f :=
    { toIntertwiningMap := n • f.toIntertwiningMap
      cont := f.cont.const_smul n }

instance : IsSMulApply ℕ (Hom ρ σ) where

instance : AddCommMonoid (Hom ρ σ) :=
  FunLike.addCommMonoid

end Codomain

/-- Composition distributes over addition on the left. -/
theorem add_comp [ContinuousAdd P] (f₁ f₂ : Hom σ τ) (g : Hom ρ σ) :
    (f₁ + f₂).comp g = f₁.comp g + f₂.comp g := by
  ext
  simp

/-- Composition distributes over addition on the right. -/
theorem comp_add [ContinuousAdd N] [ContinuousAdd P] (f : Hom σ τ) (g₁ g₂ : Hom ρ σ) :
    f.comp (g₁ + g₂) = f.comp g₁ + f.comp g₂ := by
  ext
  simp

instance [ContinuousAdd M] : NatCast (Hom ρ ρ) where
  natCast n := n • (1 : Hom ρ ρ)

instance [ContinuousAdd M] : IsNatCastApplyEqSMul (Hom ρ ρ) where

instance [ContinuousAdd M] : Semiring (Hom ρ ρ) :=
  FunLike.compSemiring

end ContinuousAdd

section AddCommGroup

variable {W : Type*} [AddCommGroup W] [Module A W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  {σ' : ContinuousRep Γ A W}

instance : Neg (Hom ρ σ') where
  neg f :=
    { toIntertwiningMap := -f.toIntertwiningMap
      cont := f.cont.neg }

instance : IsNegApply (Hom ρ σ') where

/-- Forgetting continuity preserves negation. -/
@[simp]
theorem toIntertwiningMap_neg (f : Hom ρ σ') :
    (-f).toIntertwiningMap = -f.toIntertwiningMap :=
  (rfl)

instance : Sub (Hom ρ σ') where
  sub f g :=
    { toIntertwiningMap := f.toIntertwiningMap - g.toIntertwiningMap
      cont := f.cont.sub g.cont }

instance : IsSubApply (Hom ρ σ') where

/-- Forgetting continuity preserves subtraction. -/
@[simp]
theorem toIntertwiningMap_sub (f g : Hom ρ σ') :
    (f - g).toIntertwiningMap = f.toIntertwiningMap - g.toIntertwiningMap :=
  (rfl)

instance : SMul ℤ (Hom ρ σ') where
  smul z f :=
    { toIntertwiningMap := z • f.toIntertwiningMap
      cont := f.cont.const_smul z }

instance : IsSMulApply ℤ (Hom ρ σ') where

instance : AddCommGroup (Hom ρ σ') :=
  FunLike.addCommGroup

instance : IntCast (Hom σ' σ') where
  intCast z := z • (1 : Hom σ' σ')

instance : IsIntCastApplyEqSMul (Hom σ' σ') where

instance : Ring (Hom σ' σ') :=
  FunLike.compRing

end AddCommGroup

section ContinuousLinearMapNegSub

variable {R V W : Type*} [Ring R]
  [AddCommGroup V] [Module R V] [TopologicalSpace V]
  [AddCommGroup W] [Module R W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  {ρ₁ : ContinuousRep Γ R V} {ρ₂ : ContinuousRep Γ R W}

/-- Forgetting equivariance preserves negation. -/
@[simp]
theorem toContinuousLinearMap_neg (f : Hom ρ₁ ρ₂) :
    (-f).toContinuousLinearMap = -f.toContinuousLinearMap :=
  (rfl)

/-- Forgetting equivariance preserves subtraction. -/
@[simp]
theorem toContinuousLinearMap_sub (f g : Hom ρ₁ ρ₂) :
    (f - g).toContinuousLinearMap = f.toContinuousLinearMap - g.toContinuousLinearMap :=
  (rfl)

end ContinuousLinearMapNegSub

section Module

variable {R : Type*} [CommSemiring R]
  {V₁ V₂ : Type*} [AddCommMonoid V₁] [Module R V₁] [TopologicalSpace V₁]
  [AddCommMonoid V₂] [Module R V₂] [TopologicalSpace V₂] [ContinuousConstSMul R V₂]
  {ρ₁ : ContinuousRep Γ R V₁} {ρ₂ : ContinuousRep Γ R V₂}

instance : SMul R (Hom ρ₁ ρ₂) where
  smul r f :=
    { toIntertwiningMap := r • f.toIntertwiningMap
      cont := f.cont.const_smul r }

instance : IsSMulApply R (Hom ρ₁ ρ₂) where

/-- Forgetting continuity preserves scalar multiplication. -/
@[simp]
theorem toIntertwiningMap_smul (r : R) (f : Hom ρ₁ ρ₂) :
    (r • f).toIntertwiningMap = r • f.toIntertwiningMap :=
  (rfl)

/-- Forgetting equivariance preserves scalar multiplication. -/
@[simp]
theorem toContinuousLinearMap_smul (r : R) (f : Hom ρ₁ ρ₂) :
    (r • f).toContinuousLinearMap = r • f.toContinuousLinearMap :=
  (rfl)

instance : MulAction R (Hom ρ₁ ρ₂) :=
  FunLike.mulAction

instance [ContinuousAdd V₂] : Module R (Hom ρ₁ ρ₂) :=
  FunLike.module

end Module

/-! ### Comparison with `ContIntertwiningMap` -/

section ContIntertwiningMap

variable {R V W : Type*} [Ring R]
  [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [AddCommGroup W] [Module R W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  {ρ₁ : ContinuousRep Γ R V} {ρ₂ : ContinuousRep Γ R W}

/-- The Mathlib `ContIntertwiningMap` underlying a morphism of `ContinuousRep`s. -/
def toContIntertwiningMap (f : Hom ρ₁ ρ₂) :
    ContIntertwiningMap ρ₁.toContRepresentation ρ₂.toContRepresentation where
  toContinuousLinearMap := f.toContinuousLinearMap
  isIntertwining' g := by
    ext x
    simpa using f.isIntertwining g x

/-- Every `ContIntertwiningMap` between the underlying `ContRepresentation`s is a morphism of
`ContinuousRep`s. -/
def ofContIntertwiningMap
    (f : ContIntertwiningMap ρ₁.toContRepresentation ρ₂.toContRepresentation) :
    Hom ρ₁ ρ₂ where
  toIntertwiningMap := f.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ fun g x => by
    rw [coe_toRepresentation, coe_toRepresentation, ← toContRepresentation_apply,
      ← toContRepresentation_apply]
    exact f.isIntertwining g x
  cont := f.cont

/-- Evaluating `toContIntertwiningMap` agrees with evaluating the morphism. -/
@[simp]
theorem toContIntertwiningMap_apply (f : Hom ρ₁ ρ₂) (x : V) :
    f.toContIntertwiningMap x = f x :=
  (rfl)

/-- Evaluating `ofContIntertwiningMap` agrees with evaluating the `ContIntertwiningMap`. -/
@[simp]
theorem ofContIntertwiningMap_apply
    (f : ContIntertwiningMap ρ₁.toContRepresentation ρ₂.toContRepresentation) (x : V) :
    ofContIntertwiningMap f x = f x :=
  (rfl)

/-- `toContIntertwiningMap` sends the identity morphism to `ContIntertwiningMap.id`. -/
@[simp]
theorem toContIntertwiningMap_id :
    (id ρ₁).toContIntertwiningMap = .id := by
  ext
  rfl

/-- `toContIntertwiningMap` commutes with composition. -/
@[simp]
theorem toContIntertwiningMap_comp {U : Type*} [AddCommGroup U] [Module R U] [TopologicalSpace U]
    [IsTopologicalAddGroup U] {ρ₃ : ContinuousRep Γ R U} (f : Hom ρ₂ ρ₃) (g : Hom ρ₁ ρ₂) :
    (f.comp g).toContIntertwiningMap = f.toContIntertwiningMap.comp g.toContIntertwiningMap := by
  ext
  rfl

/-- Morphisms of `ContinuousRep`s form a full subcategory of `ContRepresentation`: they are
additively equivalent to `ContIntertwiningMap`s between the underlying `ContRepresentation`s. -/
def equivContIntertwiningMap :
    Hom ρ₁ ρ₂ ≃+ ContIntertwiningMap ρ₁.toContRepresentation ρ₂.toContRepresentation where
  toFun := toContIntertwiningMap
  invFun := ofContIntertwiningMap
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_add' _ _ := by ext; rfl

@[simp]
theorem equivContIntertwiningMap_apply (f : Hom ρ₁ ρ₂) :
    equivContIntertwiningMap f = f.toContIntertwiningMap :=
  (rfl)

@[simp]
theorem equivContIntertwiningMap_symm_apply
    (f : ContIntertwiningMap ρ₁.toContRepresentation ρ₂.toContRepresentation) :
    equivContIntertwiningMap.symm f = ofContIntertwiningMap f :=
  (rfl)

end ContIntertwiningMap

section ContIntertwiningMapLinear

variable {R V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [AddCommGroup W] [Module R W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousConstSMul R W]
  {ρ₁ : ContinuousRep Γ R V} {ρ₂ : ContinuousRep Γ R W}

/-- Over a commutative ring, morphisms of `ContinuousRep`s are `R`-linearly equivalent to
`ContIntertwiningMap`s between the underlying `ContRepresentation`s. -/
def linearEquivContIntertwiningMap :
    Hom ρ₁ ρ₂ ≃ₗ[R] ContIntertwiningMap ρ₁.toContRepresentation ρ₂.toContRepresentation where
  __ := equivContIntertwiningMap
  map_smul' _ _ := by ext; rfl

@[simp]
theorem linearEquivContIntertwiningMap_apply (f : Hom ρ₁ ρ₂) :
    linearEquivContIntertwiningMap f = f.toContIntertwiningMap :=
  (rfl)

@[simp]
theorem linearEquivContIntertwiningMap_symm_apply
    (f : ContIntertwiningMap ρ₁.toContRepresentation ρ₂.toContRepresentation) :
    linearEquivContIntertwiningMap.symm f = ofContIntertwiningMap f :=
  (rfl)

end ContIntertwiningMapLinear

/-! ### Automatic continuity under the module topology -/

section AutomaticContinuity

variable [TopologicalSpace A] [IsModuleTopology A M] [ContinuousAdd N] [ContinuousSMul A N]

/-- **Automatic continuity of morphisms.** From a module carrying its module topology into any
topological `A`-module, every equivariant `A`-linear map is a morphism of continuous
representations. -/
def ofIntertwiningMap (f : ρ.toRepresentation.IntertwiningMap σ.toRepresentation) : Hom ρ σ where
  toIntertwiningMap := f
  cont := IsModuleTopology.continuous_of_linearMap f.toLinearMap

/-- `ofIntertwiningMap` has the same values as the underlying intertwining map. -/
@[simp]
theorem ofIntertwiningMap_apply (f : ρ.toRepresentation.IntertwiningMap σ.toRepresentation)
    (x : M) : ofIntertwiningMap f x = f x :=
  (rfl)

/-- Forgetting continuity recovers the original intertwining map. -/
@[simp]
theorem toIntertwiningMap_ofIntertwiningMap
    (f : ρ.toRepresentation.IntertwiningMap σ.toRepresentation) :
    (ofIntertwiningMap f).toIntertwiningMap = f :=
  (rfl)

/-- Re-bundling a morphism through `ofIntertwiningMap` returns the original morphism. -/
@[simp]
theorem ofIntertwiningMap_toIntertwiningMap (f : Hom ρ σ) :
    ofIntertwiningMap f.toIntertwiningMap = f :=
  (rfl)

/-- **Automatic continuity as an additive equivalence.** When the source carries its module topology
and the target is a topological `A`-module, forgetting continuity identifies morphisms of
continuous representations with algebraic intertwining maps. -/
def intertwiningMapAddEquiv :
    Hom ρ σ ≃+ ρ.toRepresentation.IntertwiningMap σ.toRepresentation where
  toFun := toIntertwiningMap
  invFun := ofIntertwiningMap
  left_inv := ofIntertwiningMap_toIntertwiningMap
  right_inv := toIntertwiningMap_ofIntertwiningMap
  map_add' _ _ := rfl

@[simp]
theorem intertwiningMapAddEquiv_apply (f : Hom ρ σ) :
    intertwiningMapAddEquiv f = f.toIntertwiningMap :=
  (rfl)

@[simp]
theorem intertwiningMapAddEquiv_symm_apply
    (f : ρ.toRepresentation.IntertwiningMap σ.toRepresentation) :
    intertwiningMapAddEquiv.symm f = ofIntertwiningMap f :=
  (rfl)

end AutomaticContinuity

section AutomaticContinuityIdComp

variable [TopologicalSpace A]

/-- `ofIntertwiningMap` sends the identity intertwining map to `Hom.id`. -/
@[simp]
theorem ofIntertwiningMap_id [IsModuleTopology A M] [ContinuousAdd M] :
    ofIntertwiningMap (.id ρ.toRepresentation) = id ρ :=
  (rfl)

/-- `ofIntertwiningMap` preserves composition. -/
@[simp]
theorem ofIntertwiningMap_comp [IsModuleTopology A M] [IsModuleTopology A N]
    [ContinuousAdd N] [ContinuousAdd P] [ContinuousSMul A P]
    (f : σ.toRepresentation.IntertwiningMap τ.toRepresentation)
    (g : ρ.toRepresentation.IntertwiningMap σ.toRepresentation) :
    ofIntertwiningMap (f.comp g) = (ofIntertwiningMap f).comp (ofIntertwiningMap g) :=
  (rfl)

end AutomaticContinuityIdComp

section AutomaticContinuityLinear

variable {R V₁ V₂ : Type*} [CommSemiring R] [TopologicalSpace R]
  [AddCommMonoid V₁] [Module R V₁] [TopologicalSpace V₁] [IsModuleTopology R V₁]
  [AddCommMonoid V₂] [Module R V₂] [TopologicalSpace V₂] [ContinuousAdd V₂] [ContinuousSMul R V₂]
  {ρ₁ : ContinuousRep Γ R V₁} {ρ₂ : ContinuousRep Γ R V₂}

/-- **Automatic continuity as an `R`-linear equivalence.** Over a commutative semiring, when the
source carries its module topology and the target is a topological `R`-module, forgetting
continuity is an `R`-linear isomorphism between `Hom ρ₁ ρ₂` and the algebraic intertwining maps. -/
def intertwiningMapEquiv :
    Hom ρ₁ ρ₂ ≃ₗ[R] ρ₁.toRepresentation.IntertwiningMap ρ₂.toRepresentation where
  __ := intertwiningMapAddEquiv
  map_smul' _ _ := rfl

@[simp]
theorem intertwiningMapEquiv_apply (f : Hom ρ₁ ρ₂) :
    intertwiningMapEquiv f = f.toIntertwiningMap :=
  (rfl)

@[simp]
theorem intertwiningMapEquiv_symm_apply
    (f : ρ₁.toRepresentation.IntertwiningMap ρ₂.toRepresentation) :
    intertwiningMapEquiv.symm f = ofIntertwiningMap f :=
  (rfl)

end AutomaticContinuityLinear

end Hom

/-! ### Compatibility with isomorphisms -/

namespace Iso

variable {ρ : ContinuousRep Γ A M} {σ : ContinuousRep Γ A N} {τ : ContinuousRep Γ A P}

/-- The morphism of continuous representations underlying an isomorphism. -/
def toHom (e : Iso ρ σ) : Hom ρ σ where
  toIntertwiningMap := e.toRepresentationEquiv.toIntertwiningMap
  cont := e.continuous_toFun

/-- `Iso.toHom` has the same underlying function as the isomorphism. -/
@[simp]
theorem coe_toHom (e : Iso ρ σ) : ⇑e.toHom = e :=
  (rfl)

/-- Evaluating `Iso.toHom` evaluates the isomorphism. -/
theorem toHom_apply (e : Iso ρ σ) (x : M) : e.toHom x = e x :=
  (rfl)

/-- The algebraic intertwining map of `e.toHom` is that of `e.toRepresentationEquiv`. -/
@[simp]
theorem toIntertwiningMap_toHom (e : Iso ρ σ) :
    e.toHom.toIntertwiningMap = e.toRepresentationEquiv.toIntertwiningMap :=
  (rfl)

/-- The continuous linear map of `e.toHom` is `e.toContinuousLinearEquiv.toContinuousLinearMap`. -/
@[simp]
theorem toContinuousLinearMap_toHom (e : Iso ρ σ) :
    e.toHom.toContinuousLinearMap = e.toContinuousLinearEquiv.toContinuousLinearMap :=
  (rfl)

/-- The identity isomorphism induces the identity morphism. -/
@[simp]
theorem toHom_refl : (refl ρ).toHom = .id ρ := by
  ext
  simp

/-- `Iso.trans` reverses into `Hom.comp`, matching function composition order. -/
@[simp]
theorem toHom_trans (e : Iso ρ σ) (f : Iso σ τ) :
    (e.trans f).toHom = f.toHom.comp e.toHom := by
  ext
  simp

/-- Composing an isomorphism with its inverse on the right gives the identity morphism. -/
@[simp]
theorem toHom_comp_symm_toHom (e : Iso ρ σ) : e.toHom.comp e.symm.toHom = .id σ := by
  ext
  simp

/-- Composing an isomorphism with its inverse on the left gives the identity morphism. -/
@[simp]
theorem symm_toHom_comp_toHom (e : Iso ρ σ) : e.symm.toHom.comp e.toHom = .id ρ := by
  ext
  simp

/-- `Iso.toHom` commutes with `Iso.ofEquiv` and `Hom.ofIntertwiningMap`. -/
@[simp]
theorem toHom_ofEquiv [TopologicalSpace A] [IsModuleTopology A M] [IsModuleTopology A N]
    [ContinuousAdd N] (e : ρ.toRepresentation.Equiv σ.toRepresentation) :
    (ofEquiv e).toHom = .ofIntertwiningMap e.toIntertwiningMap := by
  ext
  simp

/-- Builds an isomorphism of continuous representations from two mutually inverse morphisms. -/
def ofHomInv (f : Hom ρ σ) (g : Hom σ ρ) (hfg : g.comp f = .id ρ) (hgf : f.comp g = .id σ) :
    Iso ρ σ where
  toRepresentationEquiv :=
    .mk (LinearEquiv.ofLinearMap f.toLinearMap g.toLinearMap
      (LinearMap.ext fun x => congr($hgf x))
      (LinearMap.ext fun x => congr($hfg x))) f.isIntertwining'
  continuous_toFun := f.cont
  continuous_invFun := g.cont

@[simp]
theorem ofHomInv_apply (f : Hom ρ σ) (g : Hom σ ρ) (hfg : g.comp f = .id ρ)
    (hgf : f.comp g = .id σ) (x : M) :
    ofHomInv f g hfg hgf x = f x :=
  (rfl)

@[simp]
theorem toHom_ofHomInv (f : Hom ρ σ) (g : Hom σ ρ) (hfg : g.comp f = .id ρ)
    (hgf : f.comp g = .id σ) :
    (ofHomInv f g hfg hgf).toHom = f := by
  ext
  rfl

@[simp]
theorem ofHomInv_toHom (e : Iso ρ σ) :
    ofHomInv e.toHom e.symm.toHom e.symm_toHom_comp_toHom e.toHom_comp_symm_toHom = e := by
  ext
  rfl

@[simp]
theorem ofHomInv_symm (f : Hom ρ σ) (g : Hom σ ρ) (hfg : g.comp f = .id ρ)
    (hgf : f.comp g = .id σ) :
    (ofHomInv f g hfg hgf).symm = ofHomInv g f hgf hfg := by
  ext x
  apply EquivLike.injective (ofHomInv f g hfg hgf)
  simpa using congr($hgf x).symm

end Iso

end Basic

/-! ### Extension of scalars of morphisms -/

section BaseChange

variable {Γ A M N P : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommSemiring A] [TopologicalSpace A]
  [AddCommMonoid M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M]
  [AddCommMonoid N] [Module A N] [TopologicalSpace N] [IsModuleTopology A N] [Module.Finite A N]
  [AddCommMonoid P] [Module A P] [TopologicalSpace P] [IsModuleTopology A P] [Module.Finite A P]

variable (B : Type*) [Ring B] [TopologicalSpace B] [IsTopologicalSemiring B] [Algebra A B]
  [ContinuousSMul A B]
  [TopologicalSpace (B ⊗[A] M)] [IsModuleTopology B (B ⊗[A] M)]
  [TopologicalSpace (B ⊗[A] N)] [IsModuleTopology B (B ⊗[A] N)]
  {ρ : ContinuousRep Γ A M} {σ : ContinuousRep Γ A N} {τ : ContinuousRep Γ A P}

/-- Extension of scalars of a morphism of continuous representations along a continuous coefficient
map `A → B`. -/
noncomputable def Hom.baseChange (f : Hom ρ σ) : Hom (ρ.baseChange B) (σ.baseChange B) :=
  haveI := IsModuleTopology.toContinuousAdd B (B ⊗[A] N)
  .ofIntertwiningMap
    { toLinearMap := (f.toIntertwiningMap.baseChange B).toLinearMap
      isIntertwining' g := by
        rw [toRepresentation_baseChange, toRepresentation_baseChange]
        exact (f.toIntertwiningMap.baseChange B).isIntertwining' g }

/-- The linear map underlying `f.baseChange B` is the base change of `f.toLinearMap`. -/
@[simp]
theorem Hom.toLinearMap_baseChange (f : Hom ρ σ) :
    (f.baseChange B).toLinearMap = f.toLinearMap.baseChange B :=
  f.toIntertwiningMap.toLinearMap_baseChange B

/-- On pure tensors, `Hom.baseChange` acts on the second factor. -/
@[simp]
theorem Hom.baseChange_tmul (f : Hom ρ σ) (b : B) (x : M) :
    f.baseChange B (b ⊗ₜ x) = b ⊗ₜ f x :=
  f.toIntertwiningMap.baseChange_tmul B b x

/-- Scalar extension preserves the zero morphism. -/
@[simp]
theorem Hom.baseChange_zero :
    (0 : Hom ρ σ).baseChange B = 0 := by
  apply Hom.toLinearMap_injective
  simp

/-- Scalar extension preserves addition of morphisms. -/
@[simp]
theorem Hom.baseChange_add [ContinuousAdd N] [ContinuousAdd (B ⊗[A] N)] (f g : Hom ρ σ) :
    (f + g).baseChange B = f.baseChange B + g.baseChange B := by
  apply Hom.toLinearMap_injective
  simp

/-- Scalar extension preserves the identity morphism. -/
@[simp]
theorem Hom.baseChange_id :
    (Hom.id ρ).baseChange B = .id (ρ.baseChange B) := by
  apply Hom.toLinearMap_injective
  simp

/-- Scalar extension preserves composition of morphisms. -/
@[simp]
theorem Hom.baseChange_comp [TopologicalSpace (B ⊗[A] P)] [IsModuleTopology B (B ⊗[A] P)]
    (f : Hom σ τ) (g : Hom ρ σ) :
    (f.comp g).baseChange B = (f.baseChange B).comp (g.baseChange B) := by
  apply Hom.toLinearMap_injective
  simp [LinearMap.baseChange_comp]

/-- Scalar extension commutes with `Iso.toHom`. -/
@[simp]
theorem Iso.toHom_baseChange (e : Iso ρ σ) :
    (e.baseChange B).toHom = e.toHom.baseChange B := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul b m => simp
  | add x y hx hy => simp_all

end BaseChange

end TauCeti.ContinuousRep
