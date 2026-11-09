/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.RingQuot
public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# The signed symmetric algebra of an internally graded module

`TauCeti.SignedSym G` is the quotient of the tensor algebra by the Koszul swap relation
on homogeneous generators. Its universal property extends precisely the linear maps whose
homogeneous images satisfy that relation. In particular, degree-preserving linear maps induce
algebra maps, and degree-preserving linear equivalences induce algebra equivalences.

This is the generator-and-relations construction of the supercommutative orbit algebra in
J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1). We work over a
commutative ring; odd squares vanish when 2 is invertible. No grading of the quotient or
monomial basis is constructed in this file.

The construction uses Mathlib's `TensorAlgebra.lift` and `RingQuot.liftAlgHom` for the two
successive universal properties, rather than implementing a new quotient mechanism.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

/-- The Koszul swap relation on homogeneous generators of the tensor algebra. -/
inductive signedSwapRel (G : InternalGrading R V) :
    TensorAlgebra R V → TensorAlgebra R V → Prop where
  | swap (p q : ℤ) (x y : V) (hx : x ∈ G.piece p) (hy : y ∈ G.piece q) :
      signedSwapRel G (TensorAlgebra.ι R x * TensorAlgebra.ι R y)
        (((p * q).negOnePow : ℤ) • (TensorAlgebra.ι R y * TensorAlgebra.ι R x))

/-- The tensor algebra modulo signed swaps of homogeneous generators. -/
abbrev SignedSym (G : InternalGrading R V) := RingQuot (signedSwapRel G)

namespace SignedSym

variable (G : InternalGrading R V)

/-- The quotient map from the tensor algebra. -/
abbrev quotient : TensorAlgebra R V →ₐ[R] SignedSym G :=
  RingQuot.mkAlgHom R (signedSwapRel G)

/-- Every element of the signed symmetric algebra has a tensor-algebra representative. -/
theorem quotient_surjective : Function.Surjective (quotient G) :=
  RingQuot.mkAlgHom_surjective R (signedSwapRel G)

/-- The canonical linear map from the generating module. -/
def generator : V →ₗ[R] SignedSym G :=
  (quotient G).toLinearMap.comp (TensorAlgebra.ι R)

@[simp]
theorem quotient_ι (x : V) : quotient G (TensorAlgebra.ι R x) = generator G x := (rfl)

/-- The class of a tensor word is the product of its generators in the same order. -/
theorem quotient_tprod {n : ℕ} (x : Fin n → V) :
    quotient G (TensorAlgebra.tprod R V n x) =
      (List.ofFn fun i => generator G (x i)).prod := by
  simp only [TensorAlgebra.tprod_apply, map_list_prod, List.map_ofFn,
    Function.comp_def, quotient_ι]

/-- Homogeneous generators supercommute with the Koszul sign. -/
theorem generator_mul_generator {p q : ℤ} {x y : V}
    (hx : x ∈ G.piece p) (hy : y ∈ G.piece q) :
    generator G x * generator G y =
      ((p * q).negOnePow : ℤ) • (generator G y * generator G x) := by
  simpa only [← quotient_ι, ← map_mul, ← map_zsmul] using
    (RingQuot.mkAlgHom_rel R (signedSwapRel.swap p q x y hx hy))

/-- Induction on expressions in the generating module and the coefficient ring. -/
@[elab_as_elim]
theorem induction {P : SignedSym G → Prop}
    (algebraMap : ∀ r, P (algebraMap R (SignedSym G) r))
    (generator : ∀ x, P (SignedSym.generator G x))
    (mul : ∀ a b, P a → P b → P (a * b))
    (add : ∀ a b, P a → P b → P (a + b)) (a : SignedSym G) : P a := by
  obtain ⟨a, rfl⟩ := quotient_surjective G a
  induction a using TensorAlgebra.induction with
  | algebraMap r => simpa only [AlgHom.commutes] using algebraMap r
  | ι x => exact generator x
  | mul a b ha hb => simpa only [map_mul] using mul _ _ ha hb
  | add a b ha hb => simpa only [map_add] using add _ _ ha hb

variable {A : Type w} [Ring A] [Algebra R A]

/-- Algebra maps out of the signed symmetric algebra are determined by their generators. -/
@[ext 1200]
theorem hom_ext {f g : SignedSym G →ₐ[R] A}
    (h : ∀ x, f (generator G x) = g (generator G x)) : f = g := by
  apply RingQuot.ringQuot_ext'
  apply TensorAlgebra.hom_ext
  exact LinearMap.ext h

/-- Extend a linear map whose homogeneous images obey signed commutativity. No grading on the
receiving algebra is required: the relation is tested on the images of generators. -/
def lift (f : V →ₗ[R] A)
    (hf : ∀ (p q : ℤ) (x y : V), x ∈ G.piece p → y ∈ G.piece q →
      f x * f y = ((p * q).negOnePow : ℤ) • (f y * f x)) : SignedSym G →ₐ[R] A :=
  RingQuot.liftAlgHom R ⟨TensorAlgebra.lift R f, by
    intro a b h
    cases h with
    | swap p q x y hx hy => simpa using hf p q x y hx hy⟩

@[simp]
theorem lift_generator (f : V →ₗ[R] A) (hf) (x : V) :
    lift G f hf (generator G x) = f x := by
  rw [← quotient_ι]
  exact (RingQuot.liftAlgHom_mkAlgHom_apply R _ _ _).trans
    (TensorAlgebra.lift_ι_apply f x)

/-- The extension to the signed quotient agrees with the tensor-algebra extension on every
tensor representative. -/
@[simp]
theorem lift_quotient (f : V →ₗ[R] A) (hf) (x : TensorAlgebra R V) :
    lift G f hf (quotient G x) = TensorAlgebra.lift R f x :=
  RingQuot.liftAlgHom_mkAlgHom_apply R _ _ x

/-- The extension is unique. -/
theorem lift_unique (f : V →ₗ[R] A) (hf) (g : SignedSym G →ₐ[R] A)
    (hg : ∀ x, g (generator G x) = f x) : g = lift G f hf := by
  apply hom_ext
  simpa only [lift_generator] using hg

/-- The universal property, as an equivalence between compatible linear maps and algebra maps. -/
def liftEquiv :
    {f : V →ₗ[R] A // ∀ (p q : ℤ) (x y : V), x ∈ G.piece p → y ∈ G.piece q →
      f x * f y = ((p * q).negOnePow : ℤ) • (f y * f x)} ≃
      (SignedSym G →ₐ[R] A) where
  toFun f := lift G f.1 f.2
  invFun g := ⟨g.toLinearMap.comp (generator G), by
    intro p q x y hx hy
    simpa using congrArg g (generator_mul_generator G hx hy)⟩
  left_inv f := Subtype.ext (LinearMap.ext fun x => lift_generator G f.1 f.2 x)
  right_inv g := (lift_unique G _ _ g fun _ => rfl).symm

@[simp]
theorem liftEquiv_apply (f) : liftEquiv G (A := A) f = lift G f.1 f.2 := (rfl)

@[simp]
theorem liftEquiv_symm_apply_val (g : SignedSym G →ₐ[R] A) :
    ((liftEquiv G).symm g).val = g.toLinearMap.comp (generator G) := (rfl)

/-- Sending all generators to zero defines the canonical augmentation. -/
def augmentation : SignedSym G →ₐ[R] R :=
  lift G 0 (by simp)

@[simp]
theorem augmentation_generator (x : V) : augmentation G (generator G x) = 0 := by
  simp [augmentation]

/-- The coefficient ring embeds: applying the augmentation is a left inverse. -/
theorem algebraMap_injective : Function.Injective (algebraMap R (SignedSym G)) :=
  Function.LeftInverse.injective (fun r => (augmentation G).commutes r)

instance [Nontrivial R] : Nontrivial (SignedSym G) :=
  (algebraMap_injective G).nontrivial

section Map

variable {W : Type*} [AddCommGroup W] [Module R W]
variable (H : InternalGrading R W)

/-- A degree-preserving linear map induces a map of signed symmetric algebras. -/
def map (f : V →ₗ[R] W) (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    SignedSym G →ₐ[R] SignedSym H :=
  lift G ((generator H).comp f) (by
    intro p q x y hx hy
    exact generator_mul_generator H
      (by simpa using hf.map_mem hx) (by simpa using hf.map_mem hy))

@[simp]
theorem map_generator (f : V →ₗ[R] W) (hf) (x : V) :
    map G H f hf (generator G x) = generator H (f x) :=
  lift_generator G _ _ x

@[simp]
theorem map_id : map G G LinearMap.id (LinearMap.isHomogeneous_id G.piece) =
    AlgHom.id R (SignedSym G) := by
  ext x
  simp

variable {U : Type*} [AddCommGroup U] [Module R U]

/-- The induced algebra maps respect composition. -/
theorem map_comp (K : InternalGrading R U) (f : V →ₗ[R] W) (g : W →ₗ[R] U)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0)
    (hg : LinearMap.IsHomogeneous g H.piece K.piece 0) :
    map G K (g.comp f) (by simpa using hg.comp hf) =
      (map H K g hg).comp (map G H f hf) := by
  ext x
  simp

/-- A degree-preserving linear equivalence induces an algebra equivalence. -/
def congr (e : V ≃ₗ[R] W)
    (he : LinearMap.IsHomogeneous e.toLinearMap G.piece H.piece 0) :
    SignedSym G ≃ₐ[R] SignedSym H :=
  AlgEquiv.ofAlgHom (map G H e.toLinearMap he)
    (map H G e.symm.toLinearMap he.linearEquiv_symm)
    (by ext x; simp) (by ext x; simp)

@[simp]
theorem congr_generator (e : V ≃ₗ[R] W) (he) (x : V) :
    congr G H e he (generator G x) = generator H (e x) :=
  map_generator G H e.toLinearMap he x

/-- The induced algebra equivalence respects the identity. -/
@[simp]
theorem congr_refl :
    congr G G (LinearEquiv.refl R V) (LinearMap.isHomogeneous_id G.piece) =
      AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  exact map_id G

/-- The induced algebra equivalence respects inverses. -/
@[simp]
theorem congr_symm (e : V ≃ₗ[R] W) (he) :
    (congr G H e he).symm = congr H G e.symm he.linearEquiv_symm := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply hom_ext
  intro y
  apply (congr G H e he).injective
  simp

/-- The induced algebra equivalences respect composition. -/
theorem congr_trans (K : InternalGrading R U) (e : V ≃ₗ[R] W) (f : W ≃ₗ[R] U)
    (he : LinearMap.IsHomogeneous e.toLinearMap G.piece H.piece 0)
    (hf : LinearMap.IsHomogeneous f.toLinearMap H.piece K.piece 0) :
    congr G K (e.trans f) (by simpa using hf.comp he) =
      (congr G H e he).trans (congr H K f hf) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply hom_ext
  intro x
  simp

end Map

end SignedSym

end TauCeti
