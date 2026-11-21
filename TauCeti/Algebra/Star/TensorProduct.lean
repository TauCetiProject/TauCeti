/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Joint homomorphisms of star algebras

The unital star homomorphisms from an algebraic tensor product of star algebras are in
bijection with pairs of unital star homomorphisms having commuting ranges, via
`Algebra.TensorProduct.starLiftEquiv`.

In particular, commuting left and opposite-right representations on a Hilbert space give
the joint representation of a bimodule: `a ⊗ bᵒᵖ` acts by the product of the two operators.
No normality or completion is needed for this algebraic construction.

The lift and its universal property extend Mathlib's `Algebra.TensorProduct.lift` and
`Algebra.TensorProduct.liftEquiv`, using Mathlib's componentwise tensor-product star.
-/

public section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {R A B C : Type*} [CommSemiring R] [StarRing R]
  [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]
  [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]
  [Semiring C] [StarRing C] [Algebra R C]

/-- The left inclusion into an algebraic tensor product as a unital star homomorphism. -/
def includeLeftStarAlgHom : A →⋆ₐ[R] A ⊗[R] B where
  toAlgHom := includeLeft
  map_star' a := by simp

/-- The right inclusion into an algebraic tensor product as a unital star homomorphism. -/
def includeRightStarAlgHom : B →⋆ₐ[R] A ⊗[R] B where
  toAlgHom := includeRight
  map_star' b := by simp

@[simp]
theorem includeLeftStarAlgHom_apply (a : A) :
    includeLeftStarAlgHom (R := R) (B := B) a = a ⊗ₜ[R] 1 :=
  (rfl)

@[simp]
theorem includeRightStarAlgHom_apply (b : B) :
    includeRightStarAlgHom (R := R) (A := A) b = 1 ⊗ₜ[R] b :=
  (rfl)

/-- The joint unital star homomorphism associated to two commuting unital star
homomorphisms. On pure tensors it sends `a ⊗ b` to `f a * g b`. -/
def starLift (f : A →⋆ₐ[R] C) (g : B →⋆ₐ[R] C)
    (hfg : ∀ a b, Commute (f a) (g b)) : A ⊗[R] B →⋆ₐ[R] C :=
  { lift f.toAlgHom g.toAlgHom hfg with
    -- State the law using the algebra-hom coercion, rather than its raw `toFun` projections.
    map_star' := (by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul a b =>
        simpa only [TensorProduct.star_tmul, lift_tmul, StarAlgHom.coe_toAlgHom,
          map_star, star_mul] using
          (hfg (star a) (star b)).eq
      | add x y hx hy => simp only [star_add, map_add, hx, hy] :
      ∀ x, lift f.toAlgHom g.toAlgHom hfg (star x) =
        star (lift f.toAlgHom g.toAlgHom hfg x)) }

@[simp]
theorem starLift_tmul (f : A →⋆ₐ[R] C) (g : B →⋆ₐ[R] C)
    (hfg : ∀ a b, Commute (f a) (g b)) (a : A) (b : B) :
    starLift f g hfg (a ⊗ₜ[R] b) = f a * g b :=
  (rfl)

/-- Star homomorphisms out of a tensor product are determined by their values on the
left and right inclusions. -/
@[ext]
theorem starAlgHom_ext {f g : A ⊗[R] B →⋆ₐ[R] C}
    (hA : ∀ a, f (a ⊗ₜ[R] 1) = g (a ⊗ₜ[R] 1))
    (hB : ∀ b, f (1 ⊗ₜ[R] b) = g (1 ⊗ₜ[R] b)) : f = g := by
  have h : f.toAlgHom = g.toAlgHom :=
    Algebra.TensorProduct.ext (AlgHom.ext hA) (AlgHom.ext hB)
  exact StarAlgHom.ext fun x => DFunLike.congr_fun h x

@[simp]
theorem starLift_comp_includeLeftStarAlgHom (f : A →⋆ₐ[R] C) (g : B →⋆ₐ[R] C)
    (hfg : ∀ a b, Commute (f a) (g b)) :
    (starLift f g hfg).comp includeLeftStarAlgHom = f := by
  ext a
  simp

@[simp]
theorem starLift_comp_includeRightStarAlgHom (f : A →⋆ₐ[R] C) (g : B →⋆ₐ[R] C)
    (hfg : ∀ a b, Commute (f a) (g b)) :
    (starLift f g hfg).comp includeRightStarAlgHom = g := by
  ext b
  simp

/-- The universal property of the algebraic tensor product of star algebras: its unital
star homomorphisms are exactly the pairs of unital star homomorphisms with commuting ranges. -/
def starLiftEquiv :
    {fg : (A →⋆ₐ[R] C) × (B →⋆ₐ[R] C) // ∀ a b, Commute (fg.1 a) (fg.2 b)} ≃
      (A ⊗[R] B →⋆ₐ[R] C) where
  toFun fg := starLift fg.1.1 fg.1.2 fg.2
  invFun f := ⟨(f.comp includeLeftStarAlgHom, f.comp includeRightStarAlgHom),
    fun a b => ((Commute.one_right a).tmul (Commute.one_left b)).map f⟩
  left_inv fg := by
    apply Subtype.ext
    exact Prod.ext (starLift_comp_includeLeftStarAlgHom ..)
      (starLift_comp_includeRightStarAlgHom ..)
  right_inv f := by
    apply starAlgHom_ext <;> intro x <;> simp [← Algebra.TensorProduct.one_def]

@[simp]
theorem starLiftEquiv_apply
    (fg : {fg : (A →⋆ₐ[R] C) × (B →⋆ₐ[R] C) // ∀ a b, Commute (fg.1 a) (fg.2 b)}) :
    starLiftEquiv fg = starLift fg.1.1 fg.1.2 fg.2 :=
  (rfl)

@[simp]
theorem starLiftEquiv_symm_apply (f : A ⊗[R] B →⋆ₐ[R] C) :
    (starLiftEquiv.symm f).1 = (f.comp includeLeftStarAlgHom, f.comp includeRightStarAlgHom) :=
  (rfl)

end Algebra.TensorProduct
