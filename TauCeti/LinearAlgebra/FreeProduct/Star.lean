/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FreeProduct.Basic
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Algebra.Opposite

/-!
# The involution on an algebraic free product

The algebraic free product of unital star algebras is itself a star algebra: its involution
extends those of the factors, conjugates scalars, and reverses the order of products.
`LinearAlgebra.FreeProduct.ιStar` and `LinearAlgebra.FreeProduct.liftStar` express its
universal property for unital star algebra homomorphisms,
`LinearAlgebra.FreeProduct.iSup_range_ιStar` records that the factor images generate the free
product as a star subalgebra, and `LinearAlgebra.FreeProduct.isEmptyStarAlgEquiv` identifies the
empty star free product with `R`. Forgetting star recovers Mathlib's algebraic coproduct and its
universal maps, not a different quotient.

This is an algebraic construction. No positivity, norm, completion or faithfulness of the
factor maps is asserted. The index type can be empty.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, §1.4.

The construction uses Mathlib's `LinearAlgebra.FreeProduct.lift`, applied to the opposite
algebra with its scalar action twisted by conjugation.
-/

public section

noncomputable section

namespace LinearAlgebra.FreeProduct

open MulOpposite

variable {I : Type*} [DecidableEq I] (R : Type*) [CommSemiring R] [StarRing R]
  (A : I → Type*) [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
  [∀ i, StarRing (A i)] [∀ i, StarModule R (A i)]

/-- The conjugate-linear antihomomorphism, before proving involutivity. -/
private def starAux : FreeProduct R A →+* (FreeProduct R A)ᵐᵒᵖ := by
  letI := Algebra.compHom (FreeProduct R A)ᵐᵒᵖ (starRingEnd R)
  exact (lift R A fun {i} =>
    { toRingHom := (RingHom.op (ι R A i).toRingHom).comp
        (starRingEquiv : A i ≃+* (A i)ᵐᵒᵖ).toRingHom
      commutes' r := by
        simp [Algebra.compHom_algebraMap_apply, starRingEnd_apply,
          ← algebraMap_star_comm] }).toRingHom

private theorem starAux_ι (i : I) (a : A i) :
    starAux R A (ι R A i a) = op (ι R A i (star a)) := by
  let := Algebra.compHom (FreeProduct R A)ᵐᵒᵖ (starRingEnd R)
  exact AlgHom.congr_fun (lift_comp_ι R A _ (i := i)) a

private theorem starAux_algebraMap (r : R) :
    starAux R A (algebraMap R _ r) = op (algebraMap R _ (star r)) := by
  let := Algebra.compHom (FreeProduct R A)ᵐᵒᵖ (starRingEnd R)
  exact (lift R A _).commutes r

private theorem starAux_involutive (x : FreeProduct R A) :
    unop (starAux R A (unop (starAux R A x))) = x := by
  let f : FreeProduct R A →ₐ[R] FreeProduct R A :=
    { toFun x := unop (starAux R A (unop (starAux R A x)))
      map_one' := by simp
      map_mul' x y := by simp
      map_zero' := by simp
      map_add' x y := by simp
      commutes' r := by simp [starAux_algebraMap] }
  have hf : f = AlgHom.id R (FreeProduct R A) := by
    apply (lift R A).symm.injective
    funext i
    apply AlgHom.ext
    intro a
    simp only [lift_symm_apply, AlgHom.comp_apply, AlgHom.id_apply]
    simp [f, starAux_ι]
  exact AlgHom.congr_fun hf x

/-- The involution extending the factor involutions to the algebraic free product. -/
@[no_expose]
instance instStarRing : StarRing (FreeProduct R A) where
  star x := unop (starAux R A x)
  star_involutive := starAux_involutive R A
  star_mul x y := by simp
  star_add x y := by simp

private theorem star_algebraMap (r : R) :
    star (algebraMap R (FreeProduct R A) r) = algebraMap R _ (star r) :=
  congrArg unop (starAux_algebraMap R A r)

/-- The free-product involution conjugates scalars. -/
instance instStarModule : StarModule R (FreeProduct R A) where
  star_smul r x := by
    rw [Algebra.smul_def, Algebra.smul_def, star_mul, star_algebraMap]
    exact (Algebra.commutes (star r) (star x)).symm

/-- The involution on the free product restricts to the given involution on each factor. -/
@[simp]
theorem star_ι (i : I) (a : A i) : star (ι R A i a) = ι R A i (star a) :=
  congrArg unop (starAux_ι R A i a)

/-- The canonical map from a factor, as a unital star algebra homomorphism. -/
def ιStar (i : I) : A i →⋆ₐ[R] FreeProduct R A :=
  { ι R A i with map_star' a := (star_ι R A i a).symm }

@[simp]
theorem ιStar_toAlgHom (i : I) : (ιStar R A i).toAlgHom = ι R A i := (rfl)

@[simp]
theorem ιStar_apply (i : I) (a : A i) : ιStar R A i a = ι R A i a := (rfl)

variable {R A} {B : Type*} [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

/-- An algebra homomorphism out of the free product preserves star if it does so on every
factor. -/
theorem _root_.AlgHom.map_star_of_comp_freeProduct_ι (f : FreeProduct R A →ₐ[R] B)
    (hf : ∀ i a, f (ι R A i (star a)) = star (f (ι R A i a))) (x : FreeProduct R A) :
    f (star x) = star (f x) := by
  let g : FreeProduct R A →ₐ[R] B :=
    { toFun x := star (f (star x))
      map_one' := by simp
      map_mul' x y := by simp
      map_zero' := by simp
      map_add' x y := by simp
      commutes' r := by simp [← algebraMap_star_comm] }
  have hg : g = f := by
    apply (lift R A).symm.injective
    funext i
    apply AlgHom.ext
    intro a
    simp only [lift_symm_apply, AlgHom.comp_apply]
    simp [g, hf]
  have := AlgHom.congr_fun hg x
  simpa [g] using congrArg star this

/-- The algebraic free product is also the coproduct of unital star algebras. -/
def liftStar : ({i : I} → A i →⋆ₐ[R] B) ≃ (FreeProduct R A →⋆ₐ[R] B) where
  toFun maps :=
    { lift R A (fun {i} => (maps (i := i)).toAlgHom) with
      map_star' x := AlgHom.map_star_of_comp_freeProduct_ι _ (fun i a => by
        have h := lift_comp_ι R A (fun {i} => (maps (i := i)).toAlgHom) (i := i)
        simpa only [AlgHom.comp_apply, StarAlgHom.coe_toAlgHom] using
          (AlgHom.congr_fun h (star a)).trans ((map_star (maps (i := i)) a).trans
            (congrArg star (AlgHom.congr_fun h a).symm))) x }
  invFun f := fun {i} => f.comp (ιStar R A i)
  left_inv maps := by
    funext i
    apply StarAlgHom.ext
    intro a
    exact AlgHom.congr_fun (lift_comp_ι R A _) a
  right_inv f := by
    apply StarAlgHom.ext
    intro x
    exact AlgHom.congr_fun ((lift R A).apply_symm_apply f.toAlgHom) x

@[simp]
theorem liftStar_toAlgHom (maps : {i : I} → A i →⋆ₐ[R] B) :
    (liftStar maps).toAlgHom = lift R A (fun {i} => (maps (i := i)).toAlgHom) := (rfl)

/-- The inverse of the universal equivalence restricts a map to a factor. -/
@[simp]
theorem liftStar_symm_apply (i : I) (f : FreeProduct R A →⋆ₐ[R] B) :
    liftStar.symm f = f.comp (ιStar R A i) := (rfl)

/-- The star-universal map extends the prescribed homomorphism on each factor. -/
@[simp]
theorem liftStar_ι (maps : {i : I} → A i →⋆ₐ[R] B) (i : I) (a : A i) :
    liftStar maps (ι R A i a) = maps a :=
  AlgHom.congr_fun (lift_comp_ι R A _) a

/-- Star algebra homomorphisms out of a free product are determined on its factors. -/
@[ext]
theorem starAlgHom_ext {f g : FreeProduct R A →⋆ₐ[R] B}
    (h : ∀ i a, f (ι R A i a) = g (ι R A i a)) : f = g := by
  apply liftStar.symm.injective
  funext i
  exact StarAlgHom.ext (h i)

/-- Composing the star-universal map with a factor map recovers the given map. -/
@[simp]
theorem liftStar_comp_ιStar (maps : {i : I} → A i →⋆ₐ[R] B) (i : I) :
    (liftStar maps).comp (ιStar R A i) = maps := by
  ext a
  simp

/-- The universal map for the canonical factor maps is the identity. -/
@[simp]
theorem liftStar_ιStar :
    liftStar (fun {i} => ιStar R A i) = StarAlgHom.id R (FreeProduct R A) := by
  ext i a
  simp

/-- Postcomposition of universal maps agrees with postcomposition on each factor. -/
@[simp]
theorem liftStar_comp {C : Type*} [Semiring C] [Algebra R C] [StarRing C] [StarModule R C]
    (maps : {i : I} → A i →⋆ₐ[R] B) (g : B →⋆ₐ[R] C) :
    liftStar (fun {i} => g.comp (maps (i := i))) = g.comp (liftStar maps) := by
  ext i a
  simp

section GenerationAndEmpty

variable (R A)

/-- The star-subalgebra images of the factor embeddings generate `FreeProduct R A`. -/
theorem iSup_range_ιStar :
    (⨆ i, (ιStar R A i).range) = (⊤ : StarSubalgebra R (FreeProduct R A)) := by
  rw [← StarSubalgebra.toSubalgebra_eq_top, eq_top_iff, ← iSup_range_ι R A, iSup_le_iff]
  rintro i _ ⟨a, rfl⟩
  exact le_iSup (fun j ↦ (ιStar R A j).range) i ⟨a, rfl⟩

/-- The unital star-algebraic free product over an empty index type is canonically star-isomorphic
to the base star semiring `R`. -/
def isEmptyStarAlgEquiv [IsEmpty I] : FreeProduct R A ≃⋆ₐ[R] R :=
  StarAlgEquiv.ofStarAlgHom
    (liftStar fun {i} ↦ isEmptyElim i)
    (StarAlgHom.ofId R (FreeProduct R A))
    (starAlgHom_ext fun i ↦ isEmptyElim i)
    (StarAlgHom.ext fun r ↦ AlgHomClass.commutes (liftStar (R := R) (A := A) fun {i} ↦
      isEmptyElim i) r)

@[simp]
theorem isEmptyStarAlgEquiv_toAlgEquiv [IsEmpty I] :
    (isEmptyStarAlgEquiv R A).toAlgEquiv = isEmptyAlgEquiv R A :=
  AlgEquiv.ext fun x ↦ AlgHom.congr_fun
    (algHom_ext (f := (isEmptyStarAlgEquiv R A).toAlgEquiv.toAlgHom)
      (g := (isEmptyAlgEquiv R A).toAlgHom) fun i ↦ isEmptyElim i) x

@[simp]
theorem isEmptyStarAlgEquiv_symm_apply [IsEmpty I] (r : R) :
    (isEmptyStarAlgEquiv R A).symm r = algebraMap R (FreeProduct R A) r :=
  (rfl)

end GenerationAndEmpty

end LinearAlgebra.FreeProduct
