/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Base change of Hopf algebras

This file supplies the small API around the scalar extension `K ⊗[k] A` of a Hopf algebra
`A` over `k`. Mathlib already provides the Hopf algebra instance on tensor products of Hopf
algebras in `Mathlib.RingTheory.HopfAlgebra.TensorProduct`; the declarations here name the
base-change object and record the canonical inclusion and functoriality in bialgebra maps.

This is a prerequisite for the reductive-groups roadmap, Layer 0, "Base change":
geometric properties of affine group schemes are defined after extending scalars, and on
coordinate rings this is the Hopf algebra `K ⊗[k] A`.
-/

open scoped TensorProduct

namespace TauCeti

namespace HopfAlgebra

namespace BaseChange

variable (k K A : Type*) [CommSemiring k] [CommSemiring K] [Semiring A]
variable [Algebra k K] [HopfAlgebra k A]

/-- The scalar extension of a Hopf algebra `A` over `k` to a commutative `k`-algebra `K`.

Mathlib's tensor-product instance makes this a Hopf algebra over `K`; this abbreviation gives
the object a stable name for the algebraic-group roadmap. -/
abbrev Obj : Type _ :=
  K ⊗[k] A

variable {k K A}

/-- The canonical algebra map from a Hopf algebra to its scalar extension. -/
noncomputable abbrev includeRight : A →ₐ[k] Obj k K A :=
  Algebra.TensorProduct.includeRight

@[simp]
lemma includeRight_apply (a : A) : includeRight (k := k) (K := K) a = (1 : K) ⊗ₜ[k] a :=
  rfl

@[simp]
lemma includeRight_one : includeRight (k := k) (K := K) (A := A) 1 = 1 :=
  rfl

@[simp]
lemma includeRight_zero : includeRight (k := k) (K := K) (A := A) 0 = 0 :=
  map_zero _

@[simp]
lemma includeRight_add (a b : A) :
    includeRight (k := k) (K := K) (a + b) =
      includeRight (k := k) (K := K) a + includeRight (k := k) (K := K) b :=
  map_add _ _ _

@[simp]
lemma includeRight_mul (a b : A) :
    includeRight (k := k) (K := K) (a * b) =
      includeRight (k := k) (K := K) a * includeRight (k := k) (K := K) b :=
  map_mul _ _ _

@[simp]
lemma includeRight_algebraMap (r : k) :
    includeRight (k := k) (K := K) (A := A) (algebraMap k A r) =
      algebraMap K (Obj k K A) (algebraMap k K r) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

variable {B C : Type*} [Semiring B] [Semiring C] [HopfAlgebra k B] [HopfAlgebra k C]

/-- Scalar extension of a bialgebra homomorphism between Hopf algebras. Since Mathlib's
`BialgHom` is the bundled morphism for bialgebras, this is the map needed for Hopf algebras as
well: bialgebra morphisms between Hopf algebras automatically commute with the unique
antipodes. -/
noncomputable abbrev map (f : A →ₐc[k] B) : Obj k K A →ₐc[K] Obj k K B :=
  Bialgebra.TensorProduct.map (BialgHom.id K K) f

@[simp]
lemma map_tmul (f : A →ₐc[k] B) (r : K) (a : A) :
    map (K := K) f (r ⊗ₜ[k] a) = r ⊗ₜ[k] f a :=
  rfl

@[simp]
lemma map_includeRight (f : A →ₐc[k] B) (a : A) :
    map (K := K) f (includeRight (k := k) (K := K) a) =
      includeRight (k := k) (K := K) (f a) :=
  rfl

@[simp]
lemma map_id :
    map (K := K) (BialgHom.id k A) = BialgHom.id K (Obj k K A) := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => rfl
  | add x y hx hy => simp [hx, hy]

lemma map_comp (g : B →ₐc[k] C) (f : A →ₐc[k] B) :
    map (K := K) (g.comp f) = (map (K := K) g).comp (map (K := K) f) := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => rfl
  | add x y hx hy => simp [hx, hy]

@[simp]
lemma map_comp_apply (g : B →ₐc[k] C) (f : A →ₐc[k] B) (x : Obj k K A) :
    map (K := K) (g.comp f) x = map (K := K) g (map (K := K) f x) := by
  rw [map_comp]
  rfl

@[simp]
lemma map_toAlgHom (f : A →ₐc[k] B) :
    (map (K := K) f : Obj k K A →ₐ[K] Obj k K B) =
      Algebra.TensorProduct.map (AlgHom.id K K) (f : A →ₐ[k] B) :=
  rfl

@[simp]
lemma map_zero_apply (f : A →ₐc[k] B) : map (K := K) f 0 = 0 :=
  map_zero _

@[simp]
lemma map_add_apply (f : A →ₐc[k] B) (x y : Obj k K A) :
    map (K := K) f (x + y) = map (K := K) f x + map (K := K) f y :=
  map_add _ _ _

@[simp]
lemma map_one_apply (f : A →ₐc[k] B) : map (K := K) f 1 = 1 :=
  map_one _

@[simp]
lemma map_mul_apply (f : A →ₐc[k] B) (x y : Obj k K A) :
    map (K := K) f (x * y) = map (K := K) f x * map (K := K) f y :=
  map_mul _ _ _

@[simp]
lemma counit_map (f : A →ₐc[k] B) (x : Obj k K A) :
    Coalgebra.counit (R := K) (map (K := K) f x) = Coalgebra.counit (R := K) x :=
  CoalgHomClass.counit_comp_apply (map (K := K) f) x

@[simp]
lemma comul_map (f : A →ₐc[k] B) (x : Obj k K A) :
    TensorProduct.map (map (K := K) f : Obj k K A →ₗ[K] Obj k K B)
        (map (K := K) f : Obj k K A →ₗ[K] Obj k K B)
        (Coalgebra.comul (R := K) x) =
      Coalgebra.comul (R := K) (map (K := K) f x) :=
  CoalgHomClass.map_comp_comul_apply (map (K := K) f) x

end BaseChange

end HopfAlgebra

end TauCeti
