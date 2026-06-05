/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Base change of Hopf algebras

Given a Hopf algebra `A` over `k` and a `k`-algebra `K`, the tensor product `K ⊗[k] A` is a
Hopf algebra over `K` (supplied by Mathlib's `TensorProduct` instance). This file adds the
descriptive API that the reductive-groups roadmap (Layer 0) needs:

* `baseChange_counit_tmul`: the counit on a pure tensor `1 ⊗ a` is `algebraMap k K (counit a)`.
* `baseChangeMap`: a bialgebra morphism `f : A →ₐc[k] B` induces a `K`-linear bialgebra
  morphism `K ⊗[k] A →ₐc[K] K ⊗[k] B` given by `id_K ⊗ f`, functorial in `f`.

Commutativity and cocommutativity of the base change are already supplied by Mathlib's
`Algebra.TensorProduct.instCommSemiring` and `Coalgebra.TensorProduct.instIsCocomm`.

## References

Realises the "base change" milestone of the Tau Ceti reductive-groups roadmap (Layer 0).
The tensor-product Hopf algebra instance is the work of Amelia Livingston and Andrew Yang
in Mathlib.
-/

open scoped TensorProduct

namespace TauCeti

namespace HopfAlgebra

variable {k K A B C : Type*}
  [CommSemiring k] [CommSemiring K] [Algebra k K]
  [Semiring A] [Semiring B] [Semiring C]
  [HopfAlgebra k A] [HopfAlgebra k B] [HopfAlgebra k C]

/--
The counit of the base-changed Hopf algebra `K ⊗[k] A` on a pure tensor `1 ⊗ a` is the
image of the counit of `A` under `algebraMap k K`.
-/
@[simp]
lemma baseChange_counit_tmul (a : A) :
    Coalgebra.counit (R := K) (A := K ⊗[k] A) (1 ⊗ₜ a) = algebraMap k K (Coalgebra.counit a) := by
  simp [Algebra.smul_def, mul_one]

/--
Base change is functorial: a bialgebra morphism `f : A →ₐc[k] B` induces a bialgebra
morphism `K ⊗[k] A →ₐc[K] K ⊗[k] B` given by `id_K ⊗ f`. This is the morphism part of
the base-change functor from `k`-bialgebras to `K`-bialgebras.
-/
noncomputable def baseChangeMap (f : A →ₐc[k] B) : K ⊗[k] A →ₐc[K] K ⊗[k] B :=
  Bialgebra.TensorProduct.map (BialgHom.id K K) f

/--
`baseChangeMap` acts on pure tensors as `id_K ⊗ f`.
-/
@[simp]
lemma baseChangeMap_tmul (f : A →ₐc[k] B) (x : K) (a : A) :
    baseChangeMap f (x ⊗ₜ a) = x ⊗ₜ f a :=
  rfl

/--
`baseChangeMap` preserves the identity: the base change of the identity bialgebra morphism
is the identity.
-/
@[simp]
lemma baseChangeMap_id : (baseChangeMap (BialgHom.id k A) : K ⊗[k] A →ₐc[K] K ⊗[k] A) =
    BialgHom.id K (K ⊗[k] A) := by
  ext x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro k' a; rfl
  · intro x y hx hy; simp [hx, hy]

/--
`baseChangeMap` preserves composition:
`baseChangeMap (g ∘ f) = baseChangeMap g ∘ baseChangeMap f`.
-/
@[simp]
lemma baseChangeMap_comp (f : A →ₐc[k] B) (g : B →ₐc[k] C) :
    (baseChangeMap (g.comp f) : K ⊗[k] A →ₐc[K] K ⊗[k] C) =
    (baseChangeMap g).comp (baseChangeMap f) := by
  ext x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro k' a; rfl
  · intro x y hx hy; simp [hx, hy]

/--
The base-changed morphism applied to a pure tensor `1 ⊗ a` yields `1 ⊗ f a`.
-/
@[simp]
lemma baseChangeMap_one_tmul (f : A →ₐc[k] B) (a : A) :
    baseChangeMap f (1 ⊗ₜ[k] a) = (1 : K) ⊗ₜ f a := by
  simp [baseChangeMap_tmul]

end HopfAlgebra

end TauCeti
