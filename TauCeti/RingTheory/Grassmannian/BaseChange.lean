/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Grassmannian.Basic

import TauCeti.LinearAlgebra.TensorProduct.Kernel
import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Extension of scalars of a quotient Grassmannian point

A quotient Grassmannian point over `R` extends to every commutative `R`-algebra. Its kernel
is the extension of scalars of the original kernel. This uses the existing Grassmannian
functor through the base change of the quotient map.
-/

public section

universe u v w

open TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}
  {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- Extension of scalars of a quotient Grassmannian point. -/
noncomputable def baseChange (P : G(k, M; R)) (A : Type w) [CommRing A] [Algebra R A] :
    G(k, A ⊗[R] M; A) :=
  ofSurjective (P.toSubmodule.mkQ.baseChange A)
    (P.toSubmodule.mkQ.baseChange_surjective A P.toSubmodule.mkQ_surjective)
    (fun p ↦ (Module.rankAtStalk_baseChange p).trans (P.rankAtStalk_eq _))

/-- The kernel of an extended quotient is the extension of scalars of the original kernel. -/
@[simp]
theorem toSubmodule_baseChange (P : G(k, M; R)) :
    (P.baseChange A).toSubmodule = P.toSubmodule.baseChange A := by
  rw [baseChange, toSubmodule_ofSurjective,
    LinearMap.ker_baseChange_of_surjective A _ P.toSubmodule.mkQ_surjective,
    Submodule.ker_mkQ]

/-- Extending a point from the ground ring is natural in the coefficient algebra. -/
@[simp]
theorem map_baseChange (f : A →ₐ[R] B) (P : G(k, M; R)) :
    map f (P.baseChange A) = P.baseChange B := by
  ext : 1
  rw [map_toSubmodule_eq_span, toSubmodule_baseChange, toSubmodule_baseChange,
    Submodule.baseChange_eq_span, Submodule.span_rTensor_image_span,
    Submodule.baseChange_eq_span]
  simp only [Submodule.map_coe, Set.image_image]
  congr 1
  exact Set.image_congr fun x _ ↦ by simp

end Module.Grassmannian
