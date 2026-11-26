/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finite nonunital `⋆`-subalgebras

This file transfers finiteness of modules to nonunital `⋆`-subalgebras through their underlying
submodules.

## Main statements

* `NonUnitalStarSubalgebra.finite_toSubmodule`: a nonunital `⋆`-subalgebra is a finite module
  exactly when its underlying submodule is.
* `NonUnitalStarSubalgebra.instFiniteDimensional`: a nonunital `⋆`-subalgebra of a
  finite-dimensional `⋆`-algebra is finite-dimensional.
* `NonUnitalStarSubalgebra.instModuleFiniteMap`, `NonUnitalStarSubalgebra.instModuleFiniteProd`,
  `NonUnitalStarAlgHom.instModuleFiniteRange`: images, products and ranges of finite nonunital
  `⋆`-subalgebras are finite.
-/

public section

namespace NonUnitalStarSubalgebra

section CommSemiring

variable {R A B : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
  [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

/-- A nonunital `⋆`-subalgebra is a finite module exactly when its underlying submodule is. -/
theorem finite_toSubmodule {S : NonUnitalStarSubalgebra R A} :
    Module.Finite R S.toNonUnitalSubalgebra.toSubmodule ↔ Module.Finite R S :=
  Iff.rfl

/-- The image of a finite nonunital `⋆`-subalgebra under a `⋆`-homomorphism is finite. -/
instance instModuleFiniteMap (S : NonUnitalStarSubalgebra R A) [Module.Finite R S]
    (f : A →⋆ₙₐ[R] B) : Module.Finite R (S.map f) := by
  have := finite_toSubmodule.2 ‹Module.Finite R S›
  rw [← finite_toSubmodule, map_toNonUnitalSubalgebra, NonUnitalSubalgebra.map_toSubmodule]
  infer_instance

/-- The product of two finite nonunital `⋆`-subalgebras is finite. -/
instance instModuleFiniteProd {A B : Type*} [NonUnitalSemiring A] [StarRing A] [Module R A]
    [NonUnitalSemiring B] [StarRing B] [Module R B] (S : NonUnitalStarSubalgebra R A)
    (T : NonUnitalStarSubalgebra R B) [Module.Finite R S] [Module.Finite R T] :
    Module.Finite R (S.prod T) := by
  have := finite_toSubmodule.2 ‹Module.Finite R S›
  have := finite_toSubmodule.2 ‹Module.Finite R T›
  rw [← finite_toSubmodule, prod_toNonUnitalSubalgebra, NonUnitalSubalgebra.prod_toSubmodule]
  exact Module.Finite.equiv (Submodule.prodEquiv _ _).symm

end CommSemiring

variable {R A : Type*} [Field R] [NonUnitalNonAssocRing A] [Module R A] [Star A]

/-- A nonunital `⋆`-subalgebra of a finite-dimensional `⋆`-algebra is finite-dimensional. -/
instance instFiniteDimensional [FiniteDimensional R A] (S : NonUnitalStarSubalgebra R A) :
    FiniteDimensional R S :=
  finite_toSubmodule.1 inferInstance

end NonUnitalStarSubalgebra

namespace NonUnitalStarAlgHom

variable {R A B : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
  [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

/-- The range of a `⋆`-homomorphism out of a finite `⋆`-algebra is finite. -/
instance instModuleFiniteRange [Module.Finite R A] (f : A →⋆ₙₐ[R] B) : Module.Finite R f.range :=
  Module.Finite.of_surjective (LinearMap.ofClass f.rangeRestrict) fun ⟨_, a, ha⟩ ↦
    ⟨a, Subtype.ext ha⟩

end NonUnitalStarAlgHom
