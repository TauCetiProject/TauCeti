/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Star.Prod
public import Mathlib.Algebra.Star.StarAlgHom

/-!
# `⋆`-algebra equivalences on product types

Lifts `AlgEquiv.prodCongr` to `StarAlgEquiv.prodCongr` for pairs of `⋆`-algebras.
-/

public section

namespace StarAlgEquiv

section ProdCongr

variable {R S T A B : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Semiring A] [Semiring B]
  [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R B]
  [Star S] [Star T] [Star A] [Star B]

/-- Product of `⋆`-algebra isomorphisms. -/
def prodCongr (l : S ≃⋆ₐ[R] A) (r : T ≃⋆ₐ[R] B) : (S × T) ≃⋆ₐ[R] A × B :=
  StarAlgEquiv.ofAlgEquiv (l.toAlgEquiv.prodCongr r.toAlgEquiv) fun x ↦
    Prod.ext (map_star l x.1) (map_star r x.2)

variable (l : S ≃⋆ₐ[R] A) (r : T ≃⋆ₐ[R] B)

/-- Applying `StarAlgEquiv.prodCongr` applies each component equivalence coordinatewise. -/
@[simp low]
theorem prodCongr_apply (x : S × T) : prodCongr l r x = (l x.1, r x.2) :=
  (rfl)

/-- Applying `(StarAlgEquiv.prodCongr l r).symm` applies each inverse equivalence coordinatewise. -/
@[simp low]
theorem prodCongr_symm_apply (x : A × B) :
    (prodCongr l r).symm x = (l.symm x.1, r.symm x.2) :=
  (rfl)

end ProdCongr

end StarAlgEquiv
