/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.CenterMap
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Defect.Class

/-!
# Defect classes under scalar extension

Let `f : k → k'` be a homomorphism of fields, `G` a finite group, and `f_* : Z(k[G]) → Z(k'[G])`
the induced map of centres (`MonoidAlgebra.centerMapRingHom G f`). A `k`-algebra homomorphism
`λ : Z(k[G]) → k`, for instance the central character of a block, extends uniquely to a
`k'`-algebra homomorphism `λ' : Z(k'[G]) → k'` with `λ'(f_* x) = f(λ(x))`
(`TauCeti.existsUnique_algHom_centerMapRingHom`).

For such `λ'`, the conjugacy class `C` is a defect class of `f_* b` for `λ'` exactly when it is a
defect class of `b` for `λ`: `f_*` applies `f` to the coefficients in the class-sum basis and sends
class sums to class sums, so `a_{f_* b}(C) λ'(K_C) = f(a_b(C) λ(K_C))`, and `f` is injective. So
the defect classes of a block, like its defect groups
(`TauCeti.isDefectGroup_centerMapRingHom_iff`), do not change under scalar extension.

## Main results

* `TauCeti.repr_centerMapRingHom_mul_apply_classSumCenter`: the product `a(C) λ(K_C)` for `f_* b`
  and `λ'` is `f` of that for `b` and `λ`.
* `TauCeti.isDefectClass_centerMapRingHom_iff`: defect classes are invariant under scalar
  extension.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {G k k' : Type*} [Group G] [Fintype G] [DecidableEq G] [Field k] [Field k']
  (f : k →+* k') {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k}
  {φ' : Subalgebra.center k' (MonoidAlgebra k' G) →ₐ[k'] k'}

/-- For `λ'` extending `λ` along `f`, the product `a(C) λ(K_C)` of the coefficient of
`f_* b` on the class `C` and the value of `λ'` at the class sum `K_C` is `f` of the same product
for `b` and `λ`. -/
theorem repr_centerMapRingHom_mul_apply_classSumCenter
    (hφ : ∀ x, φ' (centerMapRingHom G f x) = f (φ x))
    (b : Subalgebra.center k (MonoidAlgebra k G)) (C : ConjClasses G) :
    classSumBasis.repr (centerMapRingHom G f b) C * φ' (classSumCenter C) =
      f (classSumBasis.repr b C * φ (classSumCenter C)) := by
  rw [classSumBasis_repr_apply, classSumBasis_repr_apply, centerToConjClasses_centerMapRingHom,
    ← centerMapRingHom_classSumCenter f C, hφ, map_mul]

/-- **Defect classes under scalar extension.** For a homomorphism of fields `f : k → k'` and a
`k'`-algebra homomorphism `λ'` of `Z(k'[G])` extending `λ` along `f`, a conjugacy class is a
defect class of `f_* b` for `λ'` exactly when it is a defect class of `b` for `λ`. -/
theorem isDefectClass_centerMapRingHom_iff (hφ : ∀ x, φ' (centerMapRingHom G f x) = f (φ x))
    {b : Subalgebra.center k (MonoidAlgebra k G)} {C : ConjClasses G} :
    IsDefectClass φ' (centerMapRingHom G f b) C ↔ IsDefectClass φ b C := by
  rw [isDefectClass_iff, isDefectClass_iff, repr_centerMapRingHom_mul_apply_classSumCenter f hφ,
    map_ne_zero]

end TauCeti
