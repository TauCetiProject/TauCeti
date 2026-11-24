/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.LinearAlgebra.LinearDisjoint
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Algebra.Star.Subalgebra
import TauCeti.LinearAlgebra.TensorProduct.Subalgebra

/-!
# Tensor product multiplication equivalences for commuting `⋆`-subalgebras

When two unital `⋆`-subalgebras `S` and `T` of a `⋆`-algebra `A` over `R` commute elementwise and
their underlying submodules are linearly disjoint, the multiplication `R`-algebra equivalence
`Subalgebra.mulAlgEquivOfCommute` also preserves `star`, yielding a unital `⋆`-algebra isomorphism
`S ⊗[R] T ≃⋆ₐ[R] ↥(S ⊔ T)`. This applies both to a factor and its commutant and to commuting
subalgebras such as `M ⊗ 1` and `1 ⊗ N` inside a spatial tensor product.

## Main declarations

* `StarSubalgebra.mulStarAlgEquivOfCommute`: for elementwise-commuting, linearly disjoint
  `⋆`-subalgebras `S T : StarSubalgebra R A`, multiplication induces a unital `⋆`-algebra
  isomorphism `S ⊗[R] T ≃⋆ₐ[R] ↥(S ⊔ T)`.
* `StarSubalgebra.coe_mulStarAlgEquivOfCommute_tmul`: `mulStarAlgEquivOfCommute` sends `a ⊗ₜ b`
  to `a * b`.
-/

public section

open scoped TensorProduct

namespace StarSubalgebra

variable {R A : Type*} [CommSemiring R] [StarRing R]
  [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

/-- If `S` and `T` are linearly disjoint `⋆`-subalgebras of `A` whose elements commute,
multiplication induces a unital `⋆`-algebra equivalence `S ⊗[R] T ≃⋆ₐ[R] ↥(S ⊔ T)`. -/
noncomputable def mulStarAlgEquivOfCommute (S T : StarSubalgebra R A)
    (hcomm : ∀ a ∈ S, ∀ b ∈ T, Commute a b) (H : S.toSubmodule.LinearDisjoint T.toSubmodule) :
    S ⊗[R] T ≃⋆ₐ[R] ↥(S ⊔ T) := by
  let f : S ⊗[R] T ≃ₐ[R] ↥(S ⊔ T) :=
    (S.toSubalgebra.mulAlgEquivOfCommute T.toSubalgebra hcomm H).trans
      (Subalgebra.equivOfEq _ _ (sup_toSubalgebra S T).symm)
  have hf (a : S) (b : T) : (f (a ⊗ₜ[R] b) : A) = (a : A) * b := by
    rw [AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply, Subtype.coe_mk,
      Subalgebra.coe_mulAlgEquivOfCommute_tmul]
  refine StarAlgEquiv.ofAlgEquiv f fun t => ?_
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    apply Subtype.ext
    rw [TensorProduct.star_tmul, StarMemClass.coe_star, hf, hf, StarMemClass.coe_star,
      StarMemClass.coe_star, star_mul]
    exact (hcomm (star (a : A)) (star_mem a.property) (star (b : A)) (star_mem b.property)).eq
  | add x y hx hy =>
    rw [star_add, map_add, hx, hy, map_add, star_add]

/-- `mulStarAlgEquivOfCommute` sends a pure tensor `a ⊗ₜ b` to the product `a * b`. -/
@[simp]
theorem coe_mulStarAlgEquivOfCommute_tmul {S T : StarSubalgebra R A}
    (hcomm : ∀ a ∈ S, ∀ b ∈ T, Commute a b) (H : S.toSubmodule.LinearDisjoint T.toSubmodule)
    (a : S) (b : T) :
    (S.mulStarAlgEquivOfCommute T hcomm H (a ⊗ₜ[R] b) : A) = (a : A) * b := by
  rw [mulStarAlgEquivOfCommute, StarAlgEquiv.ofAlgEquiv_apply, AlgEquiv.trans_apply,
    Subalgebra.equivOfEq_apply, Subtype.coe_mk, Subalgebra.coe_mulAlgEquivOfCommute_tmul]

end StarSubalgebra
