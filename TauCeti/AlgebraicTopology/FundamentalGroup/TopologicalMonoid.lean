/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.EckmannHilton
public import Mathlib.Topology.Algebra.Monoid.Defs
public import TauCeti.AlgebraicTopology.FundamentalGroup.Product

/-!
# The fundamental group of a topological monoid is abelian

Let `M` be a topological space with a continuous multiplication and a two-sided unit `1`, for
instance a topological group. Two loops `γ` and `δ` at `1` can be multiplied pointwise,
`t ↦ γ t * δ t`, and the result is again a loop at `1 * 1 = 1`. This file shows that the class
of the pointwise product is the product of the classes in `π₁(M, 1)`, and that `π₁(M, 1)` is
commutative.

Both facts are the Eckmann–Hilton argument, applied through Mathlib's `EckmannHilton.mul` and
`EckmannHilton.mul_comm`. Multiplication `M × M → M` induces a homomorphism
`π₁(M, 1) × π₁(M, 1) ≃ π₁(M × M, (1, 1)) → π₁(M, 1)`, the first map being
`FundamentalGroup.prodMulEquiv`, and on a pair of loop classes it is the class of the
pointwise product. So pointwise multiplication of loop classes is a binary operation on
`π₁(M, 1)` over which the group law distributes, and since `1` is a strict unit of `M`, the
constant loop is a two-sided unit for it. Eckmann–Hilton then says that the two operations agree
and are commutative.

A continuous map `f : M → N` between two such spaces with `f 1 = 1`, for instance a continuous
homomorphism of topological groups, induces a group homomorphism `π₁(M, 1) → π₁(N, 1)`
(`FundamentalGroup.mapOfEq`), and this homomorphism sends the class of a pointwise product of
loops to the pointwise product of the images of the two classes
(`FundamentalGroup.mapOfEq_cast_map_prod`). Since pointwise products of loops compute the group
laws on both sides, `f` need not be multiplicative.

The group law of `π₁(M, 1)` is concatenation of loops: by `FundamentalGroup.mul_def`, the product
`a * b` is the class of a loop representing `b` followed by one representing `a`. At the level of
paths, the pointwise product of two loops at `1` is homotopic to their concatenation in either
order (`Path.Homotopic.cast_mul_trans_swap` and `Path.Homotopic.cast_mul_trans`, in
`TauCeti.Topology.Homotopy.Product`), so both orders of concatenation agree with the pointwise
product, as `FundamentalGroup.cast_map_prod_mul` and `FundamentalGroup.instCommGroup` say on
classes.

For a topological group `G` the pointwise product is the group law of the universal cover based
at `1`, and `FundamentalGroup.cast_map_prod_mul` identifies the kernel of the covering
homomorphism with `π₁(G, 1)` (`TauCeti.UniversalCover.kerProjHomEquivFundamentalGroup`).

## Main results

* `FundamentalGroup.cast_map_prod_mul`: the class of the pointwise product of two loops
  at `1` is their product in the fundamental group.
* `FundamentalGroup.instCommGroup`: the fundamental group at `1` is commutative.
* `FundamentalGroup.mapOfEq_cast_map_prod`: a continuous map preserving `1` sends the class of a
  pointwise product of loops to the pointwise product of the image classes.

## References

* B. Eckmann and P. J. Hilton, *Group-like structures in general categories I. Multiplications
  and comultiplications*, Math. Ann. **145** (1962), 227–255.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.C, Exercise 5.
-/

public section

namespace FundamentalGroup

open Path.Homotopic

noncomputable section

variable {M : Type*} [TopologicalSpace M] [MulOneClass M] [ContinuousMul M]

/-- The homomorphism `π₁(M, 1) × π₁(M, 1) → π₁(M, 1)` induced by the multiplication of `M`. -/
private def mulHom :
    FundamentalGroup M 1 × FundamentalGroup M 1 →* FundamentalGroup M 1 :=
  (mapOfEq ⟨fun x : M × M ↦ x.1 * x.2, continuous_mul⟩
      (mul_one (1 : M))).comp
    (prodMulEquiv (1 : M) (1 : M)).symm.toMonoidHom

/-- The homomorphism induced by multiplication sends a pair of loop classes to the class of the
pointwise product. -/
private theorem mulHom_apply (a b : FundamentalGroup M 1) :
    mulHom (a, b) = .of
      (((prod a.asHom b.asHom).map ⟨fun x : M × M ↦ x.1 * x.2, continuous_mul⟩).cast
        (mul_one 1).symm (mul_one 1).symm) := by
  simp [mulHom, mapOfEq_apply]

/-- Multiplying a loop pointwise by the constant loop at the unit does not change its class. -/
private theorem mulHom_inl (a : FundamentalGroup M 1) :
    mulHom (a, 1) = a := by
  rw [mulHom_apply]
  obtain ⟨a⟩ := a
  induction a using Path.Homotopic.Quotient.ind with | mk γ => ?_
  rw [one_def, ← Quotient.mk_refl, prod_lift, ← Quotient.mk_map,
    ← Quotient.mk_cast]
  congr 2
  ext t
  simp

/-- Multiplying the constant loop at the unit pointwise by a loop does not change its class. -/
private theorem mulHom_inr (b : FundamentalGroup M 1) :
    mulHom (1, b) = b := by
  rw [mulHom_apply]
  obtain ⟨b⟩ := b
  induction b using Path.Homotopic.Quotient.ind with | mk δ => ?_
  rw [one_def, ← Quotient.mk_refl, prod_lift, ← Quotient.mk_map,
    ← Quotient.mk_cast]
  congr 2
  ext t
  simp

/-- The constant loop at `1` is a two-sided unit for pointwise multiplication of loop classes. -/
private theorem isUnital_mulHom :
    EckmannHilton.IsUnital (fun a b : FundamentalGroup M 1 ↦ mulHom (a, b)) 1 :=
  EckmannHilton.IsUnital.mk
    { left_id := mulHom_inr, right_id := mulHom_inl }

/-- Pointwise multiplication of loop classes is a homomorphism for the fundamental group law. -/
private theorem mulHom_mul_mul (a b c d : FundamentalGroup M 1) :
    mulHom (a * b, c * d) =
      mulHom (a, c) * mulHom (b, d) := by
  rw [← map_mul, Prod.mk_mul_mk]

/-- **The pointwise product of loops is their product in the fundamental group.** In a space
with a continuous multiplication and a two-sided unit `1`, the class of the loop
`t ↦ γ t * δ t` is the product in `π₁(M, 1)` of the classes of the loops `γ` and `δ` at `1`. -/
theorem cast_map_prod_mul (a b : FundamentalGroup M 1) :
    (.of (((prod a.asHom b.asHom).map ⟨fun x : M × M ↦ x.1 * x.2, continuous_mul⟩).cast
      (mul_one 1).symm (mul_one 1).symm) : FundamentalGroup M 1) = a * b := by
  rw [← mulHom_apply]
  exact congrFun₂ (EckmannHilton.mul isUnital_mulHom
    EckmannHilton.MulOneClass.isUnital mulHom_mul_mul) a b

/-- **The fundamental group of a topological monoid is abelian.** In a space with a continuous
multiplication and a two-sided unit `1`, the fundamental group at `1` is commutative, since the
group law distributes over pointwise multiplication of loops, which has the same unit. -/
instance instCommGroup : CommGroup (FundamentalGroup M 1) :=
  { (inferInstance : Group (FundamentalGroup M 1)) with
    -- A tactic block, so that the private helpers stay out of the exported instance term.
    mul_comm := by
      exact (EckmannHilton.mul_comm isUnital_mulHom
        EckmannHilton.MulOneClass.isUnital mulHom_mul_mul).comm }

variable {N : Type*} [TopologicalSpace N] [MulOneClass N] [ContinuousMul N]

/-- **Naturality of the pointwise product of loops.** A continuous map `f : M → N` with
`f 1 = 1`, for instance a continuous monoid homomorphism, induces a homomorphism
`π₁(M, 1) → π₁(N, 1)` that sends the class of the pointwise product of two loops at `1` to the
class of the pointwise product of loops representing the images of their classes. The map `f`
need not be multiplicative, since on both sides the pointwise product of loops is the group law
(`FundamentalGroup.cast_map_prod_mul`). -/
theorem mapOfEq_cast_map_prod (f : C(M, N)) (hf : f 1 = 1) (a b : FundamentalGroup M 1) :
    mapOfEq f hf
        (.of (((prod a.asHom b.asHom).map ⟨fun x : M × M ↦ x.1 * x.2, continuous_mul⟩).cast
          (mul_one 1).symm (mul_one 1).symm)) =
      .of (((prod (mapOfEq f hf a).asHom (mapOfEq f hf b).asHom).map
          ⟨fun x : N × N ↦ x.1 * x.2, continuous_mul⟩).cast (mul_one 1).symm (mul_one 1).symm) := by
  rw [cast_map_prod_mul, cast_map_prod_mul, map_mul]

end

end FundamentalGroup
