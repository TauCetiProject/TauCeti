/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.TopologicalMonoid

/-!
# Pointwise multiplication and concatenation of loops

In a space with continuous multiplication and a two-sided unit, pointwise multiplication of
loops at the unit is homotopic, relative to the endpoints, to concatenation in either order.
This makes the reversal in `FundamentalGroup.mul_def` explicit at the level of paths.

The comparison uses `FundamentalGroup.cast_map_prod_mul` and the commutative group structure
provided by the Eckmann–Hilton argument. A unit-preserving multiplicative continuous map
preserves the pointwise loop product as an actual path, not just a homotopy class. On classes,
the induced homomorphism is the existing `FundamentalGroup.mapOfEq`; its `map_mul` law then
identifies the images of both products without introducing a second induced-map construction.

## References

* Allen Hatcher, *Algebraic Topology*, §3.C, Exercise 5, p.291.
-/

public section

namespace Path

variable {M : Type*} [TopologicalSpace M] [MulOneClass M] [ContinuousMul M]

/-- The pointwise product of two loops at the unit is homotopic to their concatenation in
reverse order, the order used in `FundamentalGroup.mul_def`. -/
theorem cast_mul_homotopic_trans_swap (γ δ : Path (1 : M) 1) :
    ((γ.mul δ).cast (mul_one 1).symm (mul_one 1).symm).Homotopic (δ.trans γ) := by
  have h := FundamentalGroup.cast_map_prod_mul
    (FundamentalGroup.fromPath (Homotopic.Quotient.mk γ))
    (FundamentalGroup.fromPath (Homotopic.Quotient.mk δ))
  rw [FundamentalGroup.mul_def] at h
  apply Homotopic.Quotient.exact
  -- `Path.mul` is the product path followed by multiplication.
  simpa only [Path.mul, Homotopic.prod_lift, ← Homotopic.Quotient.mk_map,
    ← Homotopic.Quotient.mk_cast, ← Homotopic.Quotient.mk_trans] using
    congrArg CategoryTheory.End.asHom h

/-- The pointwise product of two loops at the unit is homotopic to traversing the first loop
and then the second. No commutativity of the underlying multiplication is required. -/
theorem cast_mul_homotopic_trans (γ δ : Path (1 : M) 1) :
    ((γ.mul δ).cast (mul_one 1).symm (mul_one 1).symm).Homotopic (γ.trans δ) := by
  have h := FundamentalGroup.cast_map_prod_mul
    (FundamentalGroup.fromPath (Homotopic.Quotient.mk γ))
    (FundamentalGroup.fromPath (Homotopic.Quotient.mk δ))
  rw [mul_comm, FundamentalGroup.mul_def] at h
  apply Homotopic.Quotient.exact
  -- `Path.mul` is the product path followed by multiplication.
  simpa only [Path.mul, Homotopic.prod_lift, ← Homotopic.Quotient.mk_map,
    ← Homotopic.Quotient.mk_cast, ← Homotopic.Quotient.mk_trans] using
    congrArg CategoryTheory.End.asHom h

/-- Concatenation of loops at the unit of a topological monoid commutes up to homotopy
relative to the endpoints. -/
theorem trans_homotopic_trans_swap (γ δ : Path (1 : M) 1) :
    (γ.trans δ).Homotopic (δ.trans γ) :=
  (γ.cast_mul_homotopic_trans δ).symm.trans (γ.cast_mul_homotopic_trans_swap δ)

variable {N : Type*} [TopologicalSpace N] [MulOneClass N] [ContinuousMul N]

/-- A unit-preserving multiplicative continuous map preserves the pointwise product of based
loops, including the endpoint transports to the unit. -/
@[simp]
theorem map_cast_mul (γ δ : Path (1 : M) 1) (f : C(M, N)) (h₁ : f 1 = 1)
    (hmul : ∀ x y, f (x * y) = f x * f y) :
    (((γ.mul δ).cast (mul_one 1).symm (mul_one 1).symm).map f.continuous).cast
        h₁.symm h₁.symm =
      (((γ.map f.continuous).cast h₁.symm h₁.symm).mul
        ((δ.map f.continuous).cast h₁.symm h₁.symm)).cast
          (mul_one 1).symm (mul_one 1).symm := by
  ext t
  exact hmul (γ t) (δ t)

end Path
