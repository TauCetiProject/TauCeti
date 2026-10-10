/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Basic
public import Mathlib.Algebra.DirectSum.Algebra

/-!
# The graded algebra of normalized cubical chains of a topological monoid

For a topological monoid `G`, the Pontryagin product of
`TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Basic` makes the family
`n ↦ C^□_n(G; R)` of normalized cubical chains a graded `R`-algebra, in the sense of Mathlib's
`DirectSum.GAlgebra`: the product of a `p`-chain and a `q`-chain is a `(p + q)`-chain, the unit
is the `0`-cube at `1`, and the scalars act through `r ↦ r • 1`.  The strict associativity and
unit laws hold up to the reindexings of `NormalizedCubicalChain.cast`, which are the equalities of
graded components `HEq` required by `GradedMonoid.GMonoid`.

Hence `⨁ n : ℕ, C^□_n(G; R)` is an `R`-algebra, `TauCeti.normalizedCubicalChainAlgebra G R`, in
which the product of homogeneous elements is their Pontryagin product (`DirectSum.of_mul_of` and
`NormalizedCubicalChain.gMul_mul`), with unit the `0`-cube at `1`
(`NormalizedCubicalChain.gOne_one`).

## Main definitions

* `TauCeti.cubicalChainLof G R n`: the inclusion of the `n`-chains, with `cubicalChainLof_mul`.
* `TauCeti.normalizedCubicalChainAlgebra G R`: the graded algebra `⨁ n, C^□_n(G; R)`.
* `TauCeti.NormalizedCubicalChain.gMonoid`, `.gRing`, `.gAlgebra`: the graded structures.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

open DirectSum

namespace TauCeti

namespace NormalizedCubicalChain

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G] {R : Type*} [CommRing R]

variable (G R) in
/-- The unit of the graded structure. -/
instance gOne : GradedMonoid.GOne fun n : ℕ ↦ NormalizedCubicalChain G R n where
  one := one G R

variable (G R) in
/-- The multiplication of the graded structure. -/
instance gMul : GradedMonoid.GMul fun n : ℕ ↦ NormalizedCubicalChain G R n where
  mul := fun {p q} a b ↦ mul G R p q a b

omit [ContinuousMul G] in
/-- The unit of the graded structure is the `0`-cube at `1`. -/
@[simp]
theorem gOne_one : (GradedMonoid.GOne.one : NormalizedCubicalChain G R 0) = one G R :=
  (rfl)

/-- The multiplication of the graded structure is the Pontryagin product. -/
@[simp]
theorem gMul_mul {p q : ℕ} (a : NormalizedCubicalChain G R p) (b : NormalizedCubicalChain G R q) :
    GradedMonoid.GMul.mul a b = mul G R p q a b :=
  (rfl)

variable (G R) in
/-- The Pontryagin product makes the normalized cubical chains a graded monoid. -/
instance gMonoid : GradedMonoid.GMonoid fun n : ℕ ↦ NormalizedCubicalChain G R n where
  one_mul := fun ⟨n, b⟩ ↦
    Sigma.ext (Nat.zero_add n) (heq_of_cast_eq (Nat.zero_add n) (one_mul b))
  mul_one := fun ⟨n, a⟩ ↦
    Sigma.ext (Nat.add_zero n) (heq_of_cast_eq (Nat.add_zero n) (mul_one a))
  mul_assoc := fun ⟨p, a⟩ ⟨q, b⟩ ⟨r, c⟩ ↦
    Sigma.ext (Nat.add_assoc p q r) (heq_of_cast_eq (Nat.add_assoc p q r) (mul_assoc a b c))

variable (G R) in
/-- The Pontryagin product makes the normalized cubical chains a graded ring. -/
instance gRing : DirectSum.GRing fun n : ℕ ↦ NormalizedCubicalChain G R n where
  mul_zero := fun {_ _} a ↦ map_zero (mul G R _ _ a)
  zero_mul := fun {_ _} b ↦ LinearMap.map_zero₂ (mul G R _ _) b
  mul_add := fun {_ _} a b c ↦ map_add (mul G R _ _ a) b c
  add_mul := fun {_ _} a b c ↦ LinearMap.map_add₂ (mul G R _ _) a b c
  natCast := fun n ↦ n • one G R
  natCast_zero := zero_nsmul _
  natCast_succ := fun n ↦ succ_nsmul _ n
  intCast := fun n ↦ n • one G R
  intCast_ofNat := fun n ↦ natCast_zsmul _ n
  intCast_negSucc_ofNat := fun n ↦ negSucc_zsmul _ n

theorem mul_zero_smul_one {q : ℕ} (r : R) (b : NormalizedCubicalChain G R q) :
    cast R (Nat.zero_add q) (mul G R 0 q (r • one G R) b) = r • b := by
  rw [LinearMap.map_smul₂, map_smul, one_mul]

theorem mul_smul_one_zero {p : ℕ} (r : R) (a : NormalizedCubicalChain G R p) :
    cast R (Nat.add_zero p) (mul G R p 0 a (r • one G R)) = r • a := by
  rw [map_smul, map_smul, mul_one]

variable (G R) in
/-- The graded semiring structure underlying `gRing`. -/
instance gSemiring : DirectSum.GSemiring fun n : ℕ ↦ NormalizedCubicalChain G R n :=
  (gRing G R).toGSemiring

variable (G R) in
/-- The graded nonunital nonassociative semiring structure underlying `gRing`. -/
instance gNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring fun n : ℕ ↦ NormalizedCubicalChain G R n :=
  (gRing G R).toGSemiring.toGNonUnitalNonAssocSemiring

variable (G R) in
/-- Scalar multiples of the unit make the normalized cubical chains a graded `R`-algebra. -/
instance gAlgebra : DirectSum.GAlgebra R fun n : ℕ ↦ NormalizedCubicalChain G R n where
  toFun := (LinearMap.toSpanSingleton R _ (one G R)).toAddMonoidHom
  map_one := one_smul R (one G R)
  map_mul r s := by
    refine congrArg (GradedMonoid.mk 0) ?_
    simp only [gMul_mul, LinearMap.toAddMonoidHom_coe, LinearMap.toSpanSingleton_apply]
    have h1 : mul G R 0 0 (one G R) (one G R) = one G R := by
      simpa using one_mul (one G R)
    rw [LinearMap.map_smul₂, map_smul, h1, mul_smul]
  commutes r := fun ⟨n, b⟩ ↦
    Sigma.ext ((Nat.zero_add n).trans (Nat.add_zero n).symm)
      ((heq_of_cast_eq (Nat.zero_add n) (mul_zero_smul_one r b)).trans
        (heq_of_cast_eq (Nat.add_zero n) (mul_smul_one_zero r b)).symm)
  smul_def r := fun ⟨n, b⟩ ↦
    Sigma.ext (Nat.zero_add n).symm
      (heq_of_cast_eq (Nat.zero_add n) (mul_zero_smul_one r b)).symm

end NormalizedCubicalChain

variable (G : Type*) [Monoid G] [TopologicalSpace G] [ContinuousMul G] (R : Type*) [CommRing R]

/-- The **graded algebra of normalized cubical chains** of a topological monoid `G`:
`⨁ n, C^□_n(G; R)` with the Pontryagin product. -/
abbrev normalizedCubicalChainAlgebra : Type _ := ⨁ n : ℕ, NormalizedCubicalChain G R n

/-- The ring structure of the graded algebra of normalized cubical chains. -/
instance : Ring (normalizedCubicalChainAlgebra G R) :=
  DirectSum.ring (fun n : ℕ ↦ NormalizedCubicalChain G R n)

/-- The inclusion of the chains of dimension `n` into the graded algebra. -/
abbrev cubicalChainLof (n : ℕ) :
    NormalizedCubicalChain G R n →ₗ[R] normalizedCubicalChainAlgebra G R :=
  DirectSum.lof R ℕ (fun n ↦ NormalizedCubicalChain G R n) n

omit [Monoid G] [ContinuousMul G] in
/-- Reindexing a chain does not change its image in the graded algebra. -/
theorem cubicalChainLof_cast {n m : ℕ} (h : n = m) (x : NormalizedCubicalChain G R n) :
    cubicalChainLof G R m (NormalizedCubicalChain.cast R h x) = cubicalChainLof G R n x := by
  subst h
  rw [NormalizedCubicalChain.cast_rfl]

/-- The product of homogeneous chains in the graded algebra is their Pontryagin product. -/
theorem cubicalChainLof_mul {p q : ℕ} (a : NormalizedCubicalChain G R p)
    (b : NormalizedCubicalChain G R q) :
    cubicalChainLof G R p a * cubicalChainLof G R q b =
      cubicalChainLof G R (p + q) (NormalizedCubicalChain.mul G R p q a b) := by
  rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_mul_of,
    NormalizedCubicalChain.gMul_mul]

end TauCeti

end
