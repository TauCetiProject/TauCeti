/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Data.ZMod.IntUnitsPower
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Module.GradedModule.Coarsen

/-!
# Coarsening the grading of a graded algebra

If `𝒜 : ι → Submodule R A` grades an `R`-algebra `A` and `f : ι →+ κ` is an additive
homomorphism of index monoids, the coarsened family `TauCeti.coarsenGrading 𝒜 f`, whose
degree-`k` piece is the sum of the pieces `𝒜 i` with `f i = k`, again grades `A`.  In particular
an integer-graded algebra is a `ZMod 2`-graded (super) algebra through its parity grading
`TauCeti.parityGrading 𝒜`.

Graded commutativity with Koszul signs `(-1) ^ (p * q)` passes to any coarsening along a ring
homomorphism `f : ι →+* κ` that preserves `(-1) ^ ·`.  In particular, integer graded commutativity
passes to the parity grading, with the signs `(-1) ^ (i * j)` for parities `i j : ZMod 2`, written
with Mathlib's power of a unit of `ℤ` by an element of `ZMod 2`.  Thus the supercommutativity
relations of an integer-graded algebra are those of its parity reduction.

## Main results

* `TauCeti.coarsenGrading_mul_le`: the product of coarsened pieces of degrees `k` and `l` lies in
  the coarsened piece of degree `k + l`.
* The instances `SetLike.GradedMul (coarsenGrading 𝒜 f)`, over a nonunital algebra,
  `SetLike.GradedMonoid (coarsenGrading 𝒜 f)` and `GradedAlgebra (coarsenGrading 𝒜 f)`, which
  apply in particular to `parityGrading 𝒜`.
* `TauCeti.mul_eq_uzpow_smul_mul_of_mem_coarsenGrading` and
  `TauCeti.mul_eq_uzpow_smul_mul_of_mem_parityGrading`: Koszul graded commutativity passes to
  sign-preserving coarsenings, and in particular from integer degree to parity.
-/

public section

open DirectSum

namespace TauCeti

universe uR uA uι uκ

section GradedMul

variable {R : Type uR} {A : Type uA} {ι : Type uι} {κ : Type uκ} {F : Type*}
  [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [AddMonoid ι] [AddMonoid κ]
  [FunLike F ι κ] [AddMonoidHomClass F ι κ] (𝒜 : ι → Submodule R A)

/-- Coarsening a graded multiplication along an additive homomorphism of index monoids gives a
graded multiplication. -/
instance [SetLike.GradedMul 𝒜] (f : F) : SetLike.GradedMul (coarsenGrading 𝒜 f) where
  mul_mem k l a b ha hb := by
    -- Both sides are additive in each factor, so it suffices to treat homogeneous elements.
    refine coarsenGrading_induction (motive := fun a ↦ a * b ∈ coarsenGrading 𝒜 f (k + l)) ha
      (fun i hi a ha ↦ ?_) (by simp) fun x y hx hy ↦ by rw [add_mul]; exact add_mem hx hy
    refine coarsenGrading_induction (motive := fun b ↦ a * b ∈ coarsenGrading 𝒜 f (k + l)) hb
      (fun j hj b hb ↦ ?_) (by simp) fun x y hx hy ↦ by rw [mul_add]; exact add_mem hx hy
    rw [← hi, ← hj, ← map_add]
    exact mem_coarsenGrading_of_mem f (SetLike.mul_mem_graded ha hb)

end GradedMul

section GradedMonoid

variable {R : Type uR} {A : Type uA} {ι : Type uι} {κ : Type uκ} {F : Type*}
  [Semiring R] [Semiring A] [Module R A] [AddMonoid ι] [AddMonoid κ]
  [FunLike F ι κ] [AddMonoidHomClass F ι κ] (𝒜 : ι → Submodule R A)

instance [SetLike.GradedMonoid 𝒜] (f : F) : SetLike.GradedMonoid (coarsenGrading 𝒜 f) :=
  { (inferInstance : SetLike.GradedMul (coarsenGrading 𝒜 f)) with
    one_mem := by simpa using mem_coarsenGrading_of_mem f (SetLike.one_mem_graded 𝒜) }

/-- The product of the coarsened pieces of degrees `k` and `l` of a graded multiplication lies
in the coarsened piece of degree `k + l`. -/
theorem coarsenGrading_mul_le [IsScalarTower R A A] [SetLike.GradedMul 𝒜] (f : F)
    (k l : κ) :
    coarsenGrading 𝒜 f k * coarsenGrading 𝒜 f l ≤ coarsenGrading 𝒜 f (k + l) :=
  Submodule.mul_le.2 fun _ ha _ hb ↦ SetLike.mul_mem_graded ha hb

end GradedMonoid

section Coarsen

variable {R : Type uR} {A : Type uA} {ι : Type uι} {κ : Type uκ} {F : Type*}
  [CommSemiring R] [Semiring A] [Algebra R A] [AddMonoid ι] [AddMonoid κ]
  [FunLike F ι κ] [AddMonoidHomClass F ι κ] (𝒜 : ι → Submodule R A)

/-- Coarsening the grading of a graded algebra along an additive homomorphism of index monoids
gives a graded algebra. -/
noncomputable instance [DecidableEq ι] [DecidableEq κ] [GradedAlgebra 𝒜] (f : F) :
    GradedAlgebra (coarsenGrading 𝒜 f) :=
  { (inferInstance : SetLike.GradedMonoid (coarsenGrading 𝒜 f)),
    (inferInstance : Decomposition (coarsenGrading 𝒜 f)) with }

end Coarsen

section CoarsenComm

variable {R : Type uR} {A : Type uA} {ι : Type uι} {κ : Type uκ}
  [Semiring R] [NonUnitalNonAssocRing A] [Module R A]
  [CommSemiring ι] [Module ι (Additive ℤˣ)] [CommSemiring κ] [Module κ (Additive ℤˣ)]
  {𝒜 : ι → Submodule R A}

/-- **Koszul graded commutativity passes to any sign-preserving coarsening.** If homogeneous
elements of degrees `p` and `q` commute up to the Koszul sign `(-1) ^ (p * q)` and the ring
homomorphism `f : ι →+* κ` preserves `(-1) ^ ·`, then elements of coarsened degrees `i` and `j`
commute up to `(-1) ^ (i * j)`. -/
theorem mul_eq_uzpow_smul_mul_of_mem_coarsenGrading {f : ι →+* κ}
    (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    (hcomm : ∀ {p q : ι} {a b : A}, a ∈ 𝒜 p → b ∈ 𝒜 q →
      a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a))
    {i j : κ} {a b : A} (ha : a ∈ coarsenGrading 𝒜 f i) (hb : b ∈ coarsenGrading 𝒜 f j) :
    a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a) := by
  -- Both sides are additive in each factor, so it suffices to treat homogeneous elements.
  refine coarsenGrading_induction (motive := fun a ↦ a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a)) ha
    (fun p hp a ha ↦ ?_) (by simp) fun x y hx hy ↦ by rw [add_mul, mul_add, hx, hy, smul_add]
  refine coarsenGrading_induction (motive := fun b ↦ a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a)) hb
    (fun q hq b hb ↦ ?_) (by simp) fun x y hx hy ↦ by rw [mul_add, add_mul, hx, hy, smul_add]
  rw [hcomm ha hb, ← hp, ← hq, ← map_mul, hf]

end CoarsenComm

section ParityComm

variable {R : Type uR} {A : Type uA} [Semiring R] [NonUnitalNonAssocRing A] [Module R A]
  {𝒜 : ℤ → Submodule R A}

/-- **Integer graded commutativity implies parity graded commutativity.** If homogeneous
elements of degrees `p` and `q` commute up to the Koszul sign `(-1) ^ (p * q)`, then elements of
parities `i` and `j` commute up to the sign `(-1) ^ (i * j)`. -/
theorem mul_eq_uzpow_smul_mul_of_mem_parityGrading
    (hcomm : ∀ {p q : ℤ} {a b : A}, a ∈ 𝒜 p → b ∈ 𝒜 q → a * b = (p * q).negOnePow • (b * a))
    {i j : ZMod 2} {a b : A} (ha : a ∈ parityGrading 𝒜 i) (hb : b ∈ parityGrading 𝒜 j) :
    a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a) :=
  mul_eq_uzpow_smul_mul_of_mem_coarsenGrading (f := Int.castRingHom (ZMod 2))
    (fun p ↦ uzpow_intCast (-1) p) hcomm ha hb

end ParityComm

end TauCeti
