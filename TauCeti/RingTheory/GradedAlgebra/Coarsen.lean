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

Graded commutativity with integer Koszul signs `(-1) ^ (p * q)` passes to the parity grading,
with the signs `(-1) ^ (i * j)` for parities `i j : ZMod 2`, written with Mathlib's power of a
unit of `ℤ` by an element of `ZMod 2`.  Thus the supercommutativity relations of an
integer-graded algebra are those of its parity reduction.

## Main results

* `TauCeti.coarsenGrading_mul_le`: the product of coarsened pieces of degrees `k` and `l` lies in
  the coarsened piece of degree `k + l`.
* The instances `SetLike.GradedMonoid (coarsenGrading 𝒜 f)` and
  `GradedAlgebra (coarsenGrading 𝒜 f)`, which apply in particular to `parityGrading 𝒜`.
* `TauCeti.mul_eq_uzpow_smul_mul_of_mem_parityGrading`: integer graded commutativity implies
  parity graded commutativity.
-/

public section

open DirectSum

namespace TauCeti

universe uR uA uι uκ

section Coarsen

variable {R : Type uR} {A : Type uA} {ι : Type uι} {κ : Type uκ}
  [CommSemiring R] [Semiring A] [Algebra R A] [AddMonoid ι] [AddMonoid κ] (𝒜 : ι → Submodule R A)

/-- The product of the coarsened pieces of degrees `k` and `l` of a graded multiplication lies
in the coarsened piece of degree `k + l`. -/
theorem coarsenGrading_mul_le [SetLike.GradedMul 𝒜] (f : ι →+ κ) (k l : κ) :
    coarsenGrading 𝒜 f k * coarsenGrading 𝒜 f l ≤ coarsenGrading 𝒜 f (k + l) := by
  rw [coarsenGrading_apply 𝒜 f k, coarsenGrading_apply 𝒜 f l]
  simp only [Submodule.iSup_mul, Submodule.mul_iSup]
  refine iSup₂_le fun i hi ↦ iSup₂_le fun j hj ↦ ?_
  rw [← hi, ← hj, ← map_add]
  exact (Submodule.mul_le.2 fun _ ha _ hb ↦ SetLike.mul_mem_graded ha hb).trans
    (le_coarsenGrading 𝒜 f _)

instance [SetLike.GradedMonoid 𝒜] (f : ι →+ κ) : SetLike.GradedMonoid (coarsenGrading 𝒜 f) where
  one_mem := by simpa using mem_coarsenGrading_of_mem f (SetLike.one_mem_graded 𝒜)
  mul_mem _ _ _ _ ha hb := coarsenGrading_mul_le 𝒜 f _ _ (Submodule.mul_mem_mul ha hb)

/-- Coarsening the grading of a graded algebra along an additive homomorphism of index monoids
gives a graded algebra. -/
noncomputable instance [DecidableEq ι] [DecidableEq κ] [GradedAlgebra 𝒜] (f : ι →+ κ) :
    GradedAlgebra (coarsenGrading 𝒜 f) :=
  { (inferInstance : SetLike.GradedMonoid (coarsenGrading 𝒜 f)),
    (inferInstance : Decomposition (coarsenGrading 𝒜 f)) with }

end Coarsen

section ParityComm

variable {R : Type uR} {A : Type uA} [Semiring R] [NonUnitalNonAssocRing A] [Module R A]
  {𝒜 : ℤ → Submodule R A}

/-- **Integer graded commutativity implies parity graded commutativity.** If homogeneous
elements of degrees `p` and `q` commute up to the Koszul sign `(-1) ^ (p * q)`, then elements of
parities `i` and `j` commute up to the sign `(-1) ^ (i * j)`. -/
theorem mul_eq_uzpow_smul_mul_of_mem_parityGrading
    (hcomm : ∀ {p q : ℤ} {a b : A}, a ∈ 𝒜 p → b ∈ 𝒜 q → a * b = (p * q).negOnePow • (b * a))
    {i j : ZMod 2} {a b : A} (ha : a ∈ parityGrading 𝒜 i) (hb : b ∈ parityGrading 𝒜 j) :
    a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a) := by
  -- Both sides are additive in each factor, so it suffices to treat homogeneous elements.
  refine coarsenGrading_induction (motive := fun a ↦ a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a)) ha
    (fun p hp a ha ↦ ?_) (by simp) fun x y hx hy ↦ by rw [add_mul, mul_add, hx, hy, smul_add]
  refine coarsenGrading_induction (motive := fun b ↦ a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a)) hb
    (fun q hq b hb ↦ ?_) (by simp) fun x y hx hy ↦ by rw [mul_add, add_mul, hx, hy, smul_add]
  rw [hcomm ha hb, ← hp, ← hq, Int.coe_castAddHom, ← Int.cast_mul, uzpow_intCast,
    Int.negOnePow_def]

end ParityComm

end TauCeti
