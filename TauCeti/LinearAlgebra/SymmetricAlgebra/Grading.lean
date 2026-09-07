/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous

/-!
# The grading of a symmetric algebra

Let `M` be a module over a commutative semiring. The powers of the image of `M` in its symmetric
algebra are not merely a spanning family: they form an internal direct sum. Thus every element of
the symmetric algebra has a unique finite decomposition into homogeneous terms.

Consequently a map out of the symmetric algebra can be studied degree by degree: it is determined
by its restrictions to the homogeneous pieces, so two such maps agreeing on all of them agree, and
if it carries each piece into a corresponding summand of an internal decomposition of its target,
then it is injective as soon as all of those restrictions are.

Directness comes from the universal property: the external direct sum of the homogeneous pieces is
again a commutative algebra, so sending a generator to its degree-one copy produces an algebra map
splitting the recomposition map. No freeness of `M` is needed. This argument follows Mathlib's
`TensorAlgebra.gradedAlgebra`, in `Mathlib/LinearAlgebra/TensorAlgebra/Grading.lean`, which grades
the tensor algebra the same way.

## Main results

* `gradedAlgebra`: the homogeneous pieces grade the symmetric algebra, so in particular they
  decompose it.
-/

public section

namespace TauCeti.SymmetricAlgebra

open Module

open scoped DirectSum

universe u v

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A version of `SymmetricAlgebra.ι` that maps directly into the graded structure. This is
primarily an auxiliary construction used to provide `gradedAlgebra`. -/
noncomputable def GradedAlgebra.ι : M →ₗ[R] ⨁ n, homogeneousSubmodule R M n :=
  DirectSum.lof R ℕ (fun n ↦ homogeneousSubmodule R M n) 1 ∘ₗ
    (SymmetricAlgebra.ι R M).codRestrict _ fun m ↦ by
      simpa only [pow_one] using LinearMap.mem_range_self _ m

/-- The defining formula for `GradedAlgebra.ι`. -/
theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι R M m = DirectSum.of (fun n ↦ homogeneousSubmodule R M n) 1
      ⟨SymmetricAlgebra.ι R M m, by simpa only [pow_one] using LinearMap.mem_range_self _ m⟩ :=
  (rfl)

/-- A symmetric algebra is graded by its homogeneous pieces, without a freeness assumption on `M`.
This supplies both the canonical decomposition and the multiplicative graded-algebra API. -/
noncomputable instance gradedAlgebra : GradedAlgebra (homogeneousSubmodule R M) :=
  GradedAlgebra.ofAlgHom _ (SymmetricAlgebra.lift (GradedAlgebra.ι R M))
    (by
      ext m
      simp only [LinearMap.coe_comp, LinearMap.coe_coe, AlgHom.coe_comp, Function.comp_apply,
        SymmetricAlgebra.lift_ι_apply, GradedAlgebra.ι_apply, DirectSum.coeAlgHom_of,
        AlgHom.coe_id, id_eq])
    -- A homogeneous element is a sum of products of `n` generators, so induction on the power
    -- reduces to the degree-one case.
    fun n x ↦ by
      obtain ⟨x, hx⟩ := x
      dsimp only [DirectSum.lof_eq_of]
      induction hx using Submodule.pow_induction_on_left' with
      | algebraMap r => rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
      | add x y i hx hy ihx ihy => rw [map_add, ihx, ihy, ← map_add]; rfl
      | mem_mul m hm i x hx ih =>
          obtain ⟨_, rfl⟩ := hm
          rw [map_mul, ih, SymmetricAlgebra.lift_ι_apply, GradedAlgebra.ι_apply,
            DirectSum.of_mul_of]
          exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

end TauCeti.SymmetricAlgebra
