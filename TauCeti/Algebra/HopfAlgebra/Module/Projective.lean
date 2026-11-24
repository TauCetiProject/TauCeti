/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.Module.Finsupp
public import TauCeti.Algebra.HopfAlgebra.Module.Regular
public import Mathlib.LinearAlgebra.TensorProduct.Projective

/-!
# Tensor products with projective modules over a Hopf algebra

Let `H` be a Hopf algebra over a commutative semiring `R`. The coproduct tensor product `H ⊗ M`
of the regular module with an `H`-module `M` is isomorphic to `H ⊗[R] M` with `H` acting on the
left factor alone (`TauCeti.BialgebraModule.regularTensorEquiv`), and for a bijective antipode
so is `M ⊗ H` (`TauCeti.BialgebraModule.tensorRegularEquiv`). So the coproduct tensor product of
the regular module with a module that is projective over `R` is a projective `H`-module.

Distributing over free modules and passing to retracts gives the main results: `P ⊗ M` is
projective whenever `P` is a projective `H`-module and `M` is projective over `R`
(`TauCeti.BialgebraModule.projective_tensor_left`), and, for a bijective antipode, so is
`M ⊗ P` (`TauCeti.BialgebraModule.projective_tensor_right`). Over a field every module
is projective over `R`, so the projective modules are closed under tensoring with arbitrary
modules on the right, and, for a bijective antipode, on the left as well. This is what makes
the maps factoring through projective modules a tensor ideal of the category of all modules,
the starting point of the stable category of a finite-dimensional Hopf algebra.

## Main declarations

* `TauCeti.BialgebraModule.projective_tensor_left`,
  `TauCeti.BialgebraModule.projective_tensor_right`: tensoring a projective module with a module
  projective over `R` on either side gives a projective module.

## References

* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications 25 (2016), Proposition 2.
* Y. Qi, *Hopfological algebra*, Compos. Math. 150 (2014), Lemma 2.3.
-/

public noncomputable section

open scoped TensorProduct
open HopfAlgebra

namespace TauCeti.BialgebraModule

variable {R H : Type*} [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]
variable {M : Type*} [AddCommMonoid M] [Module R M] [Module H M] [IsScalarTower R H M]

section Projective

variable {P : Type*} [AddCommMonoid P] [Module R P] [Module H P] [IsScalarTower R H P]

/-- The coproduct tensor product `P ⊗ M` of a projective module `P` with a module `M` that is
projective over the base is projective. -/
instance projective_tensor_left [Module.Projective H P] [Module.Projective R M] :
    Module.Projective H (Tensor R H P M) := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective H P›
  -- `P ⊗ M` is a retract of `(P →₀ H) ⊗ M`, a direct sum of copies of `H ⊗ M ≅ H ⊗[R] M`.
  have : Module.Projective H (Tensor R H H M) :=
    .of_equiv (regularTensorEquiv R H M).symm
  have : Module.Projective H (Tensor R H (P →₀ H) M) :=
    .of_equiv ((finsuppLEquivDirectSum H (Tensor R H H M) P).symm ≪≫ₗ
      (finsuppLeft R H P H M).symm)
  refine .of_split (tensorMap R H s LinearMap.id)
    (tensorMap R H (Finsupp.linearCombination H id) LinearMap.id) ?_
  rw [← tensorMap_comp, hs, LinearMap.id_comp, tensorMap_id]

variable (R H M P) in
/-- For a bijective antipode, the coproduct tensor product `M ⊗ P` of a module `M` that is
projective over the base with a projective module `P` is projective. -/
theorem projective_tensor_right (hS : Function.Bijective (antipode R : H →ₗ[R] H))
    [Module.Projective H P] [Module.Projective R M] :
    Module.Projective H (Tensor R H M P) := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective H P›
  -- `M ⊗ P` is a retract of `M ⊗ (P →₀ H)`, a direct sum of copies of `M ⊗ H ≅ H ⊗[R] M`.
  have : Module.Projective H (Tensor R H M H) :=
    .of_equiv (tensorRegularEquiv R H M hS).symm
  have : Module.Projective H (Tensor R H M (P →₀ H)) :=
    .of_equiv ((finsuppLEquivDirectSum H (Tensor R H M H) P).symm ≪≫ₗ
      (finsuppRight R H P H M).symm)
  refine .of_split (tensorMap R H LinearMap.id s)
    (tensorMap R H LinearMap.id (Finsupp.linearCombination H id)) ?_
  rw [← tensorMap_comp, hs, LinearMap.id_comp, tensorMap_id]

end Projective

end TauCeti.BialgebraModule
