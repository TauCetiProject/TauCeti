/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs

import TauCeti.LinearAlgebra.Dual.Submodule

/-!
# Linear-form separation criteria for finite integral closures

Let `R` be a Noetherian commutative ring, `K` a field that is a faithful `R`-algebra, and `L` a
commutative `R`-algebra that is a finite-dimensional `K`-vector space compatibly with `R`. Applying
the submodule linear-separation theorems of `TauCeti.LinearAlgebra.Dual.Submodule` to
`(integralClosure R L).toSubmodule` shows that any integral closure `C` of `R` in `L` is a finite
`R`-module whenever `K`-linear forms on `L` sending integral elements into
`Set.range (algebraMap R K)` separate nonzero integral elements, and that this condition is
necessary and sufficient when `K` is a fraction field of `R`.

## Main results

* `TauCeti.IsIntegralClosure.finite_of_forall_exists_dual_ne_zero`: an integral closure `C` of a
  Noetherian ring `R` in `L` is a finite `R`-module whenever `K`-linear forms on `L` carrying
  integral elements into `Set.range (algebraMap R K)` separate nonzero integral elements.
* `TauCeti.IsIntegralClosure.finite_iff_forall_exists_dual_ne_zero`: equivalence of finiteness and
  linear-form separation when `K` is a fraction field of `R`.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §4.1, Lemma 3 and Proposition 4.
-/

public section

namespace TauCeti

section IsIntegralClosure

variable {R : Type*} [CommRing R]

/-- Let `R` be a Noetherian commutative ring, `K` a field that is a faithful `R`-algebra, and `L` a
commutative `R`-algebra that is a finite-dimensional `K`-vector space compatibly with `R`. An
integral closure `C` of `R` in `L` is a finite `R`-module whenever every nonzero element of `L`
integral over `R` is separated from `0` by a `K`-linear form on `L` carrying integral elements into
`Set.range (algebraMap R K)`
(Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §4.1, Lemma 3). -/
theorem IsIntegralClosure.finite_of_forall_exists_dual_ne_zero [IsNoetherianRing R]
    {L : Type*} [CommRing L] [Algebra R L]
    (C : Type*) [CommRing C] [Algebra R C] [Algebra C L] [IsScalarTower R C L]
    [IsIntegralClosure C R L]
    (K : Type*) [Field K] [Algebra R K] [FaithfulSMul R K]
    [Module K L] [IsScalarTower R K L] [FiniteDimensional K L]
    (h : ∀ x : L, IsIntegral R x → x ≠ 0 → ∃ φ : Module.Dual K L,
      (∀ y : L, IsIntegral R y → φ y ∈ Set.range (algebraMap R K)) ∧ φ x ≠ 0) :
    Module.Finite R C := by
  have heq : (integralClosure R L).toSubmodule.FG ↔ Module.Finite R C :=
    Module.Finite.iff_fg.symm.trans <| Module.Finite.equiv_iff <|
      (integralClosure R L).toSubmoduleEquiv.trans
        (IsIntegralClosure.equiv R (integralClosure R L) L C).toLinearEquiv
  exact heq.mp <| (integralClosure R L).toSubmodule.fg_of_forall_exists_dual_mem_range_ne_zero h

/-- Over a Noetherian ring `R` with fraction field `K`, an integral closure `C` of `R` in `L` is a
finite `R`-module if and only if `K`-linear forms on `L` carrying integral elements into
`Set.range (algebraMap R K)` separate nonzero integral elements
(Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §4.1, Proposition 4). -/
theorem IsIntegralClosure.finite_iff_forall_exists_dual_ne_zero [IsNoetherianRing R]
    {C : Type*} [CommRing C] [Algebra R C]
    (K L : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing L] [Algebra R L] [Algebra C L] [IsScalarTower R C L] [IsIntegralClosure C R L]
    [Module K L] [IsScalarTower R K L] [FiniteDimensional K L] :
    Module.Finite R C ↔ ∀ x : L, IsIntegral R x → x ≠ 0 → ∃ φ : Module.Dual K L,
      (∀ y : L, IsIntegral R y → φ y ∈ Set.range (algebraMap R K)) ∧ φ x ≠ 0 := by
  have heq : Module.Finite R C ↔ (integralClosure R L).toSubmodule.FG :=
    (Module.Finite.equiv_iff <|
      (IsIntegralClosure.equiv R C L (integralClosure R L)).toLinearEquiv.trans
        (integralClosure R L).toSubmoduleEquiv.symm).trans Module.Finite.iff_fg
  exact heq.trans ((integralClosure R L).toSubmodule.fg_iff_forall_exists_dual_ne_zero K)

end IsIntegralClosure

end TauCeti
