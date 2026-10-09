/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.Algebra.Category.ModuleCat.Projective.PID

/-!
# Cycles of complexes of projective modules over a principal ideal domain

Let `X` be a homological complex of modules over a principal ideal ring `k` without zero divisors,
whose terms are projective. Since submodules of projective `k`-modules are projective
(`ModuleCat.projective_of_mono`), the cycles `Zᵢ ⊆ Xᵢ` are projective, and so is the image
`Bᵢ' ⊆ Xᵢ'` of the outgoing differential `Xᵢ ⟶ Xᵢ'`. The short exact sequence
`0 ⟶ Zᵢ ⟶ Xᵢ ⟶ Bᵢ' ⟶ 0` therefore splits, so the inclusion of the cycles is a split
monomorphism.

These are the two hypotheses of the universal coefficient sequence
`TauCeti.ChainComplex.extToHomology`, `TauCeti.ChainComplex.exact_extToHomology_kronecker` and
`TauCeti.ChainComplex.kronecker_surjective_of_isSplitMono`. With the instances of this file, the
universal coefficient theorem applies to every degreewise projective chain complex of modules over
a principal ideal domain, for instance to singular chains with integer coefficients.

## Main declarations

* `HomologicalComplex.projective_cycles`: the cycles in a projective term are projective.
* `HomologicalComplex.isSplitMono_iCycles`: their inclusion is a split monomorphism when the next
  term is projective.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, proof of Theorem 3.2.
-/

public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex

variable {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] [Small.{v} k]
  {ι : Type*} {c : ComplexShape ι} (X : HomologicalComplex (ModuleCat.{v} k) c)

/-- Over a principal ideal domain, the cycles in a projective term of a complex of modules are
projective. -/
instance projective_cycles (i : ι) [Projective (X.X i)] : Projective (X.cycles i) :=
  ModuleCat.projective_of_mono (X.iCycles i)

/-- Over a principal ideal domain, the inclusion of the cycles `Zᵢ ⟶ Xᵢ` of a complex of modules
whose next term `Xᵢ'` is projective is a split monomorphism: its cokernel is the image of the
outgoing differential, a projective submodule of `Xᵢ'`. -/
instance isSplitMono_iCycles (i : ι) [Projective (X.X (c.next i))] : IsSplitMono (X.iCycles i) := by
  have := ModuleCat.projective_of_mono (image.ι (X.d i (c.next i)))
  have hf : X.iCycles i ≫ factorThruImage (X.d i (c.next i)) = 0 := by
    rw [← cancel_mono (image.ι _), Category.assoc, image.fac, iCycles_d, zero_comp]
  -- the cycles are the kernel of `Xᵢ ⟶ Bᵢ'`, the corestriction of the differential to its image
  have hS : (ShortComplex.mk _ _ hf).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _
        (isKernelOfComp _ _ (X.cyclesIsKernel i (c.next i) rfl) hf (image.fac _)) }
  exact hS.splittingOfProjective.isSplitMono_f

end HomologicalComplex
