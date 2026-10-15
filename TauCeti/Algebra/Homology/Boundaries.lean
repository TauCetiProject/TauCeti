/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The differential onto the boundaries

Let `K` be a homological complex in an abelian category.  Write `Zⱼ` for its cycles in degree `j`,
`Hⱼ` for its homology and `Bⱼ = ker (Zⱼ ⟶ Hⱼ)` for its boundaries, the kernel of the projection of
the cycles onto the homology.  The differential `Kᵢ ⟶ Kⱼ` corestricts to a morphism
`K.toBoundaries i j : Kᵢ ⟶ Bⱼ`.  For a relation `i → j` of the shape it is the cokernel of the
inclusion `Zᵢ ⟶ Kᵢ` of the cycles (`HomologicalComplex.toBoundariesIsCokernel`), so that
`0 ⟶ Zᵢ ⟶ Kᵢ ⟶ Bⱼ ⟶ 0` is short exact.

Together with `0 ⟶ Bⱼ ⟶ Zⱼ ⟶ Hⱼ ⟶ 0`, this is the decomposition of a complex into cycles,
boundaries and homology, used for splitting complexes and for the universal coefficient sequence.

## Main declarations

* `HomologicalComplex.toBoundaries`: the corestriction `Kᵢ ⟶ Bⱼ` of the differential.
* `HomologicalComplex.epi_toBoundaries`: it is an epimorphism for a relation `i → j`.
* `HomologicalComplex.toBoundariesIsCokernel`: it is then the cokernel of `Zᵢ ⟶ Kᵢ`.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)

/-- The corestriction `Kᵢ ⟶ Bⱼ` of the differential to the boundaries `Bⱼ = ker (Zⱼ ⟶ Hⱼ)`. -/
def toBoundaries (i j : ι) : K.X i ⟶ kernel (K.homologyπ j) :=
  kernel.lift _ (K.toCycles i j) (K.toCycles_comp_homologyπ i j)

/-- The corestriction of the differential to the boundaries, followed by the inclusion of the
boundaries into the cycles, is the corestriction of the differential to the cycles. -/
@[reassoc (attr := simp)]
lemma toBoundaries_ι (i j : ι) :
    K.toBoundaries i j ≫ kernel.ι (K.homologyπ j) = K.toCycles i j :=
  kernel.lift_ι _ _ _

/-- The corestriction of the differential to the boundaries vanishes on the cycles. -/
@[reassoc (attr := simp)]
lemma iCycles_toBoundaries (i j : ι) : K.iCycles i ≫ K.toBoundaries i j = 0 := by
  rw [← cancel_mono (kernel.ι _), ← cancel_mono (K.iCycles j)]
  simp

/-- The corestriction of the differential to the boundaries vanishes on boundaries. -/
@[reassoc (attr := simp)]
lemma d_toBoundaries (h i j : ι) : K.d h i ≫ K.toBoundaries i j = 0 := by
  rw [← cancel_mono (kernel.ι _)]
  simp

/-- For a relation `i → j` of the shape, the corestriction `Kᵢ ⟶ Bⱼ` of the differential is an
epimorphism, because the homology `Hⱼ` is the cokernel of `Kᵢ ⟶ Zⱼ`. -/
lemma epi_toBoundaries {i j : ι} (hij : c.Rel i j) : Epi (K.toBoundaries i j) :=
  (ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk (K.toCycles i j) (K.homologyπ j) (K.toCycles_comp_homologyπ i j))
    (K.homologyIsCokernel i j (c.prev_eq' hij))).epi_kernelLift

/-- For a relation `i → j` of the shape, the corestriction `Kᵢ ⟶ Bⱼ` of the differential is the
cokernel of the inclusion `Zᵢ ⟶ Kᵢ` of the cycles: it is an epimorphism whose kernel is `Zᵢ`, the
kernel of the differential. -/
def toBoundariesIsCokernel {i j : ι} (hij : c.Rel i j) :
    IsColimit (CokernelCofork.ofπ (K.toBoundaries i j) (K.iCycles_toBoundaries i j)) :=
  have := K.epi_toBoundaries hij
  Abelian.epiIsCokernelOfKernel _
    (isKernelOfComp (kernel.ι _ ≫ K.iCycles j) (K.d i j) (K.cyclesIsKernel i j (c.next_eq' hij))
      (K.iCycles_toBoundaries i j) (by simp))

end HomologicalComplex
