/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation
public import TauCeti.Algebra.Homology.DG.Module.Right.Cohomology

/-!
# The unit class of an augmented differential graded algebra

Let `A` be a differential graded algebra over a nontrivial commutative ring `R` with an
augmentation `ε : A → R`. The unit `1` of `A` is a cycle of degree `0`, and it is not a boundary:
`ε` vanishes on boundaries and takes the value `1` on the unit. So the class of the unit in the
cohomology of `A`, as a right DG module over itself, is nonzero
(`TauCeti.DGAlgAugmentation.quotientMk_one_ne_zero`), and the cohomology of `A` in degree `0` is
nontrivial (`TauCeti.DGAlgAugmentation.nontrivial_cohomologyGrading_zero`). For the chains on a
loop space this is the nonvanishing of the homology in degree `0`, detected by the class of the
constant loop.

## Main results

* `TauCeti.DGAlgAugmentation.quotientMk_one_ne_zero`: the class of the unit is nonzero.
* `TauCeti.DGAlgAugmentation.nontrivial_cohomologyGrading_zero`: `H⁰(A)` is nontrivial.
-/

public section

namespace TauCeti

namespace DGAlgAugmentation

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  (e : DGAlgAugmentation h)

include e

/-- **The class of the unit of an augmented DG algebra is nonzero**: over a nontrivial ring the
unit is a cycle that is not a boundary, since the augmentation vanishes on boundaries. -/
theorem quotientMk_one_ne_zero [Nontrivial R] :
    (Submodule.Quotient.mk
        (⟨1, h.isDGRightModule.mem_cycles.2 h.map_one_eq_zero⟩ : h.isDGRightModule.cycles) :
      h.isDGRightModule.Cohomology) ≠ 0 := by
  rw [Ne, IsDGRightModule.quotientMk_eq_zero_iff, IsDGRightModule.mem_boundaries]
  rintro ⟨a, ha⟩
  have h₁ := congrArg e ha
  rw [e.map_d, map_one] at h₁
  exact zero_ne_one h₁

/-- **The cohomology of an augmented DG algebra in degree `0` is nontrivial** over a nontrivial
ring: it contains the nonzero class of the unit. -/
theorem nontrivial_cohomologyGrading_zero [Nontrivial R] :
    Nontrivial (h.isDGRightModule.cohomologyGrading 0) :=
  ⟨⟨⟨_, h.isDGRightModule.quotientMk_mem_cohomologyGrading (SetLike.one_mem_graded 𝒜)⟩, 0,
    fun h₀ ↦ e.quotientMk_one_ne_zero (congrArg Subtype.val h₀)⟩⟩

end DGAlgAugmentation

end TauCeti
