/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Bases

/-!
# Basic facts about generalized Schauder bases

The basis vectors of a generalized Schauder basis span a dense subspace whenever its summation
filter is nontrivial, since every vector is a limit of finite coordinate projections.

An unconditional basis indexed by `ℕ` is also a classical Schauder basis: convergence along the
net of all finite sets implies convergence along initial segments. The conversion
`UnconditionalSchauderBasis.toSchauderBasis` keeps the basis vectors and coordinate functionals,
so the classical theory of shrinking and boundedly complete bases applies to unconditional bases
such as the coordinate bases of `c₀` and `ℓᵖ`.

The conversion follows Mathlib's `HilbertBasis.toSchauderBasis`.
-/

public section

open Filter Set Topology

namespace GeneralSchauderBasis

variable {β 𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {L : SummationFilter β} (b : GeneralSchauderBasis β 𝕜 X L)

/-- The basis vectors of a generalized Schauder basis span a dense subspace. -/
theorem dense_span [L.NeBot] : Dense (Submodule.span 𝕜 (range b) : Set X) := fun x ↦
  mem_closure_of_tendsto (b.tendsto_proj x) (Eventually.of_forall fun A ↦ by
    rw [SetLike.mem_coe, proj_apply]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i)))

end GeneralSchauderBasis

namespace UnconditionalSchauderBasis

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (b : UnconditionalSchauderBasis ℕ 𝕜 X)

/-- An unconditional basis indexed by `ℕ` is a classical Schauder basis, with the same basis
vectors and coordinate functionals. -/
protected def toSchauderBasis : SchauderBasis 𝕜 X where
  basis := b
  coord := b.coord
  ortho := b.ortho
  expansion x := (b.expansion x).mono_left SummationFilter.le_atTop

/-- The basis vectors of the classical basis are the original basis vectors. -/
@[simp]
theorem coe_toSchauderBasis : ⇑b.toSchauderBasis = ⇑b :=
  (rfl)

/-- The coordinate functionals of the classical basis are the original coordinate functionals. -/
@[simp]
theorem toSchauderBasis_coord : b.toSchauderBasis.coord = b.coord :=
  (rfl)

/-- The initial projections of the classical basis are the projections of the unconditional basis
onto initial segments. -/
@[simp]
theorem toSchauderBasis_proj (n : ℕ) :
    b.toSchauderBasis.proj n = b.proj (Finset.range n) :=
  (rfl)

end UnconditionalSchauderBasis
