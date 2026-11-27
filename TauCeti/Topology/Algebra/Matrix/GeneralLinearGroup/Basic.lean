/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Topology.Algebra.Group.Units

/-!
# Continuity of homomorphisms into the general linear group

For the units topology on `GL n A = Matrix.GeneralLinearGroup n A`, a homomorphism from a group
with continuous inversion into `GL n A` is continuous exactly when its matrix entries are
continuous: by `MonoidHom.continuous_iff_continuous_val` the inverse matrices `ρ(g)⁻¹ = ρ(g⁻¹)`
come for free, and a matrix-valued map is continuous exactly when its entries are.

## Main results

* `MonoidHom.continuous_iff_continuous_matrix_elem`: continuity of a homomorphism into `GL n A`
  through its matrix entries.
-/

public section

/-- **Continuity into `GL n A` through the matrix entries.** For the units topology on `GL n A`, a
homomorphism `ρ : G →* GL n A` from a group with continuous inversion is continuous exactly when
every entry `g ↦ ρ(g)ᵢⱼ` is continuous; the inverse matrices are handled by
`MonoidHom.continuous_iff_continuous_val`. -/
theorem MonoidHom.continuous_iff_continuous_matrix_elem {G n A : Type*} [Group G]
    [TopologicalSpace G] [ContinuousInv G] [Fintype n] [DecidableEq n] [Semiring A]
    [TopologicalSpace A] (ρ : G →* GL n A) :
    Continuous ρ ↔ ∀ i j, Continuous fun g => (ρ g : Matrix n n A) i j :=
  ρ.continuous_iff_continuous_val.trans ⟨fun h i j => h.matrix_elem i j, continuous_matrix⟩
