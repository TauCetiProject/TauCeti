/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.StarSubalgebra

/-!
# Closedness of centralizers as `⋆`-subalgebras

In a Hausdorff topological `⋆`-ring with separately continuous multiplication, the centralizer
(relative commutant) `NonUnitalStarSubalgebra.centralizer R s` and `StarSubalgebra.centralizer R s`
of any subset `s` is closed. Together with `NonUnitalStarSubalgebra.nonUnitalCStarAlgebra` and
`StarSubalgebra.cstarAlgebra`, this equips relative commutants in C⋆-algebras (such as central
sequence algebras `A_ω ∩ A′` and `M(A)_ω ∩ A′`) with their induced C⋆-algebra structure.
-/

public section

namespace NonUnitalStarSubalgebra

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [StarRing A] [TopologicalSpace A]
  [SeparatelyContinuousMul A] [T2Space A]

/-- The centralizer of any subset as a non-unital `⋆`-subalgebra is closed. -/
instance isClosed_centralizer (s : Set A) : IsClosed (centralizer R s : Set A) := by
  rw [coe_centralizer]
  exact Set.isClosed_centralizer _

end NonUnitalStarSubalgebra

namespace StarSubalgebra

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [Algebra R A] [StarRing A]
  [StarModule R A] [TopologicalSpace A] [SeparatelyContinuousMul A] [T2Space A]

/-- The centralizer of any subset as a unital `⋆`-subalgebra is closed. -/
instance isClosed_centralizer (s : Set A) : IsClosed (centralizer R s : Set A) := by
  rw [coe_centralizer]
  exact Set.isClosed_centralizer _

end StarSubalgebra
