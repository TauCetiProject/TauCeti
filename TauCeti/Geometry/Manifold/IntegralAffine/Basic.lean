/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Manifold.SMulGroupoid
public import TauCeti.Geometry.Toric.Algebraic.IntegralAffine

/-!
# The structure groupoid of integral affine chart changes

The structure groupoid of integral affine chart changes is the `TauCeti.smulGroupoid` of the
group of integral affine self-equivalences acting on the ambient space. A chart change whose
source is connected extends uniquely to one global integral affine equivalence; this follows from
the unique-extension theorems `IntegralAffineEquiv.existsUnique_extension` and
`IntegralAffineEquiv.existsUnique_extension_connectedComponentIn`.

Adapted from `yuma-mizuno-lean/Mei`, commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`,
`Mei/Geometry/Manifold/IntegralAffine/Basic.lean` (Apache 2.0).
-/

public section

open Set Filter Topology

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : IsIntegralLattice i}

variable (h) in
/-- The structure groupoid of integral affine chart changes: open partial homeomorphisms of the
ambient space that are locally given by an integral affine self-equivalence. -/
abbrev integralAffineGroupoid : StructureGroupoid V :=
  smulGroupoid (IntegralAffineEquiv h h) V

/-- A partial homeomorphism lies in the integral affine groupoid iff it agrees near each point of
its source with an integral affine self-equivalence. -/
theorem mem_integralAffineGroupoid_iff {e : OpenPartialHomeomorph V V} :
    e ∈ integralAffineGroupoid h ↔
      ∀ x ∈ e.source, ∃ a : IntegralAffineEquiv h h, e =ᶠ[𝓝 x] a := by
  simp only [integralAffineGroupoid, mem_smulGroupoid_iff, IntegralAffineEquiv.smul_def]

/-- A connected nonempty chart-change domain has a unique global integral affine extension. -/
theorem existsUnique_extension_of_mem_integralAffineGroupoid
    {e : OpenPartialHomeomorph V V} (he : e ∈ integralAffineGroupoid h)
    (hc : IsConnected e.source) :
    ∃! a : IntegralAffineEquiv h h, EqOn e a e.source :=
  IntegralAffineEquiv.existsUnique_extension (mem_integralAffineGroupoid_iff.mp he)
    e.open_source hc

/-- Each connected component of the source of a chart change has a unique global integral
affine extension. -/
theorem existsUnique_extension_connectedComponentIn_of_mem_integralAffineGroupoid
    {e : OpenPartialHomeomorph V V} (he : e ∈ integralAffineGroupoid h) {x : V}
    (hx : x ∈ e.source) :
    ∃! a : IntegralAffineEquiv h h, EqOn e a (connectedComponentIn e.source x) :=
  IntegralAffineEquiv.existsUnique_extension_connectedComponentIn
    (mem_integralAffineGroupoid_iff.mp he) e.open_source hx

end TauCeti.Toric
