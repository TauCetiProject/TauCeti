/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.Cone.FiniteGeneration
public import TauCeti.Geometry.Convex.Cone.FiniteDuality

/-!
# Minkowski–Weyl duality for pointed cones

In finite-dimensional spaces over a linearly ordered field, finite generation
is equivalent to having finitely many defining linear inequalities. The two
directions combine finite generation under halfspace cuts with the algebraic
separation theorem for finitely generated cones. No topological closedness is
assumed in this argument, and cones with lineality are allowed.

## Provenance

Adapted from `Mei/Geometry/Convex/Cone/MinkowskiWeyl.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`68536122a97fed8e87bc6870b9427151971b9ab2`, licensed under Apache 2.0.
-/

public section

namespace Submodule.FG

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] [Module.Finite K V] {C : PointedCone K V}

/-- A finitely generated cone in a finite-dimensional space is cut out by
finitely many algebraic linear inequalities under evaluation. -/
theorem cone_dualFG (hC : C.FG) :
    C.DualFG (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V) := by
  let p : Module.Dual K V →ₗ[K] Module.Dual K V := LinearMap.id
  have hdual : (PointedCone.dual p.flip C).FG :=
    (PointedCone.DualFG.dual_of_fg p.flip hC).fg
  have hresult := PointedCone.DualFG.dual_of_fg p hdual
  rwa [hC.cone_dual_dual_flip_id] at hresult

end Submodule.FG

namespace PointedCone

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] [Module.Finite K V] {C : PointedCone K V}

/-- **Minkowski–Weyl:** a pointed cone is finitely generated exactly when it is
cut out by finitely many linear halfspaces, including when it has lineality. -/
theorem fg_iff_dualFG :
    C.FG ↔ C.DualFG (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V) :=
  ⟨Submodule.FG.cone_dualFG, DualFG.fg⟩

end PointedCone
