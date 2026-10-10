/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Prism
public import TauCeti.AlgebraicTopology.Singular.Cubical.Augment
public import TauCeti.Topology.Homotopy.Cube.Basic

/-!
# Acyclicity of cubical chains on cubes

The coordinatewise straight-line contraction of `N → I` to its zero vertex gives explicit fillings
in normalized cubical chains. In positive degrees, `∂ fill + fill ∂ = id`; in degree zero,
`∂ fill = id - ε • [0]`. Thus every positive-degree cycle and every augmentation-zero
0-chain bounds, over any ring. These are the augmented acyclicity statements on the cube
models used in the acyclic-models comparison with simplicial singular chains, taking `N := Fin k`.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
-/

public section

noncomputable section

open unitInterval

namespace TauCeti

namespace NormalizedCubicalChain

variable (R : Type*) [Ring R]

/-- A degree-one filling operator on the normalized chains of the cube `N → I`. -/
def fill (N : Type*) (n : ℕ) :
    NormalizedCubicalChain (N → I) R n →ₗ[R]
      NormalizedCubicalChain (N → I) R (n + 1) :=
  prism R (cubeContraction N) n

/-- On generators the filling is the negative of the straight-line swept cube. -/
@[simp]
theorem fill_ofCube (N : Type*) {n : ℕ} (c : SingularCube (N → I) n) :
    fill R N n (ofCube _ R c) =
      -ofCube _ R (SingularCube.prism (cubeContraction N) c) := by
  rw [fill, prism_ofCube]

/-- The filling operator contracts the normalized cubical chains in positive degrees. -/
theorem boundary_fill_add_fill_boundary (N : Type*) (n : ℕ)
    (c : NormalizedCubicalChain (N → I) R (n + 1)) :
    boundary _ R (n + 1) (fill R N (n + 1) c) +
      fill R N n (boundary _ R n c) = c := by
  simpa [fill] using boundary_prism_add_prism_boundary R (cubeContraction N) n c

/-- In degree zero, the contraction retracts onto the zero vertex through the augmentation. -/
theorem boundary_fill_zero (N : Type*) (c : NormalizedCubicalChain (N → I) R 0) :
    boundary _ R 0 (fill R N 0 c) =
      c - augment _ R c • ofCube _ R (SingularCube.point (fun _ : N ↦ (0 : I))) := by
  simpa [fill, map_const_zero] using
    boundary_prism_zero R (cubeContraction N) c

/-- The normalized cubical chains of the cube `N → I` are exact in every positive degree. -/
theorem range_boundary_eq_ker_boundary (N : Type*) (n : ℕ) :
    LinearMap.range (boundary (N → I) R (n + 1)) =
      LinearMap.ker (boundary (N → I) R n) := by
  refine le_antisymm (LinearMap.range_le_ker_iff.2 (boundary_boundary R n)) ?_
  intro c hc
  rw [LinearMap.mem_ker] at hc
  exact ⟨fill R N (n + 1) c, by simpa [hc] using boundary_fill_add_fill_boundary R N n c⟩

/-- The augmented normalized cubical chains of the cube `N → I` are exact in degree zero. -/
theorem range_boundary_eq_ker_augment (N : Type*) :
    LinearMap.range (boundary (N → I) R 0) = LinearMap.ker (augment (N → I) R) := by
  refine le_antisymm (LinearMap.range_le_ker_iff.2 (augment_boundary R)) ?_
  intro c hc
  rw [LinearMap.mem_ker] at hc
  exact ⟨fill R N 0 c, by simpa [hc] using boundary_fill_zero R N c⟩

end NormalizedCubicalChain

end TauCeti
