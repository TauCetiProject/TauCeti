/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic

/-!
# The fundamental cycle of the cube pair

The identity cube `upCube (m + 1)` of `Iᵐ⁺¹` sends the boundary of the cube into `∂Iᵐ⁺¹`, so it is
a relative cycle of the normalized cubical chains of the cube pair `(Iᵐ⁺¹, ∂Iᵐ⁺¹)`
(`TauCeti.cubeBoundaryPairCycle`). A singular cube `c` of a pair `P` sending the boundary of the
cube into the subspace is a map of pairs `c : (Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ P` (`TauCeti.cubeBoundaryPairHom`),
and it sends the class of this fundamental cycle to the class of `c` in relative cubical homology
(`TauCeti.homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle`).

## Main declarations

* `TauCeti.mapsTo_upCube_boundary`: the identity cube sends the boundary of the cube into the
  subspace of the cube pair.
* `TauCeti.cubeBoundaryPairCycle`: the fundamental relative cycle of the cube pair.
* `TauCeti.homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle`: `c_*[Iᵐ⁺¹] = [c]` in relative
  cubical homology.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Set
open scoped unitInterval

universe u

namespace TauCeti

variable (k : Type u) [Ring k]

/-- The identity cube `upCube m` sends the boundary of `Iᵐ` into the subspace `∂Iᵐ` of the cube
pair. -/
lemma mapsTo_upCube_boundary (m : ℕ) :
    MapsTo (upCube.{u} m : SingularCube (cubeBoundaryPair.{u} m).fst m) (Cube.boundary (Fin m))
      (range (cubeBoundaryPair.{u} m).map) :=
  fun y hy ↦ ⟨⟨ULift.up y, hy⟩, rfl⟩

/-- The fundamental relative cycle of the cube pair `(Iᵐ⁺¹, ∂Iᵐ⁺¹)`: the identity cube `upCube`,
as a relative cycle of the normalized cubical chains with coefficients in `k`. -/
def cubeBoundaryPairCycle (m : ℕ) :
    ((cubeBoundaryPair.{u} (m + 1)).cubicalChainComplex k).cycles (m + 1) :=
  TopPair.cubicalCycleOfCube k _ (mapsTo_upCube_boundary (m + 1))

/-- The map of pairs `c : (Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ P` given by a cube `c` sends the class of the fundamental
cycle of the cube pair to the class of `c` in relative cubical homology. -/
theorem homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle {P : TopPair.{u}} {m : ℕ}
    (c : SingularCube P.fst (m + 1)) (hc : MapsTo c (Cube.boundary (Fin (m + 1))) (range P.map)) :
    HomologicalComplex.homologyMap
        (TopPair.cubicalChainComplexMap k (cubeBoundaryPairHom c hc)) (m + 1)
        (((cubeBoundaryPair.{u} (m + 1)).cubicalChainComplex k).homologyπ (m + 1)
          (cubeBoundaryPairCycle k m)) =
      (P.cubicalChainComplex k).homologyπ (m + 1) (TopPair.cubicalCycleOfCube k c hc) := by
  -- The cube `c ∘ upCube` is `c`.
  have hcid : (TopPair.Hom.fst (cubeBoundaryPairHom c hc)).hom.comp
      (upCube.{u} (m + 1) : SingularCube (cubeBoundaryPair.{u} (m + 1)).fst (m + 1)) = c :=
    ContinuousMap.ext fun y ↦ cubeBoundaryPairHom_fst_apply c hc _
  rw [← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply]
  exact congrArg _ ((TopPair.cyclesMap_cubicalCycleOfCube k _ _ _ (by rw [hcid]; exact hc)).trans
    (by simp only [hcid]))

end TauCeti
