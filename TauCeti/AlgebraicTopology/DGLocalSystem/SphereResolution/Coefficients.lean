/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.SphereResolution
public import TauCeti.AlgebraicTopology.DGLocalSystem.CellResolution.Coefficients
public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation.Cohomology

/-!
# The sphere with coefficients in its loop chains, acted on trivially

For the sphere `Sⁿ`, `n = m + 2`, with one `0`-cell at the pole and one `n`-cell attached along the
attaching cycle `x` of its top cell, the free module `K` of `TauCeti.sphereCellCocycle` is Brown's
semi-free resolution of the ground ring `k` over the chains `C_*(Ω_b Sⁿ; k)` on the Moore loops
(`TauCeti.exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`). So the
twisted complex with coefficients in the chains on the loops, acted on by multiplication, is
identified with `K` and has the homology of the based path space of `Sⁿ`, that of a point: this is
the fibration theorem for the path-loop fibration.

The action matters. With the trivial action of the loops on their chains, through the
augmentation (`TauCeti.trivialLoopChainAction`), the attaching cycle, of positive dimension `n - 1`,
acts by zero, and the twisted complex splits: its cohomology in degree `q` is
`H^q(Ω_b Sⁿ) × H^{q + n}(Ω_b Sⁿ)` (`TauCeti.sphereCellCocycleTrivialActionHomologyEquiv`), in
homological terms `H_*(Sⁿ) ⊗ H_*(Ω_b Sⁿ)`. It does not vanish in degree `-n`, where it contains
`H_0(Ω_b Sⁿ)` (`TauCeti.nontrivial_sphereCellCocycle_trivialAction_homology`), so it is not the
homology of a point.

## Main definitions

* `TauCeti.sphereCellCocycleTrivialActionHomologyEquiv`: the twisted homology of the sphere with
  coefficients in its loop chains acted on trivially.

## Main results

* `TauCeti.nontrivial_sphereCellCocycle_trivialAction_homology`: this twisted homology is
  nonzero in degree `-n`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 7 (the fibration
  theorem).
-/

public noncomputable section

open Metric

namespace TauCeti

variable {ι : Type} [Fintype ι] {m : ℕ} (h : Fintype.card ι = m + 3) (k : Type) [CommRing k]

local notation "Sph" => sphere (0 : EuclideanSpace ℝ ι) 1

/-- **The twisted homology of the sphere with the trivial action.** For the sphere `Sⁿ`,
`n = m + 2`, the twisted complex of `TauCeti.sphereCellCocycle` with coefficients in the chains
`C_*(Ω_b Sⁿ; k)` on the loops, acted on trivially through the augmentation, has cohomology
`H^q(Ω_b Sⁿ) × H^{q + n}(Ω_b Sⁿ)` in degree `q`: the attaching cycle of the top cell acts by zero.
With the action by multiplication the same twisted complex is Brown's resolution of `k`. -/
def sphereCellCocycleTrivialActionHomologyEquiv (q : ℤ) :
    ((sphereCellCocycle h k).coefficientCochainComplex
        ((loopChain_isDGAlgebra Sph (spherePolePoint h) k).isDGRightModule.restrictScalars
          (trivialLoopChainAction Sph (spherePolePoint h) k))).homology q ≃ₗ[k]
      (loopChain_isDGAlgebra Sph (spherePolePoint h) k).isDGRightModule.cohomologyGrading q ×
        (loopChain_isDGAlgebra Sph (spherePolePoint h) k).isDGRightModule.cohomologyGrading
          (q + ((m : ℤ) + 2)) :=
  cycleCellCocycleTrivialActionHomologyEquiv _ _ (loopChainAugmentation_sphereAttachingChain h k)
      q ≪≫ₗ
    (LinearEquiv.refl k _).prodCongr (LinearEquiv.ofEq _ _ (by push_cast; ring_nf))

/-- **With the trivial action the twisted homology of the sphere is not that of a point.** Over a
nontrivial ring `k`, the twisted homology of `Sⁿ`, `n = m + 2`, with coefficients in the chains on
its loops acted on trivially is nonzero in degree `-n`, where it contains `H_0(Ω_b Sⁿ)`, the
class of the constant loop. With the action by multiplication the twisted complex is identified
with Brown's resolution of `k`
(`TauCeti.exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`), whose
homology vanishes outside degree `0`. -/
theorem nontrivial_sphereCellCocycle_trivialAction_homology [Nontrivial k] :
    Nontrivial (((sphereCellCocycle h k).coefficientCochainComplex
        ((loopChain_isDGAlgebra Sph (spherePolePoint h) k).isDGRightModule.restrictScalars
          (trivialLoopChainAction Sph (spherePolePoint h) k))).homology (-((m : ℤ) + 2))) := by
  have : Nontrivial ((loopChain_isDGAlgebra Sph (spherePolePoint h) k).isDGRightModule
      |>.cohomologyGrading (-((m : ℤ) + 2) + ((m : ℤ) + 2))) := by
    rw [neg_add_cancel]
    exact (loopChainAugmentation Sph (spherePolePoint h) k).nontrivial_cohomologyGrading_zero
  exact (sphereCellCocycleTrivialActionHomologyEquiv h k _).toEquiv.nontrivial

end TauCeti
