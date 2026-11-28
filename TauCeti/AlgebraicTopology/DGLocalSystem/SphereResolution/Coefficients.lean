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
semi-free resolution of the ground ring `k` over the chains `C_*(Ω_b Sⁿ; k)` on the Moore loops:
every cycle of `K` of augmentation zero is a boundary
(`TauCeti.exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`). Informally,
and not formalised here, the twisted complex with coefficients in the chains on the loops, acted
on by multiplication, is `K` itself, so it has the homology of the based path space of `Sⁿ`, that
of a point: this is the fibration theorem for the path-loop fibration.

The action matters. With the trivial action of the loops on their chains, through the
augmentation (`TauCeti.DGAlgAugmentation.trivialAction`), the attaching cycle, of positive
dimension `n - 1`, acts by zero, and the twisted complex splits: its cohomology in degree `q` is
`H^q(Ω_b Sⁿ) × H^{q + n}(Ω_b Sⁿ)` (`TauCeti.sphereCellCocycleTrivialActionHomologyEquiv`), in
homological terms `H_*(Sⁿ) ⊗ H_*(Ω_b Sⁿ)`. It does not vanish in degree `-n`, where it contains
`H_0(Ω_b Sⁿ)` (`TauCeti.nontrivial_sphereCellCocycle_trivialAction_homology`), so it is not the
homology of a point.

## Main definitions

* `TauCeti.sphereCellCocycleTrivialActionHomologyEquiv`: the twisted homology of the sphere with
  coefficients in its loop chains acted on trivially.

## Main results

* `TauCeti.coe_sphereCellCocycleTrivialActionHomologyEquiv_apply_fst`,
  `TauCeti.coe_sphereCellCocycleTrivialActionHomologyEquiv_apply_snd`: the components of a class
  are those given by the cell attached along the attaching cycle.
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
By contrast, the free module of `TauCeti.sphereCellCocycle` is Brown's resolution of `k`. -/
def sphereCellCocycleTrivialActionHomologyEquiv (q : ℤ) :
    ((sphereCellCocycle h k).coefficientCochainComplex
        ((loopChain_isDGAlgebra Sph (spherePolePoint h) k).isDGRightModule.restrictScalars
          (loopChainAugmentation Sph (spherePolePoint h) k).trivialAction)).homology q ≃ₗ[k]
      (loopChain_isDGAlgebra Sph (spherePolePoint h) k).isDGRightModule.cohomologyGrading q ×
        (loopChain_isDGAlgebra Sph (spherePolePoint h) k).isDGRightModule.cohomologyGrading
          (q + ((m : ℤ) + 2)) :=
  cycleCellCocycleTrivialActionHomologyEquiv _ _ (loopChainAugmentation_sphereAttachingChain h k)
      q ≪≫ₗ
    (LinearEquiv.refl k _).prodCongr
      (LinearEquiv.ofEq _ _ (by rw [show ((m + 1 : ℕ) : ℤ) + 1 = m + 2 by omega]))

/-- The `e₀`-component of `TauCeti.sphereCellCocycleTrivialActionHomologyEquiv` of a class is that
of `TauCeti.cycleCellCocycleHomologyEquivOfOpSmulEqZero` for the attaching cycle, read in
`H(Ω_b Sⁿ)`. -/
@[simp]
theorem coe_sphereCellCocycleTrivialActionHomologyEquiv_apply_fst (q : ℤ)
    (c : ((sphereCellCocycle h k).coefficientCochainComplex
        ((loopChain_isDGAlgebra Sph (spherePolePoint h) k).isDGRightModule.restrictScalars
          (loopChainAugmentation Sph (spherePolePoint h) k).trivialAction)).homology q) :
    ((sphereCellCocycleTrivialActionHomologyEquiv h k q c).1 :
        (loopChain_isDGAlgebra Sph (spherePolePoint h) k).isDGRightModule.Cohomology) =
      IsDGRightModule.restrictScalarsCohomologyEquiv
        (loopChainAugmentation Sph (spherePolePoint h) k).trivialAction
        (loopChain_isDGAlgebra Sph (spherePolePoint h) k).isDGRightModule
        (cycleCellCocycleHomologyEquivOfOpSmulEqZero (sphereAttachingChain_mem h k)
          (cubicalChainDifferential_sphereAttachingChain h k) _
          ((loopChainAugmentation Sph (spherePolePoint h) k).op_smul_eq_zero_of_eq_zero
            (loopChainAugmentation_sphereAttachingChain h k)) q c).1 := by
  unfold sphereCellCocycleTrivialActionHomologyEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    coe_cycleCellCocycleTrivialActionHomologyEquiv_apply_fst]

/-- The `e₁`-component of `TauCeti.sphereCellCocycleTrivialActionHomologyEquiv` of a class is that
of `TauCeti.cycleCellCocycleHomologyEquivOfOpSmulEqZero` for the attaching cycle, read in
`H(Ω_b Sⁿ)`. -/
@[simp]
theorem coe_sphereCellCocycleTrivialActionHomologyEquiv_apply_snd (q : ℤ)
    (c : ((sphereCellCocycle h k).coefficientCochainComplex
        ((loopChain_isDGAlgebra Sph (spherePolePoint h) k).isDGRightModule.restrictScalars
          (loopChainAugmentation Sph (spherePolePoint h) k).trivialAction)).homology q) :
    ((sphereCellCocycleTrivialActionHomologyEquiv h k q c).2 :
        (loopChain_isDGAlgebra Sph (spherePolePoint h) k).isDGRightModule.Cohomology) =
      IsDGRightModule.restrictScalarsCohomologyEquiv
        (loopChainAugmentation Sph (spherePolePoint h) k).trivialAction
        (loopChain_isDGAlgebra Sph (spherePolePoint h) k).isDGRightModule
        (cycleCellCocycleHomologyEquivOfOpSmulEqZero (sphereAttachingChain_mem h k)
          (cubicalChainDifferential_sphereAttachingChain h k) _
          ((loopChainAugmentation Sph (spherePolePoint h) k).op_smul_eq_zero_of_eq_zero
            (loopChainAugmentation_sphereAttachingChain h k)) q c).2 := by
  unfold sphereCellCocycleTrivialActionHomologyEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.coe_ofEq_apply,
    coe_cycleCellCocycleTrivialActionHomologyEquiv_apply_snd]

/-- **With the trivial action the twisted homology of the sphere is not that of a point.** Over a
nontrivial ring `k`, the twisted homology of `Sⁿ`, `n = m + 2`, with coefficients in the chains on
its loops acted on trivially is nonzero in degree `-n`, where it contains `H_0(Ω_b Sⁿ)`, the
class of the constant loop. By contrast, the free module of `TauCeti.sphereCellCocycle` resolves
`k` (`TauCeti.exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`);
informally, it is the twisted complex for the action by multiplication, whose homology is that of
a point. -/
theorem nontrivial_sphereCellCocycle_trivialAction_homology [Nontrivial k] :
    Nontrivial (((sphereCellCocycle h k).coefficientCochainComplex
        ((loopChain_isDGAlgebra Sph (spherePolePoint h) k).isDGRightModule.restrictScalars
          (loopChainAugmentation Sph (spherePolePoint h) k).trivialAction)).homology
            (-((m : ℤ) + 2))) := by
  have : Nontrivial ((loopChain_isDGAlgebra Sph (spherePolePoint h) k).isDGRightModule
      |>.cohomologyGrading (-((m : ℤ) + 2) + ((m : ℤ) + 2))) := by
    rw [neg_add_cancel]
    exact (loopChainAugmentation Sph (spherePolePoint h) k).nontrivial_cohomologyGrading_zero
  exact (sphereCellCocycleTrivialActionHomologyEquiv h k _).toEquiv.nontrivial

end TauCeti
