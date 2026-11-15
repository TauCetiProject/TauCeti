/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Sobolev.WeakDeriv.ChainRule
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# The chain rule for continuous local Sobolev maps

A continuous member `u` of `W^{1,p}_loc` on a planar set `U` composes with a map `g` that is `C¹`
on an open set containing `u '' U` to give a member of `W^{1,p}_loc(U)`. The weak derivative of
`g ∘ u` on `interior U` is `z ↦ Dg(u z) ∘ Du z`, by the weak chain rule
`TauCeti.HasWeakFDerivOn.contDiffOn_comp`. On a compact set `K` it obeys
`‖D(g ∘ u)‖_{Lᵖ(K)} ≤ (sup_{u(K)} ‖Dg‖) ‖Du‖_{Lᵖ(K)}`, by Mathlib's
`eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul` with `ContinuousLinearMap.opNNNorm_comp_le`; its
`Lᵖ` membership is `MeasureTheory.MemLp.clm_comp_of_continuousOn`. The domain-dependent form
`z ↦ g(z, u z)` follows by composing with the graph map `z ↦ (z, u z)`.

Continuity of `u` is a hypothesis here. It is automatic for `p > 2` after changing `u` on a null
set, by Morrey's embedding. Without continuity, and below that exponent, the statement fails: for
`p = 4/3` the function `u = |z|^{-2/5}` lies in `W^{1,4/3}` near `0`, but `u²` does not, since its
derivative has size `|z|^{-9/5}` and `(9/5)(4/3) > 2`.

## Main declarations

* `TauCeti.MemWkpLoc.contDiffOn_comp`: continuous `W^{1,p}_loc` maps compose with `C¹` maps.
* `TauCeti.MemWkpLoc.contDiff_comp`: the same for globally `C¹` maps.
* `TauCeti.MemWkpLoc.contDiffOn_comp_graph`: the domain-dependent composition `z ↦ g(z, u z)`.
* `TauCeti.MemWkpLoc.ring_inverse`: pointwise inverses of continuous invertible maps into a
  complete normed algebra.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (composition in local Sobolev spaces).
-/

public section

noncomputable section

namespace TauCeti

open Set TopologicalSpace
open scoped ENNReal

section MemWkpLoc

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H] {p : ℝ≥0∞} {U : Set ℂ} {k : ℕ}

variable [CompleteSpace G]

/-- **Composition of continuous `W^{1,p}_loc` maps with `C¹` maps.** If `u` is continuous on `U`
and belongs to `W^{1,p}_loc(U)`, and `g` is `C¹` on an open set containing `u '' U`, then
`g ∘ u` belongs to `W^{1,p}_loc(U)`. Its weak derivative on `interior U` is given by
`TauCeti.HasWeakFDerivOn.contDiffOn_comp`, and its `Lᵖ` membership on compact sets is
`MeasureTheory.MemLp.clm_comp_of_continuousOn` for the continuous factor `Dg ∘ u`. -/
theorem MemWkpLoc.contDiffOn_comp {u : ℂ → F} {g : F → G} {W : Set F}
    (hu : MemWkpLoc p U 1 u) (huc : ContinuousOn u U) (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W)
    (huW : MapsTo u U W) : MemWkpLoc p U 1 (fun z => g (u z)) := by
  obtain ⟨Du, hDu, hDup⟩ := hu.exists_weakFDeriv
  have hDgc : ContinuousOn (fderiv ℝ g) W := hg.continuousOn_fderiv_of_isOpen hW le_rfl
  refine memWkpLoc_succ_iff.2 ⟨(hg.continuousOn.comp huc huW).memLpLoc, _,
    hDu.contDiffOn_comp (huc.mono interior_subset) hW hg (huW.mono_left interior_subset), ?_⟩
  rw [memWkpLoc_zero_iff, memLpLoc_iff] at hDup ⊢
  intro K hKU hK
  have hgu : ContinuousOn (fun x => fderiv ℝ g (u x)) K :=
    hDgc.comp (huc.mono hKU) (huW.mono_left hKU)
  exact (hDup K hKU hK).clm_comp_of_continuousOn hgu hK hK.measurableSet subset_rfl

/-- **Composition of continuous `W^{1,p}_loc` maps with globally `C¹` maps.** -/
theorem MemWkpLoc.contDiff_comp {u : ℂ → F} {g : F → G} (hu : MemWkpLoc p U 1 u)
    (huc : ContinuousOn u U) (hg : ContDiff ℝ 1 g) : MemWkpLoc p U 1 (fun z => g (u z)) :=
  hu.contDiffOn_comp huc isOpen_univ hg.contDiffOn (mapsTo_univ _ _)

variable [CompleteSpace H] in
/-- **Composition with domain dependence.** If `u` is continuous on `U` and belongs to
`W^{1,p}_loc(U)`, and `g` is `C¹` on an open set containing the graph of `u` over `U`, then
`z ↦ g (z, u z)` belongs to `W^{1,p}_loc(U)`. Its weak derivative on `interior U` is given by
`TauCeti.HasWeakFDerivOn.contDiffOn_comp_graph`. -/
theorem MemWkpLoc.contDiffOn_comp_graph {u : ℂ → F} {g : ℂ × F → H} {W : Set (ℂ × F)}
    (hu : MemWkpLoc p U 1 u) (huc : ContinuousOn u U) (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W)
    (huW : ∀ z ∈ U, (z, u z) ∈ W) : MemWkpLoc p U 1 (fun z => g (z, u z)) := by
  have : CompleteSpace F := hu.completeSpace
  have hid : MemWkpLoc p U 1 (fun z : ℂ => z) :=
    contDiff_id.contDiffOn.memWkpLoc (Ω := ⊤) (by simp only [Opens.coe_top, subset_univ])
  exact (hid.prodMk hu).contDiffOn_comp (continuousOn_id.prodMk huc) hW hg huW

omit [CompleteSpace G] in
/-- **Pointwise inverses.** If `u` is continuous on `U`, belongs to `W^{1,p}_loc(U)` and takes
invertible values in a complete normed algebra on `U`, then `z ↦ (u z)⁻¹` belongs to
`W^{1,p}_loc(U)`, since inversion is smooth on the open set of units. -/
theorem MemWkpLoc.ring_inverse {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
    {u : ℂ → R} (hu : MemWkpLoc p U 1 u) (huc : ContinuousOn u U)
    (hunit : ∀ z ∈ U, IsUnit (u z)) : MemWkpLoc p U 1 (fun z => Ring.inverse (u z)) :=
  hu.contDiffOn_comp huc Units.isOpen
    (fun _ ⟨x, hx⟩ => hx ▸ (contDiffAt_ringInverse ℝ x).contDiffWithinAt) hunit

end MemWkpLoc

end TauCeti
