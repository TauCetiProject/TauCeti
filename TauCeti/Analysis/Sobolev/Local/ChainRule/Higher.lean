/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.ChainRule
public import TauCeti.Analysis.Sobolev.Local.Multiplication.Higher
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.WeakDeriv.ChainRule

/-!
# Composition of local Sobolev maps at every order

Let `p > 2` and `k ≥ 0`. If `u` is continuous on an open planar domain `Ω` and belongs to
`W^{k+1,p}_loc(Ω)` with finite-dimensional values, and `g` is `C^{k+1}` on an open set `W`
containing `u '' Ω`, with finite-dimensional values, then `g ∘ u ∈ W^{k+1,p}_loc(Ω)`.

The domain-dependent form `z ↦ g(z, u z)` is the shape of the coefficients `J(z, u)` and
`η(z, u)` in the interior bootstrap for pseudoholomorphic curves: once `u` is known to be in
`W^{k+1,p}_loc` with `p > 2`, these coefficients are in `W^{k+1,p}_loc` too, which is what the
next step of the bootstrap needs.

## Main declarations

* `TauCeti.MemWkpLoc.contDiffOn_comp_succ`: composition with maps that are `C^{k+1}` on an open
  neighbourhood of the image.
* `TauCeti.MemWkpLoc.contDiff_comp_succ`: composition with globally `C^{k+1}` maps.
* `TauCeti.MemWkpLoc.contDiffOn_comp_graph_succ`: the domain-dependent composition
  `z ↦ g(z, u z)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (composition in local Sobolev spaces).
-/

public noncomputable section

open Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

universe uF uG uH

variable {F : Type uF} {G : Type uG} {H : Type uH}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {Ω : Opens ℂ} {p : ℝ≥0}

/-- `TauCeti.MemWkpLoc.contDiffOn_comp_succ` for values in a universe at least that of `F`. -/
private theorem contDiffOn_comp_succ_aux {G : Type (max uF uG)}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (hp : 2 < p) {k : ℕ} {u : ℂ → F} {g : F → G}
    {W : Set F} (hu : MemWkpLoc p Ω (k + 1) u) (huc : ContinuousOn u Ω) (hW : IsOpen W)
    (hg : ContDiffOn ℝ (k + 1) g W) (huW : MapsTo u Ω W) :
    MemWkpLoc p Ω (k + 1) (fun z => g (u z)) := by
  -- Induction on `k` from the order-one statement `TauCeti.MemWkpLoc.contDiffOn_comp`. The weak
  -- derivative of `g ∘ u` is `z ↦ Dg(u z) ∘L Du z`; the induction hypothesis puts `Dg ∘ u` in
  -- `W^{k,p}_loc`, and the product theorem `TauCeti.MemWkpLoc.compL_succ` (which needs `p > 2`)
  -- handles the composition. The step passes from `g` to `fderiv ℝ g`, with values in
  -- `F →L[ℝ] G`, which lies in the universe of `F` and `G` together; restricting `G` to a
  -- universe at least that of `F` makes the statement closed under that step.
  induction k generalizing G g with
  | zero => exact hu.contDiffOn_comp huc hW (by simpa using hg) huW
  | succ k ih =>
    have hp1 : 1 < p := one_lt_two.trans hp
    obtain ⟨Du, hDu, hDuk⟩ := hu.exists_weakFDeriv_of_isOpen
    have hg1 : ContDiffOn ℝ 1 g W := hg.of_le (by exact_mod_cast Nat.le_add_left 1 (k + 1))
    have hD := hDu.contDiffOn_comp huc hW hg1 huW
    -- The derivative `Dg` is `C^{k+1}` on `W`, so `Dg ∘ u` is in `W^{k+1,p}_loc` by induction.
    have hDg : ContDiffOn ℝ (k + 1) (fderiv ℝ g) W :=
      hg.fderiv_of_isOpen hW (by push_cast; rfl)
    have hDgu := ih hu.of_succ hDg
    refine memWkpLoc_succ_iff_of_isOpen.2
      ⟨(hg.continuousOn.comp huc huW).memLpLoc, _, hD, ?_⟩
    exact hDgu.compL_succ hp hp1 le_rfl hDuk

/-- **Composition of continuous local Sobolev maps with `C^{k+1}` maps.** For `p > 2`, if `u` is
continuous on `Ω` and belongs to `W^{k+1,p}_loc(Ω)`, and `g` is `C^{k+1}` on an open set `W`
containing `u '' Ω`, then `g ∘ u` belongs to `W^{k+1,p}_loc(Ω)`. -/
theorem MemWkpLoc.contDiffOn_comp_succ (hp : 2 < p) {k : ℕ} {u : ℂ → F} {g : F → G}
    {W : Set F} (hu : MemWkpLoc p Ω (k + 1) u) (huc : ContinuousOn u Ω) (hW : IsOpen W)
    (hg : ContDiffOn ℝ (k + 1) g W) (huW : MapsTo u Ω W) :
    MemWkpLoc p Ω (k + 1) (fun z => g (u z)) := by
  -- Move the values to `ULift G`, which lies in a universe at least that of `F`.
  let e : G ≃L[ℝ] ULift.{uF} G := (LinearIsometryEquiv.ulift ℝ G).symm.toContinuousLinearEquiv
  have hg' : ContDiffOn ℝ (k + 1) (fun x => e (g x)) W := e.contDiff.comp_contDiffOn hg
  exact e.comp_memWkpLoc_iff.1
    (contDiffOn_comp_succ_aux (g := fun x => e (g x)) hp hu huc hW hg' huW)

/-- **Composition of continuous local Sobolev maps with globally `C^{k+1}` maps.** For `p > 2`,
if `u` is continuous on `Ω` and belongs to `W^{k+1,p}_loc(Ω)`, and `g` is `C^{k+1}`, then
`g ∘ u` belongs to `W^{k+1,p}_loc(Ω)`. -/
theorem MemWkpLoc.contDiff_comp_succ (hp : 2 < p) {k : ℕ} {u : ℂ → F} {g : F → G}
    (hu : MemWkpLoc p Ω (k + 1) u) (huc : ContinuousOn u Ω) (hg : ContDiff ℝ (k + 1) g) :
    MemWkpLoc p Ω (k + 1) (fun z => g (u z)) :=
  hu.contDiffOn_comp_succ hp huc isOpen_univ hg.contDiffOn (mapsTo_univ _ _)

/-- **Composition with domain dependence at every order.** For `p > 2`, if `u` is continuous on
`Ω` and belongs to `W^{k+1,p}_loc(Ω)`, and `g : ℂ × F → H` is `C^{k+1}` on an open set containing
the graph of `u` over `Ω`, then `z ↦ g (z, u z)` belongs to `W^{k+1,p}_loc(Ω)`. -/
theorem MemWkpLoc.contDiffOn_comp_graph_succ (hp : 2 < p) {k : ℕ} {u : ℂ → F}
    {g : ℂ × F → H} {W : Set (ℂ × F)} (hu : MemWkpLoc p Ω (k + 1) u) (huc : ContinuousOn u Ω)
    (hW : IsOpen W) (hg : ContDiffOn ℝ (k + 1) g W) (huW : ∀ z ∈ Ω, (z, u z) ∈ W) :
    MemWkpLoc p Ω (k + 1) (fun z => g (z, u z)) := by
  have hid : MemWkpLoc p Ω (k + 1) (fun z : ℂ => z) :=
    contDiff_id.contDiffOn.memWkpLoc (Ω := ⊤) (by simp only [Opens.coe_top, subset_univ])
  exact (hid.prodMk hu).contDiffOn_comp_succ hp (continuousOn_id.prodMk huc) hW hg huW

end TauCeti
