/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Sobolev.Local.ChainRule.Supercritical

/-!
# Composition of local Sobolev maps at every order

Let `p > 2` and `k ≥ 0`. If `u` is continuous on an open planar domain `Ω` and belongs to
`W^{k+1,p}_loc(Ω)` with finite-dimensional values, and `g` is `C^{k+1}` on an open set `W`
containing `u '' Ω`, with finite-dimensional values, then `g ∘ u ∈ W^{k+1,p}_loc(Ω)`.

The domain-dependent form `z ↦ g(z, u z)` is the shape of the coefficients `J(z, u)` and
`η(z, u)` in the interior bootstrap for pseudoholomorphic curves: once `u` is known to be in
`W^{k+1,p}_loc` with `p > 2`, these coefficients are in `W^{k+1,p}_loc` too, which is what the
next step of the bootstrap needs.

These are the case `p > 2` of the composition theorems for `kp > 2` in
`TauCeti.Analysis.Sobolev.Local.ChainRule.Supercritical`, since `(k + 1) p > 2` when `p > 2`.

## Main declarations

* `TauCeti.MemWkpLoc.contDiffOn_comp_succ`: composition with maps that are `C^{k+1}` on an open
  neighbourhood of the image.
* `TauCeti.MemWkpLoc.contDiffOn_comp_of_one_le`: the same for an order `k ≥ 1`, an extended
  exponent `p < ∞` and a plain open set.
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

/-- `(k + 1) p > 2` for `p > 2`. -/
private theorem two_lt_succ_mul (hp : 2 < p) (k : ℕ) : 2 < ((k + 1 : ℕ) : ℝ≥0) * p :=
  hp.trans_le (le_mul_of_one_le_left zero_le (by exact_mod_cast Nat.le_add_left 1 k))

/-- **Composition of continuous local Sobolev maps with `C^{k+1}` maps.** For `p > 2`, if `u` is
continuous on `Ω` and belongs to `W^{k+1,p}_loc(Ω)`, and `g` is `C^{k+1}` on an open set `W`
containing `u '' Ω`, then `g ∘ u` belongs to `W^{k+1,p}_loc(Ω)`. This is the case `p > 2` of
`TauCeti.MemWkpLoc.contDiffOn_comp_of_two_lt_mul`. -/
theorem MemWkpLoc.contDiffOn_comp_succ (hp : 2 < p) {k : ℕ} {u : ℂ → F} {g : F → G}
    {W : Set F} (hu : MemWkpLoc p Ω (k + 1) u) (huc : ContinuousOn u Ω) (hW : IsOpen W)
    (hg : ContDiffOn ℝ (k + 1) g W) (huW : MapsTo u Ω W) :
    MemWkpLoc p Ω (k + 1) (fun z => g (u z)) :=
  hu.contDiffOn_comp_of_two_lt_mul (one_lt_two.trans hp) (two_lt_succ_mul hp k) huc hW
    (by exact_mod_cast hg) huW

/-- **Composition of continuous local Sobolev maps with `C^k` maps, `k ≥ 1`.** For `2 < p < ∞`, an
order `k ≥ 1` and an open set `U`, if `u` is continuous on `U` and belongs to `W^{k,p}_loc(U)`,
and `g` is `C^k` on an open set `W` containing `u '' U`, then `g ∘ u` belongs to
`W^{k,p}_loc(U)`. This is `TauCeti.MemWkpLoc.contDiffOn_comp_succ` for an extended exponent and a
plain open set. -/
theorem MemWkpLoc.contDiffOn_comp_of_one_le {p : ℝ≥0∞} (hp : 2 < p) (hp' : p ≠ ⊤) {k : ℕ}
    (hk : 1 ≤ k) {u : ℂ → F} {g : F → G} {U : Set ℂ} {W : Set F} (hU : IsOpen U)
    (hu : MemWkpLoc p U k u) (huc : ContinuousOn u U) (hW : IsOpen W)
    (hg : ContDiffOn ℝ k g W) (huW : MapsTo u U W) :
    MemWkpLoc p U k (g ∘ u) := by
  lift p to ℝ≥0 using hp'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  exact MemWkpLoc.contDiffOn_comp_succ (Ω := ⟨U, hU⟩) (u := u) (g := g) (by exact_mod_cast hp) hu
    huc hW (by exact_mod_cast hg) huW

/-- **Composition of continuous local Sobolev maps with globally `C^{k+1}` maps.** For `p > 2`,
if `u` is continuous on `Ω` and belongs to `W^{k+1,p}_loc(Ω)`, and `g` is `C^{k+1}`, then
`g ∘ u` belongs to `W^{k+1,p}_loc(Ω)`. -/
theorem MemWkpLoc.contDiff_comp_succ (hp : 2 < p) {k : ℕ} {u : ℂ → F} {g : F → G}
    (hu : MemWkpLoc p Ω (k + 1) u) (huc : ContinuousOn u Ω) (hg : ContDiff ℝ (k + 1) g) :
    MemWkpLoc p Ω (k + 1) (fun z => g (u z)) :=
  hu.contDiff_comp_of_two_lt_mul (one_lt_two.trans hp) (two_lt_succ_mul hp k) huc
    (by exact_mod_cast hg)

/-- **Composition with domain dependence at every order.** For `p > 2`, if `u` is continuous on
`Ω` and belongs to `W^{k+1,p}_loc(Ω)`, and `g : ℂ × F → H` is `C^{k+1}` on an open set containing
the graph of `u` over `Ω`, then `z ↦ g (z, u z)` belongs to `W^{k+1,p}_loc(Ω)`. -/
theorem MemWkpLoc.contDiffOn_comp_graph_succ (hp : 2 < p) {k : ℕ} {u : ℂ → F}
    {g : ℂ × F → H} {W : Set (ℂ × F)} (hu : MemWkpLoc p Ω (k + 1) u) (huc : ContinuousOn u Ω)
    (hW : IsOpen W) (hg : ContDiffOn ℝ (k + 1) g W) (huW : ∀ z ∈ Ω, (z, u z) ∈ W) :
    MemWkpLoc p Ω (k + 1) (fun z => g (z, u z)) :=
  hu.contDiffOn_comp_graph_of_two_lt_mul (one_lt_two.trans hp) (two_lt_succ_mul hp k) huc hW
    (by exact_mod_cast hg) huW

end TauCeti
