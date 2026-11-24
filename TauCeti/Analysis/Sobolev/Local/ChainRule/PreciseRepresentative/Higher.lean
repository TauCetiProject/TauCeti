/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.ChainRule.Higher
public import TauCeti.Analysis.Sobolev.Local.ChainRule.PreciseRepresentative

/-!
# Composition of `W^{k+1,p}_loc` maps for `p > 2` without a continuity hypothesis

Let `Ω ⊆ ℂ` be open, let `F`, `G` and `H` be finite-dimensional real normed spaces, let `2 < p < ∞`
and `k ≥ 0`. The chain rule of every order `TauCeti.MemWkpLoc.contDiffOn_comp_succ` assumes that
`u ∈ W^{k+1,p}_loc(Ω, F)` is continuous on `Ω`. As at order one
(`TauCeti.Analysis.Sobolev.Local.ChainRule.PreciseRepresentative`), this hypothesis is automatic
after changing `u` on a null set: by Morrey's embedding the precise representative
`u* = preciseRepresentative volume u` is continuous on `Ω` and agrees with `u` almost everywhere on
`Ω`. Hence:

* `g ∘ u* ∈ W^{k+1,p}_loc(Ω)` whenever `g` is `C^{k+1}` on an open set containing `u* '' Ω`;
* `g ∘ u ∈ W^{k+1,p}_loc(Ω)` for every such `g`, with no continuity hypothesis on `u`, since
  `g ∘ u` and `g ∘ u*` agree almost everywhere on `Ω`; in particular for every globally `C^{k+1}`
  map `g`;
* likewise `z ↦ g (z, u z) ∈ W^{k+1,p}_loc(Ω)` for maps `g : ℂ × F → H` that are `C^{k+1}` on an
  open set containing the graph of `u*` over `Ω`, in particular for globally `C^{k+1}` maps.

## Main declarations

* `TauCeti.MemWkpLoc.contDiffOn_comp_preciseRepresentative_succ`: `g ∘ u* ∈ W^{k+1,p}_loc(Ω)` for
  `g` `C^{k+1}` on an open set containing `u* '' Ω`.
* `TauCeti.MemWkpLoc.contDiffOn_comp_succ_of_two_lt`: `g ∘ u ∈ W^{k+1,p}_loc(Ω)` for the same `g`.
* `TauCeti.MemWkpLoc.contDiff_comp_succ_of_two_lt`: `g ∘ u ∈ W^{k+1,p}_loc(Ω)` for globally
  `C^{k+1}` maps `g`.
* `TauCeti.MemWkpLoc.contDiffOn_comp_graph_preciseRepresentative_succ`,
  `TauCeti.MemWkpLoc.contDiffOn_comp_graph_succ_of_two_lt` and
  `TauCeti.MemWkpLoc.contDiff_comp_graph_succ_of_two_lt`: the domain-dependent forms
  `z ↦ g (z, u* z)` and `z ↦ g (z, u z)`.
* `TauCeti.not_continuousOn_update_and_memWkpLoc_comp_update_succ_of_two_lt`: changing a
  `C^{k+1}` map at one point of `Ω` gives a map that is not continuous on `Ω`, but whose
  composition with any globally `C^{k+1}` map still lies in `W^{k+1,p}_loc(Ω)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (composition in local Sobolev spaces).
-/

public section

noncomputable section

open Set MeasureTheory TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {Ω : Opens ℂ} {p : ℝ≥0} {k : ℕ} {u : ℂ → F}

/-- **Composition with the continuous representative at every order.** Let `2 < p < ∞`, let
`u ∈ W^{k+1,p}_loc(Ω)` and let `u*` be its precise representative, which is continuous on `Ω` by
Morrey's embedding. If `g` is `C^{k+1}` on an open set `W` containing `u* '' Ω`, then `g ∘ u*`
belongs to `W^{k+1,p}_loc(Ω)`. No continuity hypothesis is placed on `u` itself. -/
theorem MemWkpLoc.contDiffOn_comp_preciseRepresentative_succ (hp : 2 < p)
    (hu : MemWkpLoc p Ω (k + 1) u) {g : F → G} {W : Set F} (hW : IsOpen W)
    (hg : ContDiffOn ℝ (k + 1) g W) (huW : MapsTo (preciseRepresentative volume u) Ω W) :
    MemWkpLoc p Ω (k + 1) (fun z => g (preciseRepresentative volume u z)) := by
  have hp' : (2 : ℝ≥0∞) < p := by exact_mod_cast hp
  have hae := hu.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hp'.le)
  exact (hu.congr_ae hae).contDiffOn_comp_succ hp
    ((hu.of_le le_add_self).continuousOn_preciseRepresentative hp') hW hg huW

/-- **Composition of `W^{k+1,p}_loc` maps with locally `C^{k+1}` maps for `p > 2`.** Let
`2 < p < ∞`, let `u ∈ W^{k+1,p}_loc(Ω)` and let `u*` be its precise representative. If `g` is
`C^{k+1}` on an open set `W` containing `u* '' Ω`, then `g ∘ u` belongs to `W^{k+1,p}_loc(Ω)`. No
continuity hypothesis is placed on `u`: the composition agrees almost everywhere on `Ω` with
`g ∘ u*`. -/
theorem MemWkpLoc.contDiffOn_comp_succ_of_two_lt (hp : 2 < p) (hu : MemWkpLoc p Ω (k + 1) u)
    {g : F → G} {W : Set F} (hW : IsOpen W) (hg : ContDiffOn ℝ (k + 1) g W)
    (huW : MapsTo (preciseRepresentative volume u) Ω W) :
    MemWkpLoc p Ω (k + 1) (fun z => g (u z)) := by
  have hp' : (2 : ℝ≥0∞) < p := by exact_mod_cast hp
  exact (hu.contDiffOn_comp_preciseRepresentative_succ hp hW hg huW).congr_ae
    ((hu.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hp'.le)).fun_comp g).symm

/-- **Composition of `W^{k+1,p}_loc` maps with `C^{k+1}` maps for `p > 2`.** If `2 < p < ∞`,
`u ∈ W^{k+1,p}_loc(Ω)` and `g` is globally `C^{k+1}`, then `g ∘ u` belongs to
`W^{k+1,p}_loc(Ω)`. Unlike `TauCeti.MemWkpLoc.contDiff_comp_succ`, no continuity hypothesis is
placed on `u`: the composition agrees almost everywhere on `Ω` with `g ∘ u*` for the continuous
precise representative `u*`. -/
theorem MemWkpLoc.contDiff_comp_succ_of_two_lt (hp : 2 < p) (hu : MemWkpLoc p Ω (k + 1) u)
    {g : F → G} (hg : ContDiff ℝ (k + 1) g) : MemWkpLoc p Ω (k + 1) (fun z => g (u z)) :=
  hu.contDiffOn_comp_succ_of_two_lt hp isOpen_univ hg.contDiffOn (mapsTo_univ _ _)

/-- **Composition with domain dependence and the continuous representative.** Let `2 < p < ∞`,
let `u ∈ W^{k+1,p}_loc(Ω)` and let `u*` be its precise representative. If `g : ℂ × F → H` is
`C^{k+1}` on an open set `W` containing `(z, u* z)` for every `z ∈ Ω`, then `z ↦ g (z, u* z)`
belongs to `W^{k+1,p}_loc(Ω)`. -/
theorem MemWkpLoc.contDiffOn_comp_graph_preciseRepresentative_succ (hp : 2 < p)
    (hu : MemWkpLoc p Ω (k + 1) u) {g : ℂ × F → H} {W : Set (ℂ × F)} (hW : IsOpen W)
    (hg : ContDiffOn ℝ (k + 1) g W) (huW : ∀ z ∈ Ω, (z, preciseRepresentative volume u z) ∈ W) :
    MemWkpLoc p Ω (k + 1) (fun z => g (z, preciseRepresentative volume u z)) := by
  have hp' : (2 : ℝ≥0∞) < p := by exact_mod_cast hp
  have hae := hu.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hp'.le)
  exact (hu.congr_ae hae).contDiffOn_comp_graph_succ hp
    ((hu.of_le le_add_self).continuousOn_preciseRepresentative hp') hW hg huW

/-- **Composition with domain dependence and locally `C^{k+1}` maps for `p > 2`.** Let
`2 < p < ∞`, let `u ∈ W^{k+1,p}_loc(Ω)` and let `u*` be its precise representative. If
`g : ℂ × F → H` is `C^{k+1}` on an open set `W` containing `(z, u* z)` for every `z ∈ Ω`, then
`z ↦ g (z, u z)` belongs to `W^{k+1,p}_loc(Ω)`, with no continuity hypothesis on `u`. -/
theorem MemWkpLoc.contDiffOn_comp_graph_succ_of_two_lt (hp : 2 < p)
    (hu : MemWkpLoc p Ω (k + 1) u) {g : ℂ × F → H} {W : Set (ℂ × F)} (hW : IsOpen W)
    (hg : ContDiffOn ℝ (k + 1) g W) (huW : ∀ z ∈ Ω, (z, preciseRepresentative volume u z) ∈ W) :
    MemWkpLoc p Ω (k + 1) (fun z => g (z, u z)) := by
  have hp' : (2 : ℝ≥0∞) < p := by exact_mod_cast hp
  refine (hu.contDiffOn_comp_graph_preciseRepresentative_succ hp hW hg huW).congr_ae ?_
  filter_upwards [hu.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hp'.le)] with z hz
  rw [hz]

/-- **Composition with domain dependence at every order for `p > 2`.** If `2 < p < ∞`,
`u ∈ W^{k+1,p}_loc(Ω)` and `g : ℂ × F → H` is globally `C^{k+1}`, then `z ↦ g (z, u z)` belongs to
`W^{k+1,p}_loc(Ω)`, with no continuity hypothesis on `u`. -/
theorem MemWkpLoc.contDiff_comp_graph_succ_of_two_lt (hp : 2 < p) (hu : MemWkpLoc p Ω (k + 1) u)
    {g : ℂ × F → H} (hg : ContDiff ℝ (k + 1) g) : MemWkpLoc p Ω (k + 1) (fun z => g (z, u z)) :=
  hu.contDiffOn_comp_graph_succ_of_two_lt hp isOpen_univ hg.contDiffOn fun _ _ => mem_univ _

/-- **Composition after changing a `C^{k+1}` map at one point.** Let `v` be `C^{k+1}`, let
`a ∈ Ω` and let `c ≠ v a`. The map `u = Function.update v a c` is not continuous on `Ω`, so the
continuous chain rule `TauCeti.MemWkpLoc.contDiff_comp_succ` does not apply to it. For
`2 < p < ∞` its composition with any globally `C^{k+1}` map `g` is nevertheless in
`W^{k+1,p}_loc(Ω)`, by `TauCeti.MemWkpLoc.contDiff_comp_succ_of_two_lt`. -/
theorem not_continuousOn_update_and_memWkpLoc_comp_update_succ_of_two_lt (hp : 2 < p)
    {v : ℂ → F} (hv : ContDiff ℝ (k + 1) v) {a : ℂ} (ha : a ∈ Ω) {c : F} (hc : c ≠ v a)
    {g : F → G} (hg : ContDiff ℝ (k + 1) g) :
    ¬ ContinuousOn (Function.update v a c) Ω ∧
      MemWkpLoc p Ω (k + 1) (fun z => g (Function.update v a c z)) := by
  have hk : ((1 : ℕ) : WithTop ℕ∞) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 k
  refine ⟨(MemWkpLoc.contDiff_comp_update_of_two_lt (p := p) (by exact_mod_cast hp)
    (hv.of_le hk) ha hc (hg.of_le hk)).1, ?_⟩
  have hvW : MemWkpLoc p Ω (k + 1) v :=
    hv.contDiffOn.memWkpLoc (Ω := ⊤) (by simp only [Opens.coe_top, subset_univ])
  refine (hvW.congr_ae ?_).contDiff_comp_succ_of_two_lt hp hg
  filter_upwards [ae_restrict_of_ae (volume.ae_ne a)] with z hz
  rw [Function.update_of_ne hz]

end TauCeti
