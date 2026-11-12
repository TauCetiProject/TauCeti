/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.ChainRule.Higher
public import TauCeti.Analysis.Sobolev.Local.Morrey

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
* `g ∘ u ∈ W^{k+1,p}_loc(Ω)` for every globally `C^{k+1}` map `g`, with no continuity hypothesis on
  `u`, since `g ∘ u` and `g ∘ u*` agree almost everywhere on `Ω`;
* likewise `z ↦ g (z, u z) ∈ W^{k+1,p}_loc(Ω)` for globally `C^{k+1}` maps `g : ℂ × F → H`.

## Main declarations

* `TauCeti.MemWkpLoc.contDiffOn_comp_preciseRepresentative_succ`: `g ∘ u* ∈ W^{k+1,p}_loc(Ω)` for
  `g` `C^{k+1}` on an open set containing `u* '' Ω`.
* `TauCeti.MemWkpLoc.contDiff_comp_succ_of_two_lt`: `g ∘ u ∈ W^{k+1,p}_loc(Ω)` for globally
  `C^{k+1}` maps `g`.
* `TauCeti.MemWkpLoc.contDiff_comp_graph_succ_of_two_lt`: the domain-dependent form
  `z ↦ g (z, u z)`.
* `TauCeti.MemWkpLoc.contDiff_comp_update_succ_of_two_lt`: the Check of a smooth map changed at one
  point, at every order.

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

/-- **Composition of `W^{k+1,p}_loc` maps with `C^{k+1}` maps for `p > 2`.** If `2 < p < ∞`,
`u ∈ W^{k+1,p}_loc(Ω)` and `g` is globally `C^{k+1}`, then `g ∘ u` belongs to
`W^{k+1,p}_loc(Ω)`. Unlike `TauCeti.MemWkpLoc.contDiff_comp_succ`, no continuity hypothesis is
placed on `u`: the composition agrees almost everywhere on `Ω` with `g ∘ u*` for the continuous
precise representative `u*`. -/
theorem MemWkpLoc.contDiff_comp_succ_of_two_lt (hp : 2 < p) (hu : MemWkpLoc p Ω (k + 1) u)
    {g : F → G} (hg : ContDiff ℝ (k + 1) g) : MemWkpLoc p Ω (k + 1) (fun z => g (u z)) := by
  have hp' : (2 : ℝ≥0∞) < p := by exact_mod_cast hp
  exact (hu.contDiffOn_comp_preciseRepresentative_succ hp isOpen_univ hg.contDiffOn
    (mapsTo_univ _ _)).congr_ae
    ((hu.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hp'.le)).fun_comp g).symm

/-- **Composition with domain dependence at every order for `p > 2`.** If `2 < p < ∞`,
`u ∈ W^{k+1,p}_loc(Ω)` and `g : ℂ × F → H` is globally `C^{k+1}`, then `z ↦ g (z, u z)` belongs to
`W^{k+1,p}_loc(Ω)`, with no continuity hypothesis on `u`. -/
theorem MemWkpLoc.contDiff_comp_graph_succ_of_two_lt (hp : 2 < p) (hu : MemWkpLoc p Ω (k + 1) u)
    {g : ℂ × F → H} (hg : ContDiff ℝ (k + 1) g) : MemWkpLoc p Ω (k + 1) (fun z => g (z, u z)) := by
  have hp' : (2 : ℝ≥0∞) < p := by exact_mod_cast hp
  have hae := hu.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hp'.le)
  refine ((hu.congr_ae hae).contDiffOn_comp_graph_succ hp
    ((hu.of_le le_add_self).continuousOn_preciseRepresentative hp') isOpen_univ hg.contDiffOn
    fun _ _ => mem_univ _).congr_ae ?_
  filter_upwards [hae] with z hz
  rw [hz]

/-- **Check: composition without continuity at every order.** Let `v` be `C^{k+1}`, let `a ∈ Ω`
and let `c ≠ v a`. The map `u = Function.update v a c` is not continuous on `Ω`, so the continuous
chain rule `TauCeti.MemWkpLoc.contDiff_comp_succ` does not apply to it. For `2 < p < ∞` its
composition with any globally `C^{k+1}` map `g` is nevertheless in `W^{k+1,p}_loc(Ω)`, by
`TauCeti.MemWkpLoc.contDiff_comp_succ_of_two_lt`. -/
theorem MemWkpLoc.contDiff_comp_update_succ_of_two_lt (hp : 2 < p) {v : ℂ → F}
    (hv : ContDiff ℝ (k + 1) v) {a : ℂ} (ha : a ∈ Ω) {c : F} (hc : c ≠ v a) {g : F → G}
    (hg : ContDiff ℝ (k + 1) g) :
    ¬ ContinuousOn (Function.update v a c) Ω ∧
      MemWkpLoc p Ω (k + 1) (fun z => g (Function.update v a c z)) := by
  constructor
  · intro hcont
    have hat : ContinuousAt (Function.update v a c) a :=
      hcont.continuousAt (Ω.isOpen.mem_nhds ha)
    rw [continuousAt_update_same] at hat
    exact hc (tendsto_nhds_unique hat (hv.continuous.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds))
  · have hvW : MemWkpLoc p Ω (k + 1) v :=
      hv.contDiffOn.memWkpLoc (Ω := ⊤) (by simp only [Opens.coe_top, subset_univ])
    refine (hvW.congr_ae ?_).contDiff_comp_succ_of_two_lt hp hg
    filter_upwards [ae_restrict_of_ae (volume.ae_ne a)] with z hz
    rw [Function.update_of_ne hz]

end TauCeti
