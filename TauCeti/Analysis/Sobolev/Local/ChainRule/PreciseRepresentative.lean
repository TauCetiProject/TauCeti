/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.ChainRule
public import TauCeti.Analysis.Sobolev.Local.Morrey
import TauCeti.Analysis.Sobolev.WeakDeriv.ChainRule

/-!
# Composition of `W^{1,p}_loc` maps for `p > 2` without a continuity hypothesis

Let `Ω ⊆ ℂ` be open, let `F` be a finite-dimensional real normed space and let `2 < p ≤ ∞`. The
chain rule `TauCeti.MemWkpLoc.contDiffOn_comp` assumes that `u ∈ W^{1,p}_loc(Ω, F)` is continuous
on `Ω`. For `p > 2` this hypothesis is automatic after changing `u` on a null set: by Morrey's
embedding the precise representative `u* = preciseRepresentative volume u` is continuous on `Ω`
(`TauCeti.MemWkpLoc.continuousOn_preciseRepresentative`) and agrees with `u` almost everywhere
on `Ω` (`TauCeti.MemLpLoc.ae_eq_preciseRepresentative`). Hence:

* `g ∘ u* ∈ W^{1,p}_loc(Ω)` whenever `g` is `C¹` on an open set containing `u* '' Ω`;
* `g ∘ u ∈ W^{1,p}_loc(Ω)` for every globally `C¹` map `g`, with no continuity hypothesis on `u`,
  since `g ∘ u` and `g ∘ u*` agree almost everywhere on `Ω`. Its weak derivative is
  `z ↦ Dg(u* z) ∘ Du z`;
* likewise `z ↦ g (z, u z) ∈ W^{1,p}_loc(Ω)` for globally `C¹` maps `g : ℂ × F → H`.

For a map `g` that is `C¹` only on an open set `W`, the hypothesis is placed on the image of `u*`,
not on that of `u`: the values of `u` on a null set are irrelevant to `W^{1,p}_loc`, while those of
`u*` are determined by `u` up to null sets.

The bound `p > 2` cannot be dropped: for `p = 4/3` the map `u = |z|^{-2/5}` lies in `W^{1,4/3}`
near `0`, but `u²` does not, since its derivative has size `|z|^{-9/5}` and `(9/5)(4/3) > 2`. The
Check `TauCeti.MemWkpLoc.contDiff_comp_update_of_two_lt` treats a smooth map changed at one point:
the continuous chain rule does not apply to it, while the statements here do.

## Main declarations

* `TauCeti.MemWkpLoc.contDiffOn_comp_preciseRepresentative`: `g ∘ u* ∈ W^{1,p}_loc(Ω)` for `g`
  `C¹` on an open set containing `u* '' Ω`.
* `TauCeti.MemWkpLoc.contDiff_comp_of_two_lt`: `g ∘ u ∈ W^{1,p}_loc(Ω)` for globally `C¹` `g`.
* `TauCeti.HasWeakFDerivOn.contDiff_comp_of_two_lt`: its weak derivative `Dg(u*) ∘ Du`.
* `TauCeti.MemWkpLoc.contDiff_comp_graph_of_two_lt`: the domain-dependent form `z ↦ g (z, u z)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (composition in local Sobolev spaces).
-/

public section

noncomputable section

open Set MeasureTheory TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

section MemWkpLoc

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] [NormedAddCommGroup H]
  [NormedSpace ℝ H] {p : ℝ≥0∞} {Ω : Opens ℂ} {u : ℂ → F}

/-- **Composition with the continuous representative.** Let `2 < p`, let `u ∈ W^{1,p}_loc(Ω)` and
let `u*` be its precise representative, which is continuous on `Ω` by Morrey's embedding. If `g` is
`C¹` on an open set `W` containing `u* '' Ω`, then `g ∘ u*` belongs to `W^{1,p}_loc(Ω)`. No
continuity hypothesis is placed on `u` itself. -/
theorem MemWkpLoc.contDiffOn_comp_preciseRepresentative (hp : 2 < p) (hu : MemWkpLoc p Ω 1 u)
    {g : F → G} {W : Set F} (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W)
    (huW : MapsTo (preciseRepresentative volume u) Ω W) :
    MemWkpLoc p Ω 1 (fun z => g (preciseRepresentative volume u z)) :=
  (hu.congr_ae (hu.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hp.le))).contDiffOn_comp
    (hu.continuousOn_preciseRepresentative hp) hW hg huW

/-- **The weak chain rule with the continuous representative.** Let `2 < p`, let
`u ∈ W^{1,p}_loc(Ω)` have weak derivative `Du` on `Ω` and let `u*` be its precise representative.
If `g` is `C¹` on an open set `W` containing `u* '' Ω`, then `g ∘ u*` has weak derivative
`z ↦ Dg(u* z) ∘ Du z` on `Ω`. -/
theorem HasWeakFDerivOn.contDiffOn_comp_preciseRepresentative (hp : 2 < p)
    (hu : MemWkpLoc p Ω 1 u) {Du : ℂ → ℂ →L[ℝ] F} (hDu : HasWeakFDerivOn volume Ω u Du)
    {g : F → G} {W : Set F} (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W)
    (huW : MapsTo (preciseRepresentative volume u) Ω W) :
    HasWeakFDerivOn volume Ω (fun z => g (preciseRepresentative volume u z))
      fun z => (fderiv ℝ g (preciseRepresentative volume u z)).comp (Du z) :=
  (hDu.congr_ae (hu.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hp.le))).contDiffOn_comp
    (hu.continuousOn_preciseRepresentative hp) hW hg huW

/-- **Composition of `W^{1,p}_loc` maps with `C¹` maps for `p > 2`.** If `2 < p`,
`u ∈ W^{1,p}_loc(Ω)` and `g` is globally `C¹`, then `g ∘ u` belongs to `W^{1,p}_loc(Ω)`. Unlike
`TauCeti.MemWkpLoc.contDiff_comp`, no continuity hypothesis is placed on `u`: the composition
agrees almost everywhere on `Ω` with `g ∘ u*` for the continuous precise representative `u*`. -/
theorem MemWkpLoc.contDiff_comp_of_two_lt (hp : 2 < p) (hu : MemWkpLoc p Ω 1 u) {g : F → G}
    (hg : ContDiff ℝ 1 g) : MemWkpLoc p Ω 1 (fun z => g (u z)) :=
  (hu.contDiffOn_comp_preciseRepresentative hp isOpen_univ hg.contDiffOn (mapsTo_univ _ _)).congr_ae
    ((hu.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hp.le)).fun_comp g).symm

/-- **The weak chain rule for `W^{1,p}_loc` maps and `C¹` maps for `p > 2`.** If `2 < p`,
`u ∈ W^{1,p}_loc(Ω)` has weak derivative `Du` on `Ω` and `g` is globally `C¹`, then `g ∘ u` has
weak derivative `z ↦ Dg(u* z) ∘ Du z` on `Ω`, where `u*` is the continuous precise representative of
`u`. No continuity hypothesis is placed on `u`. -/
theorem HasWeakFDerivOn.contDiff_comp_of_two_lt (hp : 2 < p) (hu : MemWkpLoc p Ω 1 u)
    {Du : ℂ → ℂ →L[ℝ] F} (hDu : HasWeakFDerivOn volume Ω u Du) {g : F → G}
    (hg : ContDiff ℝ 1 g) :
    HasWeakFDerivOn volume Ω (fun z => g (u z))
      fun z => (fderiv ℝ g (preciseRepresentative volume u z)).comp (Du z) :=
  (hDu.contDiffOn_comp_preciseRepresentative hp hu isOpen_univ hg.contDiffOn
    (mapsTo_univ _ _)).congr_ae
    ((hu.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hp.le)).fun_comp g).symm

variable [CompleteSpace H] in
/-- **Composition with domain dependence for `p > 2`.** If `2 < p`, `u ∈ W^{1,p}_loc(Ω)` and
`g : ℂ × F → H` is globally `C¹`, then `z ↦ g (z, u z)` belongs to `W^{1,p}_loc(Ω)`, with no
continuity hypothesis on `u`. -/
theorem MemWkpLoc.contDiff_comp_graph_of_two_lt (hp : 2 < p) (hu : MemWkpLoc p Ω 1 u)
    {g : ℂ × F → H} (hg : ContDiff ℝ 1 g) : MemWkpLoc p Ω 1 (fun z => g (z, u z)) := by
  have hae := hu.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hp.le)
  refine ((hu.congr_ae hae).contDiffOn_comp_graph (hu.continuousOn_preciseRepresentative hp)
    isOpen_univ hg.contDiffOn fun _ _ => mem_univ _).congr_ae ?_
  filter_upwards [hae] with z hz
  rw [hz]

/-! ### Check: a smooth map changed at one point -/

/-- **Check: composition without continuity.** Let `v` be `C¹`, let `a ∈ Ω` and let `c ≠ v a`.
The map `u = Function.update v a c` is not continuous on `Ω`, so the continuous chain rule
`TauCeti.MemWkpLoc.contDiff_comp` does not apply to it. For `p > 2` its composition with any
globally `C¹` map `g` is nevertheless in `W^{1,p}_loc(Ω)`, by
`TauCeti.MemWkpLoc.contDiff_comp_of_two_lt`. -/
theorem MemWkpLoc.contDiff_comp_update_of_two_lt (hp : 2 < p) {v : ℂ → F}
    (hv : ContDiff ℝ 1 v) {a : ℂ} (ha : a ∈ Ω) {c : F} (hc : c ≠ v a) {g : F → G}
    (hg : ContDiff ℝ 1 g) :
    ¬ ContinuousOn (Function.update v a c) Ω ∧
      MemWkpLoc p Ω 1 (fun z => g (Function.update v a c z)) := by
  constructor
  · intro hcont
    have hat : ContinuousAt (Function.update v a c) a :=
      hcont.continuousAt (Ω.isOpen.mem_nhds ha)
    rw [continuousAt_update_same] at hat
    exact hc (tendsto_nhds_unique hat (hv.continuous.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds))
  · have hvW : MemWkpLoc p Ω 1 v :=
      hv.contDiffOn.memWkpLoc (Ω := ⊤) (by simp only [Opens.coe_top, subset_univ])
    refine (hvW.congr_ae ?_).contDiff_comp_of_two_lt hp hg
    filter_upwards [ae_restrict_of_ae (volume.ae_ne a)] with z hz
    rw [Function.update_of_ne hz]

end MemWkpLoc

end TauCeti
