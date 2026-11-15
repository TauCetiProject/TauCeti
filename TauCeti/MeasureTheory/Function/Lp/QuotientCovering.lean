/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Mathlib.Topology.Covering.Quotient
public import TauCeti.MeasureTheory.Function.Lp.Precomposition
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Basic
import TauCeti.MeasureTheory.Group.CountableAction

/-!
# `Lᵖ` functions on the base of a quotient covering

Let a group `G` act on a space `X`, and let `q : X → Y` be a quotient covering map for this action
(`IsQuotientCoveringMap q G`): the fibres of `q` are the `G`-orbits and every point has a
neighbourhood disjoint from its nontrivial translates, as for the orbit projection of a free action
of a finite group on a Hausdorff space. Suppose that `q` pushes a `G`-invariant measure `μ` on `X`
forward to a multiple `C • ν`, `0 < C < ∞`, of a measure `ν` on `Y`. Then the normalized pullback

`J f = C ^ (-1/p) • (f ∘ q)`

is a linear isometry `Lᵖ(ν) → Lᵖ(μ)` (`MeasureTheory.Lp.compOfMapEqSmulₗᵢ`), and this file shows
that its range is exactly the space of `G`-invariant elements of `Lᵖ(μ)`, for the action of `G` on
`Lᵖ(μ)` by precomposition through `DomMulAct`
(`IsQuotientCoveringMap.mem_range_compOfMapEqSmulₗᵢ_iff`). For `p = 2`, `J` is therefore a unitary
map from `L²(ν)` onto the invariant subspace `L²(μ)^G`, by `LinearIsometry.equivRange`.

The typical instance is a closed Riemannian manifold `X` with a free action of a finite group `G`
of isometries, and its quotient `Y = X / G` with the descended metric. The orbit projection is a
local isometry, so the Riemannian volumes satisfy `q_* vol_X = |G| • vol_Y`
(`IsQuotientCoveringMap.map_riemannianVolume`), and `J = |G| ^ (-1/2) q^*` identifies `L²(Y)`
with the `G`-invariant part of `L²(X)`. Comparing the Laplacians of the quotients `X / H` by
different subgroups `H ≤ G` through these unitaries is Bérard's transplantation proof of Sunada's
isospectrality theorem.

Pullbacks are invariant since `q (g • x) = q x`. Conversely, an invariant element `u` has an
invariant strongly measurable representative
(`MeasureTheory.AEStronglyMeasurable.exists_stronglyMeasurable_forall_smul_eq`), which is `v ∘ q`
for a function `v` on `Y` because the fibres of `q` are orbits. The function `v` is strongly
measurable because `q` is a surjective local homeomorphism out of a Lindelöf space
(`IsLocalHomeomorph.stronglyMeasurable_comp_iff`), and it lies in `Lᵖ(ν)` since
`‖v ∘ q‖_{Lᵖ(μ)} = C ^ (1/p) ‖v‖_{Lᵖ(ν)}`.

## Main results

* `IsQuotientCoveringMap.mem_range_compOfMapEqSmulₗᵢ_iff`: the range of the normalized pullback
  consists of the `G`-invariant elements of `Lᵖ(μ)`.

## References

* P. Bérard, *Transplantation et isospectralité I*, Séminaire de Théorie spectrale et
  géométrie **9** (1990–1991), §II, Lemma 16, p. 159.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace IsQuotientCoveringMap

variable {X Y G E : Type*} (𝕜 : Type*) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [LindelofSpace X] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Group G]
  [Countable G] [MulAction G X] [MeasurableConstSMul G X] {q : X → Y} {μ : Measure X}
  [SMulInvariantMeasure G X μ] {ν : Measure Y} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {C : ℝ≥0∞}

/-- **The normalized pullback along a quotient covering is onto the invariant elements.** If a
quotient covering map `q : X → Y` for a group `G` pushes a `G`-invariant measure `μ` forward to
`C • ν` with `0 < C < ∞`, then an element of `Lᵖ(μ)` is of the form `C ^ (-1/p) • (f ∘ q)` with
`f ∈ Lᵖ(ν)` exactly when it is invariant under the action of `G` by precomposition. -/
theorem mem_range_compOfMapEqSmulₗᵢ_iff (hq : IsQuotientCoveringMap q G) (hC : C ≠ ∞)
    (hC₀ : C ≠ 0) (hmap : μ.map q = C • ν) (u : Lp E p μ) :
    u ∈ LinearMap.range
        (Lp.compOfMapEqSmulₗᵢ 𝕜 hq.continuous.measurable hC hC₀ hmap).toLinearMap ↔
      ∀ g : G, DomMulAct.mk g • u = u := by
  have hq_meas : Measurable q := hq.continuous.measurable
  set J := Lp.compOfMapEqSmulₗᵢ (E := E) (p := p) 𝕜 hq_meas hC hC₀ hmap
  constructor
  · rintro ⟨f, rfl⟩ g
    apply Lp.ext
    filter_upwards [DomMulAct.smul_Lp_ae_eq (DomMulAct.mk g) (J f),
      (measurePreserving_smul g μ).quasiMeasurePreserving.ae
        (Lp.coeFn_compOfMapEqSmulₗᵢ (𝕜 := 𝕜) hq_meas hC hC₀ hmap f),
      Lp.coeFn_compOfMapEqSmulₗᵢ (𝕜 := 𝕜) hq_meas hC hC₀ hmap f] with x h₁ h₂ h₃
    rw [LinearIsometry.coe_toLinearMap, h₁, Equiv.symm_apply_apply, h₂, hq.map_smul, h₃]
  · intro hinv
    have hae (g : G) : (fun x ↦ u (g • x)) =ᵐ[μ] u := by
      simpa [hinv g] using (DomMulAct.smul_Lp_ae_eq (DomMulAct.mk g) u).symm
    -- An invariant representative `u'` of `u` descends to a function `v` on `Y`.
    obtain ⟨u', hu'm, hu'inv, hu'u⟩ :=
      (Lp.aestronglyMeasurable u).exists_stronglyMeasurable_forall_smul_eq hae
    set v : Y → E := u' ∘ Function.surjInv hq.surjective with hv_def
    have hv : v ∘ q = u' := funext fun x ↦ by
      obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.1 (Function.surjInv_eq hq.surjective (q x))
      rw [Function.comp_apply, hv_def, Function.comp_apply, ← hg, hu'inv]
    have hvm : StronglyMeasurable v :=
      (hq.isLocalHomeomorph.stronglyMeasurable_comp_iff hq.surjective).1 (hv ▸ hu'm)
    have hvLp : MemLp v p ν := by
      have h : MemLp v p (C • ν) := by
        rw [← hmap, memLp_map_measure_iff hvm.aestronglyMeasurable hq_meas.aemeasurable, hv]
        exact (Lp.memLp u).ae_eq hu'u.symm
      refine h.of_measure_le_smul (c := C⁻¹) (ENNReal.inv_ne_top.2 hC₀) ?_
      rw [smul_smul, ENNReal.inv_mul_cancel hC₀ hC, one_smul]
    -- `u` is the normalized pullback of `C ^ (1/p) • v`.
    set c : 𝕜 := ((C ^ (1 / p).toReal).toReal : 𝕜)
    have hc : c ≠ 0 := RCLike.ofReal_ne_zero.2 (ENNReal.toReal_rpow_pos hC₀ hC _).ne'
    have hqmp := QuasiMeasurePreserving.of_map_le_smul hq_meas hmap.le
    refine ⟨c • hvLp.toLp v, Lp.ext ?_⟩
    filter_upwards [Lp.coeFn_compOfMapEqSmulₗᵢ (𝕜 := 𝕜) hq_meas hC hC₀ hmap (c • hvLp.toLp v),
      hqmp.ae (Lp.coeFn_smul c (hvLp.toLp v)), hqmp.ae hvLp.coeFn_toLp, hu'u] with x h₁ h₂ h₃ h₄
    rw [LinearIsometry.coe_toLinearMap, h₁, h₂, Pi.smul_apply, h₃, inv_smul_smul₀ hc, ← h₄, ← hv,
      Function.comp_apply]

end IsQuotientCoveringMap
