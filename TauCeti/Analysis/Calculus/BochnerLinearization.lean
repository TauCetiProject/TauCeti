/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.RepresentationTheory.InvariantForm.InnerProduct
public import TauCeti.Topology.Algebra.GroupAction.GermKernel
import Mathlib.Analysis.Convex.PathConnected
import TauCeti.Algebra.BigOperators.Finset.Average
import TauCeti.Topology.OpenPartialHomeomorph.MulAction
import TauCeti.RepresentationTheory.Invariants

/-!
# Finite Bochner linearization

Let a finite group `G` act on a space `X`, and let `ρ` be a continuous linear representation of
`G` on a topological vector space `F` over a ring `𝕜` in which the order of `G` is invertible.
The *Bochner average* of a map `c : X → F` is
`bochnerAverage ρ c y = |G|⁻¹ • ∑ g, ρ g⁻¹ (c (g • y))`.
It is always `G`-equivariant: `bochnerAverage ρ c (h • y) = ρ h (bochnerAverage ρ c y)`. It is
the nonlinear analogue of the averaging of a linear map used in Maschke's theorem
(`LinearMap.equivariantProjection`), and it fixes maps that are already equivariant.

When the derivative of each `y ↦ c (g • y)` at a point is `ρ g ∘ D₀`, for a fixed linear map
`D₀`, the Bochner average also has derivative `D₀` there. This is the situation at a fixed point
`x` of the action when `c` is a chart centred at `x` and `ρ` is the derivative representation of
`G` at `x` in that chart: the average then has derivative the identity at `x`, and the inverse
function theorem turns it into a chart around `x` in which `G` acts linearly through `ρ`. This is
Bochner's linearization theorem for finite groups, the local model of a smooth orbifold around a
point with finite isotropy. No faithfulness of the action is assumed.

The chart is constructed for an action on an arbitrary topological space `X` equipped with an
`E`-valued open partial homeomorphism `χ` around the fixed point, with differentiability
expressed for the conjugated maps `χ ∘ (g • ·) ∘ χ.symm`; for `X = E` one may take `χ` to be the
identity.

## Main definitions

* `ContRepresentation.bochnerAverage ρ c`: the Bochner average of `c : X → F` with respect to `ρ`.
* `TauCeti.isotropyRepresentation`: the derivative representation of `G` at a fixed point, in the
  coordinates of a chart.
* `OpenPartialHomeomorph.bochnerChart χ ρ c hA`: the inverse-function-theorem chart of the
  Bochner average, restricted to the largest `G`-invariant open subset of its domain.

## Main results

* `ContRepresentation.bochnerAverage_smul`: the Bochner average is equivariant.
* `ContRepresentation.bochnerAverage_eq_self`: averaging an equivariant map does not change it.
* `ContRepresentation.bochnerAverage_apply_of_forall_smul_eq`: at a fixed point the Bochner
  average is `Representation.averageMap` applied to the value of `c`.
* `ContRepresentation.hasStrictFDerivAt_bochnerAverage_comp_of_intertwining`: the derivative of
  the Bochner average when the derivatives of `c (g • ·)` intertwine with `ρ`.
* `ContRepresentation.contDiffOn_bochnerAverage_comp`: the Bochner average is as smooth as the
  maps `c (g • ·)`; `OpenPartialHomeomorph.contDiffOn_bochnerChart_comp_symm` is the
  corresponding statement for the Bochner chart, and
  `OpenPartialHomeomorph.contDiffAt_comp_bochnerChart_symm` the one for its inverse.
* `OpenPartialHomeomorph.smul_mem_bochnerChart_source`,
  `OpenPartialHomeomorph.map_mem_bochnerChart_target`: the Bochner chart has a `G`-invariant
  domain and a `ρ`-invariant target.
* `OpenPartialHomeomorph.bochnerChart_smul`, `OpenPartialHomeomorph.bochnerChart_symm_map`: the
  Bochner chart and its inverse intertwine the action of `G` with `ρ`.
* `OpenPartialHomeomorph.exists_equivariant_chart`: Bochner linearization. Near a fixed point of
  a finite group action whose conjugated maps have strict derivatives `σ g` for a representation
  `σ`, there is a chart with `G`-invariant domain, centred at the point, with derivative the
  identity, in which `g` acts as `σ g`.
* `OpenPartialHomeomorph.map_eq_one_iff_mem_germKernel`: the derivative representation
  detects the ineffective kernel. An element of `G` lies in the germ kernel at the fixed point,
  that is, acts as the identity near it, exactly when its derivative there is the identity.
* `OpenPartialHomeomorph.exists_target_eq_sumOfConjugatesInnerSublevel`: over `ℝ`, in finite
  dimensions, a chart in which `G` acts linearly restricts, inside any neighbourhood of a point it
  sends to `0`, to an equivariant chart onto an invariant ball of an averaged inner product
  (`Representation.sumOfConjugatesInnerSublevel`), with invariant preconnected domain.

## References

* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46 (1945),
  372–381.
* I. Moerdijk and D. A. Pronk, *Orbifolds, sheaves and groupoids*, K-Theory 12 (1997), 3–21,
  where this linearization gives the local charts of a proper étale groupoid.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Ch. 1, for linear local models of
  orbifolds, including nonfaithful ones and their ineffective kernel.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace ContRepresentation

section Average

variable {𝕜 G X F : Type*} [CommRing 𝕜] [Group G] [Fintype G] [Invertible (Fintype.card G : 𝕜)]
  [MulAction G X] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]

/-- The Bochner average `|G|⁻¹ • ∑ g, ρ g⁻¹ (c (g • y))` of a map `c : X → F` with respect to a
continuous representation `ρ` of a finite group `G` acting on `X`. It is `G`-equivariant
(`ContRepresentation.bochnerAverage_smul`). -/
def bochnerAverage (ρ : ContRepresentation 𝕜 G F) (c : X → F) (y : X) : F :=
  ⅟(Fintype.card G : 𝕜) • ∑ g : G, ρ g⁻¹ (c (g • y))

variable (ρ : ContRepresentation 𝕜 G F) (c : X → F)

theorem bochnerAverage_def (y : X) :
    bochnerAverage ρ c y = ⅟(Fintype.card G : 𝕜) • ∑ g : G, ρ g⁻¹ (c (g • y)) := by
  rw [bochnerAverage]

/-- The Bochner average is `G`-equivariant. -/
@[simp]
theorem bochnerAverage_smul (h : G) (y : X) :
    bochnerAverage ρ c (h • y) = ρ h (bochnerAverage ρ c y) := by
  rw [bochnerAverage_def, bochnerAverage_def, map_smul, map_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => ?_
  simp [mul_smul, ← mul_apply_eq_comp, ← map_mul]

variable {ρ c} in
/-- Averaging a map that is already `G`-equivariant does not change it. -/
theorem bochnerAverage_eq_self (hc : ∀ (g : G) (y : X), c (g • y) = ρ g (c y)) :
    bochnerAverage ρ c = c := by
  ext y
  have hg (g : G) : ρ g⁻¹ (c (g • y)) = c y := by
    rw [hc]
    exact ρ.toRepresentation.inv_self_apply g (c y)
  rw [bochnerAverage_def, Finset.sum_congr rfl fun g _ => hg g, Fintype.invOf_card_smul_sum_const]

/-- At a point fixed by `G`, the Bochner average is the average of the value of `c` over the
representation, that is, its image under `Representation.averageMap`. In particular it lies in the
invariants of `ρ`. -/
theorem bochnerAverage_apply_of_forall_smul_eq {x : X} (hx : ∀ g : G, g • x = x) :
    bochnerAverage ρ c x = ρ.toRepresentation.averageMap (c x) := by
  simp only [Representation.averageMap_eq_invOf_card_smul_norm, bochnerAverage_def, hx,
    LinearMap.smul_apply, Representation.norm, LinearMap.sum_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => by simp [ContRepresentation.toMonoidHom_apply]

/-- The Bochner average along a map `f : Y → X`, as a function of the point of `Y`. -/
theorem bochnerAverage_comp_eq {Y : Type*} (f : Y → X) :
    bochnerAverage ρ c ∘ f = fun w => ⅟(Fintype.card G : 𝕜) • ∑ g : G, ρ g⁻¹ (c (g • f w)) := by
  funext w
  rw [Function.comp_apply, bochnerAverage_def]

section Regularity

variable {Y : Type*} [TopologicalSpace Y] [ContinuousConstSMul 𝕜 F] {f : Y → X}

/-- The Bochner average along `f : Y → X` is continuous on `s` if each `w ↦ c (g • f w)` is. -/
theorem continuousOn_bochnerAverage_comp {s : Set Y}
    (hc : ∀ g : G, ContinuousOn (fun w => c (g • f w)) s) :
    ContinuousOn (bochnerAverage ρ c ∘ f) s := by
  rw [bochnerAverage_comp_eq]
  exact (continuousOn_finsetSum Finset.univ fun g _ =>
    (ρ g⁻¹).continuous.comp_continuousOn (hc g)).const_smul _

/-- The Bochner average along `f : Y → X` is continuous if each `w ↦ c (g • f w)` is. -/
theorem continuous_bochnerAverage_comp (hc : ∀ g : G, Continuous fun w => c (g • f w)) :
    Continuous (bochnerAverage ρ c ∘ f) := by
  simp only [← continuousOn_univ] at hc ⊢
  exact continuousOn_bochnerAverage_comp ρ c hc

end Regularity

end Average

section Deriv

variable {𝕜 G X E F : Type*} [NontriviallyNormedField 𝕜] [Group G] [Fintype G]
  [Invertible (Fintype.card G : 𝕜)] [MulAction G X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {ρ : ContRepresentation 𝕜 G F} {c : X → F} {f : E → X} {z : E}

/-- The strict derivative of the Bochner average along a map `f : E → X`, given the strict
derivatives `D g` of the maps `w ↦ c (g • f w)`. -/
theorem hasStrictFDerivAt_bochnerAverage_comp {D : G → E →L[𝕜] F}
    (hc : ∀ g : G, HasStrictFDerivAt (fun w => c (g • f w)) (D g) z) :
    HasStrictFDerivAt (bochnerAverage ρ c ∘ f)
      (⅟(Fintype.card G : 𝕜) • ∑ g : G, (ρ g⁻¹).comp (D g)) z := by
  rw [bochnerAverage_comp_eq]
  exact (HasStrictFDerivAt.fun_sum fun g (_ : g ∈ Finset.univ) =>
    (ρ g⁻¹).hasStrictFDerivAt.comp z (hc g)).fun_const_smul _

/-- The derivative of the Bochner average along a map `f : E → X`, given the derivatives `D g` of
the maps `w ↦ c (g • f w)`. -/
theorem hasFDerivAt_bochnerAverage_comp {D : G → E →L[𝕜] F}
    (hc : ∀ g : G, HasFDerivAt (fun w => c (g • f w)) (D g) z) :
    HasFDerivAt (bochnerAverage ρ c ∘ f)
      (⅟(Fintype.card G : 𝕜) • ∑ g : G, (ρ g⁻¹).comp (D g)) z := by
  rw [bochnerAverage_comp_eq]
  exact (HasFDerivAt.fun_sum fun g (_ : g ∈ Finset.univ) =>
    (ρ g⁻¹).hasFDerivAt.comp z (hc g)).fun_const_smul _

/-- Averaging the intertwined linear maps `ρ g ∘ D₀` against `ρ g⁻¹` returns `D₀`. -/
private theorem average_comp_intertwining (D₀ : E →L[𝕜] F) :
    ⅟(Fintype.card G : 𝕜) • ∑ g : G, (ρ g⁻¹).comp ((ρ g).comp D₀) = D₀ := by
  have hg (g : G) : (ρ g⁻¹).comp ((ρ g).comp D₀) = D₀ :=
    ContinuousLinearMap.ext fun v => ρ.toRepresentation.inv_self_apply g (D₀ v)
  rw [Finset.sum_congr rfl fun g _ => hg g, Fintype.invOf_card_smul_sum_const]

/-- If the strict derivative of each `w ↦ c (g • f w)` at `z` is `ρ g ∘ D₀`, then the Bochner
average along `f` has strict derivative `D₀` at `z`. -/
theorem hasStrictFDerivAt_bochnerAverage_comp_of_intertwining {D₀ : E →L[𝕜] F}
    (hc : ∀ g : G, HasStrictFDerivAt (fun w => c (g • f w)) ((ρ g).comp D₀) z) :
    HasStrictFDerivAt (bochnerAverage ρ c ∘ f) D₀ z := by
  simpa only [average_comp_intertwining] using hasStrictFDerivAt_bochnerAverage_comp (ρ := ρ) hc

/-- If the derivative of each `w ↦ c (g • f w)` at `z` is `ρ g ∘ D₀`, then the Bochner average
along `f` has derivative `D₀` at `z`. -/
theorem hasFDerivAt_bochnerAverage_comp_of_intertwining {D₀ : E →L[𝕜] F}
    (hc : ∀ g : G, HasFDerivAt (fun w => c (g • f w)) ((ρ g).comp D₀) z) :
    HasFDerivAt (bochnerAverage ρ c ∘ f) D₀ z := by
  simpa only [average_comp_intertwining] using hasFDerivAt_bochnerAverage_comp (ρ := ρ) hc

variable {n : WithTop ℕ∞}

/-- The Bochner average along `f : E → X` is `C^n` at `z` if each `w ↦ c (g • f w)` is. -/
theorem contDiffAt_bochnerAverage_comp (hc : ∀ g : G, ContDiffAt 𝕜 n (fun w => c (g • f w)) z) :
    ContDiffAt 𝕜 n (bochnerAverage ρ c ∘ f) z := by
  rw [bochnerAverage_comp_eq]
  exact (ContDiffAt.sum fun g (_ : g ∈ Finset.univ) =>
    (ρ g⁻¹).contDiff.contDiffAt.comp z (hc g)).const_smul _

/-- The Bochner average along `f : E → X` is `C^n` on `s` if each `w ↦ c (g • f w)` is. -/
theorem contDiffOn_bochnerAverage_comp {s : Set E}
    (hc : ∀ g : G, ContDiffOn 𝕜 n (fun w => c (g • f w)) s) :
    ContDiffOn 𝕜 n (bochnerAverage ρ c ∘ f) s := by
  rw [bochnerAverage_comp_eq]
  exact (ContDiffOn.sum fun g (_ : g ∈ Finset.univ) =>
    (ρ g⁻¹).contDiff.comp_contDiffOn (hc g)).const_smul _

end Deriv

end ContRepresentation

namespace OpenPartialHomeomorph

section Chart

variable {𝕜 G X E F : Type*} [NontriviallyNormedField 𝕜] [Group G] [Fintype G]
  [Invertible (Fintype.card G : 𝕜)] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (χ : OpenPartialHomeomorph X E) (ρ : ContRepresentation 𝕜 G F) (c : X → F)
  {D : E ≃L[𝕜] F} {z : E}

/-- The composite of `χ` with the inverse-function-theorem chart of the Bochner average in the
coordinates of `χ`, before restricting to a `G`-invariant domain. -/
private def bochnerChartAux
    (hA : HasStrictFDerivAt (ρ.bochnerAverage c ∘ χ.symm) (D : E →L[𝕜] F) z) :
    OpenPartialHomeomorph X F :=
  χ.trans (hA.toOpenPartialHomeomorph _)

/-- The Bochner chart: given a strict derivative `D`, invertible, of the Bochner average in the
coordinates of `χ`, this is the inverse-function-theorem chart of the Bochner average, restricted
to the largest `G`-invariant open subset of its domain. On its domain it agrees with the Bochner
average (`OpenPartialHomeomorph.bochnerChart_apply`), so it intertwines the action of `G` with `ρ`
(`OpenPartialHomeomorph.bochnerChart_smul`). -/
def bochnerChart (hA : HasStrictFDerivAt (ρ.bochnerAverage c ∘ χ.symm) (D : E →L[𝕜] F) z) :
    OpenPartialHomeomorph X F :=
  (bochnerChartAux χ ρ c hA).restrOpen (⋂ g : G, (g • ·) ⁻¹' (bochnerChartAux χ ρ c hA).source)
    (isOpen_iInter_of_finite fun g =>
      (bochnerChartAux χ ρ c hA).open_source.preimage (continuous_const_smul g))

variable {χ ρ c}
variable (hA : HasStrictFDerivAt (ρ.bochnerAverage c ∘ χ.symm) (D : E →L[𝕜] F) z)

private theorem mem_bochnerChart_source_iff {y : X} :
    y ∈ (bochnerChart χ ρ c hA).source ↔ ∀ g : G, g • y ∈ (bochnerChartAux χ ρ c hA).source := by
  rw [bochnerChart, restrOpen_source, mem_inter_iff, mem_iInter]
  refine ⟨And.right, fun h => ⟨by simpa using h 1, h⟩⟩

/-- The domain of the Bochner chart is `G`-invariant. -/
theorem smul_mem_bochnerChart_source {y : X} (hy : y ∈ (bochnerChart χ ρ c hA).source) (g : G) :
    g • y ∈ (bochnerChart χ ρ c hA).source := by
  rw [mem_bochnerChart_source_iff] at hy ⊢
  intro g'
  simpa [smul_smul] using hy (g' * g)

/-- The domain of the Bochner chart is contained in the domain of `χ`. -/
theorem bochnerChart_source_subset : (bochnerChart χ ρ c hA).source ⊆ χ.source := fun y hy => by
  have hy1 := (mem_bochnerChart_source_iff hA).1 hy 1
  rw [one_smul, bochnerChartAux, trans_source] at hy1
  exact hy1.1

/-- A point fixed by `G` whose `χ`-coordinate is the base point `z` lies in the domain of the
Bochner chart. -/
theorem mem_bochnerChart_source {x : X} (hx : ∀ g : G, g • x = x) (hxχ : x ∈ χ.source)
    (hxz : χ x = z) : x ∈ (bochnerChart χ ρ c hA).source := by
  rw [mem_bochnerChart_source_iff]
  intro g
  rw [hx, bochnerChartAux, trans_source]
  exact ⟨hxχ, hxz ▸ hA.mem_toOpenPartialHomeomorph_source⟩

/-- On its domain, the Bochner chart is the Bochner average. -/
theorem bochnerChart_apply {y : X} (hy : y ∈ (bochnerChart χ ρ c hA).source) :
    bochnerChart χ ρ c hA y = ρ.bochnerAverage c y := by
  simp [bochnerChart, bochnerChartAux, χ.left_inv (bochnerChart_source_subset hA hy)]

/-- The Bochner chart intertwines the action of `G` with `ρ`. -/
theorem bochnerChart_smul {y : X} (hy : y ∈ (bochnerChart χ ρ c hA).source) (g : G) :
    bochnerChart χ ρ c hA (g • y) = ρ g (bochnerChart χ ρ c hA y) := by
  rw [bochnerChart_apply hA (smul_mem_bochnerChart_source hA hy g), bochnerChart_apply hA hy,
    ContRepresentation.bochnerAverage_smul]

/-- The target of the Bochner chart is invariant under `ρ`. -/
theorem map_mem_bochnerChart_target {w : F} (hw : w ∈ (bochnerChart χ ρ c hA).target) (g : G) :
    ρ g w ∈ (bochnerChart χ ρ c hA).target := by
  set e := bochnerChart χ ρ c hA
  rw [← e.right_inv hw, ← bochnerChart_smul hA (e.map_target hw)]
  exact e.map_source (smul_mem_bochnerChart_source hA (e.map_target hw) g)

/-- The inverse of the Bochner chart intertwines `ρ` with the action of `G`. -/
theorem bochnerChart_symm_map {w : F} (hw : w ∈ (bochnerChart χ ρ c hA).target) (g : G) :
    (bochnerChart χ ρ c hA).symm (ρ g w) = g • (bochnerChart χ ρ c hA).symm w := by
  set e := bochnerChart χ ρ c hA
  rw [← e.right_inv hw, ← bochnerChart_smul hA (e.map_target hw), e.right_inv hw,
    e.left_inv (smul_mem_bochnerChart_source hA (e.map_target hw) g)]

/-- In the coordinates of `χ`, the Bochner chart has strict derivative `D` at the base point. -/
theorem hasStrictFDerivAt_bochnerChart_comp_symm (hz : z ∈ χ.target) :
    HasStrictFDerivAt (bochnerChart χ ρ c hA ∘ χ.symm) (D : E →L[𝕜] F) z := by
  refine hA.congr_of_eventuallyEq ?_
  filter_upwards [χ.eventually_right_inverse hz] with w hw
  simp [bochnerChart, bochnerChartAux, hw]

/-- In the coordinates of `χ`, the Bochner chart is `C^n` on any set where the maps
`w ↦ c (g • χ.symm w)` are, intersected with the domain of the chart. -/
theorem contDiffOn_bochnerChart_comp_symm {n : WithTop ℕ∞} {s : Set E}
    (hc : ∀ g : G, ContDiffOn 𝕜 n (fun w => c (g • χ.symm w)) s) :
    ContDiffOn 𝕜 n (bochnerChart χ ρ c hA ∘ χ.symm)
      (s ∩ χ.symm ⁻¹' (bochnerChart χ ρ c hA).source) :=
  ((ρ.contDiffOn_bochnerAverage_comp hc).mono inter_subset_left).congr fun _ hw =>
    bochnerChart_apply hA hw.2

/-- In the coordinates of `χ`, the inverse of the Bochner chart is `C^n` at a point `w` of its
target, provided that, in the coordinates of `χ`, the Bochner average is `C^n` with an invertible
derivative at the point corresponding to `w`. -/
theorem contDiffAt_comp_bochnerChart_symm {n : WithTop ℕ∞} {w : F}
    (hw : w ∈ (bochnerChart χ ρ c hA).target) {D' : E ≃L[𝕜] F}
    (hD' : HasFDerivAt (ρ.bochnerAverage c ∘ χ.symm) (D' : E →L[𝕜] F)
      (χ ((bochnerChart χ ρ c hA).symm w)))
    (hc : ContDiffAt 𝕜 n (ρ.bochnerAverage c ∘ χ.symm) (χ ((bochnerChart χ ρ c hA).symm w))) :
    ContDiffAt 𝕜 n (χ ∘ (bochnerChart χ ρ c hA).symm) w := by
  set e := bochnerChart χ ρ c hA
  have hy := e.map_target hw
  have hyχ := bochnerChart_source_subset hA hy
  have heq : e ∘ χ.symm =ᶠ[𝓝 (χ (e.symm w))] ρ.bochnerAverage c ∘ χ.symm := by
    have hmem : ∀ᶠ v in 𝓝 (χ (e.symm w)), χ.symm v ∈ e.source := by
      refine (χ.continuousAt_symm (χ.map_source hyχ)).preimage_mem_nhds ?_
      rw [χ.left_inv hyχ]
      exact e.open_source.mem_nhds hy
    filter_upwards [hmem] with v hv
    exact bochnerChart_apply hA hv
  have hw' : w ∈ (χ.symm.trans e).target := by
    rw [trans_target, symm_target]
    exact ⟨hw, hyχ⟩
  have hes : ⇑(χ.symm.trans e).symm = χ ∘ e.symm := by rw [coe_trans_symm, symm_symm]
  rw [← hes]
  refine (χ.symm.trans e).contDiffAt_symm hw' (f₀' := D') ?_ ?_ <;> rw [hes, coe_trans]
  · exact hD'.congr_of_eventuallyEq heq
  · exact hc.congr_of_eventuallyEq heq

end Chart

end OpenPartialHomeomorph

namespace TauCeti

section Isotropy

variable {𝕜 G X E : Type*} [NontriviallyNormedField 𝕜] [Group G] [TopologicalSpace X]
  [MulAction G X] [ContinuousConstSMul G X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {χ : OpenPartialHomeomorph X E} {x : X}

/-- The isotropy representation of `G` at a fixed point `x`, in the coordinates of a chart `χ`
around `x`: `g` acts by the derivative at `χ x` of the conjugated map `χ ∘ (g • ·) ∘ χ.symm`.
Multiplicativity is the chain rule at the fixed point. -/
def isotropyRepresentation (hxχ : x ∈ χ.source) (hx : ∀ g : G, g • x = x)
    (hd : ∀ g : G, DifferentiableAt 𝕜 (χ ∘ (g • ·) ∘ χ.symm) (χ x)) :
    ContRepresentation 𝕜 G E :=
  .ofMonoidHom
    { toFun g := fderiv 𝕜 (χ ∘ (g • ·) ∘ χ.symm) (χ x)
      map_one' := by
        rw [(χ.conj_one_smul_eventuallyEq (χ.map_source hxχ)).fderiv_eq, fderiv_id,
          ContinuousLinearMap.one_def]
      map_mul' g h := by
        have hfix : (χ ∘ (h • ·) ∘ χ.symm) (χ x) = χ x := by simp [χ.left_inv hxχ, hx]
        rw [(χ.conj_mul_smul_eventuallyEq hxχ ((hx h).symm ▸ hxχ) g).fderiv_eq,
          fderiv_comp (χ x) (by rw [hfix]; exact hd g) (hd h), hfix,
          ContinuousLinearMap.mul_def] }

@[simp]
theorem isotropyRepresentation_apply (hxχ : x ∈ χ.source) (hx : ∀ g : G, g • x = x)
    (hd : ∀ g : G, DifferentiableAt 𝕜 (χ ∘ (g • ·) ∘ χ.symm) (χ x)) (g : G) :
    isotropyRepresentation hxχ hx hd g = fderiv 𝕜 (χ ∘ (g • ·) ∘ χ.symm) (χ x) :=
  (rfl)

/-- If each conjugated map `χ ∘ (g • ·) ∘ χ.symm` has a strict derivative at `χ x`, then this
strict derivative is given by the isotropy representation. -/
theorem hasStrictFDerivAt_conj_smul_isotropyRepresentation (hxχ : x ∈ χ.source)
    (hx : ∀ g : G, g • x = x)
    {L : G → E →L[𝕜] E} (hL : ∀ g : G, HasStrictFDerivAt (χ ∘ (g • ·) ∘ χ.symm) (L g) (χ x))
    (g : G) :
    HasStrictFDerivAt (χ ∘ (g • ·) ∘ χ.symm)
      (isotropyRepresentation hxχ hx (fun g => (hL g).differentiableAt) g) (χ x) := by
  rw [isotropyRepresentation_apply, (hL g).hasFDerivAt.fderiv]
  exact hL g

end Isotropy

end TauCeti

namespace OpenPartialHomeomorph

section Linearization

variable {𝕜 G X E : Type*} [NontriviallyNormedField 𝕜] [Group G] [Fintype G]
  [Invertible (Fintype.card G : 𝕜)] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- **Bochner linearization** for a finite group. Let `G` act on `X` fixing `x`, let `χ` be an
`E`-valued chart around `x`, and suppose that each conjugated map `χ ∘ (g • ·) ∘ χ.symm` has strict
derivative `σ g` at `χ x`, where `σ` is a continuous representation of `G` on `E`. Then there is a
chart `e` around `x` with `G`-invariant domain inside that of `χ`, sending `x` to `0`, with
derivative the identity at `x` in the coordinates of `χ`, in which `g` acts linearly as `σ g`.
The chart is the Bochner chart of `y ↦ χ y - χ x`. When the conjugated maps are strictly
differentiable at `χ x`, one can take `σ` to be `TauCeti.isotropyRepresentation`
(`TauCeti.hasStrictFDerivAt_conj_smul_isotropyRepresentation`). -/
theorem exists_equivariant_chart (χ : OpenPartialHomeomorph X E) {x : X} (hxχ : x ∈ χ.source)
    (hx : ∀ g : G, g • x = x) (σ : ContRepresentation 𝕜 G E)
    (hσ : ∀ g : G, HasStrictFDerivAt (χ ∘ (g • ·) ∘ χ.symm) (σ g) (χ x)) :
    ∃ e : OpenPartialHomeomorph X E, x ∈ e.source ∧ e x = 0 ∧ e.source ⊆ χ.source ∧
      (∀ g : G, ∀ y ∈ e.source, g • y ∈ e.source ∧ e (g • y) = σ g (e y)) ∧
      HasStrictFDerivAt (e ∘ χ.symm) (ContinuousLinearMap.id 𝕜 E) (χ x) := by
  have hA : HasStrictFDerivAt (σ.bochnerAverage (fun y => χ y - χ x) ∘ χ.symm)
      ((ContinuousLinearEquiv.refl 𝕜 E : E ≃L[𝕜] E) : E →L[𝕜] E) (χ x) := by
    refine ContRepresentation.hasStrictFDerivAt_bochnerAverage_comp_of_intertwining fun g => ?_
    simpa using (hσ g).sub_const (χ x)
  have hxs := mem_bochnerChart_source hA hx hxχ rfl
  refine ⟨bochnerChart χ σ _ hA, hxs, ?_, bochnerChart_source_subset hA,
    fun g y hy => ⟨smul_mem_bochnerChart_source hA hy g, bochnerChart_smul hA hy g⟩, ?_⟩
  · rw [bochnerChart_apply hA hxs, ContRepresentation.bochnerAverage_apply_of_forall_smul_eq _ _ hx,
      sub_self, map_zero]
  · simpa using hasStrictFDerivAt_bochnerChart_comp_symm hA (χ.map_source hxχ)

/-- **The derivative representation detects the ineffective kernel.** In the setting of
`OpenPartialHomeomorph.exists_equivariant_chart`, an element of `G` acts as the identity near the
fixed point `x`, that is, lies in the germ kernel `TauCeti.MulAction.germKernel G x`, exactly when
its derivative `σ g` at `x`, in the coordinates of `χ`, is the identity. -/
theorem map_eq_one_iff_mem_germKernel (χ : OpenPartialHomeomorph X E) {x : X}
    (hxχ : x ∈ χ.source) (hx : ∀ g : G, g • x = x) (σ : ContRepresentation 𝕜 G E)
    (hσ : ∀ g : G, HasStrictFDerivAt (χ ∘ (g • ·) ∘ χ.symm) (σ g) (χ x)) (g : G) :
    σ g = 1 ↔ g ∈ TauCeti.MulAction.germKernel G x := by
  rw [TauCeti.MulAction.mem_germKernel]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- the equivariant chart turns `g • y = y` into `σ g (e y) = e y`
    obtain ⟨e, hxe, -, -, he, -⟩ := χ.exists_equivariant_chart hxχ hx σ hσ
    filter_upwards [e.open_source.mem_nhds hxe] with y hy
    exact e.injOn (he g y hy).1 hy (by rw [(he g y hy).2, h, one_apply_eq_self])
  · -- the conjugated map `χ ∘ (g • ·) ∘ χ.symm` agrees with the identity near `χ x`
    have hev : χ ∘ (g • ·) ∘ χ.symm =ᶠ[𝓝 (χ x)] id := by
      have hsymm : ∀ᶠ w in 𝓝 (χ x), g • χ.symm w = χ.symm w :=
        (χ.continuousAt_symm (χ.map_source hxχ)).eventually (by rwa [χ.left_inv hxχ])
      filter_upwards [χ.eventually_right_inverse (χ.map_source hxχ), hsymm] with w hw hgw
      simp [hgw, hw]
    rw [ContinuousLinearMap.one_def]
    exact (hσ g).hasFDerivAt.unique ((hasFDerivAt_id _).congr_of_eventuallyEq hev)

end Linearization

section InvariantBall

variable {G X E : Type*} [Group G] [Fintype G] [TopologicalSpace X] [MulAction G X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Shrinking an equivariant chart to an invariant ball.** Let `e` be a chart centred at `x`,
with `G`-invariant domain, in which `G` acts linearly through a representation `σ` on a
finite-dimensional real inner product space. Inside any neighbourhood `s` of `x`, the chart `e`
restricts to a chart `e'` onto a positive strict sublevel set of the orbit-sum inner product of
`σ`, an open convex `σ`-invariant neighbourhood of `0`. The restriction `e'` has the same
underlying map as `e`, and its domain is `G`-invariant and preconnected. -/
theorem exists_target_eq_sumOfConjugatesInnerSublevel (e : OpenPartialHomeomorph X E)
    (σ : Representation ℝ G E) {x : X} (hxe : x ∈ e.source) (hex : e x = 0)
    (he : ∀ g : G, ∀ y ∈ e.source, g • y ∈ e.source ∧ e (g • y) = σ g (e y))
    {s : Set X} (hs : s ∈ 𝓝 x) :
    ∃ (e' : OpenPartialHomeomorph X E) (c : ℝ), 0 < c ∧ x ∈ e'.source ∧ ⇑e' = ⇑e ∧
      e'.source ⊆ e.source ∩ s ∧ e'.target = σ.sumOfConjugatesInnerSublevel c ∧
      IsPreconnected e'.source ∧
      ∀ g : G, ∀ y ∈ e'.source, g • y ∈ e'.source ∧ e' (g • y) = σ g (e' y) := by
  -- Choose an invariant sublevel set `W` among the coordinates of points of `interior s`.
  have hV : IsOpen (e.target ∩ e.symm ⁻¹' interior s) :=
    e.isOpen_inter_preimage_symm isOpen_interior
  have h0 : (0 : E) ∈ e.target ∩ e.symm ⁻¹' interior s := by
    rw [← hex, mem_inter_iff, mem_preimage, e.left_inv hxe]
    exact ⟨e.map_source hxe, mem_interior_iff_mem_nhds.2 hs⟩
  obtain ⟨c, hc, hcV⟩ := σ.exists_pos_sumOfConjugatesInnerSublevel_subset hV h0
  set W := σ.sumOfConjugatesInnerSublevel c
  have hW : IsOpen W := σ.isOpen_sumOfConjugatesInnerSublevel c
  -- Restrict `e` to the points with coordinates in `W`.
  set e' := (e.symm.restrOpen W hW).symm
  have hcoe : ⇑e' = ⇑e := rfl
  have hmem {y : X} : y ∈ e'.source ↔ y ∈ e.source ∧ e y ∈ W := by
    simp [e']
  have htarget : e'.target = W := by
    have hWt : W ⊆ e.target := fun w hw => (hcV hw).1
    simpa [e'] using hWt
  refine ⟨e', c, hc, hmem.2 ⟨hxe, hex ▸ ?_⟩, hcoe, fun y hy => ⟨(hmem.1 hy).1, ?_⟩, htarget,
    ?_, fun g y hy => ?_⟩
  · simpa [W] using hc
  · have hyW := (hcV (hmem.1 hy).2).2
    rw [mem_preimage, e.left_inv (hmem.1 hy).1] at hyW
    exact interior_subset hyW
  · rw [← e'.symm_image_target_eq_source, htarget]
    exact (σ.convex_sumOfConjugatesInnerSublevel c).isPreconnected.image _
      (e'.continuousOn_symm.mono htarget.ge)
  · obtain ⟨hgy, hgye⟩ := he g y (hmem.1 hy).1
    rw [hcoe, hgye]
    refine ⟨hmem.2 ⟨hgy, ?_⟩, rfl⟩
    rw [hgye, ← mem_preimage, σ.preimage_sumOfConjugatesInnerSublevel]
    exact (hmem.1 hy).2

end InvariantBall

end OpenPartialHomeomorph
