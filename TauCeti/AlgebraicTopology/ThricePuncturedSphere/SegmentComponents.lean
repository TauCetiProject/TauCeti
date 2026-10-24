/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PuncturedNeighborhoodComponents

import Mathlib.Topology.Algebra.Module.LocallyConvex
import TauCeti.Analysis.Convex.SimplyConnected
import TauCeti.Analysis.Complex.OpenSegment
import TauCeti.Topology.IsLocalHomeomorph

/-!
# The edges of the dessin of a cover of the thrice-punctured sphere

Let `p : E → ℂ ∖ {0, 1}` be a covering map whose fibre over the basepoint `1/2` is numbered by
`ν : p ⁻¹' {1/2} ≃ Fin n`, with monodromy triple `(σ0, σ1, σinf)`. The dessin d'enfants of the
cover is drawn on `E` by the preimage of the real segment from `0` to `1`: its edges are the
connected components of the preimage of the open segment `(0, 1)`, and its black and white
vertices are the points added over `0` and `1` when the cover is compactified, that is, the
connected components of the preimages of the punctured neighborhoods

* `D₀* = {z | ‖z‖ < 1/2}` and `D₁* = {z | ‖z - 1‖ < 1/2}`,

which are the cycles of `σ0` and of `σ1`
(`IsCoveringMap.sameCycleQuotientσ0EquivConnectedComponents` and its analogue at `1`).

This file identifies the edges and their incidences with the combinatorial dessin of the triple
(`TauCeti.PermutationTriple.ribbonGraph`), whose edges are the sheets `Fin n` and whose black and
white ends of the sheet `i` are its cycles under `σ0` and `σ1`:

* the segment `(0, 1)` is simply connected, so each component of its preimage contains exactly
  one point of the fibre over `1/2`, and the components are numbered by the sheets;
* the edge of the sheet `i` meets exactly one component over `D₀*`, the one of the cycle of `i`
  under `σ0`, and exactly one component over `D₁*`, the one of the cycle of `i` under `σ1`.

After compactification, an edge meets the component of an added point exactly when that point is
an end of the closure of the edge, so these are the incidences of the embedded graph.

## Main declarations

* `TauCeti.ThricePuncturedSphere.unitSegment`: the open real segment `(0, 1)`.
* `IsCoveringMap.finEquivConnectedComponentsUnitSegment`: the sheets are the connected components
  of `p ⁻¹' (0, 1)`, the sheet `i` going to the component of the point it numbers.
* `IsCoveringMap.exists_common_point_iff_eq_sameCycleQuotientσ0`,
  `IsCoveringMap.exists_common_point_iff_eq_sameCycleQuotientσ1`: the edge of the sheet `i`
  meets a component over `D₀*` (respectively `D₁*`) exactly when that component is the cycle of
  `i` under `σ0` (respectively `σ1`).

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §4.2 (the dessin of a Belyi map is the preimage of `[0, 1]`) and §4.3 (its monodromy).
* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer, 2004, §1.3 and §1.5.
-/

public section

noncomputable section

namespace TauCeti

open ThricePuncturedSphere Equiv Equiv.Perm Set Topology

namespace ThricePuncturedSphere

/-! ### The open segment `(0, 1)` -/

/-- The open real segment `(0, 1)` in the thrice-punctured sphere, along which the edges of the
dessin of a cover are drawn: the preimage of the open segment `openSegment ℝ 0 1` of `ℂ`. -/
def unitSegment : Set ThricePuncturedSphere :=
  ((↑) : ThricePuncturedSphere → ℂ) ⁻¹' openSegment ℝ 0 1

@[simp]
theorem mem_unitSegment {z : ThricePuncturedSphere} :
    z ∈ unitSegment ↔ (z : ℂ).im = 0 ∧ 0 < (z : ℂ).re ∧ (z : ℂ).re < 1 :=
  Complex.mem_openSegment_zero_one

/-- The basepoint `1/2` lies on the segment `(0, 1)`. -/
theorem basePt_mem_unitSegment : basePt ∈ unitSegment := by
  simp only [mem_unitSegment, coe_basePt]
  norm_num

/-- In the coordinate `z ↦ 2 * z` of `D₀*`, the segment `(0, 1)` is the positive real axis. -/
theorem mem_unitSegment_iff_coord_zero (z : ThricePuncturedSphere)
    (hz : z ∈ Puncture.zero.neighborhood) :
    z ∈ unitSegment ↔ (Puncture.zero.coord ⟨z, hz⟩ : ℂ).im = 0 ∧
      0 < (Puncture.zero.coord ⟨z, hz⟩ : ℂ).re := by
  have hre : (z : ℂ).re < 1 := by
    have : ‖(z : ℂ)‖ < 1 / 2 := by simpa using hz
    linarith [Complex.re_le_norm (z : ℂ)]
  have him2 : (2 * (z : ℂ)).im = 2 * (z : ℂ).im := by simp
  have hre2 : (2 * (z : ℂ)).re = 2 * (z : ℂ).re := by simp
  rw [mem_unitSegment, Puncture.coe_coord_zero, him2, hre2]
  constructor
  · rintro ⟨h0, h1, -⟩
    exact ⟨by rw [h0, mul_zero], by linarith⟩
  · rintro ⟨h0, h1⟩
    exact ⟨by linarith, by linarith, hre⟩

/-- In the coordinate `z ↦ 2 * (1 - z)` of `D₁*`, the segment `(0, 1)` is the positive real
axis. -/
theorem mem_unitSegment_iff_coord_one (z : ThricePuncturedSphere)
    (hz : z ∈ Puncture.one.neighborhood) :
    z ∈ unitSegment ↔ (Puncture.one.coord ⟨z, hz⟩ : ℂ).im = 0 ∧
      0 < (Puncture.one.coord ⟨z, hz⟩ : ℂ).re := by
  have hre : 0 < (z : ℂ).re := by
    have : ‖(z : ℂ) - 1‖ < 1 / 2 := by simpa using hz
    have := Complex.abs_re_le_norm ((z : ℂ) - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    linarith [neg_abs_le ((z : ℂ).re - 1)]
  have him2 : (2 * (1 - (z : ℂ))).im = -(2 * (z : ℂ).im) := by simp
  have hre2 : (2 * (1 - (z : ℂ))).re = 2 * (1 - (z : ℂ).re) := by simp
  rw [mem_unitSegment, Puncture.coe_coord_one, him2, hre2]
  constructor
  · rintro ⟨h0, -, h1⟩
    exact ⟨by rw [h0, mul_zero, neg_zero], by linarith⟩
  · rintro ⟨h0, h1⟩
    exact ⟨by linarith, hre, by linarith⟩

/-- A set of `ℂ` lying in the strip `0 < re z < 1` contains neither puncture, so it is the image
of its preimage in the thrice-punctured sphere. -/
private theorem image_coe_preimage_coe {T : Set ℂ} (hT : ∀ w ∈ T, 0 < w.re ∧ w.re < 1) :
    ((↑) : ThricePuncturedSphere → ℂ) '' ((↑) ⁻¹' T) = T := by
  have h : ((↑) : ThricePuncturedSphere → ℂ) '' ((↑) ⁻¹' T) = {w : ℂ | w ≠ 0 ∧ w ≠ 1} ∩ T :=
    Subtype.image_preimage_coe {w : ℂ | w ≠ 0 ∧ w ≠ 1} T
  refine h.trans (inter_eq_right.2 fun w hw => ⟨?_, ?_⟩)
  · rintro rfl
    simpa using (hT _ hw).1
  · rintro rfl
    simpa using (hT _ hw).2

/-- A nonempty convex set of `ℂ` in the strip `0 < re z < 1`, viewed in the thrice-punctured
sphere, is simply connected. -/
private theorem isSimplyConnected_preimage_coe {T : Set ℂ} (hT : Convex ℝ T) (hne : T.Nonempty)
    (hT01 : ∀ w ∈ T, 0 < w.re ∧ w.re < 1) :
    IsSimplyConnected (((↑) : ThricePuncturedSphere → ℂ) ⁻¹' T) := by
  rw [← isOpenEmbedding_coe.isEmbedding.isSimplyConnected_image, image_coe_preimage_coe hT01]
  exact hT.isSimplyConnected hne

/-- The segment `(0, 1)` is simply connected. -/
theorem isSimplyConnected_unitSegment : IsSimplyConnected unitSegment :=
  isSimplyConnected_preimage_coe (convex_openSegment 0 1)
    ⟨1 / 2, Complex.mem_openSegment_zero_one.2 ⟨by norm_num, by norm_num, by norm_num⟩⟩
    fun _ hw => (Complex.mem_openSegment_zero_one.1 hw).2

/-- The segment `(0, 1)` is locally path connected, being homeomorphic to a convex set of `ℂ`. -/
instance : LocallyPathConnectedSpace unitSegment := by
  have := (convex_openSegment (𝕜 := ℝ) (0 : ℂ) 1).locallyPathConnectedSpace
  have hf : IsEmbedding fun z : unitSegment => ((z : ThricePuncturedSphere) : ℂ) :=
    isOpenEmbedding_coe.isEmbedding.comp IsEmbedding.subtypeVal
  have hrange : range (fun z : unitSegment => ((z : ThricePuncturedSphere) : ℂ)) =
      openSegment ℝ 0 1 := by
    refine (range_comp ((↑) : ThricePuncturedSphere → ℂ) ((↑) : unitSegment → _)).trans ?_
    rw [Subtype.range_coe]
    exact image_coe_preimage_coe fun _ hw => (Complex.mem_openSegment_zero_one.1 hw).2
  exact (hf.toHomeomorph.trans (Homeomorph.setCongr hrange)).symm.locallyPathConnectedSpace

/-- The part `(0, 1/2)` of the segment inside the punctured neighborhood of `0` is simply
connected. -/
private theorem isSimplyConnected_unitSegment_inter_puncturedNeighborhoodZero :
    IsSimplyConnected (unitSegment ∩ puncturedNeighborhoodZero) := by
  have hball : {w : ℂ | ‖w‖ < 1 / 2} = Metric.ball 0 (1 / 2) := by
    ext
    simp
  have hset : unitSegment ∩ puncturedNeighborhoodZero = (↑) ⁻¹'
      (openSegment ℝ 0 1 ∩ {w : ℂ | ‖w‖ < 1 / 2}) := by
    ext z
    rw [mem_inter_iff, mem_puncturedNeighborhoodZero]
    rfl
  rw [hset]
  refine isSimplyConnected_preimage_coe ((convex_openSegment 0 1).inter
      (hball ▸ convex_ball 0 (1 / 2)))
    ⟨1 / 4, Complex.mem_openSegment_zero_one.2 ⟨by norm_num, by norm_num, by norm_num⟩, ?_⟩
    fun _ hw => (Complex.mem_openSegment_zero_one.1 hw.1).2
  rw [mem_ofPred_eq]
  norm_num [Complex.norm_div]

/-- The part `(1/2, 1)` of the segment inside the punctured neighborhood of `1` is simply
connected. -/
private theorem isSimplyConnected_unitSegment_inter_puncturedNeighborhoodOne :
    IsSimplyConnected (unitSegment ∩ puncturedNeighborhoodOne) := by
  have hball : {w : ℂ | ‖w - 1‖ < 1 / 2} = Metric.ball 1 (1 / 2) := by
    ext
    simp [dist_eq_norm]
  have hset : unitSegment ∩ puncturedNeighborhoodOne = (↑) ⁻¹'
      (openSegment ℝ 0 1 ∩ {w : ℂ | ‖w - 1‖ < 1 / 2}) := by
    ext z
    rw [mem_inter_iff, mem_puncturedNeighborhoodOne]
    rfl
  rw [hset]
  refine isSimplyConnected_preimage_coe ((convex_openSegment 0 1).inter
      (hball ▸ convex_ball 1 (1 / 2)))
    ⟨3 / 4, Complex.mem_openSegment_zero_one.2 ⟨by norm_num, by norm_num, by norm_num⟩, ?_⟩
    fun _ hw => (Complex.mem_openSegment_zero_one.1 hw.1).2
  have h : (3 / 4 : ℂ) - 1 = -(1 / 4) := by norm_num
  rw [mem_ofPred_eq, h, norm_neg]
  norm_num [Complex.norm_div]

end ThricePuncturedSphere

/-! ### The edges are the sheets -/

variable {n : ℕ} {E : Type*} [TopologicalSpace E] {p : E → ThricePuncturedSphere}
  (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)

include hp in
/-- The preimage of the segment `(0, 1)` is locally path connected, as a cover of it. -/
private theorem locallyPathConnectedSpace_preimage_unitSegment :
    LocallyPathConnectedSpace (p ⁻¹' unitSegment) :=
  (hp.restrictPreimage unitSegment).isLocalHomeomorph.locallyPathConnectedSpace

/-- **The edges are the sheets.** The connected components of the preimage of the segment
`(0, 1)` are numbered by the sheets: since the segment is simply connected, each component
contains exactly one point of the fibre over the basepoint `1/2`, and the sheet `i` goes to the
component of the point `ν.symm i`. These components are the edges of the dessin of the cover. -/
def _root_.IsCoveringMap.finEquivConnectedComponentsUnitSegment :
    Fin n ≃ ConnectedComponents (p ⁻¹' unitSegment) :=
  haveI := locallyPathConnectedSpace_preimage_unitSegment hp
  (ν.symm.trans (hp.fiberEquivZerothHomotopy isSimplyConnected_unitSegment
    basePt_mem_unitSegment)).trans connectedComponentsEquivZerothHomotopy.symm

/-- The edge of the sheet `i` is the component of the point of the fibre that `i` numbers. -/
@[simp]
theorem _root_.IsCoveringMap.finEquivConnectedComponentsUnitSegment_apply (i : Fin n) :
    hp.finEquivConnectedComponentsUnitSegment ν i =
      ConnectedComponents.mk ⟨ν.symm i, by
        rw [mem_preimage, (ν.symm i).2]
        exact basePt_mem_unitSegment⟩ := by
  have := locallyPathConnectedSpace_preimage_unitSegment hp
  rw [IsCoveringMap.finEquivConnectedComponentsUnitSegment, Equiv.trans_apply, Equiv.trans_apply,
    hp.fiberEquivZerothHomotopy_apply, connectedComponentsEquivZerothHomotopy_symm_apply]
  -- Mathlib states the last value as the quotient class `⟦x⟧`, which is
  -- `ConnectedComponents.mk x` by definition.
  rfl

/-! ### The ends of an edge -/

section Ends

variable {S : Set ThricePuncturedSphere} {y : ThricePuncturedSphere} {α : Path basePt y}

include hp in
/-- The endpoint of the lift of a path `α` of `(0, 1)` from the point of the sheet `i` lies on the
edge of the sheet `i`. -/
private theorem finEquivConnectedComponentsUnitSegment_eq_mk (hα : ∀ t, α t ∈ unitSegment)
    (i : Fin n) (hmem : (hp.monodromy (.mk α) (ν.symm i) : E) ∈ p ⁻¹' unitSegment) :
    hp.finEquivConnectedComponentsUnitSegment ν i = ConnectedComponents.mk ⟨_, hmem⟩ := by
  rw [hp.finEquivConnectedComponentsUnitSegment_apply, ConnectedComponents.coe_eq_coe']
  exact pathComponent_subset_component _
    ((joinedIn_iff_joined hmem _).1 (hp.joinedIn_preimage_monodromy α hα (ν.symm i)).symm)

include hp in
/-- Let `α` be a path of `(0, 1)` from the basepoint to `y ∈ S`, where `(0, 1) ∩ S` is simply
connected. A point `x` over `(0, 1) ∩ S` lies in the same component of `p ⁻¹' S` as the endpoint of
the lift of `α` from the sheet of the edge through `x`. -/
private theorem mk_eq_mk_monodromy (hyS : y ∈ unitSegment ∩ S)
    (hS : IsSimplyConnected (unitSegment ∩ S)) (hα : ∀ t, α t ∈ unitSegment) {x : E}
    (hx : p x ∈ unitSegment) (hxS : p x ∈ S)
    (hmem : (hp.monodromy (.mk α) (ν.symm ((hp.finEquivConnectedComponentsUnitSegment ν).symm
      (ConnectedComponents.mk ⟨x, hx⟩))) : E) ∈ p ⁻¹' S) :
    ConnectedComponents.mk (⟨x, hxS⟩ : p ⁻¹' S) = ConnectedComponents.mk ⟨_, hmem⟩ := by
  set i := (hp.finEquivConnectedComponentsUnitSegment ν).symm (ConnectedComponents.mk ⟨x, hx⟩)
  have hseg : unitSegment ∩ S ⊆ unitSegment := inter_subset_left
  -- Join `x` inside `p ⁻¹' ((0, 1) ∩ S)` to a point `x'` of the fibre over `y`.
  obtain ⟨x', hxx'⟩ := hp.exists_joinedIn_preimage hS.isPathConnected hyS ⟨hx, hxS⟩
  -- The point `x'` is the endpoint of the lift of `α`: both lie over `y` and are joined to
  -- `ν.symm i` inside `p ⁻¹' (0, 1)`, and `(0, 1)` is simply connected.
  have hbase : (ν.symm i : E) ∈ p ⁻¹' unitSegment := by
    rw [mem_preimage, (ν.symm i).2]
    exact basePt_mem_unitSegment
  have hi : ConnectedComponents.mk (⟨ν.symm i, hbase⟩ : p ⁻¹' unitSegment) =
      ConnectedComponents.mk ⟨x, hx⟩ := by
    rw [← hp.finEquivConnectedComponentsUnitSegment_apply, Equiv.apply_symm_apply]
  have := locallyPathConnectedSpace_preimage_unitSegment hp
  rw [ConnectedComponents.coe_eq_coe', ← pathComponent_eq_connectedComponent,
    mem_pathComponent_iff, ← joinedIn_iff_joined (F := p ⁻¹' unitSegment) hx hbase] at hi
  have hjoin : JoinedIn (p ⁻¹' unitSegment) (x' : E)
      (hp.monodromy (.mk α) (ν.symm i) : E) :=
    ((hxx'.mono (preimage_mono hseg)).symm.trans hi).trans
      (hp.joinedIn_preimage_monodromy α hα (ν.symm i))
  have := isSimplyConnected_unitSegment.simplyConnectedSpace
  have hx' : x' = hp.monodromy (.mk α) (ν.symm i) := hp.eq_of_joinedIn_preimage hyS.1 hjoin
  subst hx'
  rw [ConnectedComponents.coe_eq_coe']
  exact pathComponent_subset_component _
    ((joinedIn_iff_joined hmem hxS).1 (hxx'.mono (preimage_mono inter_subset_right)).symm)

end Ends

/-! ### The black ends: the puncture `0` -/

/-- The point `1/4` lies on the segment `(0, 1)`. -/
private theorem zeroBasePt_mem_unitSegment :
    (zeroBasePt : ThricePuncturedSphere) ∈ unitSegment := by
  simp only [mem_unitSegment, coe_zeroBasePt]
  norm_num

/-- The path `αZero` from `1/2` to `1/4` runs along the segment `(0, 1)`. -/
private theorem αZero_mem_unitSegment (t : unitInterval) : αZero t ∈ unitSegment := by
  simp only [mem_unitSegment, coe_αZero, Complex.ofReal_im, Complex.ofReal_re, true_and]
  constructor <;> linarith [t.2.1, t.2.2]

/-- **The black end of an edge is the cycle of its sheet under `σ0`.** A point `x` lying both over
the segment `(0, 1)` and over the punctured neighborhood `D₀*` of `0` lies in the component of
`p ⁻¹' D₀*` of the cycle under `σ0` of the sheet numbering the edge through `x`. -/
theorem _root_.IsCoveringMap.mk_eq_sameCycleQuotientσ0EquivConnectedComponents {x : E}
    (hx : p x ∈ unitSegment) (hx0 : p x ∈ puncturedNeighborhoodZero) :
    ConnectedComponents.mk (⟨x, hx0⟩ : p ⁻¹' puncturedNeighborhoodZero) =
      hp.sameCycleQuotientσ0EquivConnectedComponents ν (Quotient.mk _
        ((hp.finEquivConnectedComponentsUnitSegment ν).symm (ConnectedComponents.mk ⟨x, hx⟩))) := by
  rw [hp.sameCycleQuotientσ0EquivConnectedComponents_mk]
  exact mk_eq_mk_monodromy hp ν ⟨zeroBasePt_mem_unitSegment, zeroBasePt.2⟩
    isSimplyConnected_unitSegment_inter_puncturedNeighborhoodZero αZero_mem_unitSegment hx hx0 _

/-- The endpoint over `1/4` of the lift of `αZero` from the sheet `i` lies on the edge of `i`. -/
theorem _root_.IsCoveringMap.finEquivConnectedComponentsUnitSegment_eq_mk_monodromy_αZero
    (i : Fin n) :
    hp.finEquivConnectedComponentsUnitSegment ν i = ConnectedComponents.mk
      ⟨hp.monodromy (.mk αZero) (ν.symm i), by
        rw [mem_preimage, (hp.monodromy (.mk αZero) (ν.symm i)).2]
        exact zeroBasePt_mem_unitSegment⟩ :=
  finEquivConnectedComponentsUnitSegment_eq_mk hp ν αZero_mem_unitSegment i _

/-- **The black incidences of the dessin.** The edge of the sheet `i` meets a component `b` of the
preimage of the punctured neighborhood `D₀*` of `0` exactly when `b` is the component of the cycle
of `i` under `σ0`, the black end of the sheet `i` in `TauCeti.PermutationTriple.ribbonGraph`. -/
theorem _root_.IsCoveringMap.exists_common_point_iff_eq_sameCycleQuotientσ0 (i : Fin n)
    (b : ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero)) :
    (∃ (x : E) (hx : p x ∈ unitSegment) (hx0 : p x ∈ puncturedNeighborhoodZero),
        ConnectedComponents.mk ⟨x, hx⟩ = hp.finEquivConnectedComponentsUnitSegment ν i ∧
          ConnectedComponents.mk ⟨x, hx0⟩ = b) ↔
      b = hp.sameCycleQuotientσ0EquivConnectedComponents ν (Quotient.mk _ i) := by
  constructor
  · rintro ⟨x, hx, hx0, hi, rfl⟩
    rw [hp.mk_eq_sameCycleQuotientσ0EquivConnectedComponents ν hx hx0, hi, Equiv.symm_apply_apply]
  · rintro rfl
    refine ⟨_, ?_, hp.monodromy_αZero_mem_preimage (ν.symm i), ?_, ?_⟩
    · rw [(hp.monodromy (.mk αZero) (ν.symm i)).2]
      exact zeroBasePt_mem_unitSegment
    · exact (hp.finEquivConnectedComponentsUnitSegment_eq_mk_monodromy_αZero ν i).symm
    · exact (hp.sameCycleQuotientσ0EquivConnectedComponents_mk ν i).symm

/-! ### The white ends: the puncture `1` -/

/-- The point `3/4` lies on the segment `(0, 1)`. -/
private theorem oneBasePt_mem_unitSegment :
    (oneBasePt : ThricePuncturedSphere) ∈ unitSegment := by
  simp only [mem_unitSegment, coe_oneBasePt]
  norm_num

/-- The path `αOne` from `1/2` to `3/4` runs along the segment `(0, 1)`. -/
private theorem αOne_mem_unitSegment (t : unitInterval) : αOne t ∈ unitSegment := by
  simp only [mem_unitSegment, coe_αOne, Complex.ofReal_im, Complex.ofReal_re, true_and]
  constructor <;> linarith [t.2.1, t.2.2]

/-- **The white end of an edge is the cycle of its sheet under `σ1`.** A point `x` lying both over
the segment `(0, 1)` and over the punctured neighborhood `D₁*` of `1` lies in the component of
`p ⁻¹' D₁*` of the cycle under `σ1` of the sheet numbering the edge through `x`. -/
theorem _root_.IsCoveringMap.mk_eq_sameCycleQuotientσ1EquivConnectedComponents {x : E}
    (hx : p x ∈ unitSegment) (hx1 : p x ∈ puncturedNeighborhoodOne) :
    ConnectedComponents.mk (⟨x, hx1⟩ : p ⁻¹' puncturedNeighborhoodOne) =
      hp.sameCycleQuotientσ1EquivConnectedComponents ν (Quotient.mk _
        ((hp.finEquivConnectedComponentsUnitSegment ν).symm (ConnectedComponents.mk ⟨x, hx⟩))) := by
  rw [hp.sameCycleQuotientσ1EquivConnectedComponents_mk]
  exact mk_eq_mk_monodromy hp ν ⟨oneBasePt_mem_unitSegment, oneBasePt.2⟩
    isSimplyConnected_unitSegment_inter_puncturedNeighborhoodOne αOne_mem_unitSegment hx hx1 _

/-- The endpoint over `3/4` of the lift of `αOne` from the sheet `i` lies on the edge of `i`. -/
theorem _root_.IsCoveringMap.finEquivConnectedComponentsUnitSegment_eq_mk_monodromy_αOne
    (i : Fin n) :
    hp.finEquivConnectedComponentsUnitSegment ν i = ConnectedComponents.mk
      ⟨hp.monodromy (.mk αOne) (ν.symm i), by
        rw [mem_preimage, (hp.monodromy (.mk αOne) (ν.symm i)).2]
        exact oneBasePt_mem_unitSegment⟩ :=
  finEquivConnectedComponentsUnitSegment_eq_mk hp ν αOne_mem_unitSegment i _

/-- **The white incidences of the dessin.** The edge of the sheet `i` meets a component `w` of the
preimage of the punctured neighborhood `D₁*` of `1` exactly when `w` is the component of the cycle
of `i` under `σ1`, the white end of the sheet `i` in `TauCeti.PermutationTriple.ribbonGraph`. -/
theorem _root_.IsCoveringMap.exists_common_point_iff_eq_sameCycleQuotientσ1 (i : Fin n)
    (w : ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne)) :
    (∃ (x : E) (hx : p x ∈ unitSegment) (hx1 : p x ∈ puncturedNeighborhoodOne),
        ConnectedComponents.mk ⟨x, hx⟩ = hp.finEquivConnectedComponentsUnitSegment ν i ∧
          ConnectedComponents.mk ⟨x, hx1⟩ = w) ↔
      w = hp.sameCycleQuotientσ1EquivConnectedComponents ν (Quotient.mk _ i) := by
  constructor
  · rintro ⟨x, hx, hx1, hi, rfl⟩
    rw [hp.mk_eq_sameCycleQuotientσ1EquivConnectedComponents ν hx hx1, hi, Equiv.symm_apply_apply]
  · rintro rfl
    refine ⟨_, ?_, hp.monodromy_αOne_mem_preimage (ν.symm i), ?_, ?_⟩
    · rw [(hp.monodromy (.mk αOne) (ν.symm i)).2]
      exact oneBasePt_mem_unitSegment
    · exact (hp.finEquivConnectedComponentsUnitSegment_eq_mk_monodromy_αOne ν i).symm
    · exact (hp.sameCycleQuotientσ1EquivConnectedComponents_mk ν i).symm

end TauCeti
