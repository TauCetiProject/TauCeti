/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Geometry.Manifold.Boundary.MapsBoundaryInto
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Bordered
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family.Chart
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Chart
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Locality
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Locality
import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic
import TauCeti.Topology.ContinuousOn.NhdsWithin

/-!
# Weak pseudoholomorphic maps from a Riemann surface with boundary

Let `X` be a Riemann surface with boundary, a charted space modelled on the closed upper
half-plane whose chart changes lie in `TauCeti.borderedHolomorphicGroupoid`, with its almost
complex structure `j = TauCeti.SmoothAlmostComplexStructure.ofBorderedHolomorphic X`. Let `M` be a
manifold modelled on a boundaryless model `I` with model vector space `E`, `J` a domain-dependent
almost complex structure on `M` of class `C^ℓ` and `ν` an inhomogeneous term for `(j, J)`. A map
`u : X → M` is *weakly pseudoholomorphic up to the boundary* on `s ⊆ X`
(`TauCeti.IsWeakPseudoholomorphicOnBordered J ν p u s`) when it lies in the local Sobolev class
`W^{1,p}_loc` up to the boundary on `s` (`TauCeti.MemWkpLocMapOnBordered`) and, in every bordered
holomorphic chart `φ` of `X` and every smooth chart `ψ` of `M`, read in the model vector space as
`ψ̂ = ψ.extendTrans I (Homeomorph.refl E)`, the coordinate expression
`ψ̂ ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm` solves the planar weak equation
`TauCeti.IsWeakCauchyRiemannOn` on the part of the extended target of `φ` over `s`. For open `s`
that part is relatively open in the closed upper half-plane, a half-disc near the real axis, so
the planar predicate takes its `Lᵖ` bounds on compact sets reaching the real axis and its weak
derivative on the interior. The structure read in the charts is `J.chartField φ ψ̂` composed with
the model inverse, and the term is `TauCeti.InhomogeneousTerm.chartTermExtend`, which reads `ν` on
the coordinate vector `∂ₛ` given by the derivative of the extended chart inverse within the
closed upper half-plane. At points of positive imaginary part this is the term
`TauCeti.InhomogeneousTerm.chartTerm` of the restricted chart
`φ ≫ₕ ClosedUpperHalfPlane.upperHalfPlaneChart`.

The predicates and their basic API follow `TauCeti.IsWeakPseudoholomorphicOn` and
`TauCeti.IsWeakPseudoholomorphic` for Riemann surfaces without boundary, with the bordered
holomorphic charts and their extensions in place of the holomorphic charts, as
`TauCeti.MemWkpLocMapOnBordered` follows `TauCeti.MemWkpLocMapOn`.

The boundary condition `u(∂X) ⊆ ι(L)` for a map `ι : L → M` is `TauCeti.MapsBoundaryInto`. The
map `ι` is a plain map: the totally real hypothesis on `ι` belongs to the theorems that use it.

## Main results

* `TauCeti.IsWeakPseudoholomorphicOnBordered`, `TauCeti.IsWeakPseudoholomorphicBordered`: the
  predicate on a set and on the whole surface, with their unfolding, monotonicity, continuity,
  structure-equality and regularity-downgrade lemmas.
* `TauCeti.isWeakPseudoholomorphicOnBordered_iff_continuousOn_isWeakCauchyRiemannOn`: continuity
  together with the coordinate equations already gives the Sobolev class.
* `TauCeti.isWeakPseudoholomorphicOnBordered_iff_locally`,
  `TauCeti.isWeakPseudoholomorphicOnBordered_iSup_iff`: it is a sheaf condition on `X`.
* `TauCeti.IsWeakPseudoholomorphicOnBordered.isWeakCauchyRiemannOn_chart_upperHalfPlaneChart`:
  in the interior, the equation is the one of `TauCeti.IsWeakPseudoholomorphicOn` for surfaces
  without boundary, read in the restricted chart with `chartField` and `chartTerm`.
* Checks: the inclusion of the closed upper half-plane into `ℂ` is weakly pseudoholomorphic and
  maps the boundary into the real line `ℝ ⊆ ℂ`, which is totally real
  (`TauCeti.isTotallyRealEmbedding_ofRealCLM`)
  (`TauCeti.isWeakPseudoholomorphicBordered_coe`, `TauCeti.mapsBoundaryInto_coe_ofReal`);
  conjugation is not weakly pseudoholomorphic on any nonempty open set
  (`TauCeti.not_isWeakPseudoholomorphicOnBordered_conj`); the constant solutions `1/(m+2)` map
  the boundary into `L = (0, 1)` but their limit `0` does not, so the closedness hypothesis of
  `TauCeti.MapsBoundaryInto.of_tendsto` is needed
  (`TauCeti.isWeakPseudoholomorphicBordered_and_tendsto_and_not_mapsBoundaryInto_zero_Ioo`).

## Implementation notes

As for `TauCeti.MemWkpLocMapOnBordered`, the charts tested are those of the maximal atlases, so
the predicate does not depend on chosen atlases; it is intended for open sets `s` and `p > 2`.
That it suffices to test one atlas of `X` near the boundary is not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1 and Appendix B.4.
-/

public section

open Set Filter TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology ComplexConjugate

noncomputable section

namespace TauCeti

/-! ### Inhomogeneous terms in extended bordered charts -/

section Extend

open ClosedUpperHalfPlane

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  [IsManifold closedUpperHalfPlaneModel ∞ X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ∞}
  {j : ContMDiffAlmostComplexStructure closedUpperHalfPlaneModel n X}
  {J : ContMDiffAlmostComplexStructureFamily I M closedUpperHalfPlaneModel X n}

/-- At a point of positive imaginary part, an inhomogeneous term on a surface modelled on the
closed upper half-plane read in the extended chart `φ.extend closedUpperHalfPlaneModel` is the
term read in the chart `φ ≫ₕ upperHalfPlaneChart` of the interior. -/
theorem InhomogeneousTerm.chartTermExtend_apply_eq_chartTerm_trans_upperHalfPlaneChart
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (ν : InhomogeneousTerm j J)
    (φ : OpenPartialHomeomorph X ClosedUpperHalfPlane) (ψ : OpenPartialHomeomorph M G)
    {z : ℂ} (hz : 0 < z.im) (v : G) :
    ν.chartTermExtend φ ψ z v = ν.chartTerm (φ ≫ₕ upperHalfPlaneChart) ψ z v := by
  refine ν.chartTermExtend_apply_eq_chartTerm_apply φ _ ψ ?_ (Eventually.of_forall fun w ↦ ?_) v
  · rw [range_closedUpperHalfPlaneModel]
    exact mem_of_superset ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)
      fun w hw ↦ le_of_lt hw
  · simp

end Extend

/-! ### The predicate -/

section Predicate

open ClosedUpperHalfPlane

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  [HasGroupoid X borderedHolomorphicGroupoid]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ℓ : ℕ∞}
  {J : ContMDiffAlmostComplexStructureFamily I M closedUpperHalfPlaneModel X ℓ}

variable (J) in
/-- **Weak pseudoholomorphic maps up to the boundary.** For a domain-dependent almost complex
structure `J` on `M`, an inhomogeneous term `ν` for `J` and the structure `j` of the Riemann
surface with boundary `X`, and an exponent `p`, a map `u : X → M` is weakly pseudoholomorphic on
`s` up to the boundary when it is in `W^{1,p}_loc` up to the boundary on `s` and, for every
bordered holomorphic chart `φ` of `X` and every smooth chart `ψ` of `M`, read in the model vector
space as `ψ̂ = ψ.extendTrans I (Homeomorph.refl E)`, the coordinate expression
`ψ̂ ∘ u ∘ (φ.extend closedUpperHalfPlaneModel)⁻¹` is a weak solution of
`∂ₛw + J_φψ(z, w) ∂ₜw = η_φψ(z, w)` on the part of the extended target of `φ` over `s` where `u`
maps into the source of `ψ`. When `s` is open, that part is relatively open in the closed upper
half-plane: the `Lᵖ` bounds reach the real axis and the weak derivative is taken in the interior.
This is `TauCeti.IsWeakPseudoholomorphicOn` with bordered holomorphic charts. Here `J_φψ` is
`ContMDiffAlmostComplexStructureFamily.chartField` composed with the model inverse and `η_φψ` is
`InhomogeneousTerm.chartTermExtend`. The definition is intended for open `s` and `p > 2`. -/
def IsWeakPseudoholomorphicOnBordered
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofBorderedHolomorphic X).toContMDiff ℓ)
      J) (p : ENNReal) (u : X → M) (s : Set X) : Prop :=
  MemWkpLocMapOnBordered I p 1 u s ∧
    ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      IsWeakCauchyRiemannOn p ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
        (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)) ∘ closedUpperHalfPlaneModel.symm)
        (ν.chartTermExtend φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)

variable (J) in
/-- **Weak pseudoholomorphic maps on a whole Riemann surface with boundary.** A map `u : X → M` is
weakly pseudoholomorphic up to the boundary for `J`, `ν` and `p` when it is in `W^{1,p}_loc` up
to the boundary and its coordinate expressions in every bordered holomorphic chart of `X` and
every smooth chart of `M` are weak solutions of the coordinate equation, as in
`IsWeakPseudoholomorphicOnBordered`. -/
def IsWeakPseudoholomorphicBordered
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofBorderedHolomorphic X).toContMDiff ℓ)
      J) (p : ENNReal) (u : X → M) : Prop :=
  MemWkpLocMapBordered I p 1 u ∧
    ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      IsWeakCauchyRiemannOn p ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source))
        (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)) ∘ closedUpperHalfPlaneModel.symm)
        (ν.chartTermExtend φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)

variable
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofBorderedHolomorphic X).toContMDiff ℓ) J}
  {p q : ENNReal} {u : X → M} {s t : Set X}

/-- Unfolding the definition of weak pseudoholomorphic maps up to the boundary on a set. -/
theorem isWeakPseudoholomorphicOnBordered_iff : IsWeakPseudoholomorphicOnBordered J ν p u s ↔
    MemWkpLocMapOnBordered I p 1 u s ∧
      ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        IsWeakCauchyRiemannOn p ((φ.extend closedUpperHalfPlaneModel).target ∩
            (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
          (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)) ∘ closedUpperHalfPlaneModel.symm)
          (ν.chartTermExtend φ (ψ.extendTrans I (Homeomorph.refl E)))
          (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) :=
  Iff.rfl

/-- Unfolding the definition of weak pseudoholomorphic maps up to the boundary. -/
theorem isWeakPseudoholomorphicBordered_iff : IsWeakPseudoholomorphicBordered J ν p u ↔
    MemWkpLocMapBordered I p 1 u ∧
      ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        IsWeakCauchyRiemannOn p ((φ.extend closedUpperHalfPlaneModel).target ∩
            (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source))
          (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)) ∘ closedUpperHalfPlaneModel.symm)
          (ν.chartTermExtend φ (ψ.extendTrans I (Homeomorph.refl E)))
          (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) :=
  Iff.rfl

/-- On the whole surface, the predicate on a set is the predicate for maps from the surface. -/
@[simp]
theorem isWeakPseudoholomorphicOnBordered_univ :
    IsWeakPseudoholomorphicOnBordered J ν p u univ ↔ IsWeakPseudoholomorphicBordered J ν p u := by
  simp only [isWeakPseudoholomorphicOnBordered_iff, isWeakPseudoholomorphicBordered_iff,
    memWkpLocMapOnGroupoid_univ, univ_inter]

namespace IsWeakPseudoholomorphicOnBordered

/-- A weak pseudoholomorphic map up to the boundary on `s` is a local Sobolev map there. -/
theorem memWkpLocMapOnBordered (h : IsWeakPseudoholomorphicOnBordered J ν p u s) :
    MemWkpLocMapOnBordered I p 1 u s :=
  h.1

/-- A weak pseudoholomorphic map up to the boundary on `s` is continuous on `s`. -/
theorem continuousOn (h : IsWeakPseudoholomorphicOnBordered J ν p u s) : ContinuousOn u s :=
  h.1.continuousOn

/-- **Reading off the coordinate equation.** In a bordered holomorphic chart `φ` and a smooth
chart `ψ`, a weak pseudoholomorphic map up to the boundary solves the planar weak equation on the
part of the extended target of `φ` over `s` where `u` maps into the source of `ψ`, which is
relatively open in the closed upper half-plane when `s` is open. -/
theorem isWeakCauchyRiemannOn_chart (h : IsWeakPseudoholomorphicOnBordered J ν p u s)
    {φ : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X)
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    IsWeakCauchyRiemannOn p ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
      (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)) ∘ closedUpperHalfPlaneModel.symm)
      (ν.chartTermExtend φ (ψ.extendTrans I (Homeomorph.refl E)))
      (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) :=
  h.2 φ hφ ψ hψ

/-- Restriction to a smaller set, in particular to an open subset, preserves weak solutions. -/
theorem mono (h : IsWeakPseudoholomorphicOnBordered J ν p u s) (hts : t ⊆ s) :
    IsWeakPseudoholomorphicOnBordered J ν p u t :=
  ⟨h.1.mono hts, fun φ hφ ψ hψ ↦ (h.2 φ hφ ψ hψ).mono
    (inter_subset_inter_right _ (preimage_mono (inter_subset_inter_left _ hts)))⟩

/-- Decreasing the exponent preserves weak solutions. -/
theorem mono_exponent (h : IsWeakPseudoholomorphicOnBordered J ν p u s) (hqp : q ≤ p) :
    IsWeakPseudoholomorphicOnBordered J ν q u s :=
  ⟨h.1.mono_exponent hqp, fun φ hφ ψ hψ ↦ (h.2 φ hφ ψ hψ).mono_exponent hqp⟩

/-- **The interior equation.** In the interior, a weak pseudoholomorphic map up to the boundary
solves the equation of `TauCeti.IsWeakPseudoholomorphicOn` for surfaces without boundary: for a
bordered holomorphic chart `φ`, its expression in the chart `φ ≫ₕ upperHalfPlaneChart` into `ℂ`,
defined on the points that `φ` sends to the open upper half-plane, solves the planar weak equation
with the structure `ContMDiffAlmostComplexStructureFamily.chartField` and the term
`InhomogeneousTerm.chartTerm` read in that chart. -/
theorem isWeakCauchyRiemannOn_chart_upperHalfPlaneChart
    (h : IsWeakPseudoholomorphicOnBordered J ν p u s)
    {φ : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X)
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    IsWeakCauchyRiemannOn p ((φ ≫ₕ upperHalfPlaneChart).target ∩
        (φ ≫ₕ upperHalfPlaneChart).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
      (J.chartField (φ ≫ₕ upperHalfPlaneChart) (ψ.extendTrans I (Homeomorph.refl E)))
      (ν.chartTerm (φ ≫ₕ upperHalfPlaneChart) (ψ.extendTrans I (Homeomorph.refl E)))
      (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ (φ ≫ₕ upperHalfPlaneChart).symm) := by
  have hsymm : (⇑(φ ≫ₕ upperHalfPlaneChart).symm : ℂ → X) =
      ⇑(φ.extend closedUpperHalfPlaneModel).symm := by
    funext z
    simp
  -- The interior chart has the same inverse, and its target lies in the open upper half-plane.
  have hsub : (φ ≫ₕ upperHalfPlaneChart).target ⊆ {z : ℂ | 0 < z.im} ∩
      (φ.extend closedUpperHalfPlaneModel).target := by
    intro z hz
    simp only [OpenPartialHomeomorph.trans_target, upperHalfPlaneChart_target,
      upperHalfPlaneChart_symm_apply, mem_inter_iff, mem_preimage, mem_ofPred_eq] at hz
    refine ⟨hz.1, ?_⟩
    rw [OpenPartialHomeomorph.extend_target, range_closedUpperHalfPlaneModel]
    exact ⟨hz.2, le_of_lt hz.1⟩
  rw [hsymm]
  have h' := (h.isWeakCauchyRiemannOn_chart hφ hψ).mono
    (inter_subset_inter_left _ fun z hz ↦ (hsub hz).2)
  refine (isWeakCauchyRiemannOn_congr_ae ?_ ?_).1 h'
  · refine Eventually.of_forall fun z ↦ ?_
    simp [ContMDiffAlmostComplexStructureFamily.chartField_apply, hsymm]
  · refine (ae_restrict_iff' measurableSet_interior).2 (Eventually.of_forall fun z hz ↦ ?_)
    exact ν.chartTermExtend_apply_eq_chartTerm_trans_upperHalfPlaneChart φ _
      (hsub (interior_subset hz).1).1 _

end IsWeakPseudoholomorphicOnBordered

namespace IsWeakPseudoholomorphicBordered

/-- A weak pseudoholomorphic map up to the boundary is a local Sobolev map up to the boundary. -/
theorem memWkpLocMapBordered (h : IsWeakPseudoholomorphicBordered J ν p u) :
    MemWkpLocMapBordered I p 1 u :=
  h.1

/-- A weak pseudoholomorphic map up to the boundary is continuous. -/
theorem continuous (h : IsWeakPseudoholomorphicBordered J ν p u) : Continuous u :=
  h.1.continuous

/-- A weak pseudoholomorphic map up to the boundary is weakly pseudoholomorphic on every set. -/
theorem isWeakPseudoholomorphicOnBordered (h : IsWeakPseudoholomorphicBordered J ν p u) :
    IsWeakPseudoholomorphicOnBordered J ν p u s :=
  (isWeakPseudoholomorphicOnBordered_univ.2 h).mono (subset_univ s)

/-- **Reading off the coordinate equation.** In a bordered holomorphic chart `φ` and a smooth
chart `ψ`, a weak pseudoholomorphic map up to the boundary solves the planar weak equation. -/
theorem isWeakCauchyRiemannOn_chart (h : IsWeakPseudoholomorphicBordered J ν p u)
    {φ : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X)
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    IsWeakCauchyRiemannOn p ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source))
      (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)) ∘ closedUpperHalfPlaneModel.symm)
      (ν.chartTermExtend φ (ψ.extendTrans I (Homeomorph.refl E)))
      (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) :=
  h.2 φ hφ ψ hψ

/-- Decreasing the exponent preserves weak solutions. -/
theorem mono_exponent (h : IsWeakPseudoholomorphicBordered J ν p u) (hqp : q ≤ p) :
    IsWeakPseudoholomorphicBordered J ν q u :=
  isWeakPseudoholomorphicOnBordered_univ.1
    ((isWeakPseudoholomorphicOnBordered_univ.2 h).mono_exponent hqp)

/-- **The interior equation.** In the interior, a weak pseudoholomorphic map up to the boundary
solves the equation of `TauCeti.IsWeakPseudoholomorphic` for surfaces without boundary, read in
the chart `φ ≫ₕ upperHalfPlaneChart` into `ℂ` with `chartField` and `chartTerm`. -/
theorem isWeakCauchyRiemannOn_chart_upperHalfPlaneChart
    (h : IsWeakPseudoholomorphicBordered J ν p u)
    {φ : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X)
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    IsWeakCauchyRiemannOn p ((φ ≫ₕ upperHalfPlaneChart).target ∩
        (φ ≫ₕ upperHalfPlaneChart).symm ⁻¹' (u ⁻¹' ψ.source))
      (J.chartField (φ ≫ₕ upperHalfPlaneChart) (ψ.extendTrans I (Homeomorph.refl E)))
      (ν.chartTerm (φ ≫ₕ upperHalfPlaneChart) (ψ.extendTrans I (Homeomorph.refl E)))
      (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ (φ ≫ₕ upperHalfPlaneChart).symm) := by
  have h' := IsWeakPseudoholomorphicOnBordered.isWeakCauchyRiemannOn_chart_upperHalfPlaneChart
    (h.isWeakPseudoholomorphicOnBordered (s := univ)) hφ hψ
  rwa [univ_inter] at h'

end IsWeakPseudoholomorphicBordered

/-- **Continuity suffices for the Sobolev class.** A map is weakly pseudoholomorphic up to the
boundary on `s` exactly when it is continuous on `s` and solves the coordinate equation in every
pair of charts: each coordinate solution is already in `W^{1,p}_loc` up to the boundary. -/
theorem isWeakPseudoholomorphicOnBordered_iff_continuousOn_isWeakCauchyRiemannOn :
    IsWeakPseudoholomorphicOnBordered J ν p u s ↔ ContinuousOn u s ∧
      ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        IsWeakCauchyRiemannOn p ((φ.extend closedUpperHalfPlaneModel).target ∩
            (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
          (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)) ∘ closedUpperHalfPlaneModel.symm)
          (ν.chartTermExtend φ (ψ.extendTrans I (Homeomorph.refl E)))
          (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘
            (φ.extend closedUpperHalfPlaneModel).symm) := by
  refine ⟨fun h ↦ ⟨h.continuousOn, h.2⟩, fun h ↦ ⟨memWkpLocMapOnGroupoid_iff.2
    ⟨h.1, fun φ hφ ψ hψ ↦ ?_⟩, h.2⟩⟩
  rw [← ψ.coe_extendTrans_refl I]
  exact (h.2 φ hφ ψ hψ).memWkpLoc_one

/-- **Continuity suffices for the Sobolev class.** A map is weakly pseudoholomorphic up to the
boundary exactly when it is continuous and solves the coordinate equation in every pair of
charts. -/
theorem isWeakPseudoholomorphicBordered_iff_continuous_isWeakCauchyRiemannOn :
    IsWeakPseudoholomorphicBordered J ν p u ↔ Continuous u ∧
      ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        IsWeakCauchyRiemannOn p ((φ.extend closedUpperHalfPlaneModel).target ∩
            (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source))
          (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)) ∘ closedUpperHalfPlaneModel.symm)
          (ν.chartTermExtend φ (ψ.extendTrans I (Homeomorph.refl E)))
          (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘
            (φ.extend closedUpperHalfPlaneModel).symm) := by
  simp only [← isWeakPseudoholomorphicOnBordered_univ,
    isWeakPseudoholomorphicOnBordered_iff_continuousOn_isWeakCauchyRiemannOn, continuousOn_univ,
    univ_inter]

/-- Replacing `J` by an equal structure `J'`, and `ν` accordingly, does not change which maps are
weakly pseudoholomorphic up to the boundary on `s`. -/
@[simp]
theorem isWeakPseudoholomorphicOnBordered_ofEq
    {J' : ContMDiffAlmostComplexStructureFamily I M closedUpperHalfPlaneModel X ℓ} (hj)
    (hJ : J = J') :
    IsWeakPseudoholomorphicOnBordered J' (ν.ofEq hj hJ) p u s ↔
      IsWeakPseudoholomorphicOnBordered J ν p u s := by
  subst hJ
  simp only [isWeakPseudoholomorphicOnBordered_iff, InhomogeneousTerm.chartTermExtend_ofEq]

/-- Replacing `J` by an equal structure `J'`, and `ν` accordingly, does not change which maps are
weakly pseudoholomorphic up to the boundary. -/
@[simp]
theorem isWeakPseudoholomorphicBordered_ofEq
    {J' : ContMDiffAlmostComplexStructureFamily I M closedUpperHalfPlaneModel X ℓ} (hj)
    (hJ : J = J') :
    IsWeakPseudoholomorphicBordered J' (ν.ofEq hj hJ) p u ↔
      IsWeakPseudoholomorphicBordered J ν p u := by
  simp only [← isWeakPseudoholomorphicOnBordered_univ, isWeakPseudoholomorphicOnBordered_ofEq]

/-- **Regularity downgrade.** Regarding a `C^ℓ` structure `J` and an inhomogeneous term `ν` for
it as `C^m`, for `m ≤ ℓ`, does not change which maps are weakly pseudoholomorphic up to the
boundary on `s`. The downgraded structure may be given as any `J'` equal to `J.ofLE hmℓ`. -/
@[simp]
theorem isWeakPseudoholomorphicOnBordered_ofLE {m : ℕ∞} (hmℓ : m ≤ ℓ)
    {J' : ContMDiffAlmostComplexStructureFamily I M closedUpperHalfPlaneModel X m} (hj)
    (hJ : J.ofLE hmℓ = J') :
    IsWeakPseudoholomorphicOnBordered J' ((ν.ofLE hmℓ).ofEq hj hJ) p u s ↔
      IsWeakPseudoholomorphicOnBordered J ν p u s := by
  subst hJ
  simp only [isWeakPseudoholomorphicOnBordered_iff,
    ContMDiffAlmostComplexStructureFamily.chartField_ofLE, InhomogeneousTerm.chartTermExtend_ofEq,
    InhomogeneousTerm.chartTermExtend_ofLE]

/-- **Regularity downgrade.** Regarding a `C^ℓ` structure `J` and an inhomogeneous term `ν` for
it as `C^m`, for `m ≤ ℓ`, does not change which maps are weakly pseudoholomorphic up to the
boundary. The downgraded structure may be given as any `J'` equal to `J.ofLE hmℓ`. -/
@[simp]
theorem isWeakPseudoholomorphicBordered_ofLE {m : ℕ∞} (hmℓ : m ≤ ℓ)
    {J' : ContMDiffAlmostComplexStructureFamily I M closedUpperHalfPlaneModel X m} (hj)
    (hJ : J.ofLE hmℓ = J') :
    IsWeakPseudoholomorphicBordered J' ((ν.ofLE hmℓ).ofEq hj hJ) p u ↔
      IsWeakPseudoholomorphicBordered J ν p u := by
  simp only [← isWeakPseudoholomorphicOnBordered_univ, isWeakPseudoholomorphicOnBordered_ofLE]

/-- **Regularity downgrade, homogeneous case.** Regarding a `C^ℓ` structure `J` as `C^m`, for
`m ≤ ℓ`, does not change which maps are weakly pseudoholomorphic up to the boundary on `s` for the
zero term. -/
@[simp]
theorem isWeakPseudoholomorphicOnBordered_zero_ofLE {m : ℕ∞} (hmℓ : m ≤ ℓ) :
    IsWeakPseudoholomorphicOnBordered (J.ofLE hmℓ) 0 p u s ↔
      IsWeakPseudoholomorphicOnBordered J 0 p u s := by
  simpa only [InhomogeneousTerm.ofLE_zero, InhomogeneousTerm.ofEq_zero] using
    isWeakPseudoholomorphicOnBordered_ofLE (J := J) (ν := 0) (p := p) (u := u) (s := s) hmℓ
      (SmoothAlmostComplexStructure.toContMDiff_ofLE _ hmℓ) rfl

/-- **Regularity downgrade, homogeneous case.** Regarding a `C^ℓ` structure `J` as `C^m`, for
`m ≤ ℓ`, does not change which maps are weakly pseudoholomorphic up to the boundary for the zero
term. -/
@[simp]
theorem isWeakPseudoholomorphicBordered_zero_ofLE {m : ℕ∞} (hmℓ : m ≤ ℓ) :
    IsWeakPseudoholomorphicBordered (J.ofLE hmℓ) 0 p u ↔
      IsWeakPseudoholomorphicBordered J 0 p u := by
  simp only [← isWeakPseudoholomorphicOnBordered_univ, isWeakPseudoholomorphicOnBordered_zero_ofLE]

/-! ### Locality -/

section Locality

variable [CompleteSpace E]

/-- **Locality.** A map is weakly pseudoholomorphic up to the boundary on `s` exactly when every
point of `s` has a neighbourhood within `s` on which it is. -/
theorem isWeakPseudoholomorphicOnBordered_iff_locally :
    IsWeakPseudoholomorphicOnBordered J ν p u s ↔
      ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, IsWeakPseudoholomorphicOnBordered J ν p u t := by
  refine ⟨fun h _ _ ↦ ⟨s, self_mem_nhdsWithin, h⟩, fun h ↦ ⟨?_, fun φ hφ ψ hψ ↦ ?_⟩⟩
  · exact memWkpLocMapOnGroupoid_iff_locally.2 fun x hx ↦
      (h x hx).imp fun _ ht ↦ ⟨ht.1, ht.2.memWkpLocMapOnBordered⟩
  · refine isWeakCauchyRiemannOn_iff_locally.2 fun z hz ↦ ?_
    obtain ⟨t, ht, hut⟩ := h _ hz.2.1
    exact ⟨_, (φ.continuousOn_extend_symm (I := closedUpperHalfPlaneModel) z
      hz.1).inter_preimage_inter_mem_nhdsWithin ht, hut.isWeakCauchyRiemannOn_chart hφ hψ⟩

/-- **Locality on the whole surface.** A map is weakly pseudoholomorphic up to the boundary
exactly when every point has a neighbourhood on which it is. -/
theorem isWeakPseudoholomorphicBordered_iff_locally :
    IsWeakPseudoholomorphicBordered J ν p u ↔
      ∀ x, ∃ t ∈ 𝓝 x, IsWeakPseudoholomorphicOnBordered J ν p u t := by
  simp [← isWeakPseudoholomorphicOnBordered_univ,
    isWeakPseudoholomorphicOnBordered_iff_locally (s := univ)]

/-- **The sheaf property.** A map is weakly pseudoholomorphic up to the boundary on a union of
open sets exactly when it is on each of them. -/
theorem isWeakPseudoholomorphicOnBordered_iSup_iff {ι : Type*} (W : ι → Opens X) :
    IsWeakPseudoholomorphicOnBordered J ν p u (⨆ i, W i : Opens X) ↔
      ∀ i, IsWeakPseudoholomorphicOnBordered J ν p u (W i) := by
  refine ⟨fun h i ↦ h.mono (SetLike.coe_subset_coe.2 (le_iSup W i)), fun h ↦ ?_⟩
  refine isWeakPseudoholomorphicOnBordered_iff_locally.2 fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := mem_iUnion.1 (by simpa only [Opens.coe_iSup] using hx)
  exact ⟨W i, mem_nhdsWithin_of_mem_nhds ((W i).isOpen.mem_nhds hi), h i⟩

end Locality

/-! ### Constant maps -/

/-- **Constant maps solve the homogeneous equation** up to the boundary on every set, for every
domain-dependent structure. -/
@[simp]
theorem isWeakPseudoholomorphicOnBordered_const [CompleteSpace E] (y : M) :
    IsWeakPseudoholomorphicOnBordered J 0 p (fun _ ↦ y) s := by
  refine ⟨(contMDiff_const.memWkpLocMapBordered (k := 1) (n := ∞) (by simp)).memWkpLocMapOnGroupoid,
    fun φ _ ψ _ ↦ ?_⟩
  rw [InhomogeneousTerm.chartTermExtend_zero]
  exact isWeakCauchyRiemannOn_const (ψ.extendTrans I (Homeomorph.refl E) y)

/-- **Constant maps solve the homogeneous equation** up to the boundary, for every
domain-dependent structure. -/
@[simp]
theorem isWeakPseudoholomorphicBordered_const [CompleteSpace E] (y : M) :
    IsWeakPseudoholomorphicBordered J 0 p (fun _ ↦ y) :=
  isWeakPseudoholomorphicOnBordered_univ.1 (isWeakPseudoholomorphicOnBordered_const y)

end Predicate

/-! ### Checks on the closed upper half-plane -/

section Checks

open ClosedUpperHalfPlane

/-- **The boundary of the closed upper half-plane is the real line.** The inclusion of the closed
upper half-plane into `ℂ` maps the boundary into the real line `ℝ ⊆ ℂ`, which is totally real
(`TauCeti.isTotallyRealEmbedding_ofRealCLM`). -/
theorem mapsBoundaryInto_coe_ofReal :
    MapsBoundaryInto closedUpperHalfPlaneModel ((↑) : ClosedUpperHalfPlane → ℂ)
      ((↑) : ℝ → ℂ) := mapsBoundaryInto_iff.2 fun z hz ↦ by
  have h : (z : ℂ).im = 0 := (closedUpperHalfPlaneModel_isBoundaryPoint_iff z).1 hz
  exact ⟨(z : ℂ).re, by simp [Complex.ext_iff, h]⟩

variable {ℓ : ℕ∞} {p : ENNReal}

/-- The inverse of a bordered holomorphic chart of the closed upper half-plane, read in `ℂ`, is
complex smooth at the points of positive imaginary part of the target. -/
private theorem contDiffOn_coe_comp_extend_symm
    {φ : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas ClosedUpperHalfPlane) :
    ContDiffOn ℂ 1 (((↑) : ClosedUpperHalfPlane → ℂ) ∘ (φ.extend closedUpperHalfPlaneModel).symm)
      (closedUpperHalfPlaneModel.symm ⁻¹' φ.target ∩ {z : ℂ | 0 < z.im}) := by
  have hφs : φ.symm ∈ borderedHolomorphicGroupoid := by
    have h := (hφ _ (chart_mem_atlas ClosedUpperHalfPlane (ofReal 0))).1
    simpa only [chartAt_self_eq, OpenPartialHomeomorph.trans_refl] using h
  have hdiff := (mem_borderedHolomorphicGroupoid_iff.1 hφs).2.1
  rw [OpenPartialHomeomorph.symm_source] at hdiff
  have hg : ((↑) : ClosedUpperHalfPlane → ℂ) ∘ (φ.extend closedUpperHalfPlaneModel).symm =
      closedUpperHalfPlaneModel ∘ φ.symm ∘ closedUpperHalfPlaneModel.symm := by
    funext z
    simp
  rw [hg]
  exact hdiff.contDiffOn ((φ.open_target.preimage closedUpperHalfPlaneModel.continuous_symm).inter
    (isOpen_lt continuous_const Complex.continuous_im))

/-- **The inclusion is a solution.** The inclusion of the closed upper half-plane into `ℂ` is
weakly pseudoholomorphic up to the boundary for the complex structure of `ℂ` and `ν = 0`, for
every exponent. -/
theorem isWeakPseudoholomorphicBordered_coe :
    IsWeakPseudoholomorphicBordered (ContMDiffAlmostComplexStructureFamily.const
      ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ)) 0 p
        ((↑) : ClosedUpperHalfPlane → ℂ) := by
  have hu : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ, ℂ) ∞ ((↑) : ClosedUpperHalfPlane → ℂ) := by
    have h := closedUpperHalfPlaneModel.contMDiff (n := ∞)
    have he : (closedUpperHalfPlaneModel : ClosedUpperHalfPlane → ℂ) = (↑) :=
      funext closedUpperHalfPlaneModel_apply
    rwa [he] at h
  have hM : MemWkpLocMapBordered 𝓘(ℝ, ℂ) p 1 ((↑) : ClosedUpperHalfPlane → ℂ) :=
    hu.memWkpLocMapBordered (by simp)
  refine ⟨hM, fun φ hφ ψ hψ ↦ ?_⟩
  set U := (φ.extend closedUpperHalfPlaneModel).target ∩
    (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (((↑) : ClosedUpperHalfPlane → ℂ) ⁻¹' ψ.source)
  have hw := hM.memWkpLoc_chart hφ hψ
  rw [← ψ.coe_extendTrans_refl 𝓘(ℝ, ℂ)] at hw
  rw [OpenPartialHomeomorph.extendTrans_modelWithCornersSelf_refl] at hw ⊢
  set g : ℂ → ℂ := (↑) ∘ (φ.extend closedUpperHalfPlaneModel).symm
  set D := closedUpperHalfPlaneModel.symm ⁻¹' φ.target ∩ {z : ℂ | 0 < z.im}
  have hD : IsOpen D := (φ.open_target.preimage closedUpperHalfPlaneModel.continuous_symm).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  -- The interior of the half-disc `U` lies in the open upper half-plane, where `g` is holomorphic.
  have hint : interior U ⊆ D ∩ g ⁻¹' ψ.source := by
    intro z hz
    have hzr : z ∈ interior (range closedUpperHalfPlaneModel) :=
      interior_mono (fun w hw ↦ by
        have hw' := hw.1
        rw [OpenPartialHomeomorph.extend_target] at hw'
        exact hw'.2) hz
    rw [range_closedUpperHalfPlaneModel, Complex.interior_setOfPred_le_im] at hzr
    obtain ⟨hzt, hzψ⟩ := interior_subset hz
    rw [OpenPartialHomeomorph.extend_target] at hzt
    exact ⟨⟨hzt.1, hzr⟩, hzψ⟩
  have hgc := contDiffOn_coe_comp_extend_symm hφ
  have hcont : ContinuousOn (ψ ∘ g) U :=
    ψ.continuousOn.comp (continuous_subtypeVal.comp_continuousOn
      (φ.continuousOn_extend_symm.mono inter_subset_left)) fun _ hz ↦ hz.2
  refine isWeakCauchyRiemannOn_iff_continuousOn_memWkpLoc_interior.2 ⟨hcont, hw, ?_⟩
  rw [ContMDiffAlmostComplexStructureFamily.chartField_const,
    InhomogeneousTerm.chartTermExtend_zero]
  -- In the interior, `g` is a holomorphic map on the open set `D` of the Riemann surface `ℂ`.
  have hP := ((hgc.differentiableOn one_ne_zero).mdifferentiableOn.isWeakPseudoholomorphicOn
    (ℓ := ℓ) (p := p) hD).isWeakCauchyRiemannOn_chart
    (StructureGroupoid.id_mem_maximalAtlas _) hψ
  rw [OpenPartialHomeomorph.extendTrans_modelWithCornersSelf_refl,
    ContMDiffAlmostComplexStructureFamily.chartField_const, InhomogeneousTerm.chartTerm_zero] at hP
  exact hP.mono fun z hz ↦ by simpa [D, g] using hint hz

/-- **Conjugation is not a solution.** The map `z ↦ conj z` from the closed upper half-plane to
`ℂ` is not weakly pseudoholomorphic up to the boundary, for the complex structure of `ℂ` and
`ν = 0`, on any nonempty open set. -/
theorem not_isWeakPseudoholomorphicOnBordered_conj {s : Set ClosedUpperHalfPlane} (hs : IsOpen s)
    (hne : s.Nonempty) :
    ¬IsWeakPseudoholomorphicOnBordered (ContMDiffAlmostComplexStructureFamily.const
      ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ)) 0 p
        (fun z : ClosedUpperHalfPlane ↦ conj (z : ℂ)) s := by
  intro h
  -- Read the equation in the identity charts and restrict it to the open upper half-plane.
  have h' := h.isWeakCauchyRiemannOn_chart (StructureGroupoid.id_mem_maximalAtlas _)
    (StructureGroupoid.id_mem_maximalAtlas _)
  set Ω : Set ℂ := {z : ℂ | 0 < z.im} ∩ closedUpperHalfPlaneModel.symm ⁻¹' s
  have hΩ : IsOpen Ω := (isOpen_lt continuous_const Complex.continuous_im).inter
    (hs.preimage closedUpperHalfPlaneModel.continuous_symm)
  have hΩU : Ω ⊆ ((OpenPartialHomeomorph.refl ClosedUpperHalfPlane).extend
      closedUpperHalfPlaneModel).target ∩
      ((OpenPartialHomeomorph.refl ClosedUpperHalfPlane).extend closedUpperHalfPlaneModel).symm ⁻¹'
        (s ∩ (fun z : ClosedUpperHalfPlane ↦ conj (z : ℂ)) ⁻¹'
          (OpenPartialHomeomorph.refl ℂ).source) := fun z hz ↦ by
    refine ⟨?_, ?_⟩
    · simp only [OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.refl_target,
        preimage_univ, univ_inter, range_closedUpperHalfPlaneModel, mem_ofPred_eq]
      exact le_of_lt hz.1
    · simpa [OpenPartialHomeomorph.extend_coe_symm] using hz.2
  have h2 := h'.mono hΩU
  rw [OpenPartialHomeomorph.extendTrans_modelWithCornersSelf_refl,
    ContMDiffAlmostComplexStructureFamily.chartField_const,
    ContMDiffAlmostComplexStructure.chartPushforward_refl,
    InhomogeneousTerm.chartTermExtend_zero] at h2
  have hEq : EqOn ((OpenPartialHomeomorph.refl ℂ) ∘ (fun z : ClosedUpperHalfPlane ↦ conj (z : ℂ)) ∘
      ((OpenPartialHomeomorph.refl ClosedUpperHalfPlane).extend closedUpperHalfPlaneModel).symm)
      conj Ω := fun z hz ↦ by
    simp [
      coe_closedUpperHalfPlaneModel_symm_of_im_nonneg (le_of_lt hz.1)]
  have h3 := (isWeakCauchyRiemannOn_congr hEq).1 h2
  have hJ : ∀ v : ℂ, ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff
      ℓ).toEndomorphism v = Complex.I • ContinuousLinearMap.id ℝ ℂ := fun v ↦ by
    rw [SmoothAlmostComplexStructure.toContMDiff_toEndomorphism_apply,
      SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold]
  simp only [Function.comp_def, hJ] at h3
  -- A nonempty open set contains points `fold (z₀ + t i)` with `t > 0` small.
  obtain ⟨z, hzs, hz⟩ : ∃ z ∈ s, 0 < (z : ℂ).im := by
    obtain ⟨z₀, hz₀⟩ := hne
    have hc : Continuous fun t : ℝ ↦ fold ((z₀ : ℂ) + t * Complex.I) :=
      continuous_fold.comp (by fun_prop)
    have h0 : fold ((z₀ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = z₀ := by simp
    have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, fold ((z₀ : ℂ) + t * Complex.I) ∈ s :=
      nhdsWithin_le_nhds ((hc.continuousAt (x := 0)).preimage_mem_nhds
        (by rw [h0]; exact hs.mem_nhds hz₀))
    obtain ⟨t, hts, ht⟩ := (hev.and self_mem_nhdsWithin).exists
    refine ⟨_, hts, ?_⟩
    rw [im_fold]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    exact abs_pos_of_pos (add_pos_of_nonneg_of_pos (im_nonneg z₀) ht)
  exact not_isWeakCauchyRiemannOn_conj (Ω := ⟨Ω, hΩ⟩) ⟨z, hz, by simpa using hzs⟩ h3

/-- **The limit of boundary conditions can leave `L`.** For `L = (0, 1) ⊆ ℝ ⊆ ℂ`, whose image is
not closed, the constant maps `1/(m+2)` on the closed upper half-plane solve the homogeneous
equation and map the boundary into `L`, but their limit, the constant map `0`, does not. So the
closedness hypothesis of `TauCeti.MapsBoundaryInto.of_tendsto` cannot be dropped. -/
theorem isWeakPseudoholomorphicBordered_and_tendsto_and_not_mapsBoundaryInto_zero_Ioo :
    (∀ m : ℕ, IsWeakPseudoholomorphicBordered (ContMDiffAlmostComplexStructureFamily.const
      ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ)) 0 p
        (fun _ : ClosedUpperHalfPlane ↦ ((1 / (m + 2) : ℝ) : ℂ)) ∧
      MapsBoundaryInto closedUpperHalfPlaneModel
        (fun _ : ClosedUpperHalfPlane ↦ ((1 / (m + 2) : ℝ) : ℂ))
        (fun t : Ioo (0 : ℝ) 1 ↦ ((t : ℝ) : ℂ))) ∧
      Tendsto (fun m : ℕ ↦ ((1 / (m + 2) : ℝ) : ℂ)) atTop (𝓝 0) ∧
      ¬MapsBoundaryInto closedUpperHalfPlaneModel (fun _ : ClosedUpperHalfPlane ↦ (0 : ℂ))
        (fun t : Ioo (0 : ℝ) 1 ↦ ((t : ℝ) : ℂ)) := by
  refine ⟨fun m ↦ ⟨isWeakPseudoholomorphicBordered_const _,
    mapsBoundaryInto_const ⟨⟨1 / (m + 2), by positivity, ?_⟩, rfl⟩⟩, ?_, ?_⟩
  · rw [div_lt_one (by positivity)]
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  · have h : Tendsto (fun m : ℕ ↦ (1 : ℝ) / (m + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp h
    rw [Complex.ofReal_zero] at h2
    exact h2
  · intro h
    have hb : closedUpperHalfPlaneModel.IsBoundaryPoint (ofReal 0) :=
      (closedUpperHalfPlaneModel_isBoundaryPoint_iff _).2 (by simp [coe_ofReal])
    obtain ⟨y, hy⟩ := h.mem_range hb
    exact y.property.1.ne' (Complex.ofReal_eq_zero.1 hy)

end Checks

end TauCeti
