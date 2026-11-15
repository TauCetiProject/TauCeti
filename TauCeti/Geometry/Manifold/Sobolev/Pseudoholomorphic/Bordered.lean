/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Complex.TotallyReal.Basic
public import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Bordered
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family.Chart
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Chart
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Locality
import TauCeti.Analysis.Sobolev.Local.HalfPlane
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Locality
import TauCeti.LinearAlgebra.TotallyReal.Complex
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
holomorphic chart `φ` of `X` and every chart `ψ` of `M`, the coordinate expression
`ψ̂ ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm` solves the planar weak equation
`TauCeti.IsWeakCauchyRiemannOn` on the part of the extended target of `φ` over `s`. That part is
relatively open in the closed upper half-plane, so the planar predicate takes its `Lᵖ` bounds on
compact sets reaching the real axis and its weak derivative on the interior, as in the README's
half-disc form. The structure read in the charts is `J.chartField φ ψ̂` composed with the model
inverse, and the term is `TauCeti.InhomogeneousTerm.chartTermExtend`, which reads `ν` on the
coordinate vector `∂ₛ` given by the derivative of the extended chart inverse within the closed
upper half-plane. At points of positive imaginary part this is the term
`TauCeti.InhomogeneousTerm.chartTerm` of the restricted chart
`φ ≫ₕ ClosedUpperHalfPlane.upperHalfPlaneChart`.

For a map `ι : L → M`, the predicate `TauCeti.MapsBoundaryInto IX u ι` says that `u` sends the
manifold boundary of `X` into the image of `ι`, the boundary condition `u(∂X) ⊆ ι(L)`. The map
`ι` is a plain map: the totally real hypothesis on `ι` belongs to the theorems that use it.

## Main results

* `TauCeti.InhomogeneousTerm.chartTermExtend`: an inhomogeneous term read in an extended chart of
  a domain modelled on `ℂ` with corners, with
  `TauCeti.InhomogeneousTerm.chartTermExtend_apply_eq_chartTerm_apply` comparing it with
  `chartTerm` at interior points.
* `TauCeti.IsWeakPseudoholomorphicOnBordered`, `TauCeti.IsWeakPseudoholomorphicBordered`: the
  predicate on a set and on the whole surface, with their unfolding, monotonicity and continuity
  lemmas.
* `TauCeti.isWeakPseudoholomorphicOnBordered_iff_continuousOn`: continuity together with the
  coordinate equations already gives the Sobolev class.
* `TauCeti.isWeakPseudoholomorphicOnBordered_iff_locally`,
  `TauCeti.isWeakPseudoholomorphicOnBordered_iSup_iff`: it is a sheaf condition on `X`.
* `TauCeti.IsWeakPseudoholomorphicOnBordered.isWeakCauchyRiemannOn_chart_upperHalfPlaneChart`:
  in the interior, the equation is the one for surfaces without boundary, read in the restricted
  chart with `chartField` and `chartTerm`.
* `TauCeti.MapsBoundaryInto`, with `TauCeti.MapsBoundaryInto.of_tendsto` (closedness under
  pointwise limits when `range ι` is closed) and `TauCeti.MapsBoundaryInto.of_dense` (it suffices
  to check a dense subset of the boundary for continuous `u`).
* Checks: the inclusion of the closed upper half-plane into `ℂ` is weakly pseudoholomorphic and
  maps the boundary into the totally real line `ℝ ⊆ ℂ`
  (`TauCeti.isWeakPseudoholomorphicBordered_coe`, `TauCeti.mapsBoundaryInto_coe_ofReal`,
  `TauCeti.isTotallyRealEmbedding_ofRealCLM`); conjugation is not weakly pseudoholomorphic
  (`TauCeti.not_isWeakPseudoholomorphicOnBordered_conj`); the constant solutions `1/(m+2)` map
  the boundary into `L = (0, 1)` but their limit `0` does not, so the closedness hypothesis of
  `of_tendsto` is needed (`TauCeti.not_mapsBoundaryInto_limit_Ioo`).

## Implementation notes

As for `TauCeti.MemWkpLocMapOnBordered`, the charts tested are those of the maximal atlases, so
the predicate does not depend on chosen atlases; it is intended for open sets `s` and `p > 2`.
That it suffices to test one atlas of `X` near the boundary is not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Sections 2.4, 3.1 and Appendix B.4.
-/

public section

open Set Filter TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology ComplexConjugate

noncomputable section

namespace TauCeti

/-! ### The planar equation on a set and on its interior -/

section Planar

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {p : ENNReal} {U : Set ℂ}
  {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V}

/-- **The equation on a half-disc.** The weak equation holds on a set `U`, such as a half-disc
relatively open in the closed upper half-plane, exactly when `u` is continuous on `U`, lies in
`W^{1,p}_loc` of `U` with `Lᵖ` bounds up to the boundary of `U`, and solves the weak equation on
the interior of `U`. -/
theorem isWeakCauchyRiemannOn_iff_interior : IsWeakCauchyRiemannOn p U J η u ↔
    ContinuousOn u U ∧ MemWkpLoc p U 1 u ∧ IsWeakCauchyRiemannOn p (interior U) J η u := by
  refine ⟨fun h ↦ ⟨h.continuousOn, h.memWkpLoc_one, h.mono interior_subset⟩,
    fun ⟨hc, hw, h⟩ ↦ isWeakCauchyRiemannOn_iff_forall_hasWeakFDerivOn.2 ⟨hc, hw, fun D hD ↦ ?_⟩⟩
  have hO : Opens.interior (interior U) = Opens.interior U := Opens.ext interior_interior
  simpa only [interior_interior] using h.ae_eq_of_hasWeakFDerivOn (D := D) (hO ▸ hD)

end Planar

/-! ### Inhomogeneous terms in extended charts -/

namespace InhomogeneousTerm

variable {E H M HP P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace HP] {IP : ModelWithCorners ℝ ℂ HP} [TopologicalSpace P] [ChartedSpace HP P]
  [IsManifold IP ∞ P] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ∞}
  {j : ContMDiffAlmostComplexStructure IP n P}
  {J : ContMDiffAlmostComplexStructureFamily I M IP P n}

/-- An inhomogeneous term read in an extended chart `φ.extend IP` of a domain `P` modelled on `ℂ`,
possibly with corners, and a chart `ψ` of `M` with values in a normed space `G`: at `(z, v)`,
twice the value of `ν((φ.extend IP)⁻¹ z, ψ⁻¹ v)` on the coordinate vector `∂ₛ`, the image of `1`
under the derivative of `(φ.extend IP)⁻¹` within the range of the model, pushed forward along `ψ`.
At points of the interior of the range it is `chartTerm` for any chart into `ℂ` with the same
inverse near the point (`chartTermExtend_apply_eq_chartTerm_apply`). -/
def chartTermExtend (ν : InhomogeneousTerm j J) (φ : OpenPartialHomeomorph P HP)
    (ψ : OpenPartialHomeomorph M G) (z : ℂ) (v : G) : G :=
  (2 : ℝ) • mvfderiv I ψ (ψ.symm v)
    (ν.val.tangentHom ((φ.extend IP).symm z, ψ.symm v)
      (mfderivWithin 𝓘(ℝ, ℂ) IP (φ.extend IP).symm (range IP) z (1 : ℂ)))

/-- Evaluate an inhomogeneous term read in an extended chart. -/
theorem chartTermExtend_apply (ν : InhomogeneousTerm j J) (φ : OpenPartialHomeomorph P HP)
    (ψ : OpenPartialHomeomorph M G) (z : ℂ) (v : G) :
    ν.chartTermExtend φ ψ z v = (2 : ℝ) • mvfderiv I ψ (ψ.symm v)
      (ν.val.tangentHom ((φ.extend IP).symm z, ψ.symm v)
        (mfderivWithin 𝓘(ℝ, ℂ) IP (φ.extend IP).symm (range IP) z (1 : ℂ))) :=
  (rfl)

/-- The zero inhomogeneous term reads as zero in all extended charts. -/
@[simp]
theorem chartTermExtend_zero (φ : OpenPartialHomeomorph P HP) (ψ : OpenPartialHomeomorph M G) :
    (0 : InhomogeneousTerm j J).chartTermExtend φ ψ = fun _ _ ↦ 0 := by
  funext z v
  simp only [chartTermExtend_apply, ZeroMemClass.coe_zero,
    DomainDependentHomSection.tangentHom_zero, smul_eq_zero, OfNat.ofNat_ne_zero, false_or]
  -- The zero term vanishes on every tangent vector, whose type is only definitionally that of
  -- the tangent space of the point.
  exact map_zero _

/-- **Comparison at interior points.** At a point `z` in the interior of the range of the model,
an inhomogeneous term read in the extended chart `φ.extend IP` is the term read by `chartTerm` in
any chart `φ'` into `ℂ` whose inverse agrees with `(φ.extend IP)⁻¹` near `z`. -/
theorem chartTermExtend_apply_eq_chartTerm_apply (ν : InhomogeneousTerm j J)
    (φ : OpenPartialHomeomorph P HP) (φ' : OpenPartialHomeomorph P ℂ)
    (ψ : OpenPartialHomeomorph M G) {z : ℂ} (hz : range IP ∈ 𝓝 z)
    (hφ : φ'.symm =ᶠ[𝓝 z] (φ.extend IP).symm) (v : G) :
    ν.chartTermExtend φ ψ z v = ν.chartTerm φ' ψ z v := by
  rw [chartTermExtend_apply, chartTerm_apply, mfderivWithin_of_mem_nhds hz, hφ.mfderiv_eq,
    hφ.eq_of_nhds]
  -- The cast between tangent spaces at the same point is the identity.
  rfl

end InhomogeneousTerm

/-! ### The predicate -/

section Predicate

open ClosedUpperHalfPlane

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  [HasGroupoid X borderedHolomorphicGroupoid]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ℓ : ℕ∞}
  {J : ContMDiffAlmostComplexStructureFamily I M closedUpperHalfPlaneModel X ℓ}

omit [I.Boundaryless] in
/-- At a point of positive imaginary part, an inhomogeneous term on a Riemann surface with
boundary read in the extended chart `φ.extend closedUpperHalfPlaneModel` is the term read in the
chart `φ ≫ₕ upperHalfPlaneChart` of the interior. -/
theorem InhomogeneousTerm.chartTermExtend_apply_eq_chartTerm_trans_upperHalfPlaneChart
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofBorderedHolomorphic X).toContMDiff ℓ)
      J) (φ : OpenPartialHomeomorph X ClosedUpperHalfPlane) (ψ : OpenPartialHomeomorph M G)
    {z : ℂ} (hz : 0 < z.im) (v : G) :
    ν.chartTermExtend φ ψ z v = ν.chartTerm (φ ≫ₕ upperHalfPlaneChart) ψ z v := by
  refine ν.chartTermExtend_apply_eq_chartTerm_apply φ _ ψ ?_ (Eventually.of_forall fun w ↦ ?_) v
  · rw [range_closedUpperHalfPlaneModel]
    exact mem_of_superset ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)
      fun w hw ↦ le_of_lt hw
  · simp

variable (J) in
/-- **Weak pseudoholomorphic maps up to the boundary.** For a domain-dependent almost complex
structure `J` on `M`, an inhomogeneous term `ν` for `J` and the structure `j` of the Riemann
surface with boundary `X`, and an exponent `p`, a map `u : X → M` is weakly pseudoholomorphic on
`s` up to the boundary when it is in `W^{1,p}_loc` up to the boundary on `s` and, for every
bordered holomorphic chart `φ` of `X` and every smooth chart `ψ` of `M`, read in the model vector
space as `ψ̂ = ψ.extendTrans I (Homeomorph.refl E)`, the coordinate expression
`ψ̂ ∘ u ∘ (φ.extend closedUpperHalfPlaneModel)⁻¹` is a weak solution of
`∂ₛw + J_φψ(z, w) ∂ₜw = η_φψ(z, w)` on the part of the extended target of `φ` over `s` where `u`
maps into the source of `ψ`. That part is relatively open in the closed upper half-plane: the
`Lᵖ` bounds reach the real axis and the weak derivative is taken in the interior. Here `J_φψ` is
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
chart `ψ`, a weak pseudoholomorphic map up to the boundary solves the planar weak equation on a
relatively open subset of the closed upper half-plane. -/
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
solves the equation for surfaces without boundary: for a bordered holomorphic chart `φ`, its
expression in the chart `φ ≫ₕ upperHalfPlaneChart` into `ℂ`, defined on the points that `φ` sends
to the open upper half-plane, solves the planar weak equation with the structure
`ContMDiffAlmostComplexStructureFamily.chartField` and the term `InhomogeneousTerm.chartTerm` read
in that chart. -/
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

end IsWeakPseudoholomorphicBordered

/-- **Continuity suffices for the Sobolev class.** A map is weakly pseudoholomorphic up to the
boundary on `s` exactly when it is continuous on `s` and solves the coordinate equation in every
pair of charts: each coordinate solution is already in `W^{1,p}_loc` up to the boundary. -/
theorem isWeakPseudoholomorphicOnBordered_iff_continuousOn :
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
theorem isWeakPseudoholomorphicBordered_iff_continuous :
    IsWeakPseudoholomorphicBordered J ν p u ↔ Continuous u ∧
      ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        IsWeakCauchyRiemannOn p ((φ.extend closedUpperHalfPlaneModel).target ∩
            (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source))
          (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)) ∘ closedUpperHalfPlaneModel.symm)
          (ν.chartTermExtend φ (ψ.extendTrans I (Homeomorph.refl E)))
          (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘
            (φ.extend closedUpperHalfPlaneModel).symm) := by
  simp only [← isWeakPseudoholomorphicOnBordered_univ,
    isWeakPseudoholomorphicOnBordered_iff_continuousOn, continuousOn_univ, univ_inter]

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

/-! ### Boundary conditions -/

section Boundary

variable {HX EX : Type*} [TopologicalSpace HX] [NormedAddCommGroup EX] [NormedSpace ℝ EX]
  {X : Type*} [TopologicalSpace X] [ChartedSpace HX X] {M : Type*} {L L' : Type*}

variable (IX : ModelWithCorners ℝ EX HX) in
/-- **Maps the boundary into `L`.** A map `u : X → M` maps the boundary into `L` along
`ι : L → M` when it sends every point of the manifold boundary of `X`, for the model `IX`, into
the image of `ι`: the boundary condition `u(∂X) ⊆ ι(L)`. For continuous `u` this is a pointwise
condition on the boundary, and it suffices to check it on a dense subset
(`TauCeti.MapsBoundaryInto.of_dense`). The map `ι` is arbitrary here; in applications it is a
totally real embedding, an assumption made by the theorems that use it. -/
def MapsBoundaryInto (u : X → M) (ι : L → M) : Prop :=
  MapsTo u (IX.boundary X) (range ι)

variable {IX : ModelWithCorners ℝ EX HX} {u : X → M} {ι : L → M} {ι' : L' → M}

/-- Unfolding the boundary condition. -/
theorem mapsBoundaryInto_iff :
    MapsBoundaryInto IX u ι ↔ ∀ x, IX.IsBoundaryPoint x → ∃ y, ι y = u x :=
  Iff.rfl

/-- On a manifold without boundary, every map satisfies every boundary condition. -/
@[simp]
theorem mapsBoundaryInto_of_boundaryless [BoundarylessManifold IX X] :
    MapsBoundaryInto IX u ι := fun x hx ↦ by
  rw [ModelWithCorners.Boundaryless.boundary_eq_empty] at hx
  exact hx.elim

namespace MapsBoundaryInto

/-- A boundary condition into `L` implies one into any `L'` whose image contains that of `L`. -/
theorem mono (h : MapsBoundaryInto IX u ι) (hι : range ι ⊆ range ι') : MapsBoundaryInto IX u ι' :=
  h.mono_right hι

/-- **Closedness under pointwise limits.** If `range ι` is closed, a pointwise limit of maps that
eventually map the boundary into `L` maps the boundary into `L`. -/
theorem of_tendsto [TopologicalSpace M] {α : Type*} {l : Filter α} [l.NeBot] {F : α → X → M}
    (hι : IsClosed (range ι))
    (h : ∀ᶠ n in l, MapsBoundaryInto IX (F n) ι)
    (hlim : ∀ x, IX.IsBoundaryPoint x → Tendsto (fun n ↦ F n x) l (𝓝 (u x))) :
    MapsBoundaryInto IX u ι := fun x hx ↦
  hι.mem_of_tendsto (hlim x hx) (h.mono fun _ hn ↦ hn hx)

/-- **The dense-subset criterion.** If `range ι` is closed and `u` is continuous on the
boundary, it suffices that `u` maps a subset `D` of the boundary, dense in the boundary, into
`ι(L)`. -/
theorem of_dense [TopologicalSpace M] {D : Set X} (hι : IsClosed (range ι))
    (hu : ContinuousOn u (IX.boundary X))
    (hD : D ⊆ IX.boundary X) (hdense : IX.boundary X ⊆ closure D) (h : MapsTo u D (range ι)) :
    MapsBoundaryInto IX u ι := fun x hx ↦
  hι.closure_subset_iff.2 h.image_subset
    (((hu x hx).mono hD).mem_closure_image (hdense hx))

end MapsBoundaryInto

end Boundary

/-! ### Checks on the closed upper half-plane -/

section Checks

open ClosedUpperHalfPlane

/-- The real line is a totally real embedding into `ℂ` for the standard complex structure, for
every regularity. -/
theorem isTotallyRealEmbedding_ofRealCLM (n : ℕ∞ω) :
    IsTotallyRealEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) n
      (AlmostComplexStructure.ofComplexModule ℂ).constSmooth.almostComplexStructureAt
      Complex.ofRealCLM := by
  rw [ContinuousLinearMap.isTotallyRealEmbedding_iff]
  refine ⟨by simp, ?_⟩
  have hJ : (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap =
      (LinearMap.lsmul ℂ ℂ Complex.I).restrictScalars ℝ := by
    ext v
    simp [AlmostComplexStructure.ofComplexModule_apply]
  have hr : LinearMap.range Complex.ofRealCLM.toLinearMap = Submodule.span ℝ {(1 : ℂ)} := by
    ext v
    simp [Submodule.mem_span_singleton, Complex.real_smul]
  rw [hJ, hr]
  exact isMaximalTotallyReal_span_one

/-- **The boundary of the closed upper half-plane is the real line.** The inclusion of the closed
upper half-plane into `ℂ` maps the boundary into the totally real line `ℝ ⊆ ℂ`. -/
theorem mapsBoundaryInto_coe_ofReal :
    MapsBoundaryInto closedUpperHalfPlaneModel ((↑) : ClosedUpperHalfPlane → ℂ)
      ((↑) : ℝ → ℂ) := fun z hz ↦ by
  have h : (z : ℂ).im = 0 := (closedUpperHalfPlaneModel_isBoundaryPoint_iff z).1 hz
  exact ⟨(z : ℂ).re, by simp [Complex.ext_iff, h]⟩

variable {ℓ : ℕ∞} {p : ENNReal}

/-- A complex differentiable map `g : ℂ → ℂ`, read through a smooth chart `ψ` of `ℂ`, satisfies
the chart equation for the complex structure of `ℂ` at `z`. -/
private theorem fderiv_chart_comp_add_eq_zero_of_differentiableAt {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) {ψ : OpenPartialHomeomorph ℂ ℂ}
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ ℂ) (hgz : g z ∈ ψ.source) :
    fderiv ℝ (ψ ∘ g) z 1 + ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff
      ℓ).chartPushforward ψ ((ψ ∘ g) z) (fderiv ℝ (ψ ∘ g) z Complex.I) = 0 := by
  have hψd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ (g z) :=
    ((contMDiffOn_of_mem_maximalAtlas hψ).contMDiffAt
      (ψ.open_source.mem_nhds hgz)).mdifferentiableAt (by simp)
  have hψsd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ.symm (ψ (g z)) :=
    ((contMDiffOn_symm_of_mem_maximalAtlas hψ).contMDiffAt
      (ψ.open_target.mem_nhds (ψ.map_source hgz))).mdifferentiableAt (by simp)
  refine (((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff
    ℓ).fderiv_chart_comp_add_eq_zero_iff (hg.restrictScalars ℝ).mdifferentiableAt hgz hψd
      hψsd).2 fun w ↦ ?_
  simp only [mfderiv_eq_fderiv, hg.fderiv_restrictScalars ℝ]
  rw [SmoothAlmostComplexStructure.toContMDiff_toEndomorphism_apply,
    SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold]
  -- The identifications of the tangent spaces of `ℂ` with `ℂ` are the identity.
  change fderiv ℂ g z (Complex.I • w) = Complex.I • fderiv ℂ g z w
  exact map_smul _ _ _

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
    ψ.continuousOn.comp (continuous_subtype_val.comp_continuousOn
      (φ.continuousOn_extend_symm.mono inter_subset_left)) fun _ hz ↦ hz.2
  refine isWeakCauchyRiemannOn_iff_interior.2 ⟨hcont, hw, ?_⟩
  rw [ContMDiffAlmostComplexStructureFamily.chartField_const,
    InhomogeneousTerm.chartTermExtend_zero]
  have hf : ContDiffOn ℝ 1 (ψ ∘ g) (interior U) := fun z hz ↦
    (((contMDiffOn_iff_contDiffOn.1 (contMDiffOn_of_mem_maximalAtlas hψ)).contDiffAt
      (ψ.open_source.mem_nhds (hint hz).2)).of_le (by simp)).comp_contDiffWithinAt
      z ((hgc.contDiffAt (hD.mem_nhds (hint hz).1)).restrict_scalars ℝ).contDiffWithinAt
  exact isWeakCauchyRiemannOn_of_contDiffOn (Ω := ⟨interior U, isOpen_interior⟩) hf
    fun z hz ↦ fderiv_chart_comp_add_eq_zero_of_differentiableAt
      ((hgc.differentiableOn one_ne_zero).differentiableAt (hD.mem_nhds (hint hz).1)) hψ (hint hz).2

/-- **Conjugation is not a solution.** The map `z ↦ conj z` from the closed upper half-plane to
`ℂ` is not weakly pseudoholomorphic up to the boundary, for the complex structure of `ℂ` and
`ν = 0`, on any open set containing a point of positive imaginary part. -/
theorem not_isWeakPseudoholomorphicOnBordered_conj {s : Set ClosedUpperHalfPlane} (hs : IsOpen s)
    (hne : ∃ z ∈ s, 0 < (z : ℂ).im) :
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
  obtain ⟨z, hzs, hz⟩ := hne
  exact not_isWeakCauchyRiemannOn_conj (Ω := ⟨Ω, hΩ⟩) ⟨z, hz, by simpa using hzs⟩ h3

/-- **The limit of boundary conditions can leave `L`.** For `L = (0, 1) ⊆ ℝ ⊆ ℂ`, whose image is
not closed, the constant maps `1/(m+2)` on the closed upper half-plane solve the homogeneous
equation and map the boundary into `L`, but their limit, the constant map `0`, does not. So the
closedness hypothesis of `TauCeti.MapsBoundaryInto.of_tendsto` cannot be dropped. -/
theorem not_mapsBoundaryInto_limit_Ioo :
    (∀ m : ℕ, IsWeakPseudoholomorphicBordered (ContMDiffAlmostComplexStructureFamily.const
      ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ)) 0 p
        (fun _ : ClosedUpperHalfPlane ↦ ((1 / (m + 2) : ℝ) : ℂ)) ∧
      MapsBoundaryInto closedUpperHalfPlaneModel
        (fun _ : ClosedUpperHalfPlane ↦ ((1 / (m + 2) : ℝ) : ℂ))
        (fun t : Ioo (0 : ℝ) 1 ↦ ((t : ℝ) : ℂ))) ∧
      Tendsto (fun m : ℕ ↦ ((1 / (m + 2) : ℝ) : ℂ)) atTop (𝓝 0) ∧
      ¬MapsBoundaryInto closedUpperHalfPlaneModel (fun _ : ClosedUpperHalfPlane ↦ (0 : ℂ))
        (fun t : Ioo (0 : ℝ) 1 ↦ ((t : ℝ) : ℂ)) := by
  refine ⟨fun m ↦ ⟨isWeakPseudoholomorphicBordered_const _, fun _ _ ↦
    ⟨⟨1 / (m + 2), by positivity, ?_⟩, rfl⟩⟩, ?_, ?_⟩
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
    obtain ⟨y, hy⟩ := h hb
    exact y.2.1.ne' (Complex.ofReal_eq_zero.1 hy)

end Checks

end TauCeti
