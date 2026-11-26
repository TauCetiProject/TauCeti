/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Real
import TauCeti.Topology.Algebra.Module.Equiv.Pi

/-!
# Local quadrant charts for coordinate-nonnegative models with corners

Every real model with corners `I : ModelWithCorners ℝ E H` whose range is cut out by the
nonnegativity of a set `S` of coordinates under a continuous linear equivalence
`L : E ≃L[ℝ] (ι → ℝ)` (`[Finite ι]`) is locally modelled on the Euclidean quadrant
`EuclideanQuadrant (finrank ℝ E)`. Around any point `x` of a `C^r` manifold `M` modelled on `I`,
the coordinates in `S` are already nonnegative in `range I`, while translating each unconstrained
coordinate `j ∉ S` by `1 - (L (extChartAt I x x)) j` sends `x` to `1 > 0` in slot `j` and stays
strictly positive on an open neighbourhood of `x` in its preferred chart. This identifies an open
neighbourhood of `x` in `M` with an open subset of `EuclideanQuadrant (finrank ℝ E)` by a `C^r`
diffeomorphism whose underlying homeomorphism is independent of the regularity order `r`.

Separating this chart construction from `TauCeti.Geometry.Manifold.Corners.Depth` allows downstream
modules (such as `TauCeti.Geometry.Manifold.Sard.Corners`) to construct local quadrant
diffeomorphisms without importing tangent-cone or depth theory, while supplying canonical
`r`-independent local quadrant neighbourhoods (`ModelWithCorners.localQuadrantSource`,
`ModelWithCorners.localQuadrantTarget`, `ModelWithCorners.localQuadrantHomeomorph`,
`ModelWithCorners.localQuadrantDiffeomorph`) for transporting the smooth structure on depth strata
in `TauCeti.Geometry.Manifold.Corners.Stratum`.

## Main definitions

* `ModelWithCorners.quadrantShiftSource`, `ModelWithCorners.quadrantShiftTarget`: open subsets of
  `M` and `EuclideanQuadrant d` on which translating unconstrained coordinates by `c` lands inside
  the open positive orthant.
* `ModelWithCorners.coordToEuclidean`: continuous linear equivalence
  `E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E))` induced by a finite coordinate system
  `L : E ≃L[ℝ] (ι → ℝ)`.
* `ModelWithCorners.localQuadrantSource`, `ModelWithCorners.localQuadrantTarget`,
  `ModelWithCorners.localQuadrantOffset`: the canonical open neighbourhood of `x : M`, open target
  in `EuclideanQuadrant (finrank ℝ E)`, and translation vector for a coordinate-nonnegative model.
* `ModelWithCorners.localQuadrantHomeomorph`, `ModelWithCorners.localQuadrantDiffeomorph`: the
  resulting local homeomorphism and `C^r` diffeomorphism around `x`, sharing the same underlying
  equivalence for every `r`.

## Main results

* `TauCeti.isOpen_setOf_forall_pos`: openness of `{x | ∀ i, P i → 0 < coord x i}` for finitely many
  continuous coordinates.
* `ModelWithCorners.range_transContinuousLinearEquiv_of_range_eq_equiv`: coordinate formula for the
  range of `I.transContinuousLinearEquiv` along `L`, a reindexing `σ`, and `EuclideanSpace.equiv`.
* `ModelWithCorners.exists_opens_diffeomorph_opens_euclideanQuadrant_of_range_eq`,
  `ModelWithCorners.exists_opens_diffeomorph_opens_euclideanQuadrant_of_range_eq_equiv`: existence
  of open neighbourhoods `C^r`-diffeomorphic to open subsets of a Euclidean quadrant.
* `ModelWithCorners.localQuadrantOffset_eq_zero_of_apply_eq_zero`,
  `ModelWithCorners.mem_chart_source_and_extChartAt_localQuadrantHomeomorph_symm`: coordinate
  expression of `(localQuadrantHomeomorph L hI x).symm` in `extChartAt I x`, with vanishing offset
  along coordinates vanishing at the image of `x`.

## References

* D. Joyce, *On manifolds with corners*, in *Advances in Geometric Analysis*, Adv. Lect. Math. 21,
  International Press (2012), 225–258, Section 2. [arXiv:0910.3518](https://arxiv.org/abs/0910.3518)
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapter 16, section *Manifolds with Corners*.
-/

public section

noncomputable section

open Set Function Module
open scoped Manifold Topology ContDiff

namespace TauCeti

/-- For a finite index type `ι` and coordinate functions continuous in `x`, the set of points where
every coordinate satisfying `P` is strictly positive is open. -/
theorem isOpen_setOf_forall_pos {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (P : ι → Prop) {coord : X → ι → ℝ} (hcoord : ∀ i, Continuous fun x ↦ coord x i) :
    IsOpen {x : X | ∀ i, P i → 0 < coord x i} := by
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun _ ↦
    isOpen_lt continuous_const (hcoord i)

end TauCeti

namespace ModelWithCorners

section RangeTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

/-- Transporting a model with corners `I` whose range is `{y | ∀ i ∈ S, 0 ≤ L y i}` along
`L : E ≃L[ℝ] (ι → ℝ)`, a coordinate reindexing `σ : ι ≃ κ`, and `(EuclideanSpace.equiv κ ℝ).symm`
produces a model on `EuclideanSpace ℝ κ` whose range is `{z | ∀ j ∈ σ '' S, 0 ≤ z j}`. -/
theorem range_transContinuousLinearEquiv_of_range_eq_equiv {ι κ : Type*} [Fintype κ]
    (L : E ≃L[ℝ] (ι → ℝ)) (σ : ι ≃ κ) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) :
    range (I.transContinuousLinearEquiv
      (L.trans ((ContinuousLinearEquiv.piCongrLeft ℝ (fun _ ↦ ℝ) σ).trans
        (EuclideanSpace.equiv κ ℝ).symm))) =
      {z | ∀ j ∈ σ '' S, 0 ≤ z j} := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ κ :=
    L.trans ((ContinuousLinearEquiv.piCongrLeft ℝ (fun _ ↦ ℝ) σ).trans
      (EuclideanSpace.equiv κ ℝ).symm)
  rw [I.transContinuousLinearEquiv_range, hI]
  ext z
  simp only [mem_image, mem_ofPred_eq]
  refine ⟨?_, fun hz ↦ ⟨e.symm z, fun i hi ↦ ?_, e.apply_symm_apply z⟩⟩
  · rintro ⟨y, hy, rfl⟩ _ ⟨i, hi, rfl⟩
    simpa [e] using hy i hi
  · simpa [e] using hz (σ i) ⟨i, hi, rfl⟩

end RangeTransport

section QuadrantShift

variable {d : ℕ} {H : Type*} [TopologicalSpace H]
  (J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H) (S₀ : Set (Fin d))
  (c : EuclideanSpace ℝ (Fin d))
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The open subset of the preferred chart domain at `x` where the coordinates outside `S₀`,
shifted by `c`, are strictly positive. -/
def quadrantShiftSource (x : M) : TopologicalSpace.Opens M :=
  let e := chartAt H x
  ⟨e.source ∩ e ⁻¹' {h : H | ∀ j ∉ S₀, 0 < J h j + c j},
    e.continuousOn.isOpen_inter_preimage e.open_source <|
      TauCeti.isOpen_setOf_forall_pos (· ∉ S₀) fun j ↦
        (((PiLp.continuous_apply 2 _ j).comp J.continuous).add continuous_const)⟩

/-- The corresponding open subset of `EuclideanQuadrant d` under translation by `c`. -/
def quadrantShiftTarget (x : M) : TopologicalSpace.Opens (EuclideanQuadrant d) :=
  let e := chartAt H x
  ⟨{q | J.symm (q.val - c) ∈ e.target} ∩ {q | ∀ j ∉ S₀, 0 < q.val j},
    (e.open_target.preimage (by fun_prop)).inter <|
      TauCeti.isOpen_setOf_forall_pos (· ∉ S₀) fun j ↦
        (PiLp.continuous_apply 2 _ j).comp continuous_subtypeVal⟩

variable {J S₀ c}

private theorem contMDiff_quadrantShift_toFun
    {r : ℕ∞ω} [IsManifold J r M] {x : M}
    (hmemQ : ∀ u : quadrantShiftSource J S₀ c x, J (chartAt H x u.val) + c ∈ range (𝓡c d))
    (g : quadrantShiftSource J S₀ c x → quadrantShiftTarget J S₀ c x)
    (hg : ∀ u, (g u).val = (𝓡c d).symm (J (chartAt H x u.val) + c)) :
    ContMDiff J (𝓡c d) r g := fun u ↦ by
  have he : chartAt H x ∈ IsManifold.maximalAtlas J r M := IsManifold.chart_mem_maximalAtlas x
  have heu : ContMDiffAt J J r (chartAt H x ∘ (Subtype.val : quadrantShiftSource J S₀ c x → M)) u :=
    ((contMDiffOn_of_mem_maximalAtlas he u.val u.property.1).contMDiffAt
      ((chartAt H x).open_source.mem_nhds u.property.1)).comp u (contMDiff_subtypeVal u)
  have haff : ContMDiffAt J 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) r
      (fun u' : quadrantShiftSource J S₀ c x ↦ J (chartAt H x u'.val) + c) u :=
    ((contDiff_id.add contDiff_const).contMDiff.contMDiffAt.comp _ (J.contMDiff _)).comp u heu
  have hto : ContMDiffWithinAt J (𝓡c d) r (Subtype.val ∘ g) univ u := by
    simp only [comp_def, hg]
    exact ((𝓡c d).contMDiffOn_symm _ (hmemQ u)).comp u haff.contMDiffWithinAt fun u' _ ↦ hmemQ u'
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ univ u).1 hto

private theorem contMDiff_quadrantShift_invFun
    {r : ℕ∞ω} [IsManifold J r M] {x : M}
    (hmemJ : ∀ v : quadrantShiftTarget J S₀ c x, v.val.val - c ∈ range J)
    (g : quadrantShiftTarget J S₀ c x → quadrantShiftSource J S₀ c x)
    (hg : ∀ v, (g v).val = (chartAt H x).symm (J.symm (v.val.val - c))) :
    ContMDiff (𝓡c d) J r g := fun v ↦ by
  have he : chartAt H x ∈ IsManifold.maximalAtlas J r M := IsManifold.chart_mem_maximalAtlas x
  have haff : ContMDiffAt (𝓡c d) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) r
      (fun v' : quadrantShiftTarget J S₀ c x ↦ (𝓡c d) v'.val - c) v :=
    ((contDiff_id.sub contDiff_const).contMDiff.contMDiffAt.comp _
      ((𝓡c d).contMDiff _)).comp v (contMDiff_subtypeVal v)
  have hJsymm : ContMDiffAt (𝓡c d) J r
      (fun v' : quadrantShiftTarget J S₀ c x ↦ J.symm (v'.val.val - c)) v :=
    contMDiffWithinAt_univ.1
      ((J.contMDiffOn_symm _ (hmemJ v)).comp v haff.contMDiffWithinAt fun v' _ ↦ hmemJ v')
  have hinv : ContMDiffAt (𝓡c d) J r (Subtype.val ∘ g) v := by
    simp only [comp_def, hg]
    exact ((contMDiffOn_symm_of_mem_maximalAtlas he _ v.property.1).contMDiffAt
      ((chartAt H x).open_target.mem_nhds v.property.1)).comp v hJsymm
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ univ v).1 hinv.contMDiffWithinAt

private def quadrantShiftOffset (J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    (S₀ : Set (Fin d)) (x : M) : EuclideanSpace ℝ (Fin d) :=
  let _ := Classical.propDecidable
  WithLp.toLp 2 fun j ↦ if j ∈ S₀ then 0 else 1 - J (chartAt H x x) j

private theorem mem_quadrantShiftSource_self (J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    (S₀ : Set (Fin d)) (x : M) :
    x ∈ quadrantShiftSource J S₀ (quadrantShiftOffset J S₀ x) x :=
  ⟨mem_chart_source H x, fun j hj ↦ by simp [quadrantShiftOffset, hj]⟩

private theorem mem_range_quadrant_of_mem_quadrantShiftSource
    (hJ : range J = {z | ∀ j ∈ S₀, 0 ≤ z j}) {x : M}
    (u : quadrantShiftSource J S₀ (quadrantShiftOffset J S₀ x) x) :
    J (chartAt H x u.val) + quadrantShiftOffset J S₀ x ∈ range (𝓡c d) := by
  rw [range_modelWithCornersEuclideanQuadrant]
  intro j
  by_cases hj : j ∈ S₀
  · have hmem : J (chartAt H x u.val) ∈ range J := mem_range_self _
    rw [hJ] at hmem
    simpa [quadrantShiftOffset, hj] using hmem j hj
  · exact (u.property.2 j hj).le

private theorem mem_range_of_mem_quadrantShiftTarget
    (hJ : range J = {z | ∀ j ∈ S₀, 0 ≤ z j}) {x : M}
    (v : quadrantShiftTarget J S₀ (quadrantShiftOffset J S₀ x) x) :
    v.val.val - quadrantShiftOffset J S₀ x ∈ range J := by
  rw [hJ]
  intro j hj
  simpa [quadrantShiftOffset, hj] using v.val.property j

private def quadrantShiftToFun (hJ : range J = {z | ∀ j ∈ S₀, 0 ≤ z j}) (x : M)
    (u : quadrantShiftSource J S₀ (quadrantShiftOffset J S₀ x) x) :
    quadrantShiftTarget J S₀ (quadrantShiftOffset J S₀ x) x :=
  let c := quadrantShiftOffset J S₀ x
  have hvalQ : ((𝓡c d).symm (J (chartAt H x u.val) + c)).val = J (chartAt H x u.val) + c :=
    (modelWithCornersEuclideanQuadrant_apply _).symm.trans
      ((𝓡c d).right_inv (mem_range_quadrant_of_mem_quadrantShiftSource hJ u))
  ⟨(𝓡c d).symm (J (chartAt H x u.val) + c),
    ⟨by
        rw [mem_ofPred_eq, hvalQ, add_sub_cancel_right, J.left_inv]
        exact (chartAt H x).map_source u.property.1,
      by rw [mem_ofPred_eq]; intro j hj; rw [hvalQ]; exact u.property.2 j hj⟩⟩

private theorem coe_quadrantShiftToFun_apply (hJ : range J = {z | ∀ j ∈ S₀, 0 ≤ z j}) (x : M)
    (u : quadrantShiftSource J S₀ (quadrantShiftOffset J S₀ x) x) :
    (quadrantShiftToFun hJ x u).val =
      (𝓡c d).symm (J (chartAt H x u.val) + quadrantShiftOffset J S₀ x) :=
  (rfl)

private def quadrantShiftInvFun (hJ : range J = {z | ∀ j ∈ S₀, 0 ≤ z j}) (x : M)
    (v : quadrantShiftTarget J S₀ (quadrantShiftOffset J S₀ x) x) :
    quadrantShiftSource J S₀ (quadrantShiftOffset J S₀ x) x :=
  let c := quadrantShiftOffset J S₀ x
  ⟨(chartAt H x).symm (J.symm (v.val.val - c)),
    ⟨(chartAt H x).map_target v.property.1, fun j hj ↦ by
      rw [(chartAt H x).right_inv v.property.1,
        J.right_inv (mem_range_of_mem_quadrantShiftTarget hJ v), PiLp.sub_apply, sub_add_cancel]
      exact v.property.2 j hj⟩⟩

private theorem coe_quadrantShiftInvFun_apply (hJ : range J = {z | ∀ j ∈ S₀, 0 ≤ z j}) (x : M)
    (v : quadrantShiftTarget J S₀ (quadrantShiftOffset J S₀ x) x) :
    (quadrantShiftInvFun hJ x v).val =
      (chartAt H x).symm (J.symm (v.val.val - quadrantShiftOffset J S₀ x)) :=
  (rfl)

private def quadrantShiftDiffeomorph (hJ : range J = {z | ∀ j ∈ S₀, 0 ≤ z j})
    {r : ℕ∞ω} [IsManifold J r M] (x : M) :
    quadrantShiftSource J S₀ (quadrantShiftOffset J S₀ x) x ≃ₘ^r⟮J, 𝓡c d⟯
      quadrantShiftTarget J S₀ (quadrantShiftOffset J S₀ x) x where
  toFun := quadrantShiftToFun hJ x
  invFun := quadrantShiftInvFun hJ x
  left_inv u := Subtype.ext <| by
    rw [coe_quadrantShiftInvFun_apply, coe_quadrantShiftToFun_apply,
      ← modelWithCornersEuclideanQuadrant_apply,
      (𝓡c d).right_inv (mem_range_quadrant_of_mem_quadrantShiftSource hJ u),
      add_sub_cancel_right, J.left_inv, (chartAt H x).left_inv u.property.1]
  right_inv v := Subtype.ext <| by
    rw [coe_quadrantShiftToFun_apply, coe_quadrantShiftInvFun_apply,
      (chartAt H x).right_inv v.property.1,
      J.right_inv (mem_range_of_mem_quadrantShiftTarget hJ v), sub_add_cancel,
      ← modelWithCornersEuclideanQuadrant_apply, ModelWithCorners.left_inv]
  contMDiff_toFun := contMDiff_quadrantShift_toFun
    (mem_range_quadrant_of_mem_quadrantShiftSource hJ) _ (coe_quadrantShiftToFun_apply hJ x)
  contMDiff_invFun := contMDiff_quadrantShift_invFun
    (mem_range_of_mem_quadrantShiftTarget hJ) _ (coe_quadrantShiftInvFun_apply hJ x)

/-- On a `C^r` manifold modelled on a region `{z : EuclideanSpace ℝ (Fin d) | ∀ j ∈ S₀, 0 ≤ z j}`,
every point has an open neighbourhood `C^r`-diffeomorphic to an open subset of
`EuclideanQuadrant d`, obtained by translating the unconstrained coordinates into `(0, ∞)`. -/
theorem exists_opens_diffeomorph_opens_euclideanQuadrant_of_range_eq
    (hJ : range J = {z | ∀ j ∈ S₀, 0 ≤ z j})
    {r : ℕ∞ω} [IsManifold J r M] (x : M) :
    ∃ (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens (EuclideanQuadrant d)),
      x ∈ U ∧ Nonempty (U ≃ₘ^r⟮J, 𝓡c d⟯ V) :=
  ⟨_, _, mem_quadrantShiftSource_self J S₀ x, ⟨quadrantShiftDiffeomorph hJ x⟩⟩

end QuadrantShift

section LinearCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {ι : Type*} [Finite ι] (L : E ≃L[ℝ] (ι → ℝ)) (S : Set ι)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private def coordIndexEquiv : ι ≃ Fin (finrank ℝ E) :=
  let _ := Fintype.ofFinite ι
  Fintype.equivFinOfCardEq <| by
    rw [L.toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card]

/-- Reindexing a finite linear coordinate equivalence `L : E ≃L[ℝ] (ι → ℝ)` into
`EuclideanSpace ℝ (Fin (finrank ℝ E))`. -/
def coordToEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
  L.trans ((ContinuousLinearEquiv.piCongrLeft ℝ (fun _ ↦ ℝ) (coordIndexEquiv L)).trans
    (EuclideanSpace.equiv (Fin (finrank ℝ E)) ℝ).symm)

/-- The translation vector in `EuclideanSpace ℝ (Fin (finrank ℝ E))` used to form the canonical
local quadrant chart around `x : M`. -/
def localQuadrantOffset (x : M) : EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
  quadrantShiftOffset (I.transContinuousLinearEquiv (coordToEuclidean L))
    (coordIndexEquiv L '' S) x

/-- The canonical open neighbourhood of `x : M` on which `I` is locally modelled on
`EuclideanQuadrant (finrank ℝ E)`. -/
def localQuadrantSource (x : M) : TopologicalSpace.Opens M :=
  quadrantShiftSource (I.transContinuousLinearEquiv (coordToEuclidean L))
    (coordIndexEquiv L '' S) (localQuadrantOffset I L S x) x

/-- The open subset of `EuclideanQuadrant (finrank ℝ E)` corresponding to
`localQuadrantSource I L S x`. -/
def localQuadrantTarget (x : M) :
    TopologicalSpace.Opens (EuclideanQuadrant (finrank ℝ E)) :=
  quadrantShiftTarget (I.transContinuousLinearEquiv (coordToEuclidean L))
    (coordIndexEquiv L '' S) (localQuadrantOffset I L S x) x

/-- Every point `x : M` lies in `localQuadrantSource I L S x`. -/
theorem mem_localQuadrantSource (x : M) : x ∈ localQuadrantSource I L S x :=
  mem_quadrantShiftSource_self _ _ x

variable {I S}

/-- The canonical `C^r` diffeomorphism between `localQuadrantSource I L S x` and
`localQuadrantTarget I L S x` for a coordinate-nonnegative model `I`. Its underlying equivalence
is independent of the regularity order `r`. -/
def localQuadrantDiffeomorph (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {r : ℕ∞ω} [IsManifold I r M] (x : M) :
    localQuadrantSource I L S x ≃ₘ^r⟮I, 𝓡c (finrank ℝ E)⟯ localQuadrantTarget I L S x := by
  let _ := Fintype.ofFinite ι
  have hJ : range (I.transContinuousLinearEquiv (coordToEuclidean L)) =
      {z | ∀ j ∈ coordIndexEquiv L '' S, 0 ≤ z j} :=
    I.range_transContinuousLinearEquiv_of_range_eq_equiv L (coordIndexEquiv L) hI
  let Φ := quadrantShiftDiffeomorph hJ (r := r) x
  exact
    { toEquiv := Φ.toEquiv
      contMDiff_toFun :=
        (coordToEuclidean L).contMDiff_transContinuousLinearEquiv_left.1 Φ.contMDiff
      contMDiff_invFun :=
        (coordToEuclidean L).contMDiff_transContinuousLinearEquiv_right.1 Φ.symm.contMDiff }

/-- The canonical homeomorphism between `localQuadrantSource I L S x` and
`localQuadrantTarget I L S x`, independent of any manifold smoothness hypothesis on `M`. -/
def localQuadrantHomeomorph (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) (x : M) :
    localQuadrantSource I L S x ≃ₜ localQuadrantTarget I L S x :=
  (localQuadrantDiffeomorph L hI (r := 0) x).toHomeomorph

@[simp]
theorem coe_localQuadrantDiffeomorph (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {r : ℕ∞ω} [IsManifold I r M] (x : M) :
    ⇑(localQuadrantDiffeomorph L hI (r := r) x) = localQuadrantHomeomorph L hI x :=
  (rfl)

@[simp]
theorem coe_localQuadrantDiffeomorph_symm (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {r : ℕ∞ω} [IsManifold I r M] (x : M) :
    ⇑(localQuadrantDiffeomorph L hI (r := r) x).symm = (localQuadrantHomeomorph L hI x).symm :=
  (rfl)

/-- Any coordinate vanishing at the image of `x` under `localQuadrantHomeomorph L hI x` has zero
translation offset. -/
theorem localQuadrantOffset_eq_zero_of_apply_eq_zero
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) (x : M) {j : Fin (finrank ℝ E)}
    (hj : ((localQuadrantHomeomorph L hI x ⟨x, mem_localQuadrantSource I L S x⟩).val).val j = 0) :
    localQuadrantOffset I L S x j = 0 := by
  let _ := Fintype.ofFinite ι
  have hJ : range (I.transContinuousLinearEquiv (coordToEuclidean L)) =
      {z | ∀ j ∈ coordIndexEquiv L '' S, 0 ≤ z j} :=
    I.range_transContinuousLinearEquiv_of_range_eq_equiv L (coordIndexEquiv L) hI
  have hval : ((localQuadrantHomeomorph L hI x ⟨x, mem_localQuadrantSource I L S x⟩).val).val =
      I.transContinuousLinearEquiv (coordToEuclidean L) (chartAt H x x) +
        localQuadrantOffset I L S x :=
    (modelWithCornersEuclideanQuadrant_apply _).symm.trans
      ((𝓡c (finrank ℝ E)).right_inv (mem_range_quadrant_of_mem_quadrantShiftSource hJ
        ⟨x, mem_localQuadrantSource I L S x⟩))
  have hj' := (congrFun (congrArg WithLp.ofLp hval) j).symm.trans hj
  by_cases hjS : (coordIndexEquiv L).symm j ∈ S
  · simp [localQuadrantOffset, quadrantShiftOffset, hjS]
  · exfalso
    simp [localQuadrantOffset, quadrantShiftOffset, hjS] at hj'

/-- On `localQuadrantTarget I L S x`, `(localQuadrantHomeomorph L hI x).symm` lands in
`(chartAt H x).source` and reads in `extChartAt I x` as `v ↦ (coordToEuclidean L).symm (v - c)`. -/
theorem mem_chart_source_and_extChartAt_localQuadrantHomeomorph_symm
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) (x : M)
    (v : localQuadrantTarget I L S x) :
    ((localQuadrantHomeomorph L hI x).symm v).val ∈ (chartAt H x).source ∧
      extChartAt I x (((localQuadrantHomeomorph L hI x).symm v).val) =
        (coordToEuclidean L).symm (v.val.val - localQuadrantOffset I L S x) := by
  let _ := Fintype.ofFinite ι
  let J := I.transContinuousLinearEquiv (coordToEuclidean L)
  have hJ : range J = {z | ∀ j ∈ coordIndexEquiv L '' S, 0 ≤ z j} :=
    I.range_transContinuousLinearEquiv_of_range_eq_equiv L (coordIndexEquiv L) hI
  have hsymm : ((localQuadrantHomeomorph L hI x).symm v).val =
      (chartAt H x).symm (J.symm (v.val.val - localQuadrantOffset I L S x)) :=
    (rfl)
  refine ⟨hsymm ▸ (chartAt H x).map_target v.property.1, ?_⟩
  rw [hsymm, extChartAt_coe, Function.comp_apply, (chartAt H x).right_inv v.property.1]
  apply (coordToEuclidean L).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact J.right_inv (mem_range_of_mem_quadrantShiftTarget hJ v)

/-- **Local quadrant charts for coordinate-nonnegative models:** on a `C^r` manifold `M` whose model
range is cut out by the nonnegativity of a set `S` of coordinates under a continuous linear
equivalence `L : E ≃L[ℝ] (ι → ℝ)`, every point has an open neighbourhood `C^r`-diffeomorphic to an
open subset of `EuclideanQuadrant (finrank ℝ E)`. -/
theorem exists_opens_diffeomorph_opens_euclideanQuadrant_of_range_eq_equiv
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {r : ℕ∞ω} [IsManifold I r M] (x : M) :
    ∃ (U : TopologicalSpace.Opens M)
      (V : TopologicalSpace.Opens (EuclideanQuadrant (finrank ℝ E))),
      x ∈ U ∧ Nonempty (U ≃ₘ^r⟮I, 𝓡c (finrank ℝ E)⟯ V) :=
  ⟨localQuadrantSource I L S x, localQuadrantTarget I L S x, mem_localQuadrantSource I L S x,
    ⟨localQuadrantDiffeomorph L hI x⟩⟩

end LinearCoordinates

end ModelWithCorners
