/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Topology.FiberBundle.Countable
public import TauCeti.Topology.FiberBundle.LocallyCompact
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The cotangent bundle of a manifold

The cotangent bundle `T*M` of a manifold `M` modelled on `I : ModelWithCorners 𝕜 E H` is the
total space of the bundle of continuous linear functionals on the tangent spaces,

`TauCeti.CotangentBundle I M = Bundle.TotalSpace (E →L[𝕜] 𝕜) (fun x ↦ TangentSpace I x →L[𝕜] 𝕜)`.

No new structure is chosen: its topology, fibre-bundle and vector-bundle structure, charts and
manifold structure, modelled on `I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)`, are those of Mathlib's bundle of
continuous linear maps from the tangent bundle to the trivial line bundle. In particular, the
projection is a submersion by `Bundle.isSubmersion_proj`, the zero section is smooth by
`Bundle.contMDiff_zeroSection`, and the fibrewise addition and scalar multiplication are the vector
space structures of the fibres.

This file computes the trivializations and charts in coordinates. The canonical trivialization at
`x` reads a covector `p` at `y` as `p ∘ (dφ_y)⁻¹`, where `φ` is the extended chart at `x`
(`TauCeti.CotangentBundle.trivializationAt_mk_snd`), and it is the identity over `x` itself
(`TauCeti.CotangentBundle.inCoordinates_self`,
`TauCeti.CotangentBundle.continuousLinearMapAt_trivializationAt_self`,
`TauCeti.CotangentBundle.symmL_trivializationAt_self`). The preferred chart at a covector over
`x₀` sends a covector `p` at `x` to `(φ₀ x, p ∘ d(φ₀⁻¹))`, where `φ₀` is the extended chart of `M`
at `x₀` (`TauCeti.CotangentBundle.extChartAt_apply`,
`TauCeti.CotangentBundle.extChartAt_symm_apply`).
Consequently, a change of base chart `φ = φ₁ ∘ φ₀⁻¹` acts on cotangent coordinates by

`(q, p) ↦ (φ q, p ∘ (dφ_q)⁻¹)`,

the derivative of the inverse change of charts at `φ q`
(`TauCeti.CotangentBundle.extChartAt_extChartAt_symm`). The new covector pairs with the
pushed-forward tangent vector as the old covector pairs with the original one
(`TauCeti.CotangentBundle.extChartAt_extChartAt_symm_snd_apply_fderivWithin`).
This is the transformation law of covector components, dual to that of tangent vectors.
A map into the single fibre over a fixed point `q` moves only the fibre coordinate in these
charts, so its derivative is that of its covector part (`TauCeti.CotangentBundle.hasMFDerivAt_mk`),
and it is stationary exactly when its covector part is
(`TauCeti.CotangentBundle.mfderiv_mk_apply_eq_zero_iff`). The inclusion of that fibre is smooth
(`TauCeti.CotangentBundle.contMDiff_mk`).

Covectors pull back along the differential of a map `f : M → N`: a covector `p` at `f x` gives the
covector `p ∘ df_x` at `x`. For a family of covectors over a parameter manifold this is smooth:
`TauCeti.CotangentBundle.contMDiffAt_mk_comp_mfderiv` loses one degree of smoothness of `f`, as
the differential does. It gives the smoothness of the cotangent lift of a diffeomorphism
(`Diffeomorph.cotangent`). The map may also vary smoothly with the parameter
(`TauCeti.CotangentBundle.contMDiffAt_mk_comp_mfderiv_uncurry`), as the slice inclusions of a
product manifold do. Over an arbitrary topological parameter space, pulling back a continuous
family of covectors along a `C¹` map gives a continuous family
(`TauCeti.CotangentBundle.continuousAt_mk_comp_mfderiv`), and pairing a continuous family of
covectors at `f x` with the images under `df_x` of a continuous family of tangent vectors at `x` is
continuous when `f` is `C¹` (`TauCeti.CotangentBundle.continuousAt_snd_apply_mfderiv`).

Pairing a covector field along a map `u` with the image of a tangent field under a section `B` of
`End(TM)` is continuous wherever both fields are continuous into their bundles
(`ContMDiffSection.continuousAt_apply_apply`).

In a chart `c` into a normed space, differentiable with its inverse, a covector `ξ` at `x` is read
as the covector `ξ ∘ D(c⁻¹)(c x)` of the model space, and this reading is a bijection
(`OpenPartialHomeomorph.MDifferentiable.comp_mfderiv_symm_bijective`).

The construction follows the Zulip discussion `Cotangent Bundle as a Manifold` in the channel
`Is there code for X?`, which observed that Mathlib's continuous-linear-map bundle operations
already supply the cotangent total space with its manifold structure.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 11.
-/

public section

open Bundle Set
open scoped Manifold Topology

namespace TauCeti

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H]

/-- The cotangent bundle of a manifold `M` modelled on `I`: the total space of the bundle whose
fibre at `x` is the space of continuous linear functionals on `TangentSpace I x`. It is a manifold
modelled on `I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)`. -/
abbrev CotangentBundle (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] :=
  TotalSpace (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜)

namespace CotangentBundle

variable {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Two covectors are equal if they have the same base point and take the same values. -/
theorem ext {z w : CotangentBundle I M} (hproj : z.proj = w.proj)
    (h : ∀ v : TangentSpace I z.proj, z.snd v = w.snd v) : z = w := by
  obtain ⟨x, p⟩ := z
  obtain ⟨y, q⟩ := w
  obtain rfl : x = y := hproj
  exact congrArg (TotalSpace.mk' (E →L[𝕜] 𝕜) x) (ContinuousLinearMap.ext h)

variable [IsManifold I 1 M]

/-- Read in the tangent trivialization at `x`, a covector at `x` itself is its own coordinate
covector, as tangent vectors at `x` are their own coordinates there. -/
@[simp]
theorem inCoordinates_self (x : M) (p : TangentSpace I x →L[𝕜] 𝕜) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) 𝕜 (fun _ : M ↦ 𝕜) x x x x p = p := by
  ext v
  simp only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp]
  exact congrArg p (Manifold.symmL_trivializationAt_self x v)

/-- Read in the canonical trivialization at `x`, a covector at `x` itself is its own coordinate
covector, as tangent vectors at `x` are in the tangent trivialization at `x`. -/
@[simp]
theorem continuousLinearMapAt_trivializationAt_self (x : M) (p : TangentSpace I x →L[𝕜] 𝕜) :
    (trivializationAt (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) x).continuousLinearMapAt
      𝕜 x p = p := by
  refine (Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _
    (FiberBundle.mem_baseSet_trivializationAt (E →L[𝕜] 𝕜)
      (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) x) p).trans ?_
  rw [hom_trivializationAt_apply]
  exact inCoordinates_self x p

/-- **The inclusion of a fibre is smooth.** The covectors at a fixed point `x` form a smooth
family: the inclusion of the fibre over `x` into the cotangent bundle is smooth. -/
theorem contMDiff_mk (x : M) {n : WithTop ℕ∞} :
    ContMDiff 𝓘(𝕜, E →L[𝕜] 𝕜) (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
      fun p : E →L[𝕜] 𝕜 ↦
        TotalSpace.mk' (E →L[𝕜] 𝕜) (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) x p := by
  intro p₀
  rw [contMDiffAt_hom_bundle]
  exact ⟨contMDiffAt_const, contMDiffAt_id.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun p ↦ inCoordinates_self x p)⟩

/-- The canonical trivialization at `x` reads a covector at `y` as its precomposition with the
inverse of the tangent trivialization at `x`, from model vectors to tangent vectors at `y`. -/
theorem trivializationAt_mk_snd (x y : M) (p : TangentSpace I y →L[𝕜] 𝕜) :
    (trivializationAt (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) x ⟨y, p⟩).2 =
      p ∘L (trivializationAt E (TangentSpace I) x).symmL 𝕜 y := by
  ext v
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    Trivial.fiberBundle_trivializationAt', Trivial.continuousLinearMapAt_trivialization,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_apply]

/-- The inverse of the canonical trivialization at `x` sends a model covector to itself, read as
a covector at `x`. -/
theorem symmL_trivializationAt_self (x : M) (p : E →L[𝕜] 𝕜) :
    (trivializationAt (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) x).symmL 𝕜 x p = p :=
  -- `p` is read as a covector at `x`, whose coordinates at `x` are itself.
  (congrArg _ (continuousLinearMapAt_trivializationAt_self (I := I) x p).symm).trans
    (Trivialization.symmL_continuousLinearMapAt (R := 𝕜) _
      (FiberBundle.mem_baseSet_trivializationAt (E →L[𝕜] 𝕜)
        (fun y : M ↦ TangentSpace I y →L[𝕜] 𝕜) x) p)

/-- The preferred chart of the cotangent bundle at `z₀` sends a covector `z` to the chart image of
its base point and to the covector precomposed with the inverse of the tangent chart at `z₀`. -/
theorem extChartAt_apply (z₀ z : CotangentBundle I M) :
    extChartAt (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) z₀ z =
      (extChartAt I z₀.proj z.proj,
        z.snd ∘L (trivializationAt E (TangentSpace I) z₀.proj).symmL 𝕜 z.proj) := by
  simp [ContinuousLinearMap.inCoordinates]

/-- The inverse of the preferred chart of the cotangent bundle at `z₀` sends a point `q` of the
base chart and a model covector `p` to the covector `p` composed with the tangent chart, at the
point of `M` with coordinates `q`. -/
theorem extChartAt_symm_apply (z₀ : CotangentBundle I M) {q : E} (p : E →L[𝕜] 𝕜)
    (hq : q ∈ (extChartAt I z₀.proj).target) :
    (extChartAt (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) z₀).symm (q, p) =
      TotalSpace.mk' (E →L[𝕜] 𝕜) ((extChartAt I z₀.proj).symm q)
        (p ∘L (trivializationAt E (TangentSpace I) z₀.proj).continuousLinearMapAt 𝕜
          ((extChartAt I z₀.proj).symm q)) := by
  have hx := (extChartAt I z₀.proj).map_target hq
  have hb : (extChartAt I z₀.proj).symm q ∈
      (trivializationAt E (TangentSpace I) z₀.proj).baseSet := by
    simpa [extChartAt_source] using hx
  have hw : TotalSpace.mk' (E →L[𝕜] 𝕜) ((extChartAt I z₀.proj).symm q)
      (p ∘L (trivializationAt E (TangentSpace I) z₀.proj).continuousLinearMapAt 𝕜
        ((extChartAt I z₀.proj).symm q)) ∈ (extChartAt (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) z₀).source := by
    simp only [extChartAt_source] at hx
    simpa [FiberBundle.chartedSpace_chartAt, hom_trivializationAt_apply] using hx
  rw [← (extChartAt _ z₀).left_inv hw, extChartAt_apply]
  congr
  · exact ((extChartAt I z₀.proj).right_inv hq).symm
  · ext v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      (trivializationAt E (TangentSpace I) z₀.proj).continuousLinearMapAt_symmL hb]

/-- **Transition maps of the cotangent bundle.** Changing from the preferred chart at `z₀` to the
preferred chart at `z₁` sends `(q, p)` to `(φ q, p ∘ (dφ_q)⁻¹)`, where `φ` is the change of base
charts; `(dφ_q)⁻¹` is the derivative of the inverse change of charts at `φ q`. -/
theorem extChartAt_extChartAt_symm (z₀ z₁ : CotangentBundle I M) {q : E} (p : E →L[𝕜] 𝕜)
    (hq : q ∈ (extChartAt I z₀.proj).target)
    (hq₁ : (extChartAt I z₀.proj).symm q ∈ (extChartAt I z₁.proj).source) :
    extChartAt (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) z₁
        ((extChartAt (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) z₀).symm (q, p)) =
      ((extChartAt I z₁.proj ∘ (extChartAt I z₀.proj).symm) q,
        p ∘L fderivWithin 𝕜 (extChartAt I z₀.proj ∘ (extChartAt I z₁.proj).symm) (range I)
          ((extChartAt I z₁.proj ∘ (extChartAt I z₀.proj).symm) q)) := by
  have hx := (extChartAt I z₀.proj).map_target hq
  rw [extChartAt_symm_apply z₀ p hq, extChartAt_apply z₁]
  have hx₀ : (extChartAt I z₀.proj).symm q ∈ (chartAt H z₀.proj).source := by
    simpa [extChartAt_source] using hx
  have hx₁ : (extChartAt I z₀.proj).symm q ∈ (chartAt H z₁.proj).source := by
    simpa [extChartAt_source] using hq₁
  refine Prod.ext rfl ?_
  ext v
  dsimp only
  simp only [ContinuousLinearMap.comp_apply]
  rw [Manifold.continuousLinearMapAt_symmL_coordChange hx₁ hx₀, tangentCoordChange_def,
    Function.comp_apply]

/-- A change of charts of the cotangent bundle preserves the pairing of covectors with tangent
vectors: the new covector, evaluated on the image of `v` under the derivative of the change of base
charts, is the old covector evaluated on `v`. -/
theorem extChartAt_extChartAt_symm_snd_apply_fderivWithin (z₀ z₁ : CotangentBundle I M) {q : E}
    (p : E →L[𝕜] 𝕜) (hq : q ∈ (extChartAt I z₀.proj).target)
    (hq₁ : (extChartAt I z₀.proj).symm q ∈ (extChartAt I z₁.proj).source) (v : E) :
    (extChartAt (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) z₁
        ((extChartAt (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) z₀).symm (q, p))).2
      (fderivWithin 𝕜 (extChartAt I z₁.proj ∘ (extChartAt I z₀.proj).symm) (range I) q v) =
      p v := by
  have hx := (extChartAt I z₀.proj).map_target hq
  have hd : fderivWithin 𝕜 (extChartAt I z₁.proj ∘ (extChartAt I z₀.proj).symm) (range I) q =
      tangentCoordChange I z₀.proj z₁.proj ((extChartAt I z₀.proj).symm q) := by
    rw [tangentCoordChange_def, (extChartAt I z₀.proj).right_inv hq]
  rw [extChartAt_extChartAt_symm z₀ z₁ p hq hq₁, hd, ContinuousLinearMap.comp_apply,
    Function.comp_apply, ← tangentCoordChange_def, tangentCoordChange_comp ⟨⟨hx, hq₁⟩, hx⟩,
    tangentCoordChange_self hx]

/-- Pulling a `C^n` family of model covectors back through tangent-bundle coordinates gives a
`C^n` cotangent section wherever the coordinates are defined. -/
theorem contMDiffOn_mk_comp_continuousLinearMapAt {n : WithTop ℕ∞}
    [IsManifold I (n + 1) M] (x : M) {U : Set M}
    (hU : U ⊆ (trivializationAt E (TangentSpace I) x).baseSet)
    {c : M → E →L[𝕜] 𝕜} (hc : ContMDiffOn I 𝓘(𝕜, E →L[𝕜] 𝕜) n c U) :
    ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] 𝕜) y
        (c y ∘L (trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 y)) U := by
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  let e := trivializationAt E (TangentSpace I) x
  let α : Π y : M, TangentSpace I y →L[𝕜] 𝕜 :=
    fun y ↦ c y ∘L e.continuousLinearMapAt 𝕜 y
  have hU' : U ⊆ e.baseSet := hU
  let e' := trivializationAt 𝕜 (Bundle.Trivial M 𝕜) x
  let eh := e.continuousLinearMap (RingHom.id 𝕜) e'
  apply (eh.contMDiffOn_iff (f := fun y ↦ TotalSpace.mk' (E →L[𝕜] 𝕜) y (α y))
    (fun y hy ↦ eh.mem_source.mpr (by
      simp [eh, e', Trivial.eq_trivialization M 𝕜, hU' hy]))).mpr
  refine ⟨contMDiffOn_id, hc.congr ?_⟩
  intro y hy
  ext v
  simp [eh, e', α, Bundle.Trivialization.continuousLinearMap_apply,
    Trivial.eq_trivialization M 𝕜, e.continuousLinearMapAt_symmL (hU' hy)]

variable {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X] in
/-- **The derivative of a map into one fibre.** If `c : X → E →L[𝕜] 𝕜` has derivative `c'` at `y`,
then `y ↦ (q, c y)`, a map into the fibre of the cotangent bundle over the fixed point `q`, has
derivative `w ↦ (0, c' w)` at `y`, read in the preferred chart at `(q, c y)`: the base coordinate
does not move, and over `q` the tangent trivialization at `q` is the identity. -/
theorem hasMFDerivAt_mk (q : M) {c : X → E →L[𝕜] 𝕜} {y : X}
    {c' : TangentSpace IX y →L[𝕜] E →L[𝕜] 𝕜} (hc : HasMFDerivAt IX 𝓘(𝕜, E →L[𝕜] 𝕜) c y c') :
    HasMFDerivAt IX (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] 𝕜) (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) q (c y)) y
      ((ContinuousLinearMap.inr 𝕜 E (E →L[𝕜] 𝕜)).comp c') := by
  set e := trivializationAt (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) q
  have hq : q ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ q
  refine ⟨(FiberBundle.continuousAt_totalSpace _ _).2 ⟨continuousAt_const, ?_⟩, ?_⟩
  · -- In the trivialization at `q`, the fibre coordinate is a continuous linear image of `c`.
    have hcoord : (fun y' ↦ (e (TotalSpace.mk' (E →L[𝕜] 𝕜) q (c y'))).2) =
        fun y' ↦ e.continuousLinearMapAt 𝕜 q (c y') :=
      funext fun y' ↦ (e.continuousLinearMapAt_apply_of_mem (R := 𝕜) hq _).symm
    exact hcoord ▸ (e.continuousLinearMapAt 𝕜 q).continuous.continuousAt.comp hc.1
  · -- In charts the map is `u ↦ (φ q, c u)`, where `φ` is the extended chart at `q`.
    have hw : writtenInExtChartAt IX (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) y
        (fun y ↦ TotalSpace.mk' (E →L[𝕜] 𝕜) (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) q (c y)) =
        fun u ↦ (extChartAt I q q, writtenInExtChartAt IX 𝓘(𝕜, E →L[𝕜] 𝕜) y c u) := by
      funext u
      refine Prod.ext rfl (ContinuousLinearMap.ext fun w ↦ ?_)
      simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_apply,
        extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
      exact congrArg _ (TauCeti.Manifold.symmL_trivializationAt_self q w)
    rw [hw]
    exact ((hasFDerivWithinAt_const _ _ _).prodMk hc.2).congr_fderiv
      (ContinuousLinearMap.ext fun _ ↦ rfl)

variable {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X] in
/-- If `c : X → E →L[𝕜] 𝕜` has derivative `c'` at `y`, then the map `y ↦ (q, c y)` into the fibre
of the cotangent bundle over a fixed point `q` is stationary in a direction `v` exactly when `c`
is: `c' v = 0`. -/
theorem mfderiv_mk_apply_eq_zero_iff (q : M) {c : X → E →L[𝕜] 𝕜} {y : X}
    {c' : TangentSpace IX y →L[𝕜] E →L[𝕜] 𝕜} (hc : HasMFDerivAt IX 𝓘(𝕜, E →L[𝕜] 𝕜) c y c')
    (v : TangentSpace IX y) :
    mfderiv IX (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜))
        (fun y ↦ TotalSpace.mk' (E →L[𝕜] 𝕜) (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) q (c y))
        y v = 0 ↔
      c' v = 0 := by
  rw [(hasMFDerivAt_mk q hc).mfderiv]
  -- The tangent space of the model `E × (E →L[𝕜] 𝕜)` is this space itself, in which
  -- `inr (c' v) = (0, c' v)`.
  exact Prod.mk_eq_zero.trans (and_iff_right rfl)

section Pullback

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N]
  {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  {m n : WithTop ℕ∞}

/-- In bundle coordinates near `z₀`, a family of covectors `Ψ z` at `f z (g z)` pulled back along
the differentials of `f z` is the coordinate expression of `Ψ z` composed with that of the
differentials. -/
private theorem eventuallyEq_inCoordinates_comp_mfderiv {S : Type*} [TopologicalSpace S]
    {Ψ : S → CotangentBundle J N} {g : S → M} {f : S → M → N} {z₀ : S}
    (hΨg : ∀ z, (Ψ z).proj = f z (g z)) (hfg : ContinuousAt (fun z ↦ f z (g z)) z₀) :
    (fun z ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I) 𝕜 (fun _ : M ↦ 𝕜) (g z₀) (g z)
        (g z₀) (g z) ((Ψ z).snd ∘L mfderiv I J (f z) (g z))) =ᶠ[𝓝 z₀]
      fun z ↦ ContinuousLinearMap.inCoordinates E' (TangentSpace J) 𝕜 (fun _ : N ↦ 𝕜) (Ψ z₀).proj
          (Ψ z).proj (Ψ z₀).proj (Ψ z).proj (Ψ z).snd ∘L
        inTangentCoordinates I J g (fun z ↦ f z (g z)) (fun z ↦ mfderiv I J (f z) (g z)) z₀ z := by
  filter_upwards [hfg.preimage_mem_nhds
      ((trivializationAt E' (TangentSpace J) (f z₀ (g z₀))).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' _))] with z hz
  rw [hΨg z₀]
  -- Replace the covector `Ψ z` by one written over its base point `f z (g z)`.
  have hz' := hΨg z
  generalize Ψ z = w at hz' ⊢
  obtain ⟨y, p⟩ := w
  obtain rfl : y = f z (g z) := hz'
  ext v
  simp only [ContinuousLinearMap.inCoordinates, inTangentCoordinates,
    ContinuousLinearMap.comp_apply, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]
  rw [Trivialization.symmL_continuousLinearMapAt _ (b := f z (g z)) hz]

/-- In bundle coordinates, a family of covectors `Ψ z` at `f z (g z)` pulled back along the
differentials of `f z` is the coordinate expression of `Ψ z` composed with that of the
differentials. Hence the pulled-back family is `C^m` once `Ψ`, `g` and the differentials in
tangent coordinates are. -/
private theorem contMDiffAt_mk_comp_mfderiv_of_inTangentCoordinates {Ψ : X → CotangentBundle J N}
    {g : X → M} {f : X → M → N} {z₀ : X} (hΨg : ∀ z, (Ψ z).proj = f z (g z))
    (hΨ : ContMDiffAt IX (J.prod 𝓘(𝕜, E' →L[𝕜] 𝕜)) m Ψ z₀) (hg : ContMDiffAt IX I m g z₀)
    (hfg : ContinuousAt (fun z ↦ f z (g z)) z₀)
    (hd : ContMDiffAt IX 𝓘(𝕜, E →L[𝕜] E') m
      (inTangentCoordinates I J g (fun z ↦ f z (g z)) (fun z ↦ mfderiv I J (f z) (g z)) z₀) z₀) :
    ContMDiffAt IX (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) m
      (fun z ↦ (TotalSpace.mk' (E →L[𝕜] 𝕜) (g z) ((Ψ z).snd ∘L mfderiv I J (f z) (g z)) :
        CotangentBundle I M)) z₀ := by
  rw [contMDiffAt_hom_bundle] at hΨ ⊢
  exact ⟨hg, (hΨ.2.clm_comp hd).congr_of_eventuallyEq
    (eventuallyEq_inCoordinates_comp_mfderiv hΨg hfg)⟩

/-- **Pulling covectors back along a map is smooth.** Let `Ψ z` be a covector at `f (g z)`,
depending on a parameter `z`. Its pullback along the differential of `f` at `g z`,
`Ψ z ∘ df_(g z)`, is a covector at `g z`. If `Ψ` and `g` are `C^m` at `z₀` and `f` is `C^n` at
`g z₀` with `m + 1 ≤ n`, the family of pulled-back covectors is `C^m` at `z₀`. -/
theorem contMDiffAt_mk_comp_mfderiv {Ψ : X → CotangentBundle J N} {g : X → M} {f : M → N}
    {z₀ : X} (hΨg : ∀ z, (Ψ z).proj = f (g z))
    (hΨ : ContMDiffAt IX (J.prod 𝓘(𝕜, E' →L[𝕜] 𝕜)) m Ψ z₀) (hg : ContMDiffAt IX I m g z₀)
    (hf : ContMDiffAt I J n f (g z₀)) (hmn : m + 1 ≤ n) :
    ContMDiffAt IX (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) m
      (fun z ↦ (TotalSpace.mk' (E →L[𝕜] 𝕜) (g z) ((Ψ z).snd ∘L mfderiv I J f (g z)) :
        CotangentBundle I M)) z₀ :=
  -- Differentiating `f` on its own source needs no `C¹` structure on the parameter space.
  contMDiffAt_mk_comp_mfderiv_of_inTangentCoordinates (f := fun _ ↦ f) hΨg hΨ hg
    (hf.continuousAt.comp hg.continuousAt) ((hf.mfderiv_const hmn).comp z₀ hg)

/-- **Pulling covectors back along a map is smooth.** The global version of
`TauCeti.CotangentBundle.contMDiffAt_mk_comp_mfderiv`. -/
theorem contMDiff_mk_comp_mfderiv {Ψ : X → CotangentBundle J N} {g : X → M} {f : M → N}
    (hΨg : ∀ z, (Ψ z).proj = f (g z))
    (hΨ : ContMDiff IX (J.prod 𝓘(𝕜, E' →L[𝕜] 𝕜)) m Ψ) (hg : ContMDiff IX I m g)
    (hf : ContMDiff I J n f) (hmn : m + 1 ≤ n) :
    ContMDiff IX (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) m
      (fun z ↦ (TotalSpace.mk' (E →L[𝕜] 𝕜) (g z) ((Ψ z).snd ∘L mfderiv I J f (g z)) :
        CotangentBundle I M)) :=
  fun z ↦ contMDiffAt_mk_comp_mfderiv hΨg (hΨ z) (hg z) (hf (g z)) hmn

/-- **Pulling continuous covector fields back along a `C¹` map is continuous.** Let `Ψ z` be a
covector at `f (g z)`, depending on a parameter `z` in a topological space. If `Ψ` and `g` are
continuous at `z₀` and `f` is `C¹` at `g z₀`, the family of pulled-back covectors
`Ψ z ∘ df_(g z)` is continuous at `z₀`. This is the continuous counterpart of
`TauCeti.CotangentBundle.contMDiffAt_mk_comp_mfderiv`. -/
theorem continuousAt_mk_comp_mfderiv {S : Type*} [TopologicalSpace S]
    {Ψ : S → CotangentBundle J N} {g : S → M} {f : M → N} {z₀ : S}
    (hΨg : ∀ z, (Ψ z).proj = f (g z)) (hΨ : ContinuousAt Ψ z₀) (hg : ContinuousAt g z₀)
    (hf : ContMDiffAt I J 1 f (g z₀)) :
    ContinuousAt (fun z ↦ (TotalSpace.mk' (E →L[𝕜] 𝕜) (g z) ((Ψ z).snd ∘L mfderiv I J f (g z)) :
      CotangentBundle I M)) z₀ := by
  rw [continuousAt_hom_bundle] at hΨ ⊢
  -- The differential of a `C¹` map is continuous in tangent coordinates.
  have hd := (hf.mfderiv_const (m := 0) (by simp)).continuousAt.comp hg
  exact ⟨hg, (hΨ.2.clm_comp hd).congr_of_eventuallyEq
    (eventuallyEq_inCoordinates_comp_mfderiv (f := fun _ ↦ f) hΨg (hf.continuousAt.comp hg))⟩

/-- **Pulling covectors back along a family of maps is smooth.** Let `Ψ z` be a covector at
`f z (g z)`, depending on a parameter `z`. Its pullback along the differential of `f z` at `g z`,
`Ψ z ∘ d(f z)_(g z)`, is a covector at `g z`. If `Ψ` and `g` are `C^m` at `z₀` and
`(z, x) ↦ f z x` is `C^n` at `(z₀, g z₀)` with `m + 1 ≤ n`, the family of pulled-back covectors is
`C^m` at `z₀`. Unlike `TauCeti.CotangentBundle.contMDiffAt_mk_comp_mfderiv`, the map may vary with
the parameter, which is then required to range over a `C¹` manifold. -/
theorem contMDiffAt_mk_comp_mfderiv_uncurry [IsManifold IX 1 X] {Ψ : X → CotangentBundle J N}
    {g : X → M} {f : X → M → N} {z₀ : X} (hΨg : ∀ z, (Ψ z).proj = f z (g z))
    (hΨ : ContMDiffAt IX (J.prod 𝓘(𝕜, E' →L[𝕜] 𝕜)) m Ψ z₀) (hg : ContMDiffAt IX I m g z₀)
    (hf : ContMDiffAt (IX.prod I) J n (Function.uncurry f) (z₀, g z₀)) (hmn : m + 1 ≤ n) :
    ContMDiffAt IX (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) m
      (fun z ↦ (TotalSpace.mk' (E →L[𝕜] 𝕜) (g z) ((Ψ z).snd ∘L mfderiv I J (f z) (g z)) :
        CotangentBundle I M)) z₀ :=
  contMDiffAt_mk_comp_mfderiv_of_inTangentCoordinates hΨg hΨ hg
    (hf.continuousAt.comp (f := fun z ↦ (z, g z)) (continuousAt_id.prodMk hg.continuousAt))
    (hf.mfderiv f g hg hmn)

/-- **Pairing covectors with pushed-forward tangent vectors is continuous.** Let `v s` be a
tangent vector of `M` and `Ψ s` a covector at `f (v s).proj`, depending on a parameter `s` in a
topological space. If `Ψ` and `v` are continuous at `s₀` and `f` is `C¹` at `(v s₀).proj`, then
`s ↦ Ψ s (df (v s))` is continuous at `s₀`. -/
theorem continuousAt_snd_apply_mfderiv {S : Type*} [TopologicalSpace S]
    {Ψ : S → CotangentBundle J N} {v : S → TangentBundle I M} {f : M → N} {s₀ : S}
    (hΨv : ∀ s, (Ψ s).proj = f (v s).proj) (hΨ : ContinuousAt Ψ s₀) (hv : ContinuousAt v s₀)
    (hf : ContMDiffAt I J 1 f (v s₀).proj) :
    ContinuousAt (fun s ↦ (Ψ s).snd (mfderiv I J f (v s).proj (v s).snd)) s₀ := by
  -- Read `Ψ s` over the base point `f (v s).proj` of `tangentMap f (v s)`.
  have hΨ' : ContinuousAt (fun s ↦ TotalSpace.mk' (E' →L[𝕜] 𝕜)
      (E := fun y : N ↦ TangentSpace J y →L[𝕜] 𝕜) (f (v s).proj) (Ψ s).snd) s₀ := by
    have : (fun s ↦ TotalSpace.mk' (E' →L[𝕜] 𝕜) (E := fun y : N ↦ TangentSpace J y →L[𝕜] 𝕜)
        (f (v s).proj) (Ψ s).snd) = Ψ :=
      funext fun s ↦ CotangentBundle.ext (hΨv s).symm fun _ ↦ rfl
    rwa [this]
  exact continuous_snd.continuousAt.comp
    ((Bundle.Trivial.homeomorphProd N 𝕜).continuous.continuousAt.comp
      (ContinuousAt.clm_bundle_apply (E₂ := Bundle.Trivial N 𝕜) hΨ'
        ((hf.continuousAt_tangentMap le_rfl).comp hv)))

end Pullback

section SigmaCompact

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M]

/-- The cotangent bundle of a σ-compact manifold with a finite-dimensional real model is
σ-compact: the base is second countable and locally compact, so the total space is too, as a fibre
bundle with finite-dimensional fibre (`TauCeti.FiberBundle.secondCountableTopology_totalSpace`,
`TauCeti.FiberBundle.locallyCompactSpace_totalSpace`). -/
instance sigmaCompactSpace [SigmaCompactSpace M] : SigmaCompactSpace (CotangentBundle I M) := by
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  infer_instance

end SigmaCompact

end CotangentBundle

end TauCeti

namespace ContMDiffSection

open TauCeti

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M] {n : WithTop ℕ∞} {S : Type*} [TopologicalSpace S]
  {u : S → M} {w : (z : S) → TangentSpace I (u z)} {η : (z : S) → TangentSpace I (u z) →L[𝕜] 𝕜}

/-- A section `B` of `End(TM)`, evaluated along `u` on a tangent field `w` and paired with a
covector field `η`, is continuous wherever both fields are continuous into their bundles. -/
theorem continuousAt_apply_apply
    (B : Cₛ^n⟮I; E →L[𝕜] E, fun x : M ↦ TangentSpace I x →L[𝕜] TangentSpace I x⟯) {z : S}
    (hw : ContinuousAt (fun z ↦ (⟨u z, w z⟩ : TangentBundle I M)) z)
    (hη : ContinuousAt (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)) z) :
    ContinuousAt (fun z ↦ η z (B (u z) (w z))) z := by
  have hu : ContinuousAt u z :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp hw
  have hBw := (B.contMDiff.continuous.continuousAt.comp hu).clm_bundle_apply hw
  have h := ContinuousAt.clm_bundle_apply (E₂ := Bundle.Trivial M 𝕜) hη hBw
  exact continuous_snd.continuousAt.comp
    ((Bundle.Trivial.homeomorphProd M 𝕜).continuous.continuousAt.comp h)

end ContMDiffSection

namespace OpenPartialHomeomorph.MDifferentiable

variable {𝕜 E H G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [NormedAddCommGroup G] [NormedSpace 𝕜 G] {c : OpenPartialHomeomorph M G}

/-- **Covectors read in a chart.** For an open partial homeomorphism `c` into a normed space,
differentiable with its inverse, and `x` in its source, reading a covector `ξ` at `x` in `c` as
`ξ ∘ D(c⁻¹)(c x)` is a bijection onto the covectors of `G`. -/
theorem comp_mfderiv_symm_bijective (hc : c.MDifferentiable I 𝓘(𝕜, G)) {x : M}
    (hx : x ∈ c.source) :
    Function.Bijective fun ξ : TangentSpace I x →L[𝕜] 𝕜 ↦ ξ ∘L mfderiv 𝓘(𝕜, G) I c.symm (c x) := by
  refine ⟨fun ξ₁ ξ₂ h ↦ ContinuousLinearMap.ext fun w ↦ ?_, fun η ↦ ?_⟩
  · obtain ⟨u, rfl⟩ := hc.symm.mfderiv_surjective (c.map_source hx) w
    exact congr($h u)
  · refine ⟨η ∘L mfderiv I 𝓘(𝕜, G) c (c.symm (c x)), ContinuousLinearMap.ext fun u ↦ ?_⟩
    exact congr_arg η congr($(hc.comp_symm_deriv (c.map_source hx)) u)

end OpenPartialHomeomorph.MDifferentiable
