/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
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

This file computes the charts in coordinates. The preferred chart at a covector over `x₀` sends a
covector `p` at `x` to `(φ₀ x, p ∘ d(φ₀⁻¹))`, where `φ₀` is the extended chart of `M` at `x₀`
(`TauCeti.CotangentBundle.extChartAt_apply`, `TauCeti.CotangentBundle.extChartAt_symm_apply`).
Consequently, a change of base chart `φ = φ₁ ∘ φ₀⁻¹` acts on cotangent coordinates by

`(q, p) ↦ (φ q, p ∘ (dφ_q)⁻¹)`,

the derivative of the inverse change of charts at `φ q`
(`TauCeti.CotangentBundle.extChartAt_extChartAt_symm`). The new covector pairs with the
pushed-forward tangent vector as the old covector pairs with the original one
(`TauCeti.CotangentBundle.extChartAt_extChartAt_symm_snd_apply_fderivWithin`).
This is the transformation law of covector components, dual to that of tangent vectors.
A map into the single fibre over a fixed point `q` moves only the fibre coordinate in these
charts, so its derivative is that of its covector part (`TauCeti.CotangentBundle.hasMFDerivAt_mk`).

Covectors pull back along the differential of a map `f : M → N`: a covector `p` at `f x` gives the
covector `p ∘ df_x` at `x`. For a family of covectors over a parameter manifold this is smooth:
`TauCeti.CotangentBundle.contMDiffAt_mk_comp_mfderiv` loses one degree of smoothness of `f`, as
the differential does. It gives the smoothness of the cotangent lift of a diffeomorphism
(`Diffeomorph.cotangent`). The map may also vary smoothly with the parameter
(`TauCeti.CotangentBundle.contMDiffAt_mk_comp_mfderiv_uncurry`), as the slice inclusions of a
product manifold do.

The construction follows the Zulip discussion `Cotangent Bundle as a Manifold` in the channel
`Is there code for X?`, which observed that Mathlib's continuous-linear-map bundle operations
already supply the cotangent total space with its manifold structure.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 11.
-/

public section

open Bundle Set
open scoped Manifold

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
    (h : ∀ v : TangentSpace I z.proj, z.2 v = w.2 v) : z = w := by
  obtain ⟨x, p⟩ := z
  obtain ⟨y, q⟩ := w
  obtain rfl : x = y := hproj
  exact congrArg (TotalSpace.mk' (E →L[𝕜] 𝕜) x) (ContinuousLinearMap.ext h)

variable [IsManifold I 1 M]

/-- The preferred chart of the cotangent bundle at `z₀` sends a covector `z` to the chart image of
its base point and to the covector precomposed with the inverse of the tangent chart at `z₀`. -/
theorem extChartAt_apply (z₀ z : CotangentBundle I M) :
    extChartAt (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) z₀ z =
      (extChartAt I z₀.proj z.proj,
        z.2 ∘L (trivializationAt E (TangentSpace I) z₀.proj).symmL 𝕜 z.proj) := by
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

section Pullback

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N]
  {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  {m n : WithTop ℕ∞}

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
      (fun z ↦ (TotalSpace.mk' (E →L[𝕜] 𝕜) (g z) ((Ψ z).2 ∘L mfderiv I J (f z) (g z)) :
        CotangentBundle I M)) z₀ := by
  rw [contMDiffAt_hom_bundle] at hΨ ⊢
  refine ⟨hg, (hΨ.2.clm_comp hd).congr_of_eventuallyEq ?_⟩
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

/-- **Pulling covectors back along a map is smooth.** Let `Ψ z` be a covector at `f (g z)`,
depending on a parameter `z`. Its pullback along the differential of `f` at `g z`,
`Ψ z ∘ df_(g z)`, is a covector at `g z`. If `Ψ` and `g` are `C^m` at `z₀` and `f` is `C^n` at
`g z₀` with `m + 1 ≤ n`, the family of pulled-back covectors is `C^m` at `z₀`. -/
theorem contMDiffAt_mk_comp_mfderiv {Ψ : X → CotangentBundle J N} {g : X → M} {f : M → N}
    {z₀ : X} (hΨg : ∀ z, (Ψ z).proj = f (g z))
    (hΨ : ContMDiffAt IX (J.prod 𝓘(𝕜, E' →L[𝕜] 𝕜)) m Ψ z₀) (hg : ContMDiffAt IX I m g z₀)
    (hf : ContMDiffAt I J n f (g z₀)) (hmn : m + 1 ≤ n) :
    ContMDiffAt IX (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) m
      (fun z ↦ (TotalSpace.mk' (E →L[𝕜] 𝕜) (g z) ((Ψ z).2 ∘L mfderiv I J f (g z)) :
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
      (fun z ↦ (TotalSpace.mk' (E →L[𝕜] 𝕜) (g z) ((Ψ z).2 ∘L mfderiv I J f (g z)) :
        CotangentBundle I M)) :=
  fun z ↦ contMDiffAt_mk_comp_mfderiv hΨg (hΨ z) (hg z) (hf (g z)) hmn

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
      (fun z ↦ (TotalSpace.mk' (E →L[𝕜] 𝕜) (g z) ((Ψ z).2 ∘L mfderiv I J (f z) (g z)) :
        CotangentBundle I M)) z₀ :=
  contMDiffAt_mk_comp_mfderiv_of_inTangentCoordinates hΨg hΨ hg
    (hf.continuousAt.comp (f := fun z ↦ (z, g z)) (continuousAt_id.prodMk hg.continuousAt))
    (hf.mfderiv f g hg hmn)

end Pullback

end CotangentBundle

end TauCeti
