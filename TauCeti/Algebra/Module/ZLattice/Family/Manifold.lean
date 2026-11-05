/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Geometry.Manifold.Submersion
public import TauCeti.Algebra.Module.ZLattice.Family.Fiber
public import TauCeti.Geometry.Manifold.Algebra.Quotient

import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# The manifold structure of a family of tori

Let `P : Y → (Λ →ₗ[ℤ] E)` be a family of full lattices in a finite-dimensional normed space `E`
over a manifold `Y`, as in `TauCeti.Algebra.Module.ZLattice.Family.Basic`: each period
`y ↦ P y l` is continuous, and each `P y` is injective with discrete, full range. The period
translation action `l +ᵥ (y, v) = (y, v + P y l)` of `Λ` on `Y × E` is free and properly
discontinuous, so its standard orbit space `(Y × E)/Λ` carries Mathlib's quotient atlas
`AddAction.instChartedSpaceQuotient`, installed here from the direct hypotheses on `P` as
`TauCeti.torusFamilyChartedSpace`.

If the periods are `C^n` for a model `I` of `Y` over a field `𝕜`, the period translations are
`C^n`, so `(Y × E)/Λ` is a `C^n` manifold and the orbit map `q : Y × E → (Y × E)/Λ` is a `C^n`
local diffeomorphism. It is also a covering map
(`TauCeti.isAddQuotientCoveringMap_torusFamily_mk`). The projection `p : (Y × E)/Λ → Y` of the
family is a `C^n` submersion with complement `E`: in a chart of `(Y × E)/Λ` read through a local
section of `q` and in the matching chart of `Y`, it is the first projection. The zero section
`y ↦ [y, 0]` and the inclusion `E ⧸ LinearMap.range (P y) → (Y × E)/Λ` of each fibre are `C^n`.

For a complex manifold `Y`, a finite-dimensional complex normed space `E`, `𝕜 = ℂ` and holomorphic
periods, these say that `(Y × E)/Λ` is a complex manifold, `q` is a local biholomorphism and a
covering map, and `p` is a holomorphic submersion. The maps `q` and `p` are different: `q` has
discrete fibres, while the fibre of `p` over `y` is the torus `E ⧸ LinearMap.range (P y)`
(`TauCeti.torusFamilyFiberHomeomorph`), so `p` is not a local diffeomorphism when `E ≠ 0`.

Over `𝕜 = ℝ` or `ℂ`, for a boundaryless finite-dimensional model of `Y` and `n ≥ 1`, the inclusion
`E ⧸ LinearMap.range (P y) → (Y × E)/Λ` of the fibre over `y` is a `C^n` embedding in Mathlib's
sense, `Manifold.IsSmoothEmbedding`: an immersion which is a homeomorphism onto its image. Its
image is the literal fibre `p⁻¹(y)` (`TauCeti.range_torusFamilyFiberMap`), its tangent image at
each point is the vertical tangent space `ker dp`, and a map into `E ⧸ LinearMap.range (P y)` is
`C^n` exactly when its composite with the inclusion is. For a complex family this identifies the
fibre over `y`, as an embedded complex submanifold of the total space, biholomorphically with the
complex torus `E ⧸ LinearMap.range (P y)`. The immersion property is read off from a local left
inverse of the inclusion: a local inverse of `q` near `[y, v]`, followed by the second projection
and the orbit map of `E`.

The real structure of `E` enters only through the lattice hypotheses, and the regularity statements
use the `𝕜`-structure; for a complex space `E` these are its real and complex structures.

## Main definitions

* `TauCeti.torusFamilyChartedSpace`: the quotient atlas on `(Y × E)/Λ`.

## Main results

* `TauCeti.contMDiffConstVAdd_periodAddAction`: `C^n` periods give `C^n` period translations.
* `TauCeti.isManifold_torusFamily`: `(Y × E)/Λ` is a `C^n` manifold.
* `TauCeti.isLocalDiffeomorph_torusFamily_mk`: the orbit map `q` is a `C^n` local
  diffeomorphism.
* `TauCeti.isSubmersionOfComplement_torusFamilyProjection`: the projection `p` is a `C^n`
  submersion with complement `E`; in particular it is `C^n`
  (`TauCeti.contMDiff_torusFamilyProjection`).
* `TauCeti.contMDiff_torusFamily_mk_zero`: the zero section is `C^n`.
* `TauCeti.contMDiff_torusFamilyFiberMap`: the inclusion of each fibre is `C^n`.
* `TauCeti.isImmersion_torusFamilyFiberMap`,
  `TauCeti.isSmoothEmbedding_torusFamilyFiberMap`: the inclusion of each fibre is a `C^n`
  immersion and a `C^n` embedding.
* `TauCeti.range_mfderiv_torusFamilyFiberMap`: the tangent image of the fibre is the kernel of
  the derivative of the projection.
* `TauCeti.contMDiff_torusFamilyFiberMap_comp_iff`: a map into the fibre torus is `C^n` exactly
  when its composite with the inclusion of the fibre is.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices).
* Tau Ceti PR [#20968](https://github.com/TauCetiProject/TauCeti/pull/20968) (closed, unmerged)
  installed the same quotient atlas and proved the manifold and local-diffeomorphism statements;
  `TauCeti.torusFamilyChartedSpace`, `TauCeti.isManifold_torusFamily` and
  `TauCeti.isLocalDiffeomorph_torusFamily_mk` follow its outline.
-/

public section

open Function Set
open scoped Manifold ContDiff

namespace TauCeti

section Translation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {EY : Type*} [NormedAddCommGroup EY]
  [NormedSpace 𝕜 EY] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 EY H}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (P : Y → Λ →ₗ[ℤ] E) {n : WithTop ℕ∞}

/-- If every period `y ↦ P y l` is `C^n`, then every period translation
`(y, v) ↦ (y, v + P y l)` of `Y × E` is `C^n`. -/
theorem contMDiffConstVAdd_periodAddAction (hP : ∀ l, ContMDiff I 𝓘(𝕜, E) n fun y ↦ P y l) :
    letI := periodAddAction P
    ContMDiffConstVAdd (I.prod 𝓘(𝕜, E)) n Λ (Y × E) := by
  let _ := periodAddAction P
  refine ⟨fun l ↦ ?_⟩
  simp only [periodAddAction_vadd]
  exact contMDiff_fst.prodMk (contMDiff_snd.add ((hP l).comp contMDiff_fst))

end Translation

section Quotient

variable {Y : Type*} [TopologicalSpace Y] {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ]
  [Module.Finite ℤ Λ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  [T2Space Y] [LocallyCompactSpace Y]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))

variable {H : Type*} [TopologicalSpace H] [ChartedSpace H Y]

/-- **The atlas of a family of tori.** For a continuous family of full lattices, Mathlib's quotient
atlas `AddAction.instChartedSpaceQuotient` on the orbit space `(Y × E)/Λ` of the period
translation action: its charts are local sections of the orbit map followed by charts of `Y × E`.
It does not depend on the proofs `hcont` and `hinj`. -/
@[instance_reducible]
noncomputable def torusFamilyChartedSpace :
    letI := periodAddAction P
    ChartedSpace (ModelProd H E) (AddAction.orbitRel.Quotient Λ (Y × E)) :=
  letI := periodAddAction P
  haveI := continuousConstVAdd_periodAddAction P hcont
  haveI := properlyDiscontinuousVAdd_periodAddAction P hcont hinj
  haveI := isCancelVAdd_periodAddAction P hinj
  AddAction.instChartedSpaceQuotient

end Quotient

section Regularity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {EY : Type*} [NormedAddCommGroup EY]
  [NormedSpace 𝕜 EY] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 EY H}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [T2Space Y] [LocallyCompactSpace Y]
  {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace 𝕜 E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hinj : ∀ y, Injective (P y)) {n : WithTop ℕ∞} [IsManifold I n Y]
  (hP : ∀ l, ContMDiff I 𝓘(𝕜, E) n fun y ↦ P y l)

/-- **A family of tori is a manifold.** For a `C^n` family of full lattices, the orbit space
`(Y × E)/Λ` of the period translation action is a `C^n` manifold for the quotient atlas. -/
theorem isManifold_torusFamily :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    IsManifold (I.prod 𝓘(𝕜, E)) n (AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  have := continuousConstVAdd_periodAddAction P fun l ↦ (hP l).continuous
  have := properlyDiscontinuousVAdd_periodAddAction P (fun l ↦ (hP l).continuous) hinj
  have := isCancelVAdd_periodAddAction P hinj
  have := contMDiffConstVAdd_periodAddAction P hP
  exact instIsManifoldAddQuotient

/-- **The orbit map is a local diffeomorphism.** For a `C^n` family of full lattices, the orbit map
`Y × E → (Y × E)/Λ` is a `C^n` local diffeomorphism for the quotient atlas. For holomorphic
periods of a complex family it is a local biholomorphism. -/
theorem isLocalDiffeomorph_torusFamily_mk :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    IsLocalDiffeomorph (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, E)) n
      (Quotient.mk (AddAction.orbitRel Λ (Y × E))) := by
  let _ := periodAddAction P
  have := continuousConstVAdd_periodAddAction P fun l ↦ (hP l).continuous
  have := properlyDiscontinuousVAdd_periodAddAction P (fun l ↦ (hP l).continuous) hinj
  have := isCancelVAdd_periodAddAction P hinj
  have := contMDiffConstVAdd_periodAddAction P hP
  exact isLocalDiffeomorph_addQuotientMk

/-- **The projection of a family of tori is a submersion.** For a `C^n` family of full lattices,
the projection `(Y × E)/Λ → Y` is a `C^n` submersion with complement `E`: around each point there
are a chart of `(Y × E)/Λ`, given by a local section of the orbit map followed by a product chart
of `Y × E`, and a chart of `Y`, in which the projection is `(u, v) ↦ u`. -/
theorem isSubmersionOfComplement_torusFamilyProjection :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    Manifold.IsSubmersionOfComplement E (I.prod 𝓘(𝕜, E)) I n (torusFamilyProjection P) := by
  let _ := periodAddAction P
  have := continuousConstVAdd_periodAddAction P fun l ↦ (hP l).continuous
  have := properlyDiscontinuousVAdd_periodAddAction P (fun l ↦ (hP l).continuous) hinj
  have := isCancelVAdd_periodAddAction P hinj
  have := isManifold_torusFamily P hinj hP
  refine Manifold.isSubmersionOfComplement_iff.2 fun x ↦ ?_
  -- The chart of `(Y × E)/Λ` at `x` is a local section `s` of the orbit map followed by the
  -- product chart of `Y × E` at a point `z`; the chart of `Y` at `z.1` is the matching chart.
  obtain ⟨s, z, hs, hsq⟩ := exists_trans_eq_of_mem_atlas_addQuotient (chart_mem_atlas
    (ModelProd H E) x)
  set e := chartAt (ModelProd H E) x
  have hsymm : ∀ w ∈ s.target, s.symm w = Quotient.mk _ w := fun w hw ↦ by
    rw [← hsq _ (s.map_target hw), s.right_inv hw]
  have hproj : ∀ x' ∈ e.source, torusFamilyProjection P x' = (s x').1 := fun x' hx' ↦ by
    rw [← torusFamilyProjection_mk P (s x'), hsq x' (hs ▸ hx').1]
  have hx : x ∈ e.source := mem_chart_source _ x
  refine Manifold.IsSubmersionAtOfComplement.mk_of_charts (ContinuousLinearEquiv.refl 𝕜 (EY × E))
    e (chartAt H z.1) hx ?_ (IsManifold.chart_mem_maximalAtlas x)
    (IsManifold.chart_mem_maximalAtlas z.1) ?_ ?_
  · rw [hproj x hx]
    exact (hs ▸ hx).2.1
  · intro x' hx'
    rw [mem_preimage, hproj x' hx']
    exact (hs ▸ hx').2.1
  · intro w hw
    rw [← hs] at hw ⊢
    rw [OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.trans_target] at hw
    obtain ⟨⟨hwc, hws⟩, hwI⟩ := hw
    simp only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_target,
      ModelWithCorners.prod_symm_apply] at hwc
    rw [ModelWithCorners.range_prod] at hwI
    simp only [comp_apply, OpenPartialHomeomorph.extend_coe_symm,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans]
    rw [hsymm _ hws, torusFamilyProjection_mk]
    simp only [prodChartedSpace_chartAt, OpenPartialHomeomorph.extend_coe,
      ModelWithCorners.prod_symm_apply, ContinuousLinearEquiv.coe_refl', id_eq, comp_apply]
    rw [OpenPartialHomeomorph.prod_symm_apply, (chartAt H z.1).right_inv hwc.1, I.right_inv hwI.1]

/-- **The projection of a family of tori is `C^n`.** For a `C^n` family of full lattices, the
projection `(Y × E)/Λ → Y` is `C^n`; for holomorphic periods of a complex family it is
holomorphic. -/
theorem contMDiff_torusFamilyProjection :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ContMDiff (I.prod 𝓘(𝕜, E)) I n (torusFamilyProjection P) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  exact (isSubmersionOfComplement_torusFamilyProjection P hinj hP).contMDiff

/-- **The zero section of a family of tori is `C^n`.** For a `C^n` family of full lattices, the
zero section `y ↦ [y, 0]` of the projection `(Y × E)/Λ → Y` is `C^n`. -/
theorem contMDiff_torusFamily_mk_zero :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ContMDiff I (I.prod 𝓘(𝕜, E)) n
      fun y : Y ↦ Quotient.mk (AddAction.orbitRel Λ (Y × E)) (y, (0 : E)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  exact (isLocalDiffeomorph_torusFamily_mk P hinj hP).contMDiff.comp
    (contMDiff_id.prodMk contMDiff_const)

/-- **The inclusion of a fibre is `C^n`.** For a `C^n` family of full lattices, the map
`E ⧸ LinearMap.range (P y) → (Y × E)/Λ`, `[v] ↦ [y, v]`, from the quotient manifold of `E` by the
periods at `y` is `C^n`. -/
theorem contMDiff_torusFamilyFiberMap (y : Y) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ContMDiff 𝓘(𝕜, E) (I.prod 𝓘(𝕜, E)) n (torusFamilyFiberMap P y) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  rw [← (isLocalDiffeomorph_addQuotientMk (I := 𝓘(𝕜, E)) (n := n)
    (G := LinearMap.range (P y)) (M := E)).contMDiff_comp_iff Quotient.mk_surjective le_rfl,
    show torusFamilyFiberMap P y ∘ Quotient.mk _ = Quotient.mk _ ∘ fun v ↦ (y, v) from
      funext (torusFamilyFiberMap_mk P y)]
  exact (isLocalDiffeomorph_torusFamily_mk P hinj hP).contMDiff.comp
    (contMDiff_const.prodMk contMDiff_id)

end Regularity

section Embedding

variable {𝕜 : Type*} [RCLike 𝕜] {EY : Type*} [NormedAddCommGroup EY] [NormedSpace 𝕜 EY]
  [FiniteDimensional 𝕜 EY] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 EY H}
  [I.Boundaryless] {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [T2Space Y]
  [LocallyCompactSpace Y] {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hinj : ∀ y, Injective (P y)) {n : WithTop ℕ∞} [IsManifold I n Y]
  (hP : ∀ l, ContMDiff I 𝓘(𝕜, E) n fun y ↦ P y l)

/-- **The inclusion of a fibre is an immersion.** For a `C^n` family of full lattices over a
boundaryless manifold with finite-dimensional model, `n ≥ 1`, the map
`E ⧸ LinearMap.range (P y) → (Y × E)/Λ`, `[v] ↦ [y, v]`, is a `C^n` immersion. -/
theorem isImmersion_torusFamilyFiberMap (hn : 1 ≤ n) (y : Y) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    Manifold.IsImmersion 𝓘(𝕜, E) (I.prod 𝓘(𝕜, E)) n (torusFamilyFiberMap P y) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  have := isManifold_torusFamily P hinj hP
  have : CompleteSpace EY := FiniteDimensional.complete 𝕜 EY
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hφ := contMDiff_torusFamilyFiberMap P hinj hP y
  refine isImmersion_iff_forall_isImmersionAt.2 fun z ↦ ?_
  induction z using Quotient.inductionOn with | h v => ?_
  -- A left inverse near `[v]`: a local inverse of the orbit map `q` at `(y, v)`, followed by the
  -- second projection and the orbit map of `E`.
  have hq := isLocalDiffeomorph_torusFamily_mk P hinj hP (y, v)
  let g : AddAction.orbitRel.Quotient Λ (Y × E) →
      AddAction.orbitRel.Quotient (LinearMap.range (P y)) E :=
    fun x ↦ Quotient.mk _ (hq.localInverse x).2
  have hv : torusFamilyFiberMap P y (Quotient.mk _ v) = Quotient.mk _ (y, v) :=
    torusFamilyFiberMap_mk P y v
  refine hφ.contMDiffOn.isImmersionAt_of_comp_eventuallyEq_id (g := g) isOpen_univ (mem_univ _) hn
    ?_ ?_
  · rw [hv]
    exact (isLocalDiffeomorph_addQuotientMk (I := 𝓘(𝕜, E)) (n := n)
      (G := LinearMap.range (P y)) (M := E) _).mdifferentiableAt hn0 |>.comp _
      (contMDiff_snd.mdifferentiableAt hn0 |>.comp _ (hq.mdifferentiableAt_localInverse hn0))
  · have hU : hq.localInverse.source ∈ nhds (torusFamilyFiberMap P y (Quotient.mk _ v)) := by
      rw [hv]
      exact hq.localInverse_open_source.mem_nhds hq.localInverse_mem_source
    filter_upwards [hφ.continuous.continuousAt.preimage_mem_nhds hU] with z hz
    -- The local inverse sends `[y, w]` to a point over `y`, which then differs from `(y, w)` by a
    -- period at `y`; the inclusion of the fibre is injective.
    have hqz := hq.localInverse_right_inv hz
    have hy : (hq.localInverse (torusFamilyFiberMap P y z)).1 = y := by
      simpa using congrArg (torusFamilyProjection P) hqz
    apply torusFamilyFiberMap_injective P y
    have hp : ((y, (hq.localInverse (torusFamilyFiberMap P y z)).2) : Y × E) =
        hq.localInverse (torusFamilyFiberMap P y z) := Prod.ext hy.symm rfl
    rw [comp_apply, torusFamilyFiberMap_mk, id_eq, hp, hqz]

/-- **The inclusion of a fibre is an embedding.** For a `C^n` family of full lattices over a
boundaryless manifold with finite-dimensional model, `n ≥ 1`, the map
`E ⧸ LinearMap.range (P y) → (Y × E)/Λ`, `[v] ↦ [y, v]`, is a `C^n` embedding, with image the
fibre over `y` (`TauCeti.range_torusFamilyFiberMap`). For holomorphic periods of a complex family
and `n = ω`, it embeds the complex torus `E ⧸ LinearMap.range (P y)` holomorphically onto the
fibre. -/
theorem isSmoothEmbedding_torusFamilyFiberMap (hn : 1 ≤ n) (y : Y) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    Manifold.IsSmoothEmbedding 𝓘(𝕜, E) (I.prod 𝓘(𝕜, E)) n (torusFamilyFiberMap P y) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  exact ⟨isImmersion_torusFamilyFiberMap P hinj hP hn y,
    isEmbedding_torusFamilyFiberMap P y fun l ↦ (hP l).continuous⟩

/-- **The tangent space of a fibre is vertical.** For a `C^n` family of full lattices over a
boundaryless manifold with finite-dimensional model, `n ≥ 1`, the image of the derivative of the
inclusion `E ⧸ LinearMap.range (P y) → (Y × E)/Λ` at any point is the kernel of the derivative of
the projection `(Y × E)/Λ → Y` at its image. -/
theorem range_mfderiv_torusFamilyFiberMap (hn : 1 ≤ n) (y : Y)
    (z : AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    (mfderiv 𝓘(𝕜, E) (I.prod 𝓘(𝕜, E)) (torusFamilyFiberMap P y) z).range =
      (mfderiv (I.prod 𝓘(𝕜, E)) I (torusFamilyProjection P) (torusFamilyFiberMap P y z)).ker := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  have := isManifold_torusFamily P hinj hP
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hp := (isSubmersionOfComplement_torusFamilyProjection P hinj hP).isSubmersionAt
    (torusFamilyFiberMap P y z)
  refine IsRegularPoint.range_mfderiv_eq_ker_mfderiv
    (.of_forall (torusFamilyProjection_fiberMap P y))
    (isRegularPoint_iff.2 (hp.surjective_mfderiv hn0))
    (((isImmersion_torusFamilyFiberMap P hinj hP hn y).isImmersionAt z).mfderiv_injective hn0) ?_
  rw [Module.finrank_prod, add_comm]

/-- **Maps into a fibre.** For a `C^n` family of full lattices over a boundaryless manifold with
finite-dimensional model, `n ≥ 1`, a map `g` into `E ⧸ LinearMap.range (P y)` is `C^n` exactly
when its composite with the inclusion `[v] ↦ [y, v]` of the fibre over `y` is `C^n`. Every map into
the total space with values in the fibre over `y` is such a composite
(`TauCeti.range_torusFamilyFiberMap`). -/
theorem contMDiff_torusFamilyFiberMap_comp_iff (hn : 1 ≤ n) (y : Y)
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
    {J : ModelWithCorners 𝕜 EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
    {g : M → AddAction.orbitRel.Quotient (LinearMap.range (P y)) E} :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ContMDiff J (I.prod 𝓘(𝕜, E)) n (torusFamilyFiberMap P y ∘ g) ↔ ContMDiff J 𝓘(𝕜, E) n g := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  rw [ContMDiff.iff_comp_isImmersion (isImmersion_torusFamilyFiberMap P hinj hP hn y),
    and_iff_right_of_imp]
  exact fun h ↦ (isEmbedding_torusFamilyFiberMap P y fun l ↦ (hP l).continuous).continuous_iff.2
    h.continuous

end Embedding

end TauCeti
