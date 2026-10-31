/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Submersion
public import TauCeti.Algebra.Module.ZLattice.Family.Fiber
public import TauCeti.Geometry.Manifold.Algebra.Quotient

import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Manifold.Submersion

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

end TauCeti
