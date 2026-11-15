/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Topology.Homeomorph.Extend
import TauCeti.Data.Set.Function

/-!
# Extending diffeomorphisms by the identity

A diffeomorphism of an open part of a manifold extends by the identity when its moving points
are contained in a closed subset of the ambient manifold lying inside that open part.
`IsLocalDiffeomorph.exists_diffeomorph_extend` gives this extension along an open embedding which
is a local diffeomorphism. The source and ambient manifold may have different models.

For a compact set in the source, its image is closed in a Hausdorff ambient manifold, giving
`IsLocalDiffeomorph.exists_diffeomorph_extend_of_isCompact`. In particular,
`Diffeomorph.exists_extend_of_isCompact` extends a compactly supported diffeomorphism of any open
submanifold. These results transplant diffeomorphisms constructed in coordinates to the ambient
manifold while keeping control of where points move.

When the open part is the source of an extended chart, the extension has an explicit formula,
`TauCeti.chartExtend`: a map `f` of the model space which fixes every point outside a compact
subset `K` of the interior of the chart target, and maps `K` into itself, is read through the chart
on the chart source and extended by the identity elsewhere. The formula makes the dependence on
`f` visible: a family of such maps depending `C^n`-smoothly on a parameter gives a family of
self-maps of the manifold depending `C^n`-smoothly on the parameter
(`TauCeti.contMDiff_chartExtend`). A diffeomorphism of the model space supported in `K` extends to
the diffeomorphism `Diffeomorph.chartExtend` of the manifold.

The underlying homeomorphism is supplied by
`Topology.IsOpenEmbedding.exists_homeomorph_extend`. Smoothness follows locally: on the open
image, cancel the coordinate local diffeomorphism; away from the closed set, the extension is
locally the identity. This applies to the inverse as well, without any loss of regularity.

## References

* R. Palais, *Extending diffeomorphisms*, Proc. Amer. Math. Soc. 11 (1960), 274–277,
  for the use of coordinate extensions in ambient extension arguments.
* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8.
-/

public section

open Set Topology
open scoped Manifold ContDiff

namespace IsLocalDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞} {χ : N → M}

/-- A diffeomorphism of `N` extends along a smooth open embedding `χ : N → M` by the identity
if its moving points lie over a closed set `C ⊆ range χ`. The extension intertwines the original
diffeomorphism with `χ` and fixes every point outside `C`. -/
theorem exists_diffeomorph_extend (hχ : IsLocalDiffeomorph J I n χ)
    (hχo : IsOpenEmbedding χ) (Λ : N ≃ₘ^n⟮J, J⟯ N) {C : Set M} (hC : IsClosed C)
    (hCχ : C ⊆ range χ) (hΛ : ∀ z, χ z ∉ C → Λ z = z) :
    ∃ Φ : M ≃ₘ^n⟮I, I⟯ M, (∀ z, Φ (χ z) = χ (Λ z)) ∧ ∀ y ∉ C, Φ y = y := by
  obtain ⟨Φ, hΦχ, hΦC⟩ := hχo.exists_homeomorph_extend Λ.toHomeomorph hC hCχ hΛ
  simp only [Diffeomorph.coe_toHomeomorph] at hΦχ
  -- Any homeomorphism with these local formulas is smooth. Use the same argument for its inverse.
  have hsmooth (Ψ : M ≃ₜ M) (L : N ≃ₘ^n⟮J, J⟯ N)
      (hΨχ : ∀ z, Ψ (χ z) = χ (L z)) (hΨC : ∀ y ∉ C, Ψ y = y) :
      ContMDiff I I n Ψ := by
    intro y
    by_cases hy : y ∈ range χ
    · obtain ⟨z, rfl⟩ := hy
      apply ((hχ z).contMDiffAt_comp_iff le_rfl).1
      have heq : Ψ ∘ χ = χ ∘ L := funext hΨχ
      rw [heq]
      exact (hχ.contMDiff.comp L.contMDiff).contMDiffAt
    · have hyC : y ∉ C := fun hyC ↦ hy (hCχ hyC)
      apply contMDiffAt_id.congr_of_eventuallyEq
      filter_upwards [hC.isOpen_compl.mem_nhds hyC] with w hw
      exact hΨC w hw
  have hinvχ (z : N) : Φ.symm (χ z) = χ (Λ.symm z) := by
    apply Φ.injective
    rw [Φ.apply_symm_apply, hΦχ, Λ.apply_symm_apply]
  have hinvC (y : M) (hy : y ∉ C) : Φ.symm y = y := by
    rw [Φ.symm_apply_eq, hΦC y hy]
  exact ⟨{ toEquiv := Φ.toEquiv
           contMDiff_toFun := hsmooth Φ Λ hΦχ hΦC
           contMDiff_invFun := hsmooth Φ.symm Λ.symm hinvχ hinvC }, hΦχ, hΦC⟩

/-- A diffeomorphism fixing the complement of a compact set `K` extends along a smooth open
embedding into a Hausdorff manifold, fixing the complement of the compact image `χ '' K`. -/
theorem exists_diffeomorph_extend_of_isCompact [T2Space M]
    (hχ : IsLocalDiffeomorph J I n χ) (hχo : IsOpenEmbedding χ)
    (Λ : N ≃ₘ^n⟮J, J⟯ N) {K : Set N} (hK : IsCompact K) (hΛ : ∀ z ∉ K, Λ z = z) :
    ∃ Φ : M ≃ₘ^n⟮I, I⟯ M, (∀ z, Φ (χ z) = χ (Λ z)) ∧
      ∀ y ∉ χ '' K, Φ y = y := by
  apply hχ.exists_diffeomorph_extend hχo Λ (hK.image hχo.continuous).isClosed
    (image_subset_range χ K)
  intro z hz
  exact hΛ z fun hzK ↦ hz ⟨z, hzK, rfl⟩

end IsLocalDiffeomorph

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {n : WithTop ℕ∞} {U : TopologicalSpace.Opens M}

/-- A diffeomorphism of an open submanifold, equal to the identity off a compact set `K` in
that submanifold, extends to an ambient diffeomorphism equal to the identity off `K`'s image.
In particular, the ambient diffeomorphism fixes every point outside the open submanifold. -/
theorem exists_extend_of_isCompact (Λ : U ≃ₘ^n⟮I, I⟯ U) {K : Set U}
    (hK : IsCompact K) (hΛ : ∀ z ∉ K, Λ z = z) :
    ∃ Φ : M ≃ₘ^n⟮I, I⟯ M, (∀ z : U, Φ z = Λ z) ∧
      ∀ y ∉ Subtype.val '' K, Φ y = y :=
  TauCeti.isLocalDiffeomorph_subtype_val.exists_diffeomorph_extend_of_isCompact
    U.isOpen.isOpenEmbedding_subtypeVal Λ hK hΛ

end Diffeomorph

/-! ### Extension through a chart -/

namespace TauCeti

section ChartExtend

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The extension by the identity of a map `f` of the model space through the extended chart at
`x`: a point `z` of the chart source goes to `(extChartAt I x).symm (f (extChartAt I x z))`, and
every other point is fixed. -/
noncomputable def chartExtend (f : E → E) (x : M) (z : M) : M :=
  letI := Classical.dec (z ∈ (extChartAt I x).source)
  if z ∈ (extChartAt I x).source then (extChartAt I x).symm (f (extChartAt I x z)) else z

variable {I} {f g : E → E} {x z : M} {K : Set E}

/-- On the chart source, the extension of `f` is `f` read through the chart. -/
theorem chartExtend_of_mem (hz : z ∈ (extChartAt I x).source) :
    chartExtend I f x z = (extChartAt I x).symm (f (extChartAt I x z)) := by
  simp only [chartExtend, hz, ↓reduceIte]

/-- Off the chart source, the extension of `f` is the identity. -/
theorem chartExtend_of_notMem (hz : z ∉ (extChartAt I x).source) : chartExtend I f x z = z := by
  simp only [chartExtend, hz, ↓reduceIte]

/-- On the chart, the extension of `f` reads as `f`. -/
theorem chartExtend_extChartAt_symm {p : E} (hp : p ∈ (extChartAt I x).target) :
    chartExtend I f x ((extChartAt I x).symm p) = (extChartAt I x).symm (f p) := by
  rw [chartExtend_of_mem ((extChartAt I x).map_target hp), (extChartAt I x).right_inv hp]

/-- The extension of a map fixing every point outside `K` fixes every point outside the preimage
of `K` under the chart. -/
theorem chartExtend_eq_self (hf : ∀ p ∉ K, f p = p) (hz : z ∉ (extChartAt I x).symm '' K) :
    chartExtend I f x z = z := by
  by_cases hs : z ∈ (extChartAt I x).source
  · have hK : extChartAt I x z ∉ K := fun h ↦ hz ⟨_, h, (extChartAt I x).left_inv hs⟩
    rw [chartExtend_of_mem hs, hf _ hK, (extChartAt I x).left_inv hs]
  · exact chartExtend_of_notMem hs

/-- The extension of the identity is the identity. -/
@[simp]
theorem chartExtend_id : chartExtend I id x = id := by
  ext z
  by_cases hs : z ∈ (extChartAt I x).source
  · rw [chartExtend_of_mem hs, id, id, (extChartAt I x).left_inv hs]
  · exact chartExtend_of_notMem hs

/-- Extension through a chart is compatible with composition, for maps fixing every point outside
a subset `K` of the chart target and mapping `K` into itself. -/
theorem chartExtend_comp (hKt : K ⊆ (extChartAt I x).target) (hg : ∀ p ∉ K, g p = p)
    (hgK : MapsTo g K K) : chartExtend I f x ∘ chartExtend I g x = chartExtend I (f ∘ g) x := by
  ext z
  by_cases hs : z ∈ (extChartAt I x).source
  · rw [Function.comp_apply, chartExtend_of_mem (f := g) hs, chartExtend_of_mem (f := f ∘ g) hs]
    by_cases hK : extChartAt I x z ∈ K
    · rw [chartExtend_extChartAt_symm (hKt (hgK hK)), Function.comp_apply]
    · rw [hg _ hK, (extChartAt I x).left_inv hs, chartExtend_of_mem hs, Function.comp_apply,
        hg _ hK]
  · rw [Function.comp_apply, chartExtend_of_notMem hs, chartExtend_of_notMem hs,
      chartExtend_of_notMem hs]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] {n : ℕ∞ω}

/-- **Smooth dependence of the extension through a chart on parameters.** Let `Φ q`, for `q` in a
manifold `P`, be maps of the model space depending jointly `C^n`-smoothly on `q` and the point,
each fixing every point outside a compact subset `K` of the interior of the chart target and
mapping `K` into itself. Then their extensions through the chart at `x` depend jointly
`C^n`-smoothly on `q` and the point of `M`. -/
theorem contMDiff_chartExtend [T2Space M] [IsManifold I n M] {Φ : P → E → E}
    (hΦ : ContMDiff (I'.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun q : P × E ↦ Φ q.1 q.2) (hK : IsCompact K)
    (hKt : K ⊆ interior (extChartAt I x).target) (hΦK : ∀ q, MapsTo (Φ q) K K)
    (hΦ' : ∀ q, ∀ p ∉ K, Φ q p = p) :
    ContMDiff (I'.prod I) I n fun q : P × M ↦ chartExtend I (Φ q.1) x q.2 := by
  rintro ⟨q₀, z₀⟩
  have hKt' : K ⊆ (extChartAt I x).target := hKt.trans interior_subset
  by_cases hz₀ : z₀ ∈ (extChartAt I x).symm '' K
  · -- Near the moving points, the extension is `Φ` read through the chart.
    obtain ⟨p₀, hp₀, rfl⟩ := hz₀
    have hs := (extChartAt I x).map_target (hKt' hp₀)
    have hsymm : ContMDiffAt 𝓘(𝕜, E) I n (extChartAt I x).symm (Φ q₀ p₀) :=
      (contMDiffOn_extChartAt_symm x).contMDiffAt
        (mem_interior_iff_mem_nhds.1 (hKt (hΦK q₀ hp₀)))
    have hchart : ContMDiffAt (I'.prod I) (I'.prod 𝓘(𝕜, E)) n
        (fun q : P × M ↦ (q.1, extChartAt I x q.2)) (q₀, (extChartAt I x).symm p₀) :=
      contMDiffAt_fst.prodMk ((contMDiffAt_extChartAt'
        (by rwa [← extChartAt_source (I := I)])).comp _ contMDiffAt_snd)
    have hΦc : ContMDiffAt (I'.prod I) 𝓘(𝕜, E) n
        (fun q : P × M ↦ Φ q.1 (extChartAt I x q.2)) (q₀, (extChartAt I x).symm p₀) :=
      (hΦ _).comp _ hchart
    refine (hsymm.comp_of_eq hΦc (congrArg (Φ q₀)
      ((extChartAt I x).right_inv (hKt' hp₀)))).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_extChartAt_source x).mem_nhds hs |> prod_mem_nhds Filter.univ_mem]
      with q hq
    exact chartExtend_of_mem hq.2
  · -- Away from the compact set of moving points, the extension is the projection.
    have hL : IsClosed ((extChartAt I x).symm '' K) :=
      (hK.image_of_continuousOn ((continuousOn_extChartAt_symm x).mono hKt')).isClosed
    refine contMDiffAt_snd.congr_of_eventuallyEq ?_
    filter_upwards [hL.isOpen_compl.mem_nhds hz₀ |> prod_mem_nhds Filter.univ_mem] with q hq
    exact chartExtend_eq_self (hΦ' q.1) hq.2

end ChartExtend

end TauCeti

namespace Diffeomorph

open TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] {n : ℕ∞ω} [IsManifold I n M]
  {K : Set E}

/-- **The extension of a diffeomorphism of the model space through a chart.** A `C^n`
diffeomorphism `φ` of the model space fixing every point outside a compact subset `K` of the
interior of the target of the extended chart at `x` extends to a `C^n` diffeomorphism of `M`: it
reads as `φ` through the chart (`Diffeomorph.chartExtend_extChartAt_symm`) and fixes every point
outside the preimage of `K` under the chart (`Diffeomorph.chartExtend_eq_self`). Its inverse is
the extension of `φ.symm` (`Diffeomorph.chartExtend_symm`). -/
noncomputable def chartExtend (φ : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E)⟯ E) (x : M) (hK : IsCompact K)
    (hKt : K ⊆ interior (extChartAt I x).target) (hφ : ∀ p ∉ K, φ p = p) :
    M ≃ₘ^n⟮I, I⟯ M :=
  have hφ' : ∀ p ∉ K, φ.symm p = p := fun p hp ↦
    (congrArg φ.symm (hφ p hp)).symm.trans (φ.symm_apply_apply p)
  have hKt' : K ⊆ (extChartAt I x).target := hKt.trans interior_subset
  -- A single map is the constant family over the parameter manifold `𝕜`.
  have hsmooth (ψ : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E)⟯ E) (hψ : ∀ p ∉ K, ψ p = p) :
      ContMDiff I I n (TauCeti.chartExtend I ψ x) :=
    (contMDiff_chartExtend (I' := 𝓘(𝕜, 𝕜)) (Φ := fun _ ↦ ψ) (ψ.contMDiff.comp contMDiff_snd) hK
      hKt (fun _ ↦ ψ.injective.mapsTo_of_eq_self hψ) fun _ ↦ hψ).comp
        ((contMDiff_const (c := (0 : 𝕜))).prodMk contMDiff_id)
  { toFun := TauCeti.chartExtend I φ x
    invFun := TauCeti.chartExtend I φ.symm x
    left_inv := fun z ↦ by
      have hφφ : ⇑φ.symm ∘ ⇑φ = id := funext φ.symm_apply_apply
      rw [← Function.comp_apply (f := TauCeti.chartExtend I φ.symm x),
        chartExtend_comp hKt' hφ (φ.injective.mapsTo_of_eq_self hφ), hφφ, chartExtend_id, id]
    right_inv := fun z ↦ by
      have hφφ : ⇑φ ∘ ⇑φ.symm = id := funext φ.apply_symm_apply
      rw [← Function.comp_apply (f := TauCeti.chartExtend I φ x),
        chartExtend_comp hKt' hφ' (φ.symm.injective.mapsTo_of_eq_self hφ'), hφφ, chartExtend_id,
        id]
    contMDiff_toFun := hsmooth φ hφ
    contMDiff_invFun := hsmooth φ.symm hφ' }

variable {φ : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E)⟯ E} {x : M} {hK : IsCompact K}
  {hKt : K ⊆ interior (extChartAt I x).target} {hφ : ∀ p ∉ K, φ p = p}

/-- The extension of `φ` through the chart is `TauCeti.chartExtend` of `φ`. -/
@[simp]
theorem coe_chartExtend : ⇑(φ.chartExtend x hK hKt hφ) = TauCeti.chartExtend I φ x := (rfl)

/-- The inverse of the extension of `φ` through the chart is the extension of `φ.symm`. -/
@[simp]
theorem chartExtend_symm :
    (φ.chartExtend x hK hKt hφ).symm = φ.symm.chartExtend x hK hKt fun p hp ↦
      (congrArg φ.symm (hφ p hp)).symm.trans (φ.symm_apply_apply p) :=
  (rfl)

/-- The extension of `φ` through the chart reads as `φ` on the chart. -/
theorem chartExtend_extChartAt_symm {p : E} (hp : p ∈ (extChartAt I x).target) :
    φ.chartExtend x hK hKt hφ ((extChartAt I x).symm p) = (extChartAt I x).symm (φ p) :=
  TauCeti.chartExtend_extChartAt_symm hp

/-- The extension of `φ` through the chart fixes every point outside the preimage of `K`. -/
theorem chartExtend_eq_self {z : M} (hz : z ∉ (extChartAt I x).symm '' K) :
    φ.chartExtend x hK hKt hφ z = z :=
  TauCeti.chartExtend_eq_self hφ hz

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]

/-- **Smooth families of extensions through a chart.** The extensions through the chart at `x` of
a family `τ q`, `q ∈ P`, of diffeomorphisms of the model space depending jointly `C^n`-smoothly on
`q` and the point, each fixing every point outside `K`, depend jointly `C^n`-smoothly on `q` and
the point of `M`. -/
theorem contMDiff_chartExtend {τ : P → E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E)⟯ E}
    (hτ : ContMDiff (I'.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun q : P × E ↦ τ q.1 q.2)
    (hτK : ∀ q, ∀ p ∉ K, τ q p = p) :
    ContMDiff (I'.prod I) I n fun q : P × M ↦ (τ q.1).chartExtend x hK hKt (hτK q.1) q.2 :=
  TauCeti.contMDiff_chartExtend hτ hK hKt (fun q ↦ (τ q).injective.mapsTo_of_eq_self (hτK q))
    hτK

end Diffeomorph
