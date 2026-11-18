/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic

/-!
# First jets of vector bundle morphisms

A family `Φ y : V y →L[𝕜] W y` of fibre maps between two vector bundles over the same base, which
is differentiable as a section of the bundle `Hom(V, W)`, acts on first jets of sections:

`J¹Φ (j¹s(x)) = j¹(Φ s)(x)`.

In the chart and trivializations at `x`, where the local representative of `Φ` is the operator
valued function `φ(z) = e^W ∘ Φ(z) ∘ (e^V)⁻¹`, the product rule gives

`J¹Φ (v, A) = (φ(z₀) v, φ(z₀) ∘ A + dφ(z₀)(·) v)`,

which is `ContinuousLinearMap.firstJetPullback` with the identity change of base coordinates. This
file defines this prolongation `TauCeti.FirstJetBundle.map` and proves that it is natural: it
sends first jets of sections to first jets of their images, it covers `Φ` on values and on the
kernel `Hom(TₓM, Vₓ)` of the value map, so it is a morphism of the first-jet exact sequences
`0 → Hom(TM, V) → J¹V → V → 0`, it is functorial, and it is a `C^n` bundle morphism when `Φ` is
`C^(n+1)`. In particular, by functoriality, a vector bundle isomorphism `Φ` that is
differentiable in both directions induces isomorphisms `J¹Vₓ ≃ J¹Wₓ` of the fibres.

## Main definitions and results

* `TauCeti.FirstJetBundle.homLocalRep`: the local representative of a bundle morphism in a chart
  and the trivializations of source and target.
* `TauCeti.FirstJetBundle.map`: the first-jet prolongation `J¹Φ : J¹V → J¹W`.
* `TauCeti.FirstJetBundle.map_jet`: `J¹Φ (j¹s(x)) = j¹(Φ s)(x)`.
* `TauCeti.FirstJetBundle.value_map` and `TauCeti.FirstJetBundle.map_ofDeriv`: `J¹Φ` covers `Φ` on
  values and sends the jet of `L : TₓM → Vₓ` to the jet of `Φₓ ∘ L`.
* `TauCeti.FirstJetBundle.map_id` and `TauCeti.FirstJetBundle.map_comp`: functoriality.
* `TauCeti.FirstJetBundle.coordChange_map` and `TauCeti.FirstJetBundle.inCoordinates_map`: in
  every first-jet chart, `J¹Φ` is the first-jet transformation of the local representative of `Φ`
  in that chart.
* `TauCeti.FirstJetBundle.mapEquiv`: a vector bundle isomorphism induces isomorphisms of the
  fibres of the first-jet bundles.
* `TauCeti.FirstJetBundle.contMDiffOn_map`: the prolongation of a `C^(n+1)` bundle morphism is a
  `C^n` section of `Hom(J¹V, J¹W)`.
* `TauCeti.FirstJetBundle.map_trivial`: for trivial bundles over a model space,
  `J¹φ (v, A) = (φ x v, φ x ∘ A + dφ(x)(·) v)`.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.16–12.17.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti

namespace FirstJetBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)] [∀ x, AddCommGroup (W x)]
  [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)] [FiberBundle G W] [VectorBundle 𝕜 G W]
  {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
  {W' : M → Type*} [TopologicalSpace (TotalSpace G' W')] [∀ x, AddCommGroup (W' x)]
  [∀ x, Module 𝕜 (W' x)] [∀ x, TopologicalSpace (W' x)] [FiberBundle G' W']
  [VectorBundle 𝕜 G' W']

/-! ### The local representative of a bundle morphism -/

/-- The local representative `z ↦ eᵢ^W ∘ Φ(φᵢ⁻¹ z) ∘ (eᵢ^V)⁻¹` of a family of fibre maps
`Φ y : V y →L[𝕜] W y` in the extended chart `φᵢ` and the preferred trivializations of `V` and
`W` at `i`. -/
def homLocalRep (Φ : ∀ y, V y →L[𝕜] W y) (i : M) (z : E) : F →L[𝕜] G :=
  ContinuousLinearMap.inCoordinates F V G W i ((extChartAt I i).symm z) i
    ((extChartAt I i).symm z) (Φ ((extChartAt I i).symm z))

/-- `homLocalRep` is `Φ` read in the trivializations at `i`, at the inverse chart image of `z`. -/
theorem homLocalRep_apply (Φ : ∀ y, V y →L[𝕜] W y) (i : M) (z : E) :
    homLocalRep I F G Φ i z =
      ContinuousLinearMap.inCoordinates F V G W i ((extChartAt I i).symm z) i
        ((extChartAt I i).symm z) (Φ ((extChartAt I i).symm z)) :=
  (rfl)

variable {I F G}

/-- At the image of a point of the chart domain, the local representative of `Φ` is `Φ` read in
the trivializations at `i`. -/
theorem homLocalRep_extChartAt (Φ : ∀ y, V y →L[𝕜] W y) {i y : M}
    (hy : y ∈ (chartAt H i).source) :
    homLocalRep I F G Φ i (extChartAt I i y) =
      ContinuousLinearMap.inCoordinates F V G W i y i y (Φ y) := by
  rw [homLocalRep_apply, (extChartAt I i).left_inv (by rwa [extChartAt_source])]

/-- The local representative of `Φ s` is the local representative of `Φ` applied to that of `s`,
at points whose inverse chart image lies in the domains of both trivializations. -/
theorem homLocalRep_apply_localRep (Φ : ∀ y, V y →L[𝕜] W y) (s : ∀ y, V y) {i : M} {z : E}
    (hV : (extChartAt I i).symm z ∈ (trivializationAt F V i).baseSet)
    (hW : (extChartAt I i).symm z ∈ (trivializationAt G W i).baseSet) :
    homLocalRep I F G Φ i z (localRep I F s i z) = localRep I G (fun y ↦ Φ y (s y)) i z := by
  rw [homLocalRep_apply, ContinuousLinearMap.inCoordinates, localRep_apply, localRep_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Trivialization.symmL_apply _ hV, Trivialization.symm_apply_apply_mk _ hV,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _ hW]

/-- At the base point, the local representative of `Φ` is `Φ` read in the trivializations, so
on values it is `Φ` itself. -/
private theorem symm_homLocalRep_extChartAt_apply (Φ : ∀ y, V y →L[𝕜] W y) {x : M} (v : F) :
    (trivializationAt G W x).symm x (homLocalRep I F G Φ x (extChartAt I x x) v) =
      Φ x ((trivializationAt F V x).symm x v) := by
  rw [homLocalRep_extChartAt Φ (mem_chart_source H x), ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← Trivialization.symmL_apply (R := 𝕜) _ (mem_baseSet_trivializationAt G W x),
    Trivialization.symmL_continuousLinearMapAt _ (mem_baseSet_trivializationAt G W x),
    Trivialization.symmL_apply _ (mem_baseSet_trivializationAt F V x)]

/-- The local representative of a composite of bundle morphisms is the composite of their local
representatives, at points in the domain of the trivialization of the middle bundle. -/
theorem homLocalRep_comp (Φ : ∀ y, V y →L[𝕜] W y) (Ψ : ∀ y, W y →L[𝕜] W' y) {i : M} {z : E}
    (hW : (extChartAt I i).symm z ∈ (trivializationAt G W i).baseSet) :
    homLocalRep I F G' (fun y ↦ (Ψ y).comp (Φ y)) i z =
      (homLocalRep I G G' Ψ i z).comp (homLocalRep I F G Φ i z) := by
  ext v
  simp only [homLocalRep_apply, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.symmL_continuousLinearMapAt _ hW]

section Differentiable

variable [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)]

/-- The local representative in the chart and trivializations at `i` of a bundle morphism that
is `C^n` at a point `y` of their domains is `C^n` within `range I` at the image of `y`. -/
theorem contDiffWithinAt_homLocalRep {n : ℕ∞ω} [IsManifold I n M] [ContMDiffVectorBundle n F V I]
    [ContMDiffVectorBundle n G W I] {Φ : ∀ y, V y →L[𝕜] W y} {i y : M}
    (hΦ : ContMDiffAt I (I.prod 𝓘(𝕜, F →L[𝕜] G)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ V y →L[𝕜] W y) y (Φ y)) y)
    (hV : y ∈ baseSet (H := H) F V i) (hW : y ∈ (trivializationAt G W i).baseSet) :
    ContDiffWithinAt 𝕜 n (homLocalRep I F G Φ i) (range I) (extChartAt I i y) := by
  have hy := mem_extChartAt_source_of_mem_baseSet I hV
  have h₁ : ContMDiffAt I 𝓘(𝕜, F →L[𝕜] G) n
      (fun x ↦ ContinuousLinearMap.inCoordinates F V G W i x i x (Φ x))
      ((extChartAt I i).symm (extChartAt I i y)) := by
    rw [(extChartAt I i).left_inv hy]
    exact ((trivializationAt (F →L[𝕜] G) (fun y ↦ V y →L[𝕜] W y) i).contMDiffAt_section_iff
      ⟨((mem_baseSet_iff _ _).1 hV).1, hW⟩).1 hΦ
  exact contMDiffWithinAt_iff_contDiffWithinAt.1 (h₁.comp_contMDiffWithinAt _
    (contMDiffWithinAt_extChartAt_symm_range i ((extChartAt I i).map_source hy)))

variable [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle 1 G W I]

/-- The local representative in the chart and trivializations at `i` of a bundle morphism that
is differentiable at a point `y` of their domains is differentiable within `range I` at the image
of `y`. -/
theorem differentiableWithinAt_homLocalRep {Φ : ∀ y, V y →L[𝕜] W y} {i y : M}
    (hΦ : MDifferentiableAt I (I.prod 𝓘(𝕜, F →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ V y →L[𝕜] W y) y (Φ y)) y)
    (hV : y ∈ baseSet (H := H) F V i) (hW : y ∈ (trivializationAt G W i).baseSet) :
    DifferentiableWithinAt 𝕜 (homLocalRep I F G Φ i) (range I) (extChartAt I i y) := by
  have hy := mem_extChartAt_source_of_mem_baseSet I hV
  have h₁ : MDifferentiableAt I 𝓘(𝕜, F →L[𝕜] G)
      (fun x ↦ ContinuousLinearMap.inCoordinates F V G W i x i x (Φ x))
      ((extChartAt I i).symm (extChartAt I i y)) := by
    rw [(extChartAt I i).left_inv hy]
    exact ((trivializationAt (F →L[𝕜] G) (fun y ↦ V y →L[𝕜] W y) i).mdifferentiableAt_section_iff
      I Φ ⟨((mem_baseSet_iff _ _).1 hV).1, hW⟩).1 hΦ
  exact mdifferentiableWithinAt_iff_differentiableWithinAt.1 (h₁.comp_mdifferentiableWithinAt _
    (mdifferentiableWithinAt_extChartAt_symm ((extChartAt I i).map_source hy)))

/-- **Product rule for local representatives.** In the chart and trivializations at `i`, the
chart derivative of the local representative of `Φ s` is
`φ(z₀) ∘ ds(z₀) + dφ(z₀)(·)(s(z₀))`, where `φ` and `s` are the local representatives of `Φ` and
of `s`. -/
theorem fderivWithin_localRep_apply {Φ : ∀ y, V y →L[𝕜] W y} {s : ∀ y, V y} {i y : M}
    (hΦ : MDifferentiableAt I (I.prod 𝓘(𝕜, F →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ V y →L[𝕜] W y) y (Φ y)) y)
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) y)
    (hV : y ∈ baseSet (H := H) F V i) (hW : y ∈ (trivializationAt G W i).baseSet) :
    fderivWithin 𝕜 (localRep I G (fun y ↦ Φ y (s y)) i) (range I) (extChartAt I i y) =
      (homLocalRep I F G Φ i (extChartAt I i y)).comp
          (fderivWithin 𝕜 (localRep I F s i) (range I) (extChartAt I i y)) +
        (fderivWithin 𝕜 (homLocalRep I F G Φ i) (range I) (extChartAt I i y)).flip
          (localRep I F s i (extChartAt I i y)) := by
  have hy := mem_extChartAt_source_of_mem_baseSet I hV
  have hprod := (differentiableWithinAt_homLocalRep hΦ hV hW).hasFDerivWithinAt.clm_apply
    (differentiableWithinAt_localRep I F hs hV).hasFDerivWithinAt
  refine (hprod.congr_of_eventuallyEq ?_ ?_).fderivWithin
    (I.uniqueDiffOn _ (extChartAt_target_subset_range i ((extChartAt I i).map_source hy)))
  · filter_upwards [eventually_extChartAt_symm_mem_baseSet I hV ((mem_baseSet_iff _ _).1 hV).2,
      mem_nhdsWithin_of_mem_nhds (extChartAt_preimage_mem_nhds' hy
        ((trivializationAt G W i).open_baseSet.mem_nhds hW))] with z hzV hzW
    exact (homLocalRep_apply_localRep Φ s ((mem_baseSet_iff _ _).1 hzV).1 hzW).symm
  · exact (homLocalRep_apply_localRep Φ s
      (by rw [(extChartAt I i).left_inv hy]; exact ((mem_baseSet_iff _ _).1 hV).1)
      (by rw [(extChartAt I i).left_inv hy]; exact hW)).symm

end Differentiable

/-! ### The prolongation of a bundle morphism -/

variable [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle 1 G W I]

variable (I F G) in
/-- The first-jet prolongation `J¹Φ : J¹Vₓ → J¹Wₓ` of a family of fibre maps
`Φ y : V y →L[𝕜] W y`. In the chart and trivializations at `x`, with `φ` the local representative
of `Φ`, it sends `(v, A)` to `(φ(z₀) v, φ(z₀) ∘ A + dφ(z₀)(·) v)`: the transformation of first
jets by the product rule. When `Φ` is differentiable at `x` it sends `j¹s(x)` to `j¹(Φ s)(x)`
(`TauCeti.FirstJetBundle.map_jet`). -/
def map (Φ : ∀ y, V y →L[𝕜] W y) (x : M) :
    FirstJetBundle I F V x →L[𝕜] FirstJetBundle I G W x :=
  ContinuousLinearMap.firstJetPullback (homLocalRep I F G Φ x (extChartAt I x x))
    (fderivWithin 𝕜 (homLocalRep I F G Φ x) (range I) (extChartAt I x x))
    (ContinuousLinearMap.id 𝕜 E)

/-- The value coordinate of `J¹Φ (v, A)` is `φ(z₀) v`. -/
@[simp]
theorem map_fst (Φ : ∀ y, V y →L[𝕜] W y) (x : M) (j : FirstJetBundle I F V x) :
    (map I F G Φ x j).1 = homLocalRep I F G Φ x (extChartAt I x x) j.1 :=
  congrArg Prod.fst (ContinuousLinearMap.firstJetPullback_apply _ _ _ _)

/-- The derivative coordinate of `J¹Φ (v, A)` is `φ(z₀) ∘ A + dφ(z₀)(·) v`. -/
@[simp]
theorem map_snd (Φ : ∀ y, V y →L[𝕜] W y) (x : M) (j : FirstJetBundle I F V x) :
    (map I F G Φ x j).2 = (homLocalRep I F G Φ x (extChartAt I x x)).comp j.2 +
      (fderivWithin 𝕜 (homLocalRep I F G Φ x) (range I) (extChartAt I x x)).flip j.1 := by
  refine (congrArg Prod.snd (ContinuousLinearMap.firstJetPullback_apply _ _ _ _)).trans ?_
  rw [ContinuousLinearMap.comp_id, add_comm]

/-- **The prolongation covers `Φ` on values**: the value of `J¹Φ j` is `Φ` applied to the value
of `j`. -/
@[simp]
theorem value_map (Φ : ∀ y, V y →L[𝕜] W y) (x : M) (j : FirstJetBundle I F V x) :
    value I G x (map I F G Φ x j) = Φ x (value I F x j) := by
  rw [value_apply, value_apply, map_fst, symm_homLocalRep_extChartAt_apply]

/-- The value map intertwines `J¹Φ` and `Φ`. -/
theorem value_comp_map (Φ : ∀ y, V y →L[𝕜] W y) (x : M) :
    value I G x ∘L map I F G Φ x = Φ x ∘L value I F x :=
  ContinuousLinearMap.ext (value_map Φ x)

/-- **The prolongation covers `Φ` on the kernel of the value map**: it sends the jet of a
homomorphism `L : TₓM → Vₓ` to the jet of `Φₓ ∘ L`. Together with
`TauCeti.FirstJetBundle.value_map`, this makes `J¹Φ` a morphism of the first-jet sequences
`0 → Hom(TₓM, Vₓ) → J¹Vₓ → Vₓ → 0` and `0 → Hom(TₓM, Wₓ) → J¹Wₓ → Wₓ → 0`. -/
@[simp]
theorem map_ofDeriv [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)]
    (Φ : ∀ y, V y →L[𝕜] W y) (x : M) (L : TangentSpace I x →L[𝕜] V x) :
    map I F G Φ x (ofDeriv I F x L) = ofDeriv I G x ((Φ x).comp L) := by
  refine Prod.ext (by rw [map_fst, ofDeriv_fst, map_zero, ofDeriv_fst]) ?_
  rw [map_snd, ofDeriv_fst, map_zero, add_zero, ofDeriv_snd, ofDeriv_snd,
    homLocalRep_extChartAt Φ (mem_chart_source H x)]
  -- Both sides are `e^W ∘ Φₓ ∘ L`, once `(e^V)⁻¹ ∘ e^V = id` is cancelled on each vector.
  refine ContinuousLinearMap.ext fun v ↦ ?_
  exact congrArg (fun w ↦ (trivializationAt G W x).continuousLinearMapAt 𝕜 x (Φ x w))
    (Trivialization.symmL_continuousLinearMapAt _ (mem_baseSet_trivializationAt F V x) (L v))

section Differentiable

variable [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)]

/-- **Naturality of first jets.** The prolongation of a bundle morphism `Φ` differentiable at `x`
sends the first jet at `x` of a section `s` differentiable at `x` to the first jet of `Φ s`. -/
theorem map_jet {Φ : ∀ y, V y →L[𝕜] W y} {s : ∀ y, V y} {x : M}
    (hΦ : MDifferentiableAt I (I.prod 𝓘(𝕜, F →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ V y →L[𝕜] W y) y (Φ y)) x)
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) x) :
    map I F G Φ x (jet I F s x) = jet I G (fun y ↦ Φ y (s y)) x := by
  have hV := mem_baseSet_self (H := H) F V x
  have hW := mem_baseSet_trivializationAt G W x
  have hx := mem_chart_source H x
  refine Prod.ext ?_ ?_
  · rw [map_fst, jet_fst, jet_fst, ← localRep_extChartAt I F s hx,
      homLocalRep_apply_localRep Φ s (by simpa using mem_baseSet_trivializationAt F V x)
        (by simpa using hW),
      localRep_extChartAt I G _ hx]
  · rw [map_snd, jet_snd, jet_snd, fderivWithin_localRep_apply hΦ hs hV hW, jet_fst,
      localRep_extChartAt I F s hx]

/-- **Change of chart for the prolongation.** In the first-jet chart at `i`, the prolongation of
a bundle morphism `Φ` differentiable at `y` is the first-jet transformation of the local
representative `φ` of `Φ` in that chart: `(v, A) ↦ (φ(z) v, φ(z) ∘ A + dφ(z)(·) v)`. -/
theorem coordChange_map {Φ : ∀ y, V y →L[𝕜] W y} {i y : M}
    (hΦ : MDifferentiableAt I (I.prod 𝓘(𝕜, F →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ V y →L[𝕜] W y) y (Φ y)) y)
    (hV : y ∈ baseSet (H := H) F V i) (hW : y ∈ baseSet (H := H) G W i)
    (j : FirstJetBundle I F V y) :
    coordChange I G W y i y (map I F G Φ y j) =
      ContinuousLinearMap.firstJetPullback (homLocalRep I F G Φ i (extChartAt I i y))
        (fderivWithin 𝕜 (homLocalRep I F G Φ i) (range I) (extChartAt I i y))
        (ContinuousLinearMap.id 𝕜 E) (coordChange I F V y i y j) := by
  -- Realize `j` as the first jet of a section and compare both sides on its first jet.
  obtain ⟨s, hs, rfl⟩ := exists_contMDiffAt_jet_eq I F (n := 1) y j
  have hs' := hs.mdifferentiableAt one_ne_zero
  have hV' := (mem_baseSet_iff _ _).1 hV
  have hW' := (mem_baseSet_iff _ _).1 hW
  have hy : (extChartAt I i).symm (extChartAt I i y) = y :=
    (extChartAt I i).left_inv (mem_extChartAt_source_of_mem_baseSet I hV)
  rw [map_jet hΦ hs', coordChange_jet I G (hΦ.clm_bundle_apply hs') hW,
    coordChange_jet I F hs' hV, ContinuousLinearMap.firstJetPullback_apply,
    ContinuousLinearMap.comp_id, fderivWithin_localRep_apply hΦ hs' hV hW'.1, add_comm,
    ← localRep_extChartAt I F s hV'.2,
    homLocalRep_apply_localRep Φ s (by rw [hy]; exact hV'.1) (by rw [hy]; exact hW'.1),
    localRep_extChartAt I G _ hV'.2]

end Differentiable

/-! ### Functoriality -/

/-- The prolongation of the identity is the identity. -/
@[simp]
theorem map_id (x : M) :
    map I F F (fun y ↦ ContinuousLinearMap.id 𝕜 (V y)) x = ContinuousLinearMap.id 𝕜 _ := by
  have hx := mem_baseSet_self (H := H) F V x
  have hx' := mem_extChartAt_source_of_mem_baseSet I hx
  have hx₀ : (extChartAt I x).symm (extChartAt I x x) ∈ (trivializationAt F V x).baseSet := by
    rw [(extChartAt I x).left_inv hx']; exact mem_baseSet_trivializationAt F V x
  -- Near the base point the local representative of the identity is constantly the identity.
  have hrep : ∀ z, (extChartAt I x).symm z ∈ (trivializationAt F V x).baseSet →
      homLocalRep I F F (fun y ↦ ContinuousLinearMap.id 𝕜 (V y)) x z =
        ContinuousLinearMap.id 𝕜 F := fun z hz ↦ by
    ext w
    rw [homLocalRep_apply, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      Trivialization.continuousLinearMapAt_symmL _ hz, ContinuousLinearMap.id_apply]
  have hderiv : fderivWithin 𝕜 (homLocalRep I F F (fun y ↦ ContinuousLinearMap.id 𝕜 (V y)) x)
      (range I) (extChartAt I x x) = 0 := by
    refine ((hasFDerivWithinAt_const (ContinuousLinearMap.id 𝕜 F) _ _).congr_of_eventuallyEq
      ?_ ?_).fderivWithin (I.uniqueDiffOn _ (extChartAt_target_subset_range x
        ((extChartAt I x).map_source hx')))
    · filter_upwards [eventually_extChartAt_symm_mem_baseSet I hx (mem_chart_source H x)]
        with z hz
      exact hrep z ((mem_baseSet_iff _ _).1 hz).1
    · exact hrep _ hx₀
  rw [map, hderiv, hrep _ hx₀]
  exact ContinuousLinearMap.firstJetPullback_id

section Comp

variable [ContMDiffVectorBundle 1 G' W' I]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)]
  [∀ x, IsTopologicalAddGroup (W' x)] [∀ x, ContinuousSMul 𝕜 (W' x)]

/-- **Functoriality of the prolongation**: the prolongation of a composite of differentiable
bundle morphisms is the composite of their prolongations. -/
theorem map_comp {Φ : ∀ y, V y →L[𝕜] W y} {Ψ : ∀ y, W y →L[𝕜] W' y} {x : M}
    (hΦ : MDifferentiableAt I (I.prod 𝓘(𝕜, F →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ V y →L[𝕜] W y) y (Φ y)) x)
    (hΨ : MDifferentiableAt I (I.prod 𝓘(𝕜, G →L[𝕜] G'))
      (fun y ↦ TotalSpace.mk' (G →L[𝕜] G') (E := fun y ↦ W y →L[𝕜] W' y) y (Ψ y)) x) :
    map I F G' (fun y ↦ (Ψ y).comp (Φ y)) x = (map I G G' Ψ x).comp (map I F G Φ x) := by
  have hV := mem_baseSet_self (H := H) F V x
  have hW := mem_baseSet_trivializationAt G W x
  have hW' := mem_baseSet_trivializationAt G' W' x
  have hx' := mem_extChartAt_source_of_mem_baseSet I hV
  have hWx : (extChartAt I x).symm (extChartAt I x x) ∈ (trivializationAt G W x).baseSet := by
    rw [(extChartAt I x).left_inv hx']; exact hW
  -- The product rule for the composite of the local representatives.
  have hprod := (differentiableWithinAt_homLocalRep hΨ
    ((mem_baseSet_iff _ _).2 ⟨hW, ((mem_baseSet_iff _ _).1 hV).2⟩) hW').hasFDerivWithinAt.clm_comp
    (differentiableWithinAt_homLocalRep hΦ hV hW).hasFDerivWithinAt
  have hD := (hprod.congr_of_eventuallyEq ?_ (homLocalRep_comp Φ Ψ hWx)).fderivWithin
    (I.uniqueDiffOn _ (extChartAt_target_subset_range x ((extChartAt I x).map_source hx')))
  · rw [map, map, map, hD, homLocalRep_comp Φ Ψ hWx]
    refine Eq.trans ?_ (ContinuousLinearMap.firstJetPullback_comp _ _ _ _ _ _).symm
    simp only [ContinuousLinearMap.comp_id]
    rfl
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (extChartAt_preimage_mem_nhds' hx'
      ((trivializationAt G W x).open_baseSet.mem_nhds hW))] with z hz
    exact homLocalRep_comp Φ Ψ hz

end Comp

section Equiv

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)]

variable (I F G) in
/-- **Bundle isomorphisms induce isomorphisms of first jets.** If the fibre maps
`Φ y : V y ≃L[𝕜] W y` and their inverses are differentiable at `x` as sections of `Hom(V, W)` and
`Hom(W, V)`, the prolongations of `Φ` and of its inverse are mutually inverse isomorphisms
`J¹Vₓ ≃ J¹Wₓ`. -/
def mapEquiv (Φ : ∀ y, V y ≃L[𝕜] W y) (x : M)
    (hΦ : MDifferentiableAt I (I.prod 𝓘(𝕜, F →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ V y →L[𝕜] W y) y
        (Φ y : V y →L[𝕜] W y)) x)
    (hΦ' : MDifferentiableAt I (I.prod 𝓘(𝕜, G →L[𝕜] F))
      (fun y ↦ TotalSpace.mk' (G →L[𝕜] F) (E := fun y ↦ W y →L[𝕜] V y) y
        ((Φ y).symm : W y →L[𝕜] V y)) x) :
    FirstJetBundle I F V x ≃L[𝕜] FirstJetBundle I G W x :=
  ContinuousLinearEquiv.equivOfInverse (map I F G (fun y ↦ (Φ y : V y →L[𝕜] W y)) x)
    (map I G F (fun y ↦ ((Φ y).symm : W y →L[𝕜] V y)) x)
    (fun j ↦ by
      rw [← ContinuousLinearMap.comp_apply, ← map_comp hΦ hΦ']
      simp only [ContinuousLinearEquiv.coe_symm_comp_coe, map_id, ContinuousLinearMap.id_apply])
    (fun j ↦ by
      rw [← ContinuousLinearMap.comp_apply, ← map_comp hΦ' hΦ]
      simp only [ContinuousLinearEquiv.coe_comp_coe_symm, map_id, ContinuousLinearMap.id_apply])

@[simp]
theorem coe_mapEquiv (Φ : ∀ y, V y ≃L[𝕜] W y) (x : M) (hΦ hΦ') :
    (mapEquiv I F G Φ x hΦ hΦ' : FirstJetBundle I F V x →L[𝕜] FirstJetBundle I G W x) =
      map I F G (fun y ↦ (Φ y : V y →L[𝕜] W y)) x :=
  ContinuousLinearEquiv.toContinuousLinearMap_equivOfInverse _ _ _ _

@[simp]
theorem symm_mapEquiv (Φ : ∀ y, V y ≃L[𝕜] W y) (x : M) (hΦ hΦ') :
    (mapEquiv I F G Φ x hΦ hΦ').symm =
      mapEquiv I G F (fun y ↦ (Φ y).symm) x hΦ'
        (by simpa only [ContinuousLinearEquiv.symm_symm] using hΦ) :=
  ContinuousLinearEquiv.ext (funext fun _ ↦ by simp [mapEquiv])

end Equiv

/-! ### Smoothness of the prolongation -/

section Smooth

variable [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)]

/-- **The prolongation in the first-jet charts.** Read in the preferred trivializations of `J¹V`
and `J¹W` at `x₀`, the prolongation at a point `y` of their domains, where `Φ` is differentiable,
is the first-jet transformation of the local representative `φ` of `Φ` at `x₀`:
`(v, A) ↦ (φ(z) v, φ(z) ∘ A + dφ(z)(·) v)` with `z` the chart coordinate of `y`. -/
theorem inCoordinates_map {Φ : ∀ y, V y →L[𝕜] W y} {x₀ y : M}
    (hΦ : MDifferentiableAt I (I.prod 𝓘(𝕜, F →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ V y →L[𝕜] W y) y (Φ y)) y)
    (hV : y ∈ baseSet (H := H) F V x₀) (hW : y ∈ baseSet (H := H) G W x₀) :
    ContinuousLinearMap.inCoordinates (F × (E →L[𝕜] F)) (FirstJetBundle I F V)
        (G × (E →L[𝕜] G)) (FirstJetBundle I G W) x₀ y x₀ y (map I F G Φ y) =
      ContinuousLinearMap.firstJetPullback (homLocalRep I F G Φ x₀ (extChartAt I x₀ y))
        (fderivWithin 𝕜 (homLocalRep I F G Φ x₀) (range I) (extChartAt I x₀ y))
        (ContinuousLinearMap.id 𝕜 E) := by
  refine ContinuousLinearMap.ext fun j ↦ ?_
  refine (congrArg (fun T ↦ T j) (VectorBundleCore.inCoordinates_eq (firstJetBundleCore I F V)
    (firstJetBundleCore I G W) (map I F G Φ y)
    (by rw [firstJetBundleCore_baseSet, firstJetBundleCore_indexAt]; exact hV)
    (by rw [firstJetBundleCore_baseSet, firstJetBundleCore_indexAt]; exact hW))).trans ?_
  simp only [firstJetBundleCore_indexAt, firstJetBundleCore_coordChange]
  -- The prolongation is the first-jet transformation of `φ` in the chart at `x₀`
  -- (`coordChange_map`), and the two first-jet coordinate changes around it cancel.
  refine (coordChange_map hΦ hV hW (coordChange I F V x₀ y y j)).trans ?_
  rw [coordChange_comp_apply hV (mem_baseSet_self F V y) hV, coordChange_self_apply hV]

/-- **The prolongation of a `C^(n+1)` bundle morphism is a `C^n` bundle morphism** of first-jet
bundles: if `Φ` is a `C^(n+1)` section of `Hom(V, W)` on an open set `U`, then `J¹Φ` is a `C^n`
section of `Hom(J¹V, J¹W)` on `U`. -/
theorem contMDiffOn_map {n : ℕ∞ω} [IsManifold I (n + 1) M] [ContMDiffVectorBundle (n + 1) F V I]
    [ContMDiffVectorBundle (n + 1) G W I] {Φ : ∀ y, V y →L[𝕜] W y} {U : Set M} (hU : IsOpen U)
    (hΦ : ContMDiffOn I (I.prod 𝓘(𝕜, F →L[𝕜] G)) (n + 1)
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ V y →L[𝕜] W y) y (Φ y)) U) :
    ContMDiffOn I (I.prod 𝓘(𝕜, (F × (E →L[𝕜] F)) →L[𝕜] G × (E →L[𝕜] G))) n
      (fun y ↦ TotalSpace.mk' ((F × (E →L[𝕜] F)) →L[𝕜] G × (E →L[𝕜] G))
        (E := fun y ↦ FirstJetBundle I F V y →L[𝕜] FirstJetBundle I G W y) y
        (map I F G Φ y)) U := by
  have : IsManifold I n M := .of_le (n := n + 1) le_self_add
  intro x₀ hx₀
  refine ContMDiffAt.contMDiffWithinAt ((contMDiffAt_hom_bundle _).2 ⟨contMDiffAt_id, ?_⟩)
  -- The set of chart coordinates where the local representative of `Φ` at `x₀` is `C^(n+1)`.
  set T := (extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹'
    (U ∩ (baseSet (H := H) F V x₀ ∩ baseSet (H := H) G W x₀))
  have hTr : T ⊆ range I := fun z hz ↦ extChartAt_target_subset_range x₀ hz.1
  have hT : ∀ z ∈ T, ContDiffWithinAt 𝕜 (n + 1) (homLocalRep I F G Φ x₀) (range I) z := by
    rintro z ⟨hz, hzU, hzV, hzW⟩
    rw [← (extChartAt I x₀).right_inv hz]
    exact contDiffWithinAt_homLocalRep ((hΦ _ hzU).contMDiffAt (hU.mem_nhds hzU)) hzV
      ((mem_baseSet_iff _ _).1 hzW).1
  -- In the chart at `x₀`, the prolongation is the first-jet transformation of the local
  -- representative, which depends `C^n` on the chart coordinate.
  have hΨ : ContDiffOn 𝕜 n (fun z ↦ ContinuousLinearMap.firstJetPullback
      (homLocalRep I F G Φ x₀ z) (fderivWithin 𝕜 (homLocalRep I F G Φ x₀) (range I) z)
      (ContinuousLinearMap.id 𝕜 E)) T :=
    ContDiffOn.firstJetPullback (fun z hz ↦ ((hT z hz).mono hTr).of_le le_self_add)
      (fun z hz ↦ ((hT z hz).fderivWithin_right I.uniqueDiffOn le_rfl (hTr hz)).mono hTr)
      contDiffOn_const
  set N := U ∩ (baseSet (H := H) F V x₀ ∩ baseSet (H := H) G W x₀)
  have hN : N ∈ 𝓝 x₀ := (hU.inter ((isOpen_baseSet F V x₀).inter
    (isOpen_baseSet G W x₀))).mem_nhds ⟨hx₀, mem_baseSet_self F V x₀, mem_baseSet_self G W x₀⟩
  have hmaps : MapsTo (extChartAt I x₀) N T := fun y hy ↦ by
    have hy' := mem_extChartAt_source_of_mem_baseSet I hy.2.1
    exact ⟨(extChartAt I x₀).map_source hy', by rwa [mem_preimage, (extChartAt I x₀).left_inv hy']⟩
  refine (((contMDiffOn_iff_contDiffOn.2 hΨ).comp (contMDiffOn_extChartAt.mono fun y (hy : y ∈ N) ↦
    ((mem_baseSet_iff _ _).1 hy.2.1).2) hmaps).contMDiffAt hN).congr_of_eventuallyEq ?_
  filter_upwards [hN] with y hy
  exact inCoordinates_map (((hΦ y hy.1).contMDiffAt (hU.mem_nhds hy.1)).mdifferentiableAt
    (by simp)) hy.2.1 hy.2.2

end Smooth

/-! ### Trivial bundles -/

section Trivial

/-- For trivial bundles over a model space, the local representative of a family of fibre maps
`φ y : F →L[𝕜] G` is `φ` itself. -/
@[simp]
theorem homLocalRep_trivial (φ : E → F →L[𝕜] G) (x : E) :
    homLocalRep 𝓘(𝕜, E) F G (V := Bundle.Trivial E F) (W := Bundle.Trivial E G) φ x = φ := by
  funext z
  ext v
  simp [homLocalRep_apply, ContinuousLinearMap.inCoordinates]

/-- For trivial bundles over a model space, the prolongation of `φ : E → F →L[𝕜] G` sends the
first jet `(v, A)` to `(φ x v, φ x ∘ A + dφ(x)(·) v)`. The second term records the derivative of
the bundle morphism: for instance multiplication by `φ y = y` on the trivial line bundle over `𝕜`
sends the jet `(1, 0)` of the constant section `1` at `x` to `(x, 1)`. -/
theorem map_trivial (φ : E → F →L[𝕜] G) (x : E)
    (j : FirstJetBundle 𝓘(𝕜, E) F (Bundle.Trivial E F) x) :
    map 𝓘(𝕜, E) F G (V := Bundle.Trivial E F) (W := Bundle.Trivial E G) φ x j =
      ((φ x j.1, (φ x).comp j.2 + (fderiv 𝕜 φ x).flip j.1) :
        FirstJetBundle 𝓘(𝕜, E) G (Bundle.Trivial E G) x) :=
  Prod.ext (by simp) (by simp [fderivWithin_univ])

end Trivial

end FirstJetBundle

end TauCeti
