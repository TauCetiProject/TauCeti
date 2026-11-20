/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic
public import TauCeti.Topology.VectorBundle.Coordinates
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Naturality of the first-jet bundle under bundle maps

Let `V₁` and `V₂` be `C^1` vector bundles over `M` with model fibres `F₁` and `F₂`, and let
`Φ x : V₁ x →L[𝕜] V₂ x` be a field of continuous linear maps, a section of the hom bundle. A
section `s` of `V₁` is sent to the section `Φ s : x ↦ Φ x (s x)` of `V₂`, and the first jet of
`Φ s` at `x` only depends on the first jet of `s` at `x` and on the first jet of `Φ` there, for
`Φ` and `s` differentiable at `x`. This file constructs the induced map of first jets, the
*prolongation*

`J¹Φ x : J¹V₁ x →L[𝕜] J¹V₂ x`

(`TauCeti.FirstJetBundle.map`), and proves that it is natural for the structure of first-jet
bundles (Kolář–Michor–Slovák, §12.16, for the functor `J¹` on bundle morphisms).

In the chart at `x` of `M` and the preferred trivializations at `x` of `V₁` and `V₂`, the field
`Φ` reads as a map `g : E → (F₁ →L[𝕜] F₂)` (`TauCeti.FirstJetBundle.homLocalRep`), and a first
jet `(w, A)` (value and chart derivative) is sent to

`(g(φ x) w, Dg(φ x)(·) w + g(φ x) ∘ A)`,

the value transformed by `Φ x` and the derivative by the product rule
(`TauCeti.FirstJetBundle.map_apply`).

## Main results

* `TauCeti.FirstJetBundle.map_jet`: **naturality of jet extension**. If `Φ` and `s` are
  differentiable at `x`, then `J¹Φ x (j¹s(x)) = j¹(Φ s)(x)`.
* `TauCeti.FirstJetBundle.eq_map_of_forall_jet`: this characterizes `J¹Φ x` among all continuous
  linear maps of first jets.
* `TauCeti.FirstJetBundle.value_map` and `TauCeti.FirstJetBundle.map_ofDeriv`: **naturality of
  the first-jet sequence** `0 → Hom(TₓM, Vₓ) → J¹Vₓ → Vₓ → 0`. The prolongation lies over `Φ x`
  on values, and on the kernel `Hom(TₓM, V₁ x)` it is composition with `Φ x`.
* `TauCeti.FirstJetBundle.map_id` and `TauCeti.FirstJetBundle.map_comp`: functoriality,
  `J¹(id) = id` and `J¹(Ψ ∘ Φ) = J¹Ψ ∘ J¹Φ` for differentiable `Φ` and `Ψ`.
* `TauCeti.FirstJetBundle.mapEquiv`: a field of continuous linear equivalences which is
  differentiable at `x` together with its inverse, for instance a smooth isomorphism of vector
  bundles, induces a continuous linear equivalence `J¹V₁ x ≃L[𝕜] J¹V₂ x`. Since it preserves jet
  extension and the first-jet sequence, isomorphic bundles have isomorphic first-jet sequences.
* `TauCeti.FirstJetBundle.coordChange_map`: the formula for `J¹Φ` above holds in the chart and
  trivializations at every point `i`, with the local representative of `Φ` at `i`.
* `TauCeti.FirstJetBundle.contMDiffAt_map`, `TauCeti.FirstJetBundle.contMDiffOn_map` and
  `TauCeti.FirstJetBundle.contMDiff_map`: if `Φ` is a `C^(n+1)` section of the hom bundle (at a
  point, on an open set, or everywhere), then `x ↦ J¹Φ x` is a `C^n` section of the bundle of
  continuous linear maps from `J¹V₁` to `J¹V₂` there. So a `C^(n+1)` morphism of vector bundles
  induces a `C^n` morphism of their first-jet bundles.

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
  (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, AddCommGroup (V₁ x)]
  [∀ x, Module 𝕜 (V₁ x)] [∀ x, TopologicalSpace (V₁ x)] [FiberBundle F₁ V₁]
  [VectorBundle 𝕜 F₁ V₁]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, AddCommGroup (V₂ x)]
  [∀ x, Module 𝕜 (V₂ x)] [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂]
  [VectorBundle 𝕜 F₂ V₂]

/-! ### The local representative of a field of linear maps -/

/-- The local representative `z ↦ e₂ ∘ Φ (φᵢ⁻¹ z) ∘ e₁⁻¹` of a field of continuous linear maps
`Φ x : V₁ x →L[𝕜] V₂ x` in the extended chart `φᵢ` at `i` and the preferred trivializations
`e₁` of `V₁` and `e₂` of `V₂` at `i`. -/
def homLocalRep (Φ : ∀ x, V₁ x →L[𝕜] V₂ x) (i : M) (z : E) : F₁ →L[𝕜] F₂ :=
  ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ i ((extChartAt I i).symm z) i
    ((extChartAt I i).symm z) (Φ ((extChartAt I i).symm z))

/-- The local representative at `z` is `Φ` at the point with chart coordinate `z`, read in the
trivializations at `i`. -/
theorem homLocalRep_apply (Φ : ∀ x, V₁ x →L[𝕜] V₂ x) (i : M) (z : E) :
    homLocalRep I F₁ F₂ Φ i z =
      ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ i ((extChartAt I i).symm z) i
        ((extChartAt I i).symm z) (Φ ((extChartAt I i).symm z)) :=
  (rfl)

variable {I F₁ F₂}

/-- At the image of a point of the chart domain, the local representative is `Φ` at that point,
read in the trivializations at `i`. -/
theorem homLocalRep_extChartAt (Φ : ∀ x, V₁ x →L[𝕜] V₂ x) {i y : M}
    (hy : y ∈ (chartAt H i).source) :
    homLocalRep I F₁ F₂ Φ i (extChartAt I i y) =
      ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ i y i y (Φ y) := by
  rw [homLocalRep_apply, (extChartAt I i).left_inv (by rwa [extChartAt_source])]

variable (I) in
/-- Read in the trivializations at `i`, the vector `Φ y v` is the local representative of `Φ`
applied to `v` read in the trivialization at `i`. -/
theorem homLocalRep_extChartAt_apply (Φ : ∀ x, V₁ x →L[𝕜] V₂ x) {i y : M}
    (h₁ : y ∈ baseSet (H := H) F₁ V₁ i) (h₂ : y ∈ (trivializationAt F₂ V₂ i).baseSet)
    (v : V₁ y) :
    homLocalRep I F₁ F₂ Φ i (extChartAt I i y) (trivializationAt F₁ V₁ i ⟨y, v⟩).2 =
      (trivializationAt F₂ V₂ i ⟨y, Φ y v⟩).2 := by
  obtain ⟨h₁e, h₁c⟩ := (mem_baseSet_iff F₁ V₁).1 h₁
  rw [homLocalRep_extChartAt Φ h₁c, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Trivialization.symmL_apply (R := 𝕜) _ h₁e, Trivialization.symm_apply_apply_mk _ h₁e,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _ h₂]

/-- Near the image of `y`, the local representative of `Φ s` is the local representative of `Φ`
applied to that of `s`. -/
private theorem localRep_eventuallyEq_homLocalRep_apply (Φ : ∀ x, V₁ x →L[𝕜] V₂ x)
    (s : ∀ x, V₁ x) {i y : M} (h₁ : y ∈ baseSet (H := H) F₁ V₁ i)
    (h₂ : y ∈ baseSet (H := H) F₂ V₂ i) :
    localRep I F₂ (fun y ↦ Φ y (s y)) i =ᶠ[𝓝[range I] extChartAt I i y]
      fun z ↦ homLocalRep I F₁ F₂ Φ i z (localRep I F₁ s i z) := by
  have h₂c := ((mem_baseSet_iff F₂ V₂).1 h₂).2
  filter_upwards [eventually_extChartAt_symm_mem_baseSet I h₁ h₂c,
    eventually_extChartAt_symm_mem_baseSet I h₂ h₂c, extChartAt_target_mem_nhdsWithin' (I := I)
      (mem_extChartAt_source_of_mem_baseSet I h₂)] with z hz₁ hz₂ hzt
  have h := homLocalRep_extChartAt_apply I (F₂ := F₂) Φ hz₁ ((mem_baseSet_iff F₂ V₂).1 hz₂).1
    (s ((extChartAt I i).symm z))
  rw [(extChartAt I i).right_inv hzt] at h
  rw [localRep_apply, localRep_apply, h]

section Differentiable

variable [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]

/-- The local representative of a field of linear maps is its local representative as a section of
the hom bundle. -/
theorem homLocalRep_eq_localRep (Φ : ∀ x, V₁ x →L[𝕜] V₂ x) (i : M) :
    homLocalRep I F₁ F₂ Φ i =
      localRep I (F₁ →L[𝕜] F₂) (V := fun y ↦ V₁ y →L[𝕜] V₂ y) Φ i := by
  funext z
  rw [homLocalRep_apply, localRep_apply, hom_trivializationAt_apply]

/-- The local representative at `i` of a field of linear maps that is `C^n` at a point `x` of the
chart domains at `i`, as a section of the hom bundle, is `C^n` within `range I` at the image of
`x`. -/
theorem contDiffWithinAt_homLocalRep {n : ℕ∞ω} [IsManifold I n M]
    [ContMDiffVectorBundle n F₁ V₁ I] [ContMDiffVectorBundle n F₂ V₂ I]
    {Φ : ∀ x, V₁ x →L[𝕜] V₂ x} {i x : M}
    (hΦ : ContMDiffAt I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ V₁ y →L[𝕜] V₂ y) y (Φ y)) x)
    (h₁ : x ∈ baseSet (H := H) F₁ V₁ i) (h₂ : x ∈ (trivializationAt F₂ V₂ i).baseSet) :
    ContDiffWithinAt 𝕜 n (homLocalRep I F₁ F₂ Φ i) (range I) (extChartAt I i x) := by
  rw [homLocalRep_eq_localRep]
  exact contDiffWithinAt_localRep I (F₁ →L[𝕜] F₂) hΦ
    ((mem_baseSet_iff _ _).2 ⟨Set.mem_inter ((mem_baseSet_iff F₁ V₁).1 h₁).1 h₂,
      ((mem_baseSet_iff F₁ V₁).1 h₁).2⟩)

variable [IsManifold I 1 M] [ContMDiffVectorBundle 1 F₁ V₁ I] [ContMDiffVectorBundle 1 F₂ V₂ I]

/-- The local representative at `i` of a field of linear maps that is differentiable at a point
`x` of the chart domains at `i`, as a section of the hom bundle, is differentiable within
`range I` at the image of `x`. -/
theorem differentiableWithinAt_homLocalRep {Φ : ∀ x, V₁ x →L[𝕜] V₂ x} {i x : M}
    (hΦ : MDifferentiableAt I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ V₁ y →L[𝕜] V₂ y) y (Φ y)) x)
    (h₁ : x ∈ baseSet (H := H) F₁ V₁ i) (h₂ : x ∈ (trivializationAt F₂ V₂ i).baseSet) :
    DifferentiableWithinAt 𝕜 (homLocalRep I F₁ F₂ Φ i) (range I) (extChartAt I i x) := by
  rw [homLocalRep_eq_localRep]
  exact differentiableWithinAt_localRep I (F₁ →L[𝕜] F₂) hΦ
    ((mem_baseSet_iff _ _).2 ⟨Set.mem_inter ((mem_baseSet_iff F₁ V₁).1 h₁).1 h₂,
      ((mem_baseSet_iff F₁ V₁).1 h₁).2⟩)

/-- **Product rule for local representatives.** In the chart and trivializations at `i`, the
derivative of the local representative of `Φ s` is that of the local representative of `Φ`
applied to the value of `s`, plus the local representative of `Φ` composed with the derivative of
the local representative of `s`. -/
private theorem fderivWithin_localRep_apply {Φ : ∀ x, V₁ x →L[𝕜] V₂ x} {s : ∀ x, V₁ x}
    {i x : M}
    (hΦ : MDifferentiableAt I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ V₁ y →L[𝕜] V₂ y) y (Φ y)) x)
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F₁)) (fun y ↦ TotalSpace.mk' F₁ y (s y)) x)
    (h₁ : x ∈ baseSet (H := H) F₁ V₁ i) (h₂ : x ∈ baseSet (H := H) F₂ V₂ i) :
    fderivWithin 𝕜 (localRep I F₂ (fun y ↦ Φ y (s y)) i) (range I) (extChartAt I i x) =
      (fderivWithin 𝕜 (homLocalRep I F₁ F₂ Φ i) (range I) (extChartAt I i x)).flip
          (trivializationAt F₁ V₁ i ⟨x, s x⟩).2 +
        (homLocalRep I F₁ F₂ Φ i (extChartAt I i x)).comp
          (fderivWithin 𝕜 (localRep I F₁ s i) (range I) (extChartAt I i x)) := by
  have hx := mem_extChartAt_source_of_mem_baseSet I h₁
  have h₂e := ((mem_baseSet_iff F₂ V₂).1 h₂).1
  have hr := localRep_extChartAt I F₁ s ((mem_baseSet_iff F₁ V₁).1 h₁).2
  have hval := homLocalRep_extChartAt_apply I Φ h₁ h₂e (s x)
  rw [(((differentiableWithinAt_homLocalRep hΦ h₁ h₂e).hasFDerivWithinAt.clm_apply
    (differentiableWithinAt_localRep I F₁ hs h₁).hasFDerivWithinAt).congr_of_eventuallyEq
    (localRep_eventuallyEq_homLocalRep_apply Φ s h₁ h₂) ?_).fderivWithin
    (I.uniqueDiffOn _ (extChartAt_target_subset_range i ((extChartAt I i).map_source hx))), hr,
    add_comm]
  rw [localRep_extChartAt I F₂ _ ((mem_baseSet_iff F₂ V₂).1 h₂).2, hr, hval]

end Differentiable

/-! ### The prolongation of a field of linear maps -/

section Prolongation

variable [IsManifold I 1 M] [ContMDiffVectorBundle 1 F₁ V₁ I] [ContMDiffVectorBundle 1 F₂ V₂ I]

variable (I F₁ F₂) in
/-- The **prolongation** `J¹Φ x : J¹V₁ x →L[𝕜] J¹V₂ x` of a field of continuous linear maps
`Φ x : V₁ x →L[𝕜] V₂ x`. In the chart and trivializations at `x`, with `g` the local
representative of `Φ`, it sends the first jet `(w, A)` to `(g w, Dg(·) w + g ∘ A)`. When `Φ` is
differentiable at `x`, this is the first jet of `Φ s` for every section `s` differentiable at `x`
with first jet `(w, A)` (`FirstJetBundle.map_jet`). -/
def map (Φ : ∀ x, V₁ x →L[𝕜] V₂ x) (x : M) :
    FirstJetBundle I F₁ V₁ x →L[𝕜] FirstJetBundle I F₂ V₂ x :=
  (homLocalRep I F₁ F₂ Φ x (extChartAt I x x)).firstJetPullback
    (fderivWithin 𝕜 (homLocalRep I F₁ F₂ Φ x) (range I) (extChartAt I x x))
    (ContinuousLinearMap.id 𝕜 E)

/-- The prolongation transforms the value coordinate by `Φ x` read in the trivializations at `x`,
and the derivative coordinate by the product rule. -/
theorem map_apply (Φ : ∀ x, V₁ x →L[𝕜] V₂ x) (x : M) (j : FirstJetBundle I F₁ V₁ x) :
    map I F₁ F₂ Φ x j =
      ((homLocalRep I F₁ F₂ Φ x (extChartAt I x x) j.1,
        (fderivWithin 𝕜 (homLocalRep I F₁ F₂ Φ x) (range I) (extChartAt I x x)).flip j.1 +
          (homLocalRep I F₁ F₂ Φ x (extChartAt I x x)).comp j.2) :
        FirstJetBundle I F₂ V₂ x) :=
  (ContinuousLinearMap.firstJetPullback_apply _ _ _ j).trans (by rw [ContinuousLinearMap.comp_id])

/-- The value coordinate of `J¹Φ x j` is the value coordinate of `j` transformed by `Φ x`, read in
the trivializations at `x`. -/
@[simp]
theorem map_apply_fst (Φ : ∀ x, V₁ x →L[𝕜] V₂ x) (x : M) (j : FirstJetBundle I F₁ V₁ x) :
    (map I F₁ F₂ Φ x j).1 =
      ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x x x x (Φ x) j.1 := by
  rw [map_apply, homLocalRep_extChartAt Φ (mem_chart_source H x)]

/-- The derivative coordinate of `J¹Φ x j` is given by the product rule: the derivative of the
local representative of `Φ` applied to the value coordinate of `j`, plus `Φ x`, read in the
trivializations at `x`, composed with the derivative coordinate of `j`. -/
@[simp]
theorem map_apply_snd (Φ : ∀ x, V₁ x →L[𝕜] V₂ x) (x : M) (j : FirstJetBundle I F₁ V₁ x) :
    (map I F₁ F₂ Φ x j).2 =
      (fderivWithin 𝕜 (homLocalRep I F₁ F₂ Φ x) (range I) (extChartAt I x x)).flip j.1 +
        (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x x x x (Φ x)).comp j.2 := by
  rw [map_apply, homLocalRep_extChartAt Φ (mem_chart_source H x)]

section Naturality

variable [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]

/-- **Naturality of jet extension.** If a field `Φ` of continuous linear maps and a section `s`
are differentiable at `x`, the prolongation of `Φ` sends the first jet of `s` at `x` to the first
jet of `Φ s`. -/
theorem map_jet {Φ : ∀ x, V₁ x →L[𝕜] V₂ x} {s : ∀ x, V₁ x} {x : M}
    (hΦ : MDifferentiableAt I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ V₁ y →L[𝕜] V₂ y) y (Φ y)) x)
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F₁)) (fun y ↦ TotalSpace.mk' F₁ y (s y)) x) :
    map I F₁ F₂ Φ x (jet I F₁ s x) = jet I F₂ (fun y ↦ Φ y (s y)) x := by
  have h₁ := mem_baseSet_self (H := H) F₁ V₁ x
  have hval := homLocalRep_extChartAt_apply I Φ h₁ (mem_baseSet_trivializationAt F₂ V₂ x)
    (s x)
  rw [map_apply]
  refine Prod.ext ?_ ?_
  · rw [jet_fst, jet_fst, hval]
  · rw [jet_snd, jet_snd, fderivWithin_localRep_apply hΦ hs h₁ (mem_baseSet_self (H := H) F₂ V₂ x),
      jet_fst]

/-- **The prolongation is characterized by naturality of jet extension.** A continuous linear map
of first jets at `x` that sends the first jet of every section `C^1` at `x` to the first jet of
its image under `Φ` is the prolongation `J¹Φ x`. -/
theorem eq_map_of_forall_jet {Φ : ∀ x, V₁ x →L[𝕜] V₂ x} {x : M}
    (hΦ : MDifferentiableAt I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ V₁ y →L[𝕜] V₂ y) y (Φ y)) x)
    (T : FirstJetBundle I F₁ V₁ x →L[𝕜] FirstJetBundle I F₂ V₂ x)
    (hT : ∀ s : ∀ x, V₁ x,
      ContMDiffAt I (I.prod 𝓘(𝕜, F₁)) 1 (fun y ↦ TotalSpace.mk' F₁ y (s y)) x →
        T (jet I F₁ s x) = jet I F₂ (fun y ↦ Φ y (s y)) x) :
    T = map I F₁ F₂ Φ x := by
  refine ContinuousLinearMap.ext fun j ↦ ?_
  obtain ⟨s, hs, rfl⟩ := exists_contMDiffAt_jet_eq (n := 1) I F₁ x j
  rw [hT s hs, map_jet hΦ (hs.mdifferentiableAt one_ne_zero)]

/-- **The prolongation in an arbitrary chart.** In the chart and trivializations at `i`, with `g`
the local representative of `Φ` there, the prolongation of a field `Φ` differentiable at `x` sends
the first jet `(w, A)` to `(g w, Dg(·) w + g ∘ A)`, by the same formula as in the chart at `x`. -/
theorem coordChange_map {Φ : ∀ x, V₁ x →L[𝕜] V₂ x} {i x : M}
    (hΦ : MDifferentiableAt I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ V₁ y →L[𝕜] V₂ y) y (Φ y)) x)
    (h₁ : x ∈ baseSet (H := H) F₁ V₁ i) (h₂ : x ∈ baseSet (H := H) F₂ V₂ i)
    (j : FirstJetBundle I F₁ V₁ x) :
    coordChange I F₂ V₂ x i x (map I F₁ F₂ Φ x j) =
      (homLocalRep I F₁ F₂ Φ i (extChartAt I i x)).firstJetPullback
        (fderivWithin 𝕜 (homLocalRep I F₁ F₂ Φ i) (range I) (extChartAt I i x))
        (ContinuousLinearMap.id 𝕜 E) (coordChange I F₁ V₁ x i x j) := by
  obtain ⟨s, hs, rfl⟩ := exists_contMDiffAt_jet_eq (n := 1) I F₁ x j
  have hs' := hs.mdifferentiableAt one_ne_zero
  rw [map_jet hΦ hs', coordChange_jet I F₂ (hΦ.clm_bundle_apply hs') h₂,
    coordChange_jet I F₁ hs' h₁, ContinuousLinearMap.firstJetPullback_apply,
    ContinuousLinearMap.comp_id, fderivWithin_localRep_apply hΦ hs' h₁ h₂,
    homLocalRep_extChartAt_apply I Φ h₁ ((mem_baseSet_iff F₂ V₂).1 h₂).1 (s x)]

end Naturality

/-! ### The first-jet sequence -/

/-- **The prolongation lies over `Φ`.** The value of `J¹Φ x j` is `Φ x` applied to the value of
`j`. -/
@[simp]
theorem value_map (Φ : ∀ x, V₁ x →L[𝕜] V₂ x) (x : M) (j : FirstJetBundle I F₁ V₁ x) :
    value I F₂ x (map I F₁ F₂ Φ x j) = Φ x (value I F₁ x j) := by
  have h₁ := mem_baseSet_trivializationAt F₁ V₁ x
  have h₂ := mem_baseSet_trivializationAt F₂ V₂ x
  have h := DFunLike.congr_fun
    (ContinuousLinearMap.inCoordinates_comp_continuousLinearMapAt (F' := F₂) (y₀ := x) (Φ x) h₁)
    ((trivializationAt F₁ V₁ x).symmL 𝕜 x j.1)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_symmL _ h₁] at h
  rw [value_apply, value_apply, map_apply_fst, h, ← Trivialization.symmL_apply (R := 𝕜) _ h₂,
    Trivialization.symmL_continuousLinearMapAt _ h₂, Trivialization.symmL_apply (R := 𝕜) _ h₁]

/-- The square formed by the projections `J¹Vᵢ x → Vᵢ x`, the prolongation `J¹Φ x` and `Φ x`
commutes. -/
@[simp]
theorem value_comp_map (Φ : ∀ x, V₁ x →L[𝕜] V₂ x) (x : M) :
    value I F₂ x ∘L map I F₁ F₂ Φ x = Φ x ∘L value I F₁ x :=
  ContinuousLinearMap.ext (value_map Φ x)

section Kernel

variable [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul 𝕜 (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]

/-- **The prolongation on the kernel of the first-jet sequence.** On first jets with value zero,
identified with `Hom(TₓM, V₁ x)`, the prolongation `J¹Φ x` is composition with `Φ x`. -/
@[simp]
theorem map_ofDeriv (Φ : ∀ x, V₁ x →L[𝕜] V₂ x) (x : M) (L : TangentSpace I x →L[𝕜] V₁ x) :
    map I F₁ F₂ Φ x (ofDeriv I F₁ x L) = ofDeriv I F₂ x ((Φ x).comp L) := by
  rw [map_apply, ofDeriv_apply, ofDeriv_apply]
  refine Prod.ext (map_zero _) ?_
  simp only [map_zero, zero_add]
  rw [homLocalRep_extChartAt Φ (mem_chart_source H x)]
  exact (ContinuousLinearMap.comp_assoc _ _ L).symm.trans
    ((congrArg (· ∘L L) (ContinuousLinearMap.inCoordinates_comp_continuousLinearMapAt (Φ x)
      (mem_baseSet_trivializationAt F₁ V₁ x))).trans (ContinuousLinearMap.comp_assoc _ _ L))

end Kernel

/-! ### Functoriality -/

/-- **The prolongation of the identity is the identity.** -/
@[simp]
theorem map_id (x : M) :
    map I F₁ F₁ (fun y ↦ ContinuousLinearMap.id 𝕜 (V₁ y)) x = ContinuousLinearMap.id 𝕜 _ := by
  have h₁ := mem_baseSet_self (H := H) F₁ V₁ x
  -- Near the image of `x`, the local representative of the identity is constant.
  have hc : homLocalRep I F₁ F₁ (fun y ↦ ContinuousLinearMap.id 𝕜 (V₁ y)) x
      =ᶠ[𝓝[range I] extChartAt I x x] fun _ ↦ ContinuousLinearMap.id 𝕜 F₁ := by
    filter_upwards [eventually_extChartAt_symm_mem_baseSet I h₁ (mem_chart_source H x)] with z hz
    exact ContinuousLinearMap.inCoordinates_id ((mem_baseSet_iff F₁ V₁).1 hz).1
  have hx : homLocalRep I F₁ F₁ (fun y ↦ ContinuousLinearMap.id 𝕜 (V₁ y)) x
      (extChartAt I x x) = ContinuousLinearMap.id 𝕜 F₁ := by
    rw [homLocalRep_extChartAt _ (mem_chart_source H x)]
    exact ContinuousLinearMap.inCoordinates_id (mem_baseSet_trivializationAt F₁ V₁ x)
  rw [map, hc.fderivWithin_eq hx, fderivWithin_const_apply, hx]
  exact ContinuousLinearMap.firstJetPullback_id

section Comp

variable {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {V₃ : M → Type*} [TopologicalSpace (TotalSpace F₃ V₃)] [∀ x, AddCommGroup (V₃ x)]
  [∀ x, Module 𝕜 (V₃ x)] [∀ x, TopologicalSpace (V₃ x)] [FiberBundle F₃ V₃]
  [VectorBundle 𝕜 F₃ V₃] [ContMDiffVectorBundle 1 F₃ V₃ I]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul 𝕜 (V₃ x)]

/-- **Functoriality of the prolongation.** For fields of linear maps `Φ` and `Ψ` differentiable at
`x`, the prolongation of `Ψ ∘ Φ` is the composite of the prolongations. -/
theorem map_comp {Φ : ∀ x, V₁ x →L[𝕜] V₂ x} {Ψ : ∀ x, V₂ x →L[𝕜] V₃ x} {x : M}
    (hΨ : MDifferentiableAt I (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₃))
      (fun y ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃) (E := fun y ↦ V₂ y →L[𝕜] V₃ y) y (Ψ y)) x)
    (hΦ : MDifferentiableAt I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ V₁ y →L[𝕜] V₂ y) y (Φ y)) x) :
    map I F₁ F₃ (fun y ↦ (Ψ y).comp (Φ y)) x = map I F₂ F₃ Ψ x ∘L map I F₁ F₂ Φ x := by
  refine (eq_map_of_forall_jet (hΨ.clm_bundle_comp hΦ) _ fun s hs ↦ ?_).symm
  have hs' := hs.mdifferentiableAt one_ne_zero
  rw [ContinuousLinearMap.comp_apply, map_jet hΦ hs', map_jet hΨ (hΦ.clm_bundle_apply hs')]
  simp only [ContinuousLinearMap.comp_apply]

end Comp

/-! ### Isomorphisms of vector bundles -/

section Equiv

variable [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul 𝕜 (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]

variable (I F₁ F₂) in
/-- The prolongation of a field `Φ` of continuous linear equivalences which is differentiable at
`x` together with its inverse, for instance of a smooth isomorphism of vector bundles: a continuous
linear equivalence `J¹V₁ x ≃L[𝕜] J¹V₂ x`, whose inverse is the prolongation of the inverse. -/
def mapEquiv (Φ : ∀ x, V₁ x ≃L[𝕜] V₂ x) (x : M)
    (hΦ : MDifferentiableAt I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ V₁ y →L[𝕜] V₂ y) y (Φ y)) x)
    (hΦ' : MDifferentiableAt I (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁))
      (fun y ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun y ↦ V₂ y →L[𝕜] V₁ y) y (Φ y).symm) x) :
    FirstJetBundle I F₁ V₁ x ≃L[𝕜] FirstJetBundle I F₂ V₂ x :=
  ContinuousLinearEquiv.equivOfInverse' (map I F₁ F₂ (fun y ↦ Φ y) x)
    (map I F₂ F₁ (fun y ↦ (Φ y).symm) x)
    (by
      rw [← map_comp hΦ hΦ']
      simp_rw [ContinuousLinearEquiv.coe_comp_coe_symm]
      exact map_id x)
    (by
      rw [← map_comp hΦ' hΦ]
      simp_rw [ContinuousLinearEquiv.coe_symm_comp_coe]
      exact map_id x)

variable {Φ : ∀ x, V₁ x ≃L[𝕜] V₂ x} {x : M}
  {hΦ : MDifferentiableAt I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
    (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ V₁ y →L[𝕜] V₂ y) y (Φ y)) x}
  {hΦ' : MDifferentiableAt I (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁))
    (fun y ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun y ↦ V₂ y →L[𝕜] V₁ y) y (Φ y).symm) x}

/-- The equivalence `mapEquiv` is the prolongation of `Φ`. -/
@[simp]
theorem coe_mapEquiv :
    (mapEquiv I F₁ F₂ Φ x hΦ hΦ' : FirstJetBundle I F₁ V₁ x →L[𝕜] FirstJetBundle I F₂ V₂ x) =
      map I F₁ F₂ (fun y ↦ Φ y) x :=
  (rfl)

/-- The inverse of `mapEquiv` is the prolongation of the inverse of `Φ`. -/
@[simp]
theorem coe_mapEquiv_symm :
    ((mapEquiv I F₁ F₂ Φ x hΦ hΦ').symm :
        FirstJetBundle I F₂ V₂ x →L[𝕜] FirstJetBundle I F₁ V₁ x) =
      map I F₂ F₁ (fun y ↦ (Φ y).symm) x :=
  (rfl)

/-- The equivalence `mapEquiv` applies the prolongation of `Φ`. -/
@[simp]
theorem mapEquiv_apply (j : FirstJetBundle I F₁ V₁ x) :
    mapEquiv I F₁ F₂ Φ x hΦ hΦ' j = map I F₁ F₂ (fun y ↦ Φ y) x j :=
  (rfl)

/-- The inverse of `mapEquiv` applies the prolongation of the inverse of `Φ`. -/
@[simp]
theorem mapEquiv_symm_apply (j : FirstJetBundle I F₂ V₂ x) :
    (mapEquiv I F₁ F₂ Φ x hΦ hΦ').symm j = map I F₂ F₁ (fun y ↦ (Φ y).symm) x j :=
  (rfl)

end Equiv

end Prolongation

/-! ### Smoothness of the prolongation -/

variable [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]

/-- **The prolongation of a `C^(n+1)` field of linear maps is a `C^n` bundle map.** If `Φ` is a
`C^(n+1)` section of the hom bundle at `x₀`, then `x ↦ J¹Φ x` is a `C^n` section of the bundle of
continuous linear maps from `J¹V₁` to `J¹V₂` at `x₀`. -/
theorem contMDiffAt_map {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [ContMDiffVectorBundle (n + 1) F₁ V₁ I] [ContMDiffVectorBundle (n + 1) F₂ V₂ I]
    {Φ : ∀ x, V₁ x →L[𝕜] V₂ x} {x₀ : M}
    (hΦ : ContMDiffAt I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) (n + 1)
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ V₁ y →L[𝕜] V₂ y) y (Φ y)) x₀) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffVectorBundle 1 F₁ V₁ I := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffVectorBundle 1 F₂ V₂ I := .of_le (n := n + 1) le_add_self
    ContMDiffAt I (I.prod 𝓘(𝕜, (F₁ × (E →L[𝕜] F₁)) →L[𝕜] F₂ × (E →L[𝕜] F₂))) n
      (fun y ↦ TotalSpace.mk' ((F₁ × (E →L[𝕜] F₁)) →L[𝕜] F₂ × (E →L[𝕜] F₂))
        (E := fun y ↦ FirstJetBundle I F₁ V₁ y →L[𝕜] FirstJetBundle I F₂ V₂ y) y
        (map I F₁ F₂ Φ y)) x₀ := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : ContMDiffVectorBundle 1 F₁ V₁ I := .of_le (n := n + 1) le_add_self
  have : ContMDiffVectorBundle 1 F₂ V₂ I := .of_le (n := n + 1) le_add_self
  have h₁ := mem_baseSet_self (H := H) F₁ V₁ x₀
  have h₂ := mem_baseSet_self (H := H) F₂ V₂ x₀
  have hx₀' : x₀ ∈ (extChartAt I x₀).source := mem_extChartAt_source x₀
  -- `Φ` is `C^1`, hence differentiable, on a neighbourhood `u` of `x₀`.
  obtain ⟨u, hu, hΦu⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (n := 1) (by simp)).1 (hΦ.of_le le_add_self)
  refine (contMDiffAt_hom_bundle _).2 ⟨contMDiffAt_id, ?_⟩
  -- In the chart at `x₀`, the prolongation is the first-jet transformation with coefficients
  -- the local representative `g` of `Φ` and its derivative, which is `C^n`.
  have hg := contDiffWithinAt_homLocalRep hΦ h₁ (mem_baseSet_trivializationAt F₂ V₂ x₀)
  have hQ := (hg.of_le le_self_add).firstJetPullback (hg.fderivWithin_right I.uniqueDiffOn le_rfl
    (extChartAt_target_subset_range x₀ ((extChartAt I x₀).map_source hx₀')))
    (contDiffWithinAt_const (c := ContinuousLinearMap.id 𝕜 E))
  have hQ' : ContMDiffAt I 𝓘(𝕜, (F₁ × (E →L[𝕜] F₁)) →L[𝕜] F₂ × (E →L[𝕜] F₂)) n
      (fun y ↦ (homLocalRep I F₁ F₂ Φ x₀ (extChartAt I x₀ y)).firstJetPullback
        (fderivWithin 𝕜 (homLocalRep I F₁ F₂ Φ x₀) (range I) (extChartAt I x₀ y))
        (ContinuousLinearMap.id 𝕜 E)) x₀ := by
    rw [← contMDiffWithinAt_univ]
    exact (contMDiffWithinAt_iff_contDiffWithinAt.2 hQ).comp x₀
      contMDiffAt_extChartAt.contMDiffWithinAt fun x _ ↦ by
        rw [extChartAt_coe]; exact mem_range_self _
  refine hQ'.congr_of_eventuallyEq ?_
  filter_upwards [eventually_eventually_nhds.2 hu, (isOpen_baseSet F₁ V₁ x₀).mem_nhds h₁,
    (isOpen_baseSet F₂ V₂ x₀).mem_nhds h₂] with y hyu hy₁ hy₂
  have hΦy := (hΦu.contMDiffAt hyu).mdifferentiableAt (by simp)
  -- Read in the trivializations of the first-jet bundles at `x₀`, the prolongation is conjugated
  -- by first-jet coordinate changes.
  refine (VectorBundleCore.inCoordinates_eq (firstJetBundleCore I F₁ V₁)
    (firstJetBundleCore I F₂ V₂) (map I F₁ F₂ Φ y)
    (by rw [firstJetBundleCore_indexAt, firstJetBundleCore_baseSet]; exact hy₁)
    (by rw [firstJetBundleCore_indexAt, firstJetBundleCore_baseSet]; exact hy₂)).trans
    (ContinuousLinearMap.ext fun k ↦ ?_)
  simp only [firstJetBundleCore_coordChange, firstJetBundleCore_indexAt]
  -- The fibres of `J¹Vᵢ` are type synonyms of their model fibres, so the composition lemmas
  -- cannot rewrite the composite of first-jet coordinate changes and `J¹Φ y`; unfold it by
  -- `change`.
  change coordChange I F₂ V₂ y x₀ y (map I F₁ F₂ Φ y (coordChange I F₁ V₁ x₀ y y k)) = _
  exact (coordChange_map hΦy hy₁ hy₂ (coordChange I F₁ V₁ x₀ y y k)).trans (by
    rw [coordChange_comp_apply hy₁ (mem_baseSet_self F₁ V₁ y) hy₁, coordChange_self_apply hy₁])

/-- **The prolongation of a `C^(n+1)` field of linear maps is a `C^n` bundle map.** If `Φ` is a
`C^(n+1)` section of the hom bundle on an open set `U`, then `x ↦ J¹Φ x` is a `C^n` section of the
bundle of continuous linear maps from `J¹V₁` to `J¹V₂` on `U`. -/
theorem contMDiffOn_map {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [ContMDiffVectorBundle (n + 1) F₁ V₁ I] [ContMDiffVectorBundle (n + 1) F₂ V₂ I]
    {Φ : ∀ x, V₁ x →L[𝕜] V₂ x} {U : Set M} (hU : IsOpen U)
    (hΦ : ContMDiffOn I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) (n + 1)
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ V₁ y →L[𝕜] V₂ y) y (Φ y)) U) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffVectorBundle 1 F₁ V₁ I := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffVectorBundle 1 F₂ V₂ I := .of_le (n := n + 1) le_add_self
    ContMDiffOn I (I.prod 𝓘(𝕜, (F₁ × (E →L[𝕜] F₁)) →L[𝕜] F₂ × (E →L[𝕜] F₂))) n
      (fun y ↦ TotalSpace.mk' ((F₁ × (E →L[𝕜] F₁)) →L[𝕜] F₂ × (E →L[𝕜] F₂))
        (E := fun y ↦ FirstJetBundle I F₁ V₁ y →L[𝕜] FirstJetBundle I F₂ V₂ y) y
        (map I F₁ F₂ Φ y)) U := fun _ hx ↦
  (contMDiffAt_map (hΦ.contMDiffAt (hU.mem_nhds hx))).contMDiffWithinAt

/-- **The prolongation of a `C^(n+1)` field of linear maps is a `C^n` bundle map.** -/
theorem contMDiff_map {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [ContMDiffVectorBundle (n + 1) F₁ V₁ I] [ContMDiffVectorBundle (n + 1) F₂ V₂ I]
    {Φ : ∀ x, V₁ x →L[𝕜] V₂ x}
    (hΦ : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) (n + 1)
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ V₁ y →L[𝕜] V₂ y) y (Φ y))) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffVectorBundle 1 F₁ V₁ I := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffVectorBundle 1 F₂ V₂ I := .of_le (n := n + 1) le_add_self
    ContMDiff I (I.prod 𝓘(𝕜, (F₁ × (E →L[𝕜] F₁)) →L[𝕜] F₂ × (E →L[𝕜] F₂))) n
      fun y ↦ TotalSpace.mk' ((F₁ × (E →L[𝕜] F₁)) →L[𝕜] F₂ × (E →L[𝕜] F₂))
        (E := fun y ↦ FirstJetBundle I F₁ V₁ y →L[𝕜] FirstJetBundle I F₂ V₂ y) y
        (map I F₁ F₂ Φ y) :=
  fun x₀ ↦ contMDiffAt_map (hΦ x₀)

end FirstJetBundle

end TauCeti
