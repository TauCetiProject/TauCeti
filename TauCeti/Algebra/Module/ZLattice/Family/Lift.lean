/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.Algebra.Module.ZLattice.Family.Manifold

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Lifting maps into a family of tori

Let `P : Y → (Λ →ₗ[ℤ] E)` be a continuous family of full lattices, with total space the orbit
space `X = (Y × E)/Λ` of the period translation action. The orbit map `Y × E → X` is a covering
map (`TauCeti.isAddQuotientCoveringMap_torusFamily_mk`), and this file applies the lifting
theory of covering maps to it.

A continuous map `σ : Z → X` from a simply connected, locally path-connected space has a
continuous vector lift `β : Z → E`, with `σ z = [p (σ z), β z]` for the projection `p : X → Y`
(`TauCeti.exists_continuous_lift_torusFamily`). Two continuous lifts differ by a single period
(`TauCeti.exists_eq_add_period_of_mk_eq_mk`), since a continuous family of periods over a
preconnected space is a single period (`TauCeti.exists_eq_period_of_mem_range`). For a `C^n`
family of lattices, a continuous lift of a `C^n` map is `C^n`, since the orbit map is a local
diffeomorphism (`TauCeti.contMDiff_of_torusFamily_mk_eq`); over `ℂ` a holomorphic map has
holomorphic lifts.

For the rotation `z ↦ ζ z` of a disc by a primitive `m`-th root of unity, this applies to a
generator acting by translations with holomorphic translation section `b`: the section lifts
holomorphically through the period covering of the simply connected disc. The orbit sum of the
lift is then a constant lattice vector (`TauCeti.exists_birkhoffSum_translation_eq_period` in
`TauCeti.Algebra.Module.ZLattice.Family.AffineAction`). This is the input to the normalization of
the translation part in the construction of logarithmic transforms.

## Main results

* `TauCeti.exists_continuous_lift_torusFamily`: maps from simply connected, locally path-connected
  spaces lift continuously to `E`.
* `TauCeti.exists_eq_add_period_of_mk_eq_mk`: two continuous lifts differ by a single period.
* `TauCeti.contMDiff_of_torusFamily_mk_eq`, `TauCeti.exists_contMDiff_lift_torusFamily`: lifts
  of `C^n` maps are `C^n`.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*, second
  edition, Springer (2004), Chapter V, section *Logarithmic transformations*, for the
  normalization of cyclic translations on families of tori over a disc.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Proposition 1.33 (the lifting criterion) and Proposition 1.34 (uniqueness of lifts).
-/

public section

open Function
open scoped Manifold ContDiff

namespace TauCeti

variable {Y : Type*} [TopologicalSpace Y] {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ]
  [Module.Finite ℤ Λ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))] {Z : Type*} [TopologicalSpace Z]

/-! ### Lifts through the period covering -/

section Lift

variable [T2Space Y] [LocallyCompactSpace Y] (hcont : ∀ l, Continuous fun y ↦ P y l)
  (hinj : ∀ y, Injective (P y))
include hcont hinj

/-- **Lifting maps into a family of tori.** A continuous map `σ` from a simply connected,
locally path-connected space `Z` into the family of tori has a continuous vector lift: a
continuous `β : Z → E` with `σ z = [p (σ z), β z]`, where `p` is the projection to `Y`. -/
theorem exists_continuous_lift_torusFamily [SimplyConnectedSpace Z] [LocallyPathConnectedSpace Z]
    {σ : Z → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)}
    (hσ : Continuous σ) :
    ∃ β : Z → E, Continuous β ∧
      ∀ z, Quotient.mk _ (torusFamilyProjection P (σ z), β z) = σ z := by
  let _ := periodAddAction P
  obtain ⟨z₀⟩ : Nonempty Z := inferInstance
  obtain ⟨e₀, he₀⟩ := Quotient.exists_rep (σ z₀)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := (isAddQuotientCoveringMap_torusFamily_mk P hcont hinj).isCoveringMap
    |>.existsUnique_continuousMap_lifts ⟨σ, hσ⟩ z₀ e₀ he₀
  refine ⟨fun z ↦ (F z).2, continuous_snd.comp F.continuous, fun z ↦ ?_⟩
  have hz : Quotient.mk _ (F z) = σ z := congrFun hF z
  rw [← hz, torusFamilyProjection_mk]

/-- **Uniqueness of lifts up to a period.** Over a preconnected space `Z`, two continuous vector
lifts `β`, `β'` of the same map into the family of tori, lying over `f`, differ by a single
period: `β' z = β z + P (f z) l` for one `l : Λ`. -/
theorem exists_eq_add_period_of_mk_eq_mk [PreconnectedSpace Z] {f : Z → Y} (hf : Continuous f)
    {β β' : Z → E} (hβ : Continuous β) (hβ' : Continuous β')
    (h : ∀ z, letI := periodAddAction P
      Quotient.mk (AddAction.orbitRel Λ (Y × E)) (f z, β' z) = Quotient.mk _ (f z, β z)) :
    ∃ l : Λ, ∀ z, β' z = β z + P (f z) l := by
  let _ := periodAddAction P
  obtain ⟨l, hl⟩ := exists_eq_period_of_mem_range P hcont hinj hf (hβ'.sub hβ) fun z ↦
    ((mem_orbit_periodAddAction_iff P).1 (Quotient.exact (h z))).2
  exact ⟨l, fun z ↦ eq_add_of_sub_eq' (hl z)⟩

end Lift

/-! ### Smooth and holomorphic lifts -/

section Regularity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {EY : Type*} [NormedAddCommGroup EY]
  [NormedSpace 𝕜 EY] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 EY H}
  [ChartedSpace H Y] [T2Space Y] [LocallyCompactSpace Y] [NormedSpace 𝕜 E]
  {EZ : Type*} [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ] {HZ : Type*} [TopologicalSpace HZ]
  {J : ModelWithCorners 𝕜 EZ HZ} [ChartedSpace HZ Z]
  (hinj : ∀ y, Injective (P y)) {n : WithTop ℕ∞} [IsManifold I n Y]
  (hP : ∀ l, ContMDiff I 𝓘(𝕜, E) n fun y ↦ P y l)
include hinj hP

/-- **Lifts of `C^n` maps are `C^n`.** For a `C^n` family of full lattices, a continuous vector
lift `β` of a `C^n` map `σ` into the family of tori, `σ z = [f z, β z]`, is `C^n`, because the
orbit map `Y × E → (Y × E)/Λ` is a `C^n` local diffeomorphism. Over `ℂ`, lifts of holomorphic
maps are holomorphic. -/
theorem contMDiff_of_torusFamily_mk_eq
    {σ : Z → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)}
    (hσ : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
      ContMDiff J (I.prod 𝓘(𝕜, E)) n σ)
    {f : Z → Y} {β : Z → E} (hβ : Continuous β) (h : ∀ z, Quotient.mk _ (f z, β z) = σ z) :
    ContMDiff J 𝓘(𝕜, E) n β := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  -- The base component `f = p ∘ σ` is `C^n`, since the projection `p` is.
  have hf : f = torusFamilyProjection P ∘ σ := funext fun z ↦ by simp [← h z]
  have hfβ : ContMDiff J (I.prod 𝓘(𝕜, E)) n fun z ↦ (f z, β z) :=
    ContMDiff.of_comp_isLocalDiffeomorph (isLocalDiffeomorph_torusFamily_mk P hinj hP)
      (by rw [hf]; exact ((continuous_torusFamilyProjection P).comp hσ.continuous).prodMk hβ)
      (by rwa [← funext h] at hσ)
  exact contMDiff_snd.comp hfβ

/-- **`C^n` lifts.** For a `C^n` family of full lattices, a `C^n` map `σ` from a simply
connected, locally path-connected manifold `Z` into the family of tori has a `C^n` vector lift `β`,
with `σ z = [p (σ z), β z]`. Over `ℂ`, holomorphic maps have holomorphic lifts. -/
theorem exists_contMDiff_lift_torusFamily [SimplyConnectedSpace Z] [LocallyPathConnectedSpace Z]
    {σ : Z → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)}
    (hσ : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
      ContMDiff J (I.prod 𝓘(𝕜, E)) n σ) :
    ∃ β : Z → E, ContMDiff J 𝓘(𝕜, E) n β ∧
      ∀ z, Quotient.mk _ (torusFamilyProjection P (σ z), β z) = σ z := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  obtain ⟨β, hβ, h⟩ := exists_continuous_lift_torusFamily P (fun l ↦ (hP l).continuous) hinj
    hσ.continuous
  exact ⟨β, contMDiff_of_torusFamily_mk_eq P hinj hP hσ hβ h, h⟩

end Regularity

end TauCeti
