/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Gluing fibre-preserving local diffeomorphisms along nested balls

Let `Φ : X × F → X × F` preserve the first coordinate, with `F` a pseudometric space, and suppose
that near each point `b` of a set `U`, `Φ` agrees with a partial diffeomorphism `e b` whose source
contains a product `V b ×ˢ ball c (r b)`. Over each point of `X` the balls `ball c (r b)` meeting
it are nested, since they share their centre, so two points of the union of the products with the
same image under `Φ` lie in a single product, where `Φ` is injective. Hence `Φ` is a partial
diffeomorphism on the union of the products
(`TauCeti.exists_partialDiffeomorph_eq_of_biUnion_prod_ball`).

This is how local normal forms which are all restrictions of one fibre-preserving map, such as the
parametric Morse coordinate, glue to a single chart along the whole zero section `X × {c}`.

## Main results

* `TauCeti.injOn_biUnion_prod_ball`: a fibre-preserving map injective on each product of a set with
  a ball about a common centre is injective on their union.
* `TauCeti.exists_partialDiffeomorph_eq_of_biUnion_prod_ball`: a fibre-preserving map which is a
  partial diffeomorphism near each such product is a partial diffeomorphism on their union.
-/

public section

noncomputable section

open Set

namespace TauCeti

variable {X F : Type*} [PseudoMetricSpace F] {Φ : X × F → X × F} {U : Set X} {V : X → Set X}
  {c : F} {r : X → ℝ}

/-- A map of `X × F` preserving the first coordinate and injective on each product
`V b ×ˢ ball c (r b)`, `b ∈ U`, is injective on their union: over each point of `X` the balls are
nested, so two points with the same image lie in the product with the larger ball. -/
theorem injOn_biUnion_prod_ball (hΦ : ∀ z, (Φ z).1 = z.1)
    (hinj : ∀ b ∈ U, InjOn Φ (V b ×ˢ Metric.ball c (r b))) :
    InjOn Φ (⋃ b ∈ U, V b ×ˢ Metric.ball c (r b)) := by
  intro z hz z' hz' h
  simp only [mem_iUnion, exists_prop] at hz hz'
  obtain ⟨b, hb, hzb⟩ := hz
  obtain ⟨b', hb', hzb'⟩ := hz'
  have h1 : z.1 = z'.1 := by rw [← hΦ z, ← hΦ z', h]
  wlog hle : r b ≤ r b' generalizing z z' b b'
  · exact (this h.symm b' hb' hzb' b hb hzb h1.symm (le_of_not_ge hle)).symm
  exact hinj b' hb' ⟨h1 ▸ hzb'.1, Metric.ball_subset_ball hle hzb.2⟩ hzb' h

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace X] [ChartedSpace H (X × F)] {n : WithTop ℕ∞}

/-- **Gluing along nested balls.** Let `Φ : X × F → X × F` preserve the first coordinate and agree,
for each `b ∈ U`, with a partial diffeomorphism `e b` on its source, which contains the product
`V b ×ˢ ball c (r b)` of an open set with a ball about a common centre `c`. Then `Φ` is a partial
diffeomorphism on the union of these products. -/
theorem exists_partialDiffeomorph_eq_of_biUnion_prod_ball (hΦ : ∀ z, (Φ z).1 = z.1)
    {e : X → PartialDiffeomorph I I (X × F) (X × F) n} (hV : ∀ b ∈ U, IsOpen (V b))
    (hVe : ∀ b ∈ U, V b ×ˢ Metric.ball c (r b) ⊆ (e b).source)
    (hΦe : ∀ b ∈ U, EqOn Φ (e b) (e b).source) :
    ∃ ψ : PartialDiffeomorph I I (X × F) (X × F) n,
      ψ.source = ⋃ b ∈ U, V b ×ˢ Metric.ball c (r b) ∧ ⇑ψ = Φ := by
  set T := ⋃ b ∈ U, V b ×ˢ Metric.ball c (r b) with hTdef
  have hmemT {z : X × F} : z ∈ T ↔ ∃ b ∈ U, z ∈ V b ×ˢ Metric.ball c (r b) := by
    simp only [hTdef, mem_iUnion, exists_prop]
  have hT : IsOpen T := isOpen_biUnion fun b hb ↦ (hV b hb).prod Metric.isOpen_ball
  have hinj : InjOn Φ T := injOn_biUnion_prod_ball hΦ fun b hb ↦
    ((e b).toPartialEquiv.injOn.mono (hVe b hb)).congr fun z hz ↦ (hΦe b hb (hVe b hb hz)).symm
  have hld : IsLocalDiffeomorphOn I I n Φ T := fun ⟨z, hz⟩ ↦ by
    obtain ⟨b, hb, hzb⟩ := hmemT.mp hz
    exact isLocalDiffeomorphAt_of_eqOn (hVe b hb hzb) (hΦe b hb)
  rcases isEmpty_or_nonempty (X × F) with hXF | hXF
  · -- On an empty space the identity has the empty source, and is `Φ`.
    let ψ : PartialDiffeomorph I I (X × F) (X × F) n :=
      { toPartialEquiv := PartialEquiv.refl _
        open_source := isOpen_univ
        open_target := isOpen_univ
        contMDiffOn_toFun := fun z ↦ isEmptyElim z
        contMDiffOn_invFun := fun z ↦ isEmptyElim z }
    exact ⟨ψ, Subsingleton.elim _ _, funext fun z ↦ isEmptyElim z⟩
  exact ⟨hld.partialDiffeomorphOfInjOn hT hinj,
    hld.partialDiffeomorphOfInjOn_source hT hinj, hld.coe_partialDiffeomorphOfInjOn hT hinj⟩

end TauCeti
