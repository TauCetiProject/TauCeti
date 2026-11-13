/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Topology.MetricSpace.Pseudo.Prod
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Gluing fibre-preserving local diffeomorphisms along nested balls

Let `Φ : X × F → X × F'` preserve the first coordinate, with `F` a pseudometric space, and suppose
that for each index `i` of a set `U`, `Φ` agrees with a partial diffeomorphism `e i` on a product
`V i ×ˢ ball c (r i)` contained in its source. Over each point of `X` the balls `ball c (r i)`
meeting it are nested, since they share their centre, so two points of the union of the products
with the same image under `Φ` lie in a single product, where `Φ` is injective
(`TauCeti.injOn_biUnion_prod_ball`). Hence `Φ` is a partial diffeomorphism on the union of the
products (`TauCeti.exists_partialDiffeomorph_source_eq_biUnion_prod_ball`).

This is how local normal forms which are all restrictions of one fibre-preserving map, such as the
parametric Morse coordinate, glue to a single chart. When every radius `r i` is positive, its source
contains the part of the zero section lying over `⋃ i ∈ U, V i`; when moreover the `V i` cover `X`,
this is the whole zero section `X × {c}`.

## Main results

* `TauCeti.exists_partialDiffeomorph_source_eq_biUnion_prod_ball`: a fibre-preserving map which
  is a partial diffeomorphism on each product of a set with a ball about a common centre is a
  partial diffeomorphism on their union.
-/

public section

noncomputable section

open Set

namespace TauCeti

variable {ι X F F' : Type*} [PseudoMetricSpace F] {Φ : X × F → X × F'} {U : Set ι}
  {V : ι → Set X} {c : F} {r : ι → ℝ}
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E E' : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H G : Type*} [TopologicalSpace H]
  [TopologicalSpace G] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  [TopologicalSpace X] [ChartedSpace H (X × F)] [TopologicalSpace F'] [ChartedSpace G (X × F')]
  {n : WithTop ℕ∞}

/-- **Gluing along nested balls.** Let `Φ : X × F → X × F'` preserve the first coordinate on the
union of the products `V i ×ˢ ball c (r i)`, `i ∈ U`, of open sets with balls about a common centre
`c`, and agree on each product with a partial diffeomorphism `e i` whose source contains it. Then
`Φ` is a partial diffeomorphism with source the union of these products. -/
theorem exists_partialDiffeomorph_source_eq_biUnion_prod_ball
    (hΦ : ∀ z ∈ ⋃ i ∈ U, V i ×ˢ Metric.ball c (r i), (Φ z).1 = z.1)
    {e : ι → PartialDiffeomorph I J (X × F) (X × F') n} (hV : ∀ i ∈ U, IsOpen (V i))
    (hVe : ∀ i ∈ U, V i ×ˢ Metric.ball c (r i) ⊆ (e i).source)
    (hΦe : ∀ i ∈ U, EqOn Φ (e i) (V i ×ˢ Metric.ball c (r i))) :
    ∃ ψ : PartialDiffeomorph I J (X × F) (X × F') n,
      ψ.source = ⋃ i ∈ U, V i ×ˢ Metric.ball c (r i) ∧ ⇑ψ = Φ := by
  set T := ⋃ i ∈ U, V i ×ˢ Metric.ball c (r i) with hTdef
  have hP (i : ι) (hi : i ∈ U) : IsOpen (V i ×ˢ Metric.ball c (r i)) :=
    (hV i hi).prod Metric.isOpen_ball
  have hT : IsOpen T := isOpen_biUnion hP
  have hinj : InjOn Φ T := injOn_biUnion_prod_ball hΦ fun i hi ↦
    ((e i).toPartialEquiv.injOn.mono (hVe i hi)).congr fun z hz ↦ (hΦe i hi hz).symm
  have hld : IsLocalDiffeomorphOn I J n Φ T := fun ⟨z, hz⟩ ↦ by
    simp only [hTdef, mem_iUnion, exists_prop] at hz
    obtain ⟨i, hi, hzi⟩ := hz
    -- Restricted to the product, `e i` has source the product, on which it is `Φ`.
    have hsource : ((e i).restrOpen _ (hP i hi)).source = V i ×ˢ Metric.ball c (r i) := by
      rw [PartialDiffeomorph.restrOpen_source, inter_eq_right.mpr (hVe i hi)]
    refine isLocalDiffeomorphAt_of_eqOn (hsource ▸ hzi) ?_
    rw [hsource, PartialDiffeomorph.coe_restrOpen]
    exact hΦe i hi
  rcases isEmpty_or_nonempty (X × F) with hXF | hXF
  · -- `X` is empty, as `F` contains `c`; so are both products, and `Φ` is the empty map.
    have : IsEmpty X := ⟨fun x ↦ isEmptyElim (x, c)⟩
    let ψ : PartialDiffeomorph I J (X × F) (X × F') n :=
      { toPartialEquiv := (Equiv.equivOfIsEmpty (X × F) (X × F')).toPartialEquiv
        open_source := isOpen_univ
        open_target := isOpen_univ
        contMDiffOn_toFun := fun z ↦ isEmptyElim z
        contMDiffOn_invFun := fun z ↦ isEmptyElim z }
    exact ⟨ψ, Subsingleton.elim _ _, funext fun z ↦ isEmptyElim z⟩
  exact ⟨hld.partialDiffeomorphOfInjOn hT hinj,
    hld.partialDiffeomorphOfInjOn_source hT hinj, hld.coe_partialDiffeomorphOfInjOn hT hinj⟩

end TauCeti
