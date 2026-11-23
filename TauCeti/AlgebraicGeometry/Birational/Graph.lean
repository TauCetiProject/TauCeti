/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# The graph of a rational map

For a rational map `f : X ⤏ Y` with representative `(V, g)` (Mathlib's
`Scheme.RationalMap.representative`), the *graph* `Γ_f` is the scheme-theoretic image of
`γ_f = (ι_V, g) : V → X × Y`, and its *projections* `π_1 : Γ_f → X` and `π_2 : Γ_f → Y` are the
closed immersion `Γ_f → X × Y` followed by the projections of the product. The map `γ_f` factors
through `Γ_f`, with `π_1 ∘ γ_f = ι_V` and `π_2 ∘ γ_f = g`.

When `X` is a Noetherian topological space, `γ_f` is quasi-compact, so `Γ_f` is supported on the
closure of the image of `V`, the factorization `V → Γ_f` is dominant, and `Γ_f` is integral when
`X` is integral.

## Main definitions

* `AlgebraicGeometry.Scheme.RationalMap.graphLift`: the morphism `γ_f = (ι_V, g) : V → X × Y`.
* `AlgebraicGeometry.Scheme.RationalMap.graph`: the graph `Γ_f`.
* `AlgebraicGeometry.Scheme.RationalMap.graphι`: the closed immersion `Γ_f → X × Y`.
* `AlgebraicGeometry.Scheme.RationalMap.graphFst`, `AlgebraicGeometry.Scheme.RationalMap.graphSnd`:
  the projections `π_1` and `π_2`.
* `AlgebraicGeometry.Scheme.RationalMap.toGraph`: the factorization `V → Γ_f` of `γ_f`.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.toGraph_graphFst` and
  `AlgebraicGeometry.Scheme.RationalMap.toGraph_graphSnd`: `π_1 ∘ γ_f = ι_V` and `π_2 ∘ γ_f = g`.
* `AlgebraicGeometry.Scheme.RationalMap.range_graphι`: the graph is supported on the closure of
  the image of `γ_f`.
* `AlgebraicGeometry.Scheme.RationalMap.isIntegral_graph`: the graph of a rational map out of a
  Noetherian integral scheme is integral.
-/

public section

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.RationalMap

universe u

variable {X Y : Scheme.{u}} (f : X ⤏ Y)

/-- The morphism `γ_f = (ι_V, g) : V → X × Y` for the representative `(V, g)` of `f`. -/
def graphLift : f.representative.domain.toScheme ⟶ X ⨯ Y :=
  prod.lift f.representative.domain.ι f.representative.hom

/-- The graph `Γ_f` of a rational map `f : X ⤏ Y`: the scheme-theoretic image of
`γ_f = (ι_V, g) : V → X × Y` for the representative `(V, g)` of `f`. -/
def graph : Scheme.{u} :=
  (graphLift f).image

/-- The closed immersion of the graph `Γ_f` into `X × Y`. -/
def graphι : graph f ⟶ X ⨯ Y :=
  (graphLift f).imageι

/-- The first projection `π_1 : Γ_f → X` of the graph. -/
def graphFst : graph f ⟶ X :=
  graphι f ≫ prod.fst

/-- The second projection `π_2 : Γ_f → Y` of the graph. -/
def graphSnd : graph f ⟶ Y :=
  graphι f ≫ prod.snd

/-- The factorization `V → Γ_f` of `γ_f` through the graph. -/
def toGraph : f.representative.domain.toScheme ⟶ graph f :=
  (graphLift f).toImage

/-- The graph is a closed subscheme of `X × Y`. -/
instance isClosedImmersion_graphι : IsClosedImmersion (graphι f) :=
  inferInstanceAs (IsClosedImmersion (graphLift f).ker.subschemeι)

/-- The first projection of `γ_f` is the inclusion of the domain of the representative. -/
@[reassoc (attr := simp)]
theorem graphLift_fst : graphLift f ≫ prod.fst = f.representative.domain.ι :=
  prod.lift_fst _ _

/-- The second projection of `γ_f` is the representative. -/
@[reassoc (attr := simp)]
theorem graphLift_snd : graphLift f ≫ prod.snd = f.representative.hom :=
  prod.lift_snd _ _

/-- The factorization through the graph followed by its inclusion is `γ_f`. -/
@[reassoc (attr := simp)]
theorem toGraph_graphι : toGraph f ≫ graphι f = graphLift f :=
  (graphLift f).toImage_imageι

/-- `π_1 ∘ γ_f = ι_V`. -/
@[reassoc (attr := simp)]
theorem toGraph_graphFst : toGraph f ≫ graphFst f = f.representative.domain.ι := by
  rw [graphFst, toGraph_graphι_assoc, graphLift_fst]

/-- `π_2 ∘ γ_f = g`: the second projection restricts to the representative. -/
@[reassoc (attr := simp)]
theorem toGraph_graphSnd : toGraph f ≫ graphSnd f = f.representative.hom := by
  rw [graphSnd, toGraph_graphι_assoc, graphLift_snd]

section Noetherian

variable [NoetherianSpace X]

/-- Out of a Noetherian space, `γ_f` is quasi-compact: its source is an open subspace of a
Noetherian space. -/
instance quasiCompact_graphLift : QuasiCompact (graphLift f) :=
  have : NoetherianSpace f.representative.domain.toScheme :=
    NoetherianSpace.set (f.representative.domain : Set X)
  quasiCompact_of_noetherianSpace_source _

/-- Out of a Noetherian space, the factorization of `γ_f` through the graph is quasi-compact. -/
instance quasiCompact_toGraph : QuasiCompact (toGraph f) := by
  have : QuasiCompact (toGraph f ≫ graphι f) := by
    rw [toGraph_graphι]
    infer_instance
  exact QuasiCompact.of_comp (toGraph f) (graphι f)

/-- The graph is supported on the closure of the image of `γ_f`. -/
theorem range_graphι : Set.range (graphι f) = closure (Set.range (graphLift f)) :=
  (graphLift f).range_imageι

/-- The factorization of `γ_f` through the graph is dominant. -/
instance isDominant_toGraph : IsDominant (toGraph f) :=
  have : IsSchemeTheoreticallyDominant (toGraph f) :=
    (graphLift f).isSchemeTheoreticallyDominant_toImage
  inferInstance

/-- The graph of a rational map out of a Noetherian integral scheme is integral. -/
instance isIntegral_graph [IsIntegral X] : IsIntegral (graph f) := by
  have : Nonempty f.representative.domain :=
    f.representative.dense_domain.nonempty.to_subtype
  unfold graph
  infer_instance

end Noetherian

end AlgebraicGeometry.Scheme.RationalMap
