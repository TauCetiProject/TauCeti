/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.GraphClosure

/-!
# The graph of a rational map

For a rational map `f : X ⤏ Y` with representative `(V, g)` (Mathlib's
`Scheme.RationalMap.representative`), the *graph* `Γ_f` is the scheme-theoretic image of
`γ_f = (ι_V, g) : V → X × Y`, and its *projections* `π_1 : Γ_f → X` and `π_2 : Γ_f → Y` are the
closed immersion `Γ_f → X × Y` followed by the projections of the product. The map `γ_f` factors
through `Γ_f`, with `π_1 ∘ γ_f = ι_V` and `π_2 ∘ γ_f = g`.

This is Tau Ceti's graph closure `TauCeti.AlgebraicGeometry.graphClosure` over the terminal
scheme: `X × Y` is the fibre product `X ×_{Spec ℤ} Y` (Mathlib's `prodIsoPullback` identifies it
with the categorical product), and the definitions below are abbreviations, so the graph closure
API applies to them. For instance, `TauCeti.AlgebraicGeometry.toGraphClosure_graphClosureFst` and
`TauCeti.AlgebraicGeometry.toGraphClosure_graphClosureSnd` give `π_1 ∘ γ_f = ι_V` and
`π_2 ∘ γ_f = g`, and `TauCeti.AlgebraicGeometry.isIso_graphClosureFst_restrict` shows that `π_1`
is an isomorphism over `V` when `Y` is separated and `V → X` is quasi-compact.

When `γ_f` is quasi-compact (for instance when `X` is a Noetherian topological space, or when
`V → X` is quasi-compact and `Y` is quasi-separated), the scheme-theoretic image API applies.
Mathlib's instances make the factorization `V → Γ_f` quasi-compact and dominant. Tau Ceti's
`Scheme.Hom.range_imageι` (in `TauCeti/AlgebraicGeometry/SchemeTheoreticImage/Basic.lean`) shows
that `Γ_f` is supported on the closure of the image of `V`, and Tau Ceti's
`Scheme.Hom.isIntegral_image` (same file) gives that `Γ_f` is integral when `X` is integral.

## Main definitions

* `AlgebraicGeometry.Scheme.RationalMap.graphLift`: the morphism `γ_f = (ι_V, g) : V → X × Y`.
* `AlgebraicGeometry.Scheme.RationalMap.graph`: the graph `Γ_f`.
* `AlgebraicGeometry.Scheme.RationalMap.graphι`: the closed immersion `Γ_f → X × Y`.
* `AlgebraicGeometry.Scheme.RationalMap.graphFst`, `AlgebraicGeometry.Scheme.RationalMap.graphSnd`:
  the projections `π_1` and `π_2`.
* `AlgebraicGeometry.Scheme.RationalMap.toGraph`: the factorization `V → Γ_f` of `γ_f`.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.isIntegral_graph`: the graph of a rational map out of an
  integral scheme is integral when `γ_f` is quasi-compact, for instance when `X` is Noetherian.

## References

* [T.-C. Dinh and N. Sibony, *Une borne supérieure pour l'entropie topologique d'une application
  rationnelle*, Ann. of Math. 161 (2005)](https://arxiv.org/abs/math/0303271), the graph of a
  rational map and its projections.
-/

public section

open CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.RationalMap

universe u

variable {X Y : Scheme.{u}} (f : X ⤏ Y)

/-- The morphism `γ_f = (ι_V, g) : V → X × Y` for the representative `(V, g)` of `f`, with
`X × Y` the fibre product over the terminal scheme. -/
abbrev graphLift :
    f.representative.domain.toScheme ⟶ pullback (terminal.from X) (terminal.from Y) :=
  opensGraph (terminal.from X) (terminal.from Y) f.representative.domain f.representative.hom
    (terminal.hom_ext _ _)

/-- The graph `Γ_f` of a rational map `f : X ⤏ Y`: the scheme-theoretic image of
`γ_f = (ι_V, g) : V → X × Y` for the representative `(V, g)` of `f`, that is, the graph closure
of `g` over the terminal scheme. -/
abbrev graph : Scheme.{u} :=
  graphClosure (terminal.from X) (terminal.from Y) f.representative.domain f.representative.hom
    (terminal.hom_ext _ _)

/-- The closed immersion of the graph `Γ_f` into `X × Y`. -/
abbrev graphι : graph f ⟶ pullback (terminal.from X) (terminal.from Y) :=
  (graphLift f).imageι

/-- The first projection `π_1 : Γ_f → X` of the graph. -/
abbrev graphFst : graph f ⟶ X :=
  graphClosureFst (terminal.from X) (terminal.from Y) f.representative.domain f.representative.hom
    (terminal.hom_ext _ _)

/-- The second projection `π_2 : Γ_f → Y` of the graph. -/
abbrev graphSnd : graph f ⟶ Y :=
  graphClosureSnd (terminal.from X) (terminal.from Y) f.representative.domain f.representative.hom
    (terminal.hom_ext _ _)

/-- The factorization `V → Γ_f` of `γ_f` through the graph. -/
abbrev toGraph : f.representative.domain.toScheme ⟶ graph f :=
  toGraphClosure (terminal.from X) (terminal.from Y) f.representative.domain f.representative.hom
    (terminal.hom_ext _ _)

/-- Out of a Noetherian space, `γ_f` is quasi-compact: its source is an open subspace of a
Noetherian space. -/
instance quasiCompact_graphLift [NoetherianSpace X] : QuasiCompact (graphLift f) :=
  have : NoetherianSpace f.representative.domain.toScheme :=
    NoetherianSpace.set (f.representative.domain : Set X)
  quasiCompact_of_noetherianSpace_source _

/-- The graph of a rational map out of an integral scheme is integral when `γ_f` is
quasi-compact. -/
instance isIntegral_graph [IsIntegral X] [QuasiCompact (graphLift f)] : IsIntegral (graph f) :=
  have : Nonempty f.representative.domain :=
    f.representative.dense_domain.nonempty.to_subtype
  inferInstance

end AlgebraicGeometry.Scheme.RationalMap
