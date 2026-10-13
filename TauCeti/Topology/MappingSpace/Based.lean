/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.Topology.ContinuousMap.Precomp
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map

/-!
# Based mapping spaces out of a quotient of the cube

For a topological space `B` with a basepoint `b₀`, the based mapping space `Map_*(B, X)` is the
space of continuous maps `B → X` sending `b₀` to a prescribed point `x`, with the compact-open
topology. If `B` is a Hausdorff quotient of the cube `I^N` in which exactly the boundary
`Cube.boundary N` is collapsed to the basepoint — for instance a sphere `S^n = I^n / ∂I^n` —
then `Map_*(B, X)` is homeomorphic to the space `Ω^ N X x` of generalized loops, by precomposition
with the quotient map.

## Main declarations

* `TauCeti.BasedMap`: the based mapping space `Map_*(B, X)`.
* `TauCeti.BasedMap.map`: the map `Map_*(B, X) → Map_*(B, Y)` induced by a based map `X → Y`,
  continuous by `TauCeti.BasedMap.continuous_map`.
* `TauCeti.BasedMap.homeomorphGenLoop`: `Map_*(B, X) ≃ₜ Ω^ N X x` for a Hausdorff quotient `B` of
  the cube collapsing exactly the boundary to the basepoint, with
  `TauCeti.BasedMap.homeomorphGenLoop_apply` its action: precomposition with the quotient map.
  It is natural in `X` by `TauCeti.BasedMap.homeomorphGenLoop_map`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.
-/

public section

open Function Set Topology Topology.Homotopy
open scoped unitInterval

namespace TauCeti

/-- The based mapping space `Map_*(B, X)`: continuous maps `B → X` sending the basepoint `b₀` to
the point `x`, with the compact-open topology. -/
abbrev BasedMap (B X : Type*) [TopologicalSpace B] [TopologicalSpace X] (b₀ : B) (x : X) :=
  {f : C(B, X) // f b₀ = x}

namespace BasedMap

section Map

variable {B X Y : Type*} [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]
  {b₀ : B} {x : X} {y : Y}

/-- A based map `g : X → Y` induces a map of based mapping spaces by postcomposition. -/
def map (g : C(X, Y)) (hg : g x = y) (f : BasedMap B X b₀ x) : BasedMap B Y b₀ y :=
  ⟨g.comp f.1, by rw [ContinuousMap.comp_apply, f.2, hg]⟩

@[simp]
theorem map_apply (g : C(X, Y)) (hg : g x = y) (f : BasedMap B X b₀ x) (b : B) :
    (map g hg f).1 b = g (f.1 b) := by
  rw [map]
  rfl

@[simp]
theorem map_id (f : BasedMap B X b₀ x) : map (ContinuousMap.id X) rfl f = f :=
  Subtype.ext rfl

theorem map_comp {Z : Type*} [TopologicalSpace Z] {z : Z} (g : C(Y, Z)) (hg : g y = z)
    (h : C(X, Y)) (hh : h x = y) (f : BasedMap B X b₀ x) :
    map g hg (map h hh f) = map (g.comp h) (by rw [ContinuousMap.comp_apply, hh, hg]) f :=
  Subtype.ext rfl

theorem continuous_map (g : C(X, Y)) (hg : g x = y) :
    Continuous (map (B := B) (b₀ := b₀) g hg) :=
  continuous_induced_rng.2 ((ContinuousMap.continuous_postcomp g).comp continuous_subtype_val)

end Map

variable {N B X : Type*} [TopologicalSpace B] [TopologicalSpace X] {x : X}
  (q : C(N → I, B)) (b₀ : B) (hb : ∀ z, q z = b₀ ↔ z ∈ Cube.boundary N)

/-- Precomposition with a map `q : I^N → B` collapsing exactly the cube boundary to `b₀` sends
based maps out of `B` to generalized loops. -/
def precompGenLoop (f : BasedMap B X b₀ x) : Ω^ N X x :=
  ⟨f.1.comp q, fun z hz => by simpa [(hb z).2 hz] using f.2⟩

@[simp]
theorem precompGenLoop_apply (f : BasedMap B X b₀ x) (z : N → I) :
    precompGenLoop q b₀ hb f z = f.1 (q z) := by
  rw [precompGenLoop]
  rfl

variable [T2Space B] (hq : Surjective q)
  (hinj : ∀ z z', q z = q z' → z = z' ∨ (z ∈ Cube.boundary N ∧ z' ∈ Cube.boundary N))

include hq in
theorem isEmbedding_precompGenLoop : IsEmbedding (precompGenLoop (X := X) (x := x) q b₀ hb) := by
  have hcont : Continuous (precompGenLoop (X := X) (x := x) q b₀ hb) :=
    continuous_induced_rng.2
      ((ContinuousMap.continuous_precomp q).comp continuous_subtype_val)
  refine ⟨?_, fun f g h => Subtype.ext ((ContinuousMap.cancel_right hq).1
    (congrArg Subtype.val h))⟩
  exact IsInducing.of_comp hcont continuous_subtype_val
    ((ContinuousMap.isInducing_precomp_of_surjective q hq).comp IsInducing.subtypeVal)

include hq hb hinj in
theorem precompGenLoop_surjective : Surjective (precompGenLoop (X := X) (x := x) q b₀ hb) := by
  have hqm : IsQuotientMap q :=
    (q.continuous.isClosedMap).isQuotientMap q.continuous hq
  intro p
  have hfac : FactorsThrough p.1 q := fun z z' h => by
    rcases hinj z z' h with rfl | ⟨h1, h2⟩
    · rfl
    · exact (p.2 z h1).trans (p.2 z' h2).symm
  refine ⟨⟨hqm.lift p.1 hfac, ?_⟩, Subtype.ext (hqm.lift_comp p.1 hfac)⟩
  obtain ⟨z, hz⟩ := hq b₀
  have := p.2 z ((hb z).1 hz)
  rw [← hz]
  exact (congrFun (congrArg DFunLike.coe (hqm.lift_comp p.1 hfac)) z).trans this

include hq hb hinj in
/-- **Based maps out of a quotient of the cube are generalized loops.** If a continuous surjection
`q : I^N → B` onto a Hausdorff space collapses exactly the cube boundary to the point `b₀` and is
injective elsewhere, then precomposition with `q` is a homeomorphism from the based mapping space
`Map_*(B, X)` onto the space `Ω^ N X x` of generalized loops. -/
noncomputable def homeomorphGenLoop : BasedMap B X b₀ x ≃ₜ Ω^ N X x :=
  (isEmbedding_precompGenLoop q b₀ hb hq).toHomeomorphOfSurjective
    (precompGenLoop_surjective q b₀ hb hq hinj)

@[simp]
theorem homeomorphGenLoop_apply (f : BasedMap B X b₀ x) (z : N → I) :
    homeomorphGenLoop q b₀ hb hq hinj f z = f.1 (q z) := by
  rw [homeomorphGenLoop, IsEmbedding.toHomeomorphOfSurjective_apply]
  exact precompGenLoop_apply q b₀ hb f z

include hq hb hinj in
/-- The homeomorphism `homeomorphGenLoop` is natural in `X`: it commutes with postcomposition by
a based map `g : X → Y`. -/
theorem homeomorphGenLoop_map {Y : Type*} [TopologicalSpace Y] {y : Y} (g : C(X, Y)) (hg : g x = y)
    (f : BasedMap B X b₀ x) :
    homeomorphGenLoop q b₀ hb hq hinj (map g hg f) =
      GenLoop.map g hg (homeomorphGenLoop q b₀ hb hq hinj f) :=
  GenLoop.ext _ _ fun z => by
    rw [homeomorphGenLoop_apply, GenLoop.map_apply, homeomorphGenLoop_apply, map_apply]

end BasedMap

end TauCeti
