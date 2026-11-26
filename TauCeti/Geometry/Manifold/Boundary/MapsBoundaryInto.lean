/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Maps sending the manifold boundary into a subset

Let `X` be a charted space with model `IX`, possibly with boundary, and `ι : L → M` a map. The
predicate `TauCeti.MapsBoundaryInto IX u ι` says that `u : X → M` sends the manifold boundary of
`X` into the image of `ι`: the boundary condition `u(∂X) ⊆ ι(L)` of boundary value problems for
maps from manifolds with boundary, such as pseudoholomorphic curves with totally real boundary
conditions. The map `ι` is a plain map: hypotheses such as total reality belong to the theorems
that use them.

## Main results

* `TauCeti.MapsBoundaryInto`, with its eliminators `TauCeti.MapsBoundaryInto.mapsTo` and
  `TauCeti.MapsBoundaryInto.mem_range`, and its behaviour under constant maps, `congr`, `mono` and
  composition; `TauCeti.mapsBoundaryInto_comp_iff` for composition with an injective map, and
  `TauCeti.mapsBoundaryInto_comp_diffeomorph_iff` for precomposition with a diffeomorphism.
* `TauCeti.mapsBoundaryInto_of_boundaryless`: on a manifold without boundary every map satisfies
  every boundary condition.
* `TauCeti.MapsBoundaryInto.of_tendsto`: closedness under pointwise limits when `range ι` is
  closed.
* `TauCeti.MapsBoundaryInto.of_subset_closure`: for `range ι` closed and `u` continuous on the
  boundary, it suffices to check a subset of the boundary whose closure contains the boundary.
-/

public section

open Set Filter
open scoped Topology Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {HX EX : Type*} [TopologicalSpace HX]
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
  {M N : Type*} {L L' : Type*}

variable (IX : ModelWithCorners 𝕜 EX HX) in
/-- **Maps the boundary into `L`.** A map `u : X → M` maps the boundary into `L` along
`ι : L → M` when it sends every point of the manifold boundary of `X`, for the model `IX`, into
the image of `ι`: the boundary condition `u(∂X) ⊆ ι(L)`. This is a pointwise condition on the
boundary, meaningful for Sobolev maps once they are continuous. When `range ι` is closed and `u`
is continuous on the boundary, it suffices to check it on a subset whose closure contains the
boundary (`TauCeti.MapsBoundaryInto.of_subset_closure`). -/
def MapsBoundaryInto (u : X → M) (ι : L → M) : Prop :=
  MapsTo u (IX.boundary X) (range ι)

variable {IX : ModelWithCorners 𝕜 EX HX} {u v : X → M} {ι : L → M} {ι' : L' → M}

/-- The boundary condition is `MapsTo` on the manifold boundary. -/
theorem mapsBoundaryInto_iff_mapsTo :
    MapsBoundaryInto IX u ι ↔ MapsTo u (IX.boundary X) (range ι) :=
  Iff.rfl

/-- Unfolding the boundary condition pointwise. -/
theorem mapsBoundaryInto_iff :
    MapsBoundaryInto IX u ι ↔ ∀ x, IX.IsBoundaryPoint x → ∃ y, ι y = u x :=
  Iff.rfl

/-- On a manifold without boundary, every map satisfies every boundary condition. -/
@[simp]
theorem mapsBoundaryInto_of_boundaryless [BoundarylessManifold IX X] :
    MapsBoundaryInto IX u ι := fun x hx ↦ by
  rw [ModelWithCorners.Boundaryless.boundary_eq_empty] at hx
  exact hx.elim

/-- A constant map with value in the image of `ι` satisfies the boundary condition. -/
theorem mapsBoundaryInto_const {c : M} (hc : c ∈ range ι) :
    MapsBoundaryInto IX (fun _ : X ↦ c) ι := fun _ _ ↦ hc

namespace MapsBoundaryInto

/-- A boundary condition is `MapsTo` on the manifold boundary. -/
theorem mapsTo (h : MapsBoundaryInto IX u ι) : MapsTo u (IX.boundary X) (range ι) :=
  h

/-- A map satisfying a boundary condition sends each boundary point into the image of `ι`. -/
theorem mem_range (h : MapsBoundaryInto IX u ι) {x : X} (hx : IX.IsBoundaryPoint x) :
    u x ∈ range ι :=
  h hx

/-- The boundary condition only depends on the values of `u` on the boundary. -/
theorem congr (h : MapsBoundaryInto IX u ι) (huv : EqOn u v (IX.boundary X)) :
    MapsBoundaryInto IX v ι := fun _ hx ↦ huv hx ▸ h hx

/-- A boundary condition into `L` implies one into any `L'` whose image contains that of `L`. -/
theorem mono (h : MapsBoundaryInto IX u ι) (hι : range ι ⊆ range ι') :
    MapsBoundaryInto IX u ι' :=
  h.mono_right hι

/-- Composing with a map `g : M → N` carries a boundary condition along `ι` to one along
`g ∘ ι`. -/
theorem comp (h : MapsBoundaryInto IX u ι) (g : M → N) : MapsBoundaryInto IX (g ∘ u) (g ∘ ι) :=
  fun _ hx ↦ by
    obtain ⟨y, hy⟩ := h hx
    exact ⟨y, by simp [hy]⟩

/-- **Closedness under pointwise limits.** If `range ι` is closed, a pointwise limit of maps that
eventually map the boundary into `L` maps the boundary into `L`. -/
theorem of_tendsto [TopologicalSpace M] {α : Type*} {l : Filter α} [l.NeBot] {F : α → X → M}
    (hι : IsClosed (range ι)) (h : ∀ᶠ n in l, MapsBoundaryInto IX (F n) ι)
    (hlim : ∀ x, IX.IsBoundaryPoint x → Tendsto (fun n ↦ F n x) l (𝓝 (u x))) :
    MapsBoundaryInto IX u ι := fun x hx ↦
  hι.mem_of_tendsto (hlim x hx) (h.mono fun _ hn ↦ hn hx)

/-- **The closure criterion.** If `range ι` is closed and `u` is continuous on the boundary, it
suffices that `u` maps a subset `D` of the boundary, whose closure contains the boundary, into
`ι(L)`. -/
theorem of_subset_closure [TopologicalSpace M] {D : Set X} (hι : IsClosed (range ι))
    (hu : ContinuousOn u (IX.boundary X)) (hD : D ⊆ IX.boundary X)
    (hdense : IX.boundary X ⊆ closure D) (h : MapsTo u D (range ι)) :
    MapsBoundaryInto IX u ι := fun x hx ↦
  hι.closure_subset_iff.2 h.image_subset
    (((hu x hx).mono hD).mem_closure_image (hdense hx))

end MapsBoundaryInto

/-- **Transport along an injective map.** For an injective `g : M → N`, the map `g ∘ u` maps the
boundary into `L` along `g ∘ ι` exactly when `u` maps it into `L` along `ι`. -/
theorem mapsBoundaryInto_comp_iff {g : M → N} (hg : Function.Injective g) :
    MapsBoundaryInto IX (g ∘ u) (g ∘ ι) ↔ MapsBoundaryInto IX u ι := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ h.comp g⟩
  obtain ⟨y, hy⟩ := h hx
  exact ⟨y, hg hy⟩

/-- **Invariance under diffeomorphisms of the domain.** A diffeomorphism `Φ : X' → X` maps the
boundary of `X'` onto the boundary of `X`, so `u ∘ Φ` maps the boundary into `L` along `ι` exactly
when `u` does. -/
theorem mapsBoundaryInto_comp_diffeomorph_iff {HX' EX' : Type*} [TopologicalSpace HX']
    [NormedAddCommGroup EX'] [NormedSpace 𝕜 EX'] {IX' : ModelWithCorners 𝕜 EX' HX'}
    {X' : Type*} [TopologicalSpace X'] [ChartedSpace HX' X'] {n : WithTop ℕ∞} (hn : n ≠ 0)
    (Φ : X' ≃ₘ^n⟮IX', IX⟯ X) : MapsBoundaryInto IX' (u ∘ Φ) ι ↔ MapsBoundaryInto IX u ι := by
  rw [mapsBoundaryInto_iff_mapsTo, mapsBoundaryInto_iff_mapsTo, ← Φ.preimage_boundary hn]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ h hx⟩
  simpa using h (x := Φ.symm x) (by simpa using hx)

end TauCeti
