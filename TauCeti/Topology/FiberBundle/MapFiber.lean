/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import TauCeti.Topology.FiberBundle.Principal.Basic

/-!
# The fibre bundle of a locally trivial map

Let `proj : P → B` be a map of topological spaces, and suppose every point of `B` lies in the base
set of a trivialization of `proj`, a homeomorphism `proj⁻¹ U ≃ U × F` over an open set `U`. Then
the fibres `TauCeti.MapFiber proj b = {p // proj p = b}`, with their subspace topologies, form a
fibre bundle over `B` with model fibre `F` in Mathlib's sense. Its total space is identified with
`P` by `⟨b, p⟩ ↦ p` (`TauCeti.MapFiber.totalSpaceHomeomorph`), and it carries the topology of `P`
transported along this bijection; no other topology is put on it. Every trivialization `e` of
`proj` gives a trivialization `e.toMapFiber` of this bundle with the same base set and the same
coordinate changes.

This is the passage from a bundle given by its total space, as in classical differential geometry,
to Mathlib's `FiberBundle` on a family of fibres. The trivializations are packaged as a
`TauCeti.MapFiber.Atlas F proj` (optionally with an explicit covering set `charts` containing each
`trivAt b`, or built from a covering set via `TauCeti.MapFiber.Atlas.ofSet`), and the fibre bundle
is the definition `TauCeti.MapFiber.Atlas.fiberBundle` rather than an instance, because it depends
on the atlas.

When `G` is a group with a right action on `P` (an action of `Gᵐᵒᵖ`) preserving each fibre of
`proj`, the action restricts to the fibres (`TauCeti.MapFiber.mulAction`). If every trivialization
of the atlas intertwines it with right multiplication on `G`, the bundle of fibres is a principal
`G`-bundle (`TauCeti.MapFiber.Atlas.principalBundle`).

## Main definitions

* `TauCeti.MapFiber proj b`: the fibre of `proj` over `b`.
* `TauCeti.MapFiber.totalSpaceHomeomorph`: the total space of the fibres is homeomorphic to `P`.
* `Bundle.Trivialization.toMapFiber`: a trivialization of `proj` as a trivialization of the bundle
  of its fibres.
* `TauCeti.MapFiber.Atlas`: a choice of a trivialization of `proj` around every point of `B`,
  together with a set `charts` of trivializations containing each chosen chart.
* `TauCeti.MapFiber.Atlas.ofSet`: builds an atlas from any covering set of trivializations.
* `TauCeti.MapFiber.Atlas.fiberBundle`: the fibre bundle structure on the fibres of `proj`.
* `TauCeti.MapFiber.mulAction`: a fibre-preserving action restricted to the fibres.

## Main results

* `TauCeti.MapFiber.Atlas.principalBundle`: equivariant trivializations make the bundle of fibres
  a principal bundle.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Chapter I, §5 (principal bundles given by their total space and local trivializations).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §2.
-/

public section

open Bundle Set Topology MulOpposite

namespace TauCeti

variable {B P F : Type*}

/-- The fibre `{p // proj p = b}` of a map `proj : P → B` over `b`. With their subspace topologies
the fibres of a locally trivial map form a fibre bundle over `B`, whose total space is `P`. -/
abbrev MapFiber (proj : P → B) (b : B) : Type _ := {p : P // proj p = b}

namespace MapFiber

variable {proj : P → B}

section MulAction

variable {M : Type*} [Monoid M] [MulAction M P]

/-- An action on `P` that preserves each fibre of `proj` restricts to an action on each fibre. -/
@[instance_reducible]
def mulAction (hproj : ∀ (m : M) (p : P), proj (m • p) = proj p) (b : B) :
    MulAction M (MapFiber proj b) where
  smul m p := ⟨m • p.val, (hproj m p.val).trans p.property⟩
  one_smul p := Subtype.ext (one_smul M p.val)
  mul_smul m m' p := Subtype.ext (mul_smul m m' p.val)

/-- The restricted action is the action on `P`, read on points of a fibre. -/
@[simp]
theorem coe_smul (hproj : ∀ (m : M) (p : P), proj (m • p) = proj p) {b : B} (m : M)
    (p : MapFiber proj b) :
    letI := mulAction hproj
    (m • p).val = m • p.val :=
  (rfl)

end MulAction

variable [TopologicalSpace P]

/-- The total space of the fibres of `proj` carries the topology of `P`, induced by
`⟨b, p⟩ ↦ p`. -/
instance : TopologicalSpace (TotalSpace F (MapFiber proj)) :=
  TopologicalSpace.induced (fun x ↦ x.snd.val) ‹TopologicalSpace P›

variable (F proj) in
/-- The total space of the fibres of `proj` is homeomorphic to `P` by `⟨b, p⟩ ↦ p`. -/
def totalSpaceHomeomorph : TotalSpace F (MapFiber proj) ≃ₜ P :=
  Equiv.toHomeomorphOfIsInducing
    { toFun x := x.snd.val
      invFun p := ⟨proj p, ⟨p, rfl⟩⟩
      left_inv := by
        rintro ⟨b, p, rfl⟩
        rfl
      right_inv _ := rfl } ⟨rfl⟩

@[simp]
theorem totalSpaceHomeomorph_apply (x : TotalSpace F (MapFiber proj)) :
    totalSpaceHomeomorph F proj x = x.snd.val :=
  (rfl)

@[simp]
theorem totalSpaceHomeomorph_symm_apply (p : P) :
    (totalSpaceHomeomorph F proj).symm p = ⟨proj p, ⟨p, rfl⟩⟩ :=
  (rfl)

/-- The point of `P` underlying a point of the total space of the fibres lies over its base
point. -/
theorem proj_totalSpaceHomeomorph (x : TotalSpace F (MapFiber proj)) :
    proj (totalSpaceHomeomorph F proj x) = x.proj :=
  x.snd.property

/-- The base point of the point of the total space corresponding to `p` is `proj p`. -/
theorem proj_totalSpaceHomeomorph_symm (p : P) :
    ((totalSpaceHomeomorph F proj).symm p).proj = proj p :=
  (rfl)

variable (F) in
/-- Each fibre is embedded in the total space of the fibres, since both carry topologies induced
from `P`. -/
theorem isInducing_totalSpaceMk (b : B) :
    IsInducing (TotalSpace.mk b : MapFiber proj b → TotalSpace F (MapFiber proj)) :=
  (totalSpaceHomeomorph F proj).isInducing.of_comp_iff.1 <| by
    have h : ⇑(totalSpaceHomeomorph F proj) ∘
        (TotalSpace.mk b : MapFiber proj b → TotalSpace F (MapFiber proj)) = Subtype.val :=
      funext fun _ ↦ totalSpaceHomeomorph_apply _
    rw [h]
    exact IsEmbedding.subtypeVal.isInducing

end MapFiber

end TauCeti

/-! ### Trivializations of a map as trivializations of its fibres -/

namespace Bundle.Trivialization

open TauCeti

variable {B P F : Type*} [TopologicalSpace B] [TopologicalSpace P] [TopologicalSpace F]
  {proj : P → B} (e : Trivialization F proj)

/-- A trivialization of a map `proj` as a trivialization, with the same base set, of the bundle of
fibres of `proj`: the point `p` of the fibre over `b` is sent to `e p`. -/
def toMapFiber : Trivialization F (π F (MapFiber proj)) where
  toOpenPartialHomeomorph :=
    (MapFiber.totalSpaceHomeomorph F proj).transOpenPartialHomeomorph e.toOpenPartialHomeomorph
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := by
    ext x
    simp [e.mem_source, x.snd.property]
  target_eq := e.target_eq
  proj_toFun x hx := by
    have hx : proj (MapFiber.totalSpaceHomeomorph F proj x) ∈ e.baseSet := by
      simpa [e.mem_source] using hx
    exact (e.coe_fst' hx).trans x.snd.property

@[simp]
theorem toMapFiber_apply (x : TotalSpace F (MapFiber proj)) :
    e.toMapFiber x = e (MapFiber.totalSpaceHomeomorph F proj x) :=
  (rfl)

@[simp]
theorem toMapFiber_symm_apply (y : B × F) :
    e.toMapFiber.toOpenPartialHomeomorph.symm y =
      (MapFiber.totalSpaceHomeomorph F proj).symm (e.toOpenPartialHomeomorph.symm y) :=
  (rfl)

@[simp]
theorem toMapFiber_baseSet : e.toMapFiber.baseSet = e.baseSet :=
  (rfl)

@[simp]
theorem toMapFiber_source :
    e.toMapFiber.source = (MapFiber.totalSpaceHomeomorph F proj) ⁻¹' e.source :=
  (rfl)

/-- The coordinate changes between trivializations of the fibres of `proj` are those between the
trivializations of `proj` they come from. -/
@[simp]
theorem toMapFiber_coordChange (e' : Trivialization F proj) :
    e.toMapFiber.coordChange e'.toMapFiber = e.coordChange e' :=
  (rfl)

end Bundle.Trivialization

/-! ### The fibre bundle of a locally trivial map -/

namespace TauCeti

variable {B P F : Type*} [TopologicalSpace B] [TopologicalSpace P] [TopologicalSpace F]

namespace MapFiber

variable (F) in
/-- An atlas of a map `proj : P → B` with model fibre `F`: a trivialization `trivAt b` of `proj`
whose base set contains `b`, for every point `b` of `B`, together with the set `charts` of
trivializations belonging to the atlas. -/
structure Atlas (proj : P → B) where
  /-- The trivialization chosen at a point of the base. -/
  trivAt : B → Trivialization F proj
  /-- The trivialization chosen at `b` trivializes `proj` over a neighbourhood of `b`. -/
  mem_baseSet_trivAt : ∀ b, b ∈ (trivAt b).baseSet
  /-- The set of trivializations belonging to the atlas. -/
  charts : Set (Trivialization F proj)
  /-- Every chosen trivialization `trivAt b` belongs to `charts`. -/
  trivAt_mem_charts : ∀ b, trivAt b ∈ charts

namespace Atlas

variable {proj : P → B} (A : Atlas F proj)

/-- Construct a `MapFiber.Atlas` from a choice of trivialization `trivAt b` at every base point
`b`. -/
def ofTrivAt (trivAt : B → Trivialization F proj)
    (mem_baseSet_trivAt : ∀ b, b ∈ (trivAt b).baseSet) :
    Atlas F proj where
  trivAt := trivAt
  mem_baseSet_trivAt := mem_baseSet_trivAt
  charts := range trivAt
  trivAt_mem_charts := mem_range_self

/-- Construct a `MapFiber.Atlas` from a covering set `charts` of trivializations of `proj`. -/
noncomputable def ofSet (charts : Set (Trivialization F proj))
    (hcharts : ∀ b : B, ∃ t ∈ charts, b ∈ t.baseSet) : Atlas F proj where
  trivAt b := (hcharts b).choose
  mem_baseSet_trivAt b := (hcharts b).choose_spec.2
  charts := charts
  trivAt_mem_charts b := (hcharts b).choose_spec.1

/-- The chart set of `Atlas.ofSet charts hcharts` is `charts`. -/
@[simp]
theorem charts_ofSet (charts : Set (Trivialization F proj))
    (hcharts : ∀ b : B, ∃ t ∈ charts, b ∈ t.baseSet) :
    (ofSet charts hcharts).charts = charts :=
  (rfl)

/-- **The fibre bundle of a locally trivial map.** The fibres of `proj`, with their subspace
topologies, form a fibre bundle over `B` with model fibre `F` and total space `P`, whose atlas
consists of the trivializations of `A`. -/
@[instance_reducible]
def fiberBundle : FiberBundle F (MapFiber proj) where
  totalSpaceMk_isInducing' := isInducing_totalSpaceMk F
  trivializationAtlas' := Bundle.Trivialization.toMapFiber '' A.charts
  trivializationAt' b := (A.trivAt b).toMapFiber
  mem_baseSet_trivializationAt' := A.mem_baseSet_trivAt
  trivialization_mem_atlas' b := ⟨A.trivAt b, A.trivAt_mem_charts b, rfl⟩

theorem trivializationAt_eq (b : B) :
    letI := A.fiberBundle
    trivializationAt F (MapFiber proj) b = (A.trivAt b).toMapFiber :=
  (rfl)

/-- The trivialization atlas of `A.fiberBundle` is
`Bundle.Trivialization.toMapFiber '' A.charts`. -/
@[simp]
theorem trivializationAtlas_fiberBundle :
    letI := A.fiberBundle
    trivializationAtlas F (MapFiber proj) = Bundle.Trivialization.toMapFiber '' A.charts :=
  (rfl)

/-- The trivializations of the atlas of the bundle of fibres are those of `A`. -/
theorem mem_trivializationAtlas_iff (e : Trivialization F (π F (MapFiber proj))) :
    letI := A.fiberBundle
    e ∈ trivializationAtlas F (MapFiber proj) ↔ ∃ t ∈ A.charts, t.toMapFiber = e :=
  Iff.rfl

end Atlas

/-! ### Principal bundles given by their total space -/


variable {G : Type*} [Group G] [TopologicalSpace G] [MulAction Gᵐᵒᵖ P] {proj : P → B}

/-- **Principal bundles given by their total space.** Let `G` act on the right on `P`, preserving
the fibres of `proj`, and let every trivialization of the atlas `A` intertwine the action with right
multiplication on `G`. Then the fibres of `proj` form a principal `G`-bundle. -/
theorem Atlas.principalBundle (A : Atlas G proj)
    (hproj : ∀ (g : Gᵐᵒᵖ) (p : P), proj (g • p) = proj p)
    (hA : ∀ t ∈ A.charts, ∀ (p : P), proj p ∈ t.baseSet → ∀ g : G,
      (t (op g • p)).2 = (t p).2 * g) :
    letI := A.fiberBundle
    letI := mulAction hproj
    PrincipalBundle G (MapFiber proj) := by
  let := A.fiberBundle
  let := mulAction hproj
  refine ⟨fun e he ↦ ?_⟩
  obtain ⟨t, ht, rfl⟩ := he.out
  refine ⟨fun b' hb' p g ↦ ?_⟩
  rw [Bundle.Trivialization.toMapFiber_baseSet, ← p.property] at hb'
  simpa only [Bundle.Trivialization.toMapFiber_apply, totalSpaceHomeomorph_apply, coe_smul] using
    hA t ht p.val hb' g

end MapFiber

end TauCeti
