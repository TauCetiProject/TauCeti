/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import TauCeti.Topology.FiberBundle.Principal.Basic
public import TauCeti.Topology.FiberBundle.Trivialization

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

More generally, any family of fibres `Q` over `B` whose total space is identified with `P` over `B`
by a homeomorphism `h` is a fibre bundle (`TauCeti.MapFiber.Atlas.fiberBundleOfHomeomorph`), with
the trivializations `e.compTotalSpaceHomeomorph h` transported along `h`; the fibres of `proj` are
the case `h = TauCeti.MapFiber.totalSpaceHomeomorph`. This lets a bundle given by its total space
be presented by fibres of a prescribed type, for instance in a smaller universe.

When `G` is a group with a right action on `P` (an action of `Gᵐᵒᵖ`) preserving each fibre of
`proj`, the action restricts to the fibres (`TauCeti.MapFiber.mulAction`). If every trivialization
of the atlas intertwines it with right multiplication on `G`, the bundle of fibres is a principal
`G`-bundle (`TauCeti.MapFiber.Atlas.principalBundle`), and likewise for a family of fibres
identified with `P` by an equivariant homeomorphism
(`TauCeti.MapFiber.Atlas.principalBundle_of_homeomorph`).

## Main definitions

* `TauCeti.MapFiber proj b`: the fibre of `proj` over `b`.
* `TauCeti.MapFiber.totalSpaceHomeomorph`: the total space of the fibres is homeomorphic to `P`.
* `Bundle.Trivialization.compTotalSpaceHomeomorph`: a trivialization of `proj` as a trivialization
  of a family of fibres whose total space is homeomorphic to `P` over `B`.
* `Bundle.Trivialization.toMapFiber`: a trivialization of `proj` as a trivialization of the bundle
  of its fibres.
* `TauCeti.MapFiber.Atlas`: a choice of a trivialization of `proj` around every point of `B`,
  together with a set `charts` of trivializations containing each chosen chart.
* `TauCeti.MapFiber.Atlas.ofTrivAt`, `TauCeti.MapFiber.Atlas.ofSet`: build an atlas from chosen
  trivializations or from any covering set of trivializations.
* `TauCeti.MapFiber.Atlas.fiberBundleOfHomeomorph`: the fibre bundle structure on a family of
  fibres whose total space is homeomorphic to `P` over `B`.
* `TauCeti.MapFiber.Atlas.fiberBundle`: the fibre bundle structure on the fibres of `proj`.
* `TauCeti.MapFiber.mulAction`: a fibre-preserving action restricted to the fibres.

## Main results

* `Bundle.Trivialization.isEquivariant_toMapFiber_iff`: equivariance characterization for
  `t.toMapFiber`.
* `TauCeti.MapFiber.Atlas.principalBundle_of_homeomorph`, `TauCeti.MapFiber.Atlas.principalBundle`:
  equivariant trivializations make the bundle of fibres a principal bundle.

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

section TotalSpaceHomeomorph

variable {Q : B → Type*} [TopologicalSpace (TotalSpace F Q)] (h : TotalSpace F Q ≃ₜ P)
  (hh : ∀ x, proj (h x) = x.proj)

/-- A trivialization of a map `proj : P → B` as a trivialization, with the same base set, of a
family of fibres `Q` whose total space is identified with `P` over `B` by the homeomorphism `h`:
the point `x` of the total space is sent to `e (h x)`. -/
def compTotalSpaceHomeomorph : Trivialization F (π F Q) :=
  e.compHomeomorphOfEq h hh

@[simp]
theorem compTotalSpaceHomeomorph_apply (x : TotalSpace F Q) :
    e.compTotalSpaceHomeomorph h hh x = e (h x) :=
  e.compHomeomorphOfEq_apply h hh x

@[simp]
theorem compTotalSpaceHomeomorph_symm_apply (y : B × F) :
    (e.compTotalSpaceHomeomorph h hh).toOpenPartialHomeomorph.symm y =
      h.symm (e.toOpenPartialHomeomorph.symm y) :=
  e.compHomeomorphOfEq_toOpenPartialHomeomorph_symm_apply h hh y

@[simp]
theorem compTotalSpaceHomeomorph_baseSet :
    (e.compTotalSpaceHomeomorph h hh).baseSet = e.baseSet :=
  e.compHomeomorphOfEq_baseSet h hh

@[simp]
theorem compTotalSpaceHomeomorph_source :
    (e.compTotalSpaceHomeomorph h hh).source = h ⁻¹' e.source :=
  e.compHomeomorphOfEq_source h hh

/-- The coordinate changes between the trivializations of `Q` coming from trivializations of
`proj` are those between the trivializations of `proj`. -/
@[simp]
theorem compTotalSpaceHomeomorph_coordChange (e' : Trivialization F proj) :
    (e.compTotalSpaceHomeomorph h hh).coordChange (e'.compTotalSpaceHomeomorph h hh) =
      e.coordChange e' :=
  e.compHomeomorphOfEq_coordChange e' h hh

end TotalSpaceHomeomorph

/-- A trivialization of a map `proj` as a trivialization, with the same base set, of the bundle of
fibres of `proj`: the point `p` of the fibre over `b` is sent to `e p`. -/
def toMapFiber : Trivialization F (π F (MapFiber proj)) :=
  e.compTotalSpaceHomeomorph (MapFiber.totalSpaceHomeomorph F proj)
    MapFiber.proj_totalSpaceHomeomorph

@[simp]
theorem toMapFiber_apply (x : TotalSpace F (MapFiber proj)) :
    e.toMapFiber x = e (MapFiber.totalSpaceHomeomorph F proj x) :=
  e.compHomeomorphOfEq_apply _ _ x

@[simp]
theorem toMapFiber_symm_apply (y : B × F) :
    e.toMapFiber.toOpenPartialHomeomorph.symm y =
      (MapFiber.totalSpaceHomeomorph F proj).symm (e.toOpenPartialHomeomorph.symm y) :=
  e.compHomeomorphOfEq_toOpenPartialHomeomorph_symm_apply _ _ y

@[simp]
theorem toMapFiber_baseSet : e.toMapFiber.baseSet = e.baseSet :=
  e.compHomeomorphOfEq_baseSet _ _

@[simp]
theorem toMapFiber_source :
    e.toMapFiber.source = (MapFiber.totalSpaceHomeomorph F proj) ⁻¹' e.source :=
  e.compHomeomorphOfEq_source _ _

/-- The coordinate changes between trivializations of the fibres of `proj` are those between the
trivializations of `proj` they come from. -/
@[simp]
theorem toMapFiber_coordChange (e' : Trivialization F proj) :
    e.toMapFiber.coordChange e'.toMapFiber = e.coordChange e' :=
  e.compHomeomorphOfEq_coordChange e' (MapFiber.totalSpaceHomeomorph F proj)
    MapFiber.proj_totalSpaceHomeomorph

/-- `t.toMapFiber` is `G`-equivariant iff `t` intertwines the right `G`-action on
`proj ⁻¹' t.baseSet` with right multiplication on the second factor `G`. -/
theorem isEquivariant_toMapFiber_iff {G : Type*} [Group G] [TopologicalSpace G]
    [MulAction Gᵐᵒᵖ P] (t : Trivialization G proj)
    (hinv : ∀ (g : Gᵐᵒᵖ) (x : P), proj (g • x) = proj x) :
    (letI := TauCeti.MapFiber.mulAction hinv; t.toMapFiber.IsEquivariant) ↔
      ∀ x : P, proj x ∈ t.baseSet → ∀ g : G, (t (op g • x)).2 = (t x).2 * g :=
  letI := TauCeti.MapFiber.mulAction hinv
  isEquivariant_iff_of_equiv t.toMapFiber t (TauCeti.MapFiber.totalSpaceHomeomorph G proj).toEquiv
    t.toMapFiber_baseSet
    (fun p ↦ TauCeti.MapFiber.proj_totalSpaceHomeomorph p)
    (fun p ↦ t.toMapFiber_apply p)
    fun g p ↦ by
      simp only [Homeomorph.coe_toEquiv, TauCeti.MapFiber.totalSpaceHomeomorph_apply]
      exact TauCeti.MapFiber.coe_smul hinv (op g) p.snd

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

/-- The chosen trivialization of `Atlas.ofTrivAt trivAt h` is `trivAt`. -/
@[simp]
theorem trivAt_ofTrivAt (trivAt : B → Trivialization F proj)
    (mem_baseSet_trivAt : ∀ b, b ∈ (trivAt b).baseSet) :
    (ofTrivAt trivAt mem_baseSet_trivAt).trivAt = trivAt :=
  (rfl)

/-- The chart set of `Atlas.ofTrivAt trivAt h` is `range trivAt`. -/
@[simp]
theorem charts_ofTrivAt (trivAt : B → Trivialization F proj)
    (mem_baseSet_trivAt : ∀ b, b ∈ (trivAt b).baseSet) :
    (ofTrivAt trivAt mem_baseSet_trivAt).charts = range trivAt :=
  (rfl)

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

/-- **A family of fibres of a locally trivial map is a fibre bundle.** Let `Q` be a family of
fibres over `B` whose total space is identified with `P` over `B` by the homeomorphism `h`, and in
whose total space each fibre is embedded. Then `Q` is a fibre bundle over `B` with model fibre `F`,
whose atlas consists of the trivializations of `A` transported along `h`. -/
@[instance_reducible]
def fiberBundleOfHomeomorph {Q : B → Type*} [TopologicalSpace (TotalSpace F Q)]
    [∀ b, TopologicalSpace (Q b)] (h : TotalSpace F Q ≃ₜ P) (hh : ∀ x, proj (h x) = x.proj)
    (hQ : ∀ b, IsInducing (TotalSpace.mk b : Q b → TotalSpace F Q)) : FiberBundle F Q where
  totalSpaceMk_isInducing' := hQ
  trivializationAtlas' := (fun t ↦ t.compTotalSpaceHomeomorph h hh) '' A.charts
  trivializationAt' b := (A.trivAt b).compTotalSpaceHomeomorph h hh
  mem_baseSet_trivializationAt' b := by simp [A.mem_baseSet_trivAt]
  trivialization_mem_atlas' b := ⟨A.trivAt b, A.trivAt_mem_charts b, rfl⟩

/-- The trivialization at `b` of the bundle `A.fiberBundleOfHomeomorph h hh hQ` is that of `A`,
transported along `h`. -/
theorem trivializationAt_fiberBundleOfHomeomorph {Q : B → Type*}
    [TopologicalSpace (TotalSpace F Q)] [∀ b, TopologicalSpace (Q b)] (h : TotalSpace F Q ≃ₜ P)
    (hh : ∀ x, proj (h x) = x.proj) (hQ : ∀ b, IsInducing (TotalSpace.mk b : Q b → TotalSpace F Q))
    (b : B) :
    letI := A.fiberBundleOfHomeomorph h hh hQ
    trivializationAt F Q b = (A.trivAt b).compTotalSpaceHomeomorph h hh :=
  (rfl)

/-- The trivializations of the atlas of `A.fiberBundleOfHomeomorph h hh hQ` are those of `A`,
transported along `h`. -/
theorem mem_trivializationAtlas_fiberBundleOfHomeomorph_iff {Q : B → Type*}
    [TopologicalSpace (TotalSpace F Q)] [∀ b, TopologicalSpace (Q b)] (h : TotalSpace F Q ≃ₜ P)
    (hh : ∀ x, proj (h x) = x.proj) (hQ : ∀ b, IsInducing (TotalSpace.mk b : Q b → TotalSpace F Q))
    (e : Trivialization F (π F Q)) :
    letI := A.fiberBundleOfHomeomorph h hh hQ
    e ∈ trivializationAtlas F Q ↔ ∃ t ∈ A.charts, t.compTotalSpaceHomeomorph h hh = e :=
  Iff.rfl

/-- **The fibre bundle of a locally trivial map.** The fibres of `proj`, with their subspace
topologies, form a fibre bundle over `B` with model fibre `F` and total space `P`, whose atlas
consists of the trivializations of `A`. -/
@[instance_reducible]
def fiberBundle : FiberBundle F (MapFiber proj) :=
  A.fiberBundleOfHomeomorph (totalSpaceHomeomorph F proj) proj_totalSpaceHomeomorph
    (isInducing_totalSpaceMk F)

theorem trivializationAt_eq (b : B) :
    letI := A.fiberBundle
    trivializationAt F (MapFiber proj) b = (A.trivAt b).toMapFiber :=
  A.trivializationAt_fiberBundleOfHomeomorph _ _ _ b

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
  A.mem_trivializationAtlas_fiberBundleOfHomeomorph_iff _ _ _ e

end Atlas

/-! ### Principal bundles given by their total space -/

variable {G : Type*} [Group G] [TopologicalSpace G] [MulAction Gᵐᵒᵖ P] {proj : P → B}

/-- **Principal bundles given by their total space.** Let `G` act on the right on `P` and on a
family of fibres `Q` whose total space is identified with `P` over `B` by the equivariant
homeomorphism `h`, and let every trivialization of the atlas `A` intertwine the action on `P` with
right multiplication on `G`. Then `Q` is a principal `G`-bundle. -/
theorem Atlas.principalBundle_of_homeomorph (A : Atlas G proj) {Q : B → Type*}
    [TopologicalSpace (TotalSpace G Q)] [∀ b, TopologicalSpace (Q b)] [∀ b, MulAction Gᵐᵒᵖ (Q b)]
    (h : TotalSpace G Q ≃ₜ P) (hh : ∀ x, proj (h x) = x.proj)
    (hQ : ∀ b, IsInducing (TotalSpace.mk b : Q b → TotalSpace G Q))
    (hsmul : ∀ b (q : Q b) (g : Gᵐᵒᵖ), h ⟨b, g • q⟩ = g • h ⟨b, q⟩)
    (hA : ∀ t ∈ A.charts, ∀ (p : P), proj p ∈ t.baseSet → ∀ g : G,
      (t (op g • p)).2 = (t p).2 * g) :
    letI := A.fiberBundleOfHomeomorph h hh hQ
    PrincipalBundle G Q := by
  let := A.fiberBundleOfHomeomorph h hh hQ
  refine ⟨fun e he ↦ ?_⟩
  obtain ⟨t, ht, rfl⟩ := (A.mem_trivializationAtlas_fiberBundleOfHomeomorph_iff _ _ _ e).1 he.out
  refine ⟨fun b' hb' q g ↦ ?_⟩
  have hq : proj (h ⟨b', q⟩) ∈ t.baseSet := by
    rw [hh]
    simpa using hb'
  simpa only [Bundle.Trivialization.compTotalSpaceHomeomorph_apply, hsmul] using hA t ht _ hq g

/-- **Principal bundles given by their total space.** Let `G` act on the right on `P`, preserving
the fibres of `proj`, and let every trivialization of the atlas `A` intertwine the action with right
multiplication on `G`. Then the fibres of `proj` form a principal `G`-bundle. -/
theorem Atlas.principalBundle (A : Atlas G proj)
    (hproj : ∀ (g : Gᵐᵒᵖ) (p : P), proj (g • p) = proj p)
    (hA : ∀ t ∈ A.charts, ∀ (p : P), proj p ∈ t.baseSet → ∀ g : G,
      (t (op g • p)).2 = (t p).2 * g) :
    letI := A.fiberBundle
    letI := mulAction hproj
    PrincipalBundle G (MapFiber proj) :=
  letI := mulAction hproj
  A.principalBundle_of_homeomorph _ _ _ (fun _ _ _ ↦ rfl) hA

end MapFiber

end TauCeti
