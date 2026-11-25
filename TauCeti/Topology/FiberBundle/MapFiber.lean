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
`TauCeti.MapFiber.Atlas F proj`, and the fibre bundle is the definition
`TauCeti.MapFiber.Atlas.fiberBundle` rather than an instance, because it depends on the atlas.

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
* `TauCeti.MapFiber.Atlas`: a choice of a trivialization of `proj` around every point of `B`.
* `TauCeti.MapFiber.Atlas.fiberBundleOfHomeomorph`: the fibre bundle structure on a family of
  fibres whose total space is homeomorphic to `P` over `B`.
* `TauCeti.MapFiber.Atlas.fiberBundle`: the fibre bundle structure on the fibres of `proj`.
* `TauCeti.MapFiber.mulAction`: a fibre-preserving action restricted to the fibres.

## Main results

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
the point `x` of the total space is sent to `e (h x)`. This is `e.compHomeomorph h` with its
projection `proj ∘ h` replaced by `π F Q` using `hh`. -/
def compTotalSpaceHomeomorph : Trivialization F (π F Q) where
  __ := e.compHomeomorph h
  source_eq := by
    ext x
    simp [(e.compHomeomorph h).mem_source, hh]
  proj_toFun x hx := ((e.compHomeomorph h).proj_toFun x hx).trans (hh x)

@[simp]
theorem compTotalSpaceHomeomorph_apply (x : TotalSpace F Q) :
    e.compTotalSpaceHomeomorph h hh x = e (h x) :=
  (rfl)

@[simp]
theorem compTotalSpaceHomeomorph_symm_apply (y : B × F) :
    (e.compTotalSpaceHomeomorph h hh).toOpenPartialHomeomorph.symm y =
      h.symm (e.toOpenPartialHomeomorph.symm y) :=
  (rfl)

@[simp]
theorem compTotalSpaceHomeomorph_baseSet :
    (e.compTotalSpaceHomeomorph h hh).baseSet = e.baseSet :=
  (rfl)

@[simp]
theorem compTotalSpaceHomeomorph_source :
    (e.compTotalSpaceHomeomorph h hh).source = h ⁻¹' e.source :=
  (rfl)

/-- The coordinate changes between the trivializations of `Q` coming from trivializations of
`proj` are those between the trivializations of `proj`. -/
@[simp]
theorem compTotalSpaceHomeomorph_coordChange (e' : Trivialization F proj) :
    (e.compTotalSpaceHomeomorph h hh).coordChange (e'.compTotalSpaceHomeomorph h hh) =
      e.coordChange e' :=
  funext fun _ ↦ funext fun _ ↦ by
    simp [Trivialization.coordChange, compTotalSpaceHomeomorph_apply]

end TotalSpaceHomeomorph

/-- A trivialization of a map `proj` as a trivialization, with the same base set, of the bundle of
fibres of `proj`: the point `p` of the fibre over `b` is sent to `e p`. -/
def toMapFiber : Trivialization F (π F (MapFiber proj)) :=
  e.compTotalSpaceHomeomorph (MapFiber.totalSpaceHomeomorph F proj)
    MapFiber.proj_totalSpaceHomeomorph

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
whose base set contains `b`, for every point `b` of `B`. -/
structure Atlas (proj : P → B) where
  /-- The trivialization chosen at a point of the base. -/
  trivAt : B → Trivialization F proj
  /-- The trivialization chosen at `b` trivializes `proj` over a neighbourhood of `b`. -/
  mem_baseSet_trivAt : ∀ b, b ∈ (trivAt b).baseSet

namespace Atlas

variable {proj : P → B} (A : Atlas F proj)

/-- **A family of fibres of a locally trivial map is a fibre bundle.** Let `Q` be a family of
fibres over `B` whose total space is identified with `P` over `B` by the homeomorphism `h`, and in
whose total space each fibre is embedded. Then `Q` is a fibre bundle over `B` with model fibre `F`,
whose atlas consists of the trivializations of `A` transported along `h`. -/
@[instance_reducible]
def fiberBundleOfHomeomorph {Q : B → Type*} [TopologicalSpace (TotalSpace F Q)]
    [∀ b, TopologicalSpace (Q b)] (h : TotalSpace F Q ≃ₜ P) (hh : ∀ x, proj (h x) = x.proj)
    (hQ : ∀ b, IsInducing (TotalSpace.mk b : Q b → TotalSpace F Q)) : FiberBundle F Q where
  totalSpaceMk_isInducing' := hQ
  trivializationAtlas' := range fun b ↦ (A.trivAt b).compTotalSpaceHomeomorph h hh
  trivializationAt' b := (A.trivAt b).compTotalSpaceHomeomorph h hh
  mem_baseSet_trivializationAt' := A.mem_baseSet_trivAt
  trivialization_mem_atlas' b := mem_range_self b

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
    e ∈ trivializationAtlas F Q ↔ ∃ b, (A.trivAt b).compTotalSpaceHomeomorph h hh = e :=
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

/-- The trivializations of the atlas of the bundle of fibres are those of `A`. -/
theorem mem_trivializationAtlas_iff (e : Trivialization F (π F (MapFiber proj))) :
    letI := A.fiberBundle
    e ∈ trivializationAtlas F (MapFiber proj) ↔ ∃ b, (A.trivAt b).toMapFiber = e :=
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
    (hA : ∀ b (p : P), proj p ∈ (A.trivAt b).baseSet → ∀ g : G,
      (A.trivAt b (op g • p)).2 = (A.trivAt b p).2 * g) :
    letI := A.fiberBundleOfHomeomorph h hh hQ
    PrincipalBundle G Q := by
  let := A.fiberBundleOfHomeomorph h hh hQ
  refine ⟨fun e he ↦ ?_⟩
  obtain ⟨b, rfl⟩ := he.out
  refine ⟨fun b' hb' q g ↦ ?_⟩
  have hq : proj (h ⟨b', q⟩) ∈ (A.trivAt b).baseSet := by
    rw [hh]
    exact hb'
  simpa only [Bundle.Trivialization.compTotalSpaceHomeomorph_apply, hsmul] using hA b _ hq g

/-- **Principal bundles given by their total space.** Let `G` act on the right on `P`, preserving
the fibres of `proj`, and let every trivialization of the atlas `A` intertwine the action with right
multiplication on `G`. Then the fibres of `proj` form a principal `G`-bundle. -/
theorem Atlas.principalBundle (A : Atlas G proj)
    (hproj : ∀ (g : Gᵐᵒᵖ) (p : P), proj (g • p) = proj p)
    (hA : ∀ b (p : P), proj p ∈ (A.trivAt b).baseSet → ∀ g : G,
      (A.trivAt b (op g • p)).2 = (A.trivAt b p).2 * g) :
    letI := A.fiberBundle
    letI := mulAction hproj
    PrincipalBundle G (MapFiber proj) :=
  letI := mulAction hproj
  A.principalBundle_of_homeomorph _ _ _ (fun _ _ _ ↦ rfl) hA

end MapFiber

end TauCeti
