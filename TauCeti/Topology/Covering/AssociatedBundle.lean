/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Vector bundles associated with representations of a deck group

Let `p : E → X` present `X` as the quotient of `E` by a group `G` in the sense of Mathlib's
`IsQuotientCoveringMap p G`, and let `ρ : G →* (F →L[𝕜] F)ˣ` be a representation of `G` on a
normed space `F`. The associated vector bundle `E ×_G F` over `X` is the quotient of `E × F` by
`g • (y, v) = (g • y, ρ g v)`. Rather than forming that quotient, this file builds the bundle
from its transition functions, as a Mathlib `VectorBundleCore`,
`IsQuotientCoveringMap.associatedCore`, and then identifies its total space with the quotient.

The charts are indexed by the points of `E`. The chart through `e : E` lives over the domain of
the local section `IsLocalHomeomorph.localInverseAt` of `p` through `e`. Over a point `x` where
the local sections through `e` and `e'` are both defined, they differ by a unique deck
transformation `IsQuotientCoveringMap.deckChange e e' x`. As `x` varies this group element is
locally constant (`IsQuotientCoveringMap.eventually_deckChange_eq`), and it satisfies the cocycle
identity `deckChange e' e'' x * deckChange e e' x = deckChange e e'' x`. The transition from the
chart through `e` to the chart through `e'` is `ρ (deckChange e e' x)`. Being locally constant,
these transitions are smooth, even analytic, for any manifold structure on `X`; the manifold
consequences are in `TauCeti.Geometry.Manifold.Quotient.AssociatedBundle`.

Sections of the associated bundle are the same as `ρ`-equivariant functions `f : E → F`, those
with `f (g • y) = ρ g (f y)` (`IsQuotientCoveringMap.associatedSectionEquiv`). The value of `f`
at `y` is the coordinate of the section at `p y` in the chart through `y`, and over the domain of
the chart through `y` the section reads `x ↦ f (localInverseAt y x)`
(`IsQuotientCoveringMap.localTriv_associatedCore_apply_snd`).

For a character `χ : G →* 𝕜ˣ` the associated bundle is the line bundle
`IsQuotientCoveringMap.characterCore χ`, whose transitions multiply by `χ (deckChange e e' x)`.
The trivial character gives the identity transitions
(`IsQuotientCoveringMap.characterCore_one_coordChange`), so the trivial line bundle is a case of
the same construction.

The pair `(y, v) ∈ E × F` represents the point over `p y` whose coordinate in the chart through
`y` is `v` (`IsQuotientCoveringMap.associatedMk`). Two pairs represent the same point exactly when
they lie in one orbit of `g • (y, v) = (g • y, ρ g v)`
(`IsQuotientCoveringMap.associatedMk_eq_associatedMk_iff`). Near `(e, v)` the map
`E × F → E ×_G F` is `p × id` read in the chart through `e`, because over the image of the local
section of `p` through `e` the deck transformation between the local sections through `y` and `e`
is trivial (`IsQuotientCoveringMap.deckChange_eq_one_of_mem_target`). So it is a local
homeomorphism (`IsQuotientCoveringMap.isLocalHomeomorph_associatedMk`) and an open quotient map
(`IsQuotientCoveringMap.isOpenQuotientMap_associatedMk`): the total space of the bundle built from
transition functions is homeomorphic to the quotient of `E × F` by the orbit relation
(`IsQuotientCoveringMap.associatedQuotientHomeomorph`).

## Main definitions

* `IsQuotientCoveringMap.deckChange`: the deck transformation between two local sections.
* `IsQuotientCoveringMap.associatedCore`: the vector bundle associated with a representation.
* `IsQuotientCoveringMap.characterCore`: the line bundle associated with a character.
* `IsQuotientCoveringMap.associatedSectionEquiv`: sections of the associated bundle are
  equivariant functions upstairs.
* `IsQuotientCoveringMap.associatedMk`: the point of the associated bundle represented by a pair
  in `E × F`.

## Main results

* `IsQuotientCoveringMap.associatedMk_eq_associatedMk_iff`: the fibres of `E × F → E ×_G F` are
  the orbits of the diagonal action.
* `IsQuotientCoveringMap.isOpenQuotientMap_associatedMk`: the total space of `E ×_G F` is the
  quotient of `E × F`.
* `IsQuotientCoveringMap.associatedQuotientHomeomorph`: the homeomorphism from the quotient of
  `E × F` by the orbit relation `IsQuotientCoveringMap.associatedOrbitRel` to the total space.

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, Part I,
  §§2–3 and §8 (bundles from coordinate transformations, associated bundles).
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2
  (holomorphic line bundles from cocycles).
-/

public section

open Bundle Filter Set Topology

namespace IsQuotientCoveringMap

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [Group G] [MulAction G E]
  {p : E → X} (hp : IsQuotientCoveringMap p G)

/-! ### Deck transformations between local sections -/

section DeckChange

variable {e e' e'' : E} {x : X}

open scoped Classical in
/-- The deck transformation carrying the local section of `p` through `e` to the local section
through `e'` over the point `x`. It is `1` when `x` lies outside the domain of either section. -/
noncomputable def deckChange (e e' : E) (x : X) : G :=
  if h : x ∈ (hp.isLocalHomeomorph.localInverseAt e).source ∩
      (hp.isLocalHomeomorph.localInverseAt e').source then
    hp.fiberEquivGroup ⟨_, hp.isLocalHomeomorph.apply_localInverseAt_of_mem h.1⟩
      ⟨_, hp.isLocalHomeomorph.apply_localInverseAt_of_mem h.2⟩
  else 1

/-- Over a common point of their domains, `deckChange e e' x` is the unique group element
carrying the local section through `e` to the local section through `e'`. -/
theorem deckChange_eq_iff (h : x ∈ (hp.isLocalHomeomorph.localInverseAt e).source ∩
      (hp.isLocalHomeomorph.localInverseAt e').source) {g : G} :
    hp.deckChange e e' x = g ↔
      g • hp.isLocalHomeomorph.localInverseAt e x = hp.isLocalHomeomorph.localInverseAt e' x := by
  simp only [deckChange, h, ↓reduceDIte, fiberEquivGroup_eq_iff]
  exact eq_comm

/-- The deck transformation `deckChange e e' x` carries the local section through `e` to the
local section through `e'` over `x`. -/
theorem deckChange_smul_localInverseAt (h : x ∈ (hp.isLocalHomeomorph.localInverseAt e).source ∩
      (hp.isLocalHomeomorph.localInverseAt e').source) :
    hp.deckChange e e' x • hp.isLocalHomeomorph.localInverseAt e x =
      hp.isLocalHomeomorph.localInverseAt e' x :=
  (hp.deckChange_eq_iff h).1 rfl

/-- A local section differs from itself by the identity. -/
@[simp]
theorem deckChange_self (h : x ∈ (hp.isLocalHomeomorph.localInverseAt e).source) :
    hp.deckChange e e x = 1 :=
  (hp.deckChange_eq_iff ⟨h, h⟩).2 (one_smul _ _)

/-- The deck transformations between local sections form a cocycle. -/
theorem deckChange_mul_deckChange (h : x ∈ (hp.isLocalHomeomorph.localInverseAt e).source ∩
      (hp.isLocalHomeomorph.localInverseAt e').source ∩
      (hp.isLocalHomeomorph.localInverseAt e'').source) :
    hp.deckChange e' e'' x * hp.deckChange e e' x = hp.deckChange e e'' x :=
  ((hp.deckChange_eq_iff ⟨h.1.1, h.2⟩).2 <| by
    rw [mul_smul, hp.deckChange_smul_localInverseAt h.1,
      hp.deckChange_smul_localInverseAt ⟨h.1.2, h.2⟩]).symm

/-- The local section through `y` passes through `g • y` after the deck transformation `g`. -/
@[simp]
theorem deckChange_self_smul (y : E) (g : G) : hp.deckChange y (g • y) (p y) = g := by
  have h := hp.isLocalHomeomorph.localInverseAt_apply_self (x := g • y)
  have hmem := hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source (x := g • y)
  rw [hp.map_smul] at h hmem
  refine (hp.deckChange_eq_iff
    ⟨hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source (x := y), hmem⟩).2 ?_
  rw [h, hp.isLocalHomeomorph.localInverseAt_apply_self]

/-- Over a point `x` of its domain, the local section through `e` and the local section through
its own value at `x` differ by the identity. -/
@[simp]
theorem deckChange_localInverseAt (h : x ∈ (hp.isLocalHomeomorph.localInverseAt e).source) :
    hp.deckChange e (hp.isLocalHomeomorph.localInverseAt e x) x = 1 := by
  set z := hp.isLocalHomeomorph.localInverseAt e x
  have hz : p z = x := hp.isLocalHomeomorph.apply_localInverseAt_of_mem h
  have hself := hp.isLocalHomeomorph.localInverseAt_apply_self (x := z)
  have hmem := hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source (x := z)
  rw [hz] at hself hmem
  exact (hp.deckChange_eq_iff ⟨h, hmem⟩).2 (by rw [one_smul, hself])

/-- The deck transformation between two local sections is locally constant on the intersection of
their domains. -/
theorem eventually_deckChange_eq (h : x ∈ (hp.isLocalHomeomorph.localInverseAt e).source ∩
      (hp.isLocalHomeomorph.localInverseAt e').source) :
    ∀ᶠ x' in 𝓝 x, hp.deckChange e e' x' = hp.deckChange e e' x := by
  have := hp.toContinuousConstSMul
  set s := hp.isLocalHomeomorph.localInverseAt e
  set s' := hp.isLocalHomeomorph.localInverseAt e'
  set g := hp.deckChange e e' x
  have hcont : ContinuousAt (fun x' ↦ g • s x') x :=
    (continuous_const_smul g).continuousAt.comp (s.continuousAt h.1)
  have htarget : s'.target ∈ 𝓝 (g • s x) := by
    rw [hp.deckChange_smul_localInverseAt h]
    exact s'.open_target.mem_nhds (s'.map_source h.2)
  filter_upwards [s.open_source.mem_nhds h.1, s'.open_source.mem_nhds h.2, hcont htarget]
    with x' h₁ h₂ h₃
  -- Both `g • s x'` and `s' x'` lie over `x'` in the target of `s'`, where `p` is injective.
  refine (hp.deckChange_eq_iff ⟨h₁, h₂⟩).2
    (hp.isLocalHomeomorph.injOn_localInverseAt_target (x := e') h₃ (s'.map_source h₂) ?_)
  rw [hp.map_smul, hp.isLocalHomeomorph.apply_localInverseAt_of_mem h₁,
    hp.isLocalHomeomorph.apply_localInverseAt_of_mem h₂]

/-- The local section through `g • y` passes through `y` after the deck transformation `g⁻¹`. -/
@[simp]
theorem deckChange_smul_self (y : E) (g : G) : hp.deckChange (g • y) y (p y) = g⁻¹ := by
  have hgy := hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source (x := g • y)
  have hy := hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source (x := y)
  rw [hp.map_smul] at hgy
  have h := hp.deckChange_mul_deckChange (e := g • y) (e' := y) (e'' := g • y) ⟨⟨hgy, hy⟩, hgy⟩
  rw [deckChange_self_smul, hp.deckChange_self hgy] at h
  exact eq_inv_of_mul_eq_one_right h

/-- A point `y` in the image of the local section through `e` defines the same local section as
`e` over `p y`. -/
theorem deckChange_eq_one_of_mem_target {y : E}
    (h : y ∈ (hp.isLocalHomeomorph.localInverseAt e).target) :
    hp.deckChange y e (p y) = 1 := by
  set s := hp.isLocalHomeomorph.localInverseAt e
  have hs : p y ∈ s.source := by
    simpa only [s, IsLocalHomeomorph.localInverseAt_symm] using s.map_target h
  refine (hp.deckChange_eq_iff ⟨hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source, hs⟩).2 ?_
  rw [one_smul, IsLocalHomeomorph.localInverseAt_apply_self]
  simpa only [s, IsLocalHomeomorph.localInverseAt_symm] using (s.right_inv h).symm

end DeckChange

/-! ### The associated vector bundle -/

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (ρ : G →* (F →L[𝕜] F)ˣ) {y : E}

/-- The vector bundle `E ×_G F` over `X` associated with a representation `ρ` of the deck group
on `F`. Its chart through `e : E` lives over the domain of the local section of `p` through `e`,
and the transition from the chart through `e` to the chart through `e'` over `x` is
`ρ (deckChange e e' x)`. -/
noncomputable def associatedCore : VectorBundleCore 𝕜 X F E where
  baseSet e := (hp.isLocalHomeomorph.localInverseAt e).source
  isOpen_baseSet e := (hp.isLocalHomeomorph.localInverseAt e).open_source
  indexAt := Function.surjInv hp.surjective
  mem_baseSet_at x := by
    simpa only [Function.surjInv_eq hp.surjective x] using
      hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source
        (x := Function.surjInv hp.surjective x)
  coordChange e e' x := ρ (hp.deckChange e e' x)
  coordChange_self e x hx v := by
    rw [hp.deckChange_self hx, map_one, Units.val_one, one_apply_eq_self]
  continuousOn_coordChange e e' x hx :=
    (continuousAt_const.congr (by
      filter_upwards [hp.eventually_deckChange_eq hx] with x' hx'
      rw [hx'])).continuousWithinAt
  coordChange_comp e e' e'' x hx v := by
    rw [← hp.deckChange_mul_deckChange hx, map_mul, Units.val_mul, mul_apply_eq_comp]

/-- The chart through `e` lives over the domain of the local section of `p` through `e`. -/
theorem associatedCore_baseSet (e : E) :
    (hp.associatedCore ρ).baseSet e = (hp.isLocalHomeomorph.localInverseAt e).source :=
  (rfl)

/-- The chart through `e` lives over the domain of the local section of `p` through `e`. -/
@[simp]
theorem associatedCore_localTriv_baseSet (e : E) :
    ((hp.associatedCore ρ).localTriv e).baseSet =
      (hp.isLocalHomeomorph.localInverseAt e).source :=
  (rfl)

/-- The chart through `y` is defined at `p y`. -/
theorem mem_associatedCore_baseSet_self (y : E) : p y ∈ (hp.associatedCore ρ).baseSet y := by
  rw [associatedCore_baseSet]
  exact hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source

/-- The preferred chart at `x` is the chart through a chosen point over `x`. -/
theorem associatedCore_indexAt (x : X) :
    (hp.associatedCore ρ).indexAt x = Function.surjInv hp.surjective x :=
  (rfl)

/-- The transitions of the associated bundle apply `ρ` to the deck transformations between local
sections. -/
@[simp]
theorem associatedCore_coordChange (e e' : E) (x : X) :
    (hp.associatedCore ρ).coordChange e e' x = ρ (hp.deckChange e e' x) :=
  (rfl)

/-- The transitions of the associated bundle are locally constant. -/
theorem eventually_associatedCore_coordChange_eq {e e' : E} {x : X}
    (hx : x ∈ (hp.associatedCore ρ).baseSet e ∩ (hp.associatedCore ρ).baseSet e') :
    ∀ᶠ x' in 𝓝 x,
      (hp.associatedCore ρ).coordChange e e' x' = (hp.associatedCore ρ).coordChange e e' x := by
  rw [associatedCore_baseSet, associatedCore_baseSet] at hx
  filter_upwards [hp.eventually_deckChange_eq hx] with x' hx'
  rw [associatedCore_coordChange, associatedCore_coordChange, hx']

/-! ### The line bundle of a character -/

/-- The line bundle over `X` associated with a character `χ` of the deck group: the transition
from the chart through `e` to the chart through `e'` multiplies by `χ (deckChange e e' x)`. -/
noncomputable def characterCore (χ : G →* 𝕜ˣ) : VectorBundleCore 𝕜 X 𝕜 E :=
  hp.associatedCore ((Units.map (algebraMap 𝕜 (𝕜 →L[𝕜] 𝕜)).toMonoidHom).comp χ)

/-- The line bundle of a character is the bundle associated with the character, acting on `𝕜` by
multiplication. -/
theorem characterCore_def (χ : G →* 𝕜ˣ) :
    hp.characterCore χ =
      hp.associatedCore ((Units.map (algebraMap 𝕜 (𝕜 →L[𝕜] 𝕜)).toMonoidHom).comp χ) :=
  (rfl)

/-- The transitions of the line bundle of `χ` multiply by the values of `χ`. -/
@[simp]
theorem characterCore_coordChange_apply (χ : G →* 𝕜ˣ) (e e' : E) (x : X) (v : 𝕜) :
    (hp.characterCore χ).coordChange e e' x v = χ (hp.deckChange e e' x) * v := by
  simp [characterCore_def, ContinuousLinearMap.algebraMap_apply, smul_eq_mul]

/-- The trivial character gives the identity transitions. -/
@[simp]
theorem characterCore_one_coordChange (e e' : E) (x : X) :
    (hp.characterCore (1 : G →* 𝕜ˣ)).coordChange e e' x = ContinuousLinearMap.id 𝕜 𝕜 := by
  ext
  simp

/-! ### Sections as equivariant functions -/

/-- Passing from the chart through `y` to the chart through `g • y` at `p y` applies `ρ g`. -/
private theorem associatedCore_coordChange_smul {e : E} (he : p y ∈ (hp.associatedCore ρ).baseSet e)
    (g : G) (v : F) :
    (hp.associatedCore ρ).coordChange e (g • y) (p y) v =
      (ρ g : F →L[𝕜] F) ((hp.associatedCore ρ).coordChange e y (p y) v) := by
  have hmem := hp.mem_associatedCore_baseSet_self ρ (g • y)
  rw [hp.map_smul] at hmem
  rw [← (hp.associatedCore ρ).coordChange_comp _ y (g • y) (p y)
    ⟨⟨he, hp.mem_associatedCore_baseSet_self ρ y⟩, hmem⟩,
    associatedCore_coordChange, deckChange_self_smul]

/-- At a point `x` of its domain, the chart through `y` agrees with the chart through the point of
the local section through `y` over `x`. -/
private theorem associatedCore_coordChange_localInverseAt {e : E} {x : X}
    (he : x ∈ (hp.associatedCore ρ).baseSet e)
    (hx : x ∈ (hp.isLocalHomeomorph.localInverseAt y).source) (v : F) :
    (hp.associatedCore ρ).coordChange e (hp.isLocalHomeomorph.localInverseAt y x) x v =
      (hp.associatedCore ρ).coordChange e y x v := by
  have hz := hp.isLocalHomeomorph.apply_localInverseAt_of_mem hx
  have hmem := hp.mem_associatedCore_baseSet_self ρ (hp.isLocalHomeomorph.localInverseAt y x)
  rw [hz] at hmem
  have hy : x ∈ (hp.associatedCore ρ).baseSet y := by rwa [associatedCore_baseSet]
  rw [← (hp.associatedCore ρ).coordChange_comp _ y _ x ⟨⟨he, hy⟩, hmem⟩,
    associatedCore_coordChange, hp.deckChange_localInverseAt hx, map_one, Units.val_one,
    one_apply_eq_self]

/-- The equivariance of the coordinates of a section in the charts through the points of `E`. -/
private theorem localTriv_associatedCore_smul (σ : ∀ x, (hp.associatedCore ρ).Fiber x) (g : G)
    (y : E) :
    ((hp.associatedCore ρ).localTriv (g • y) ⟨p (g • y), σ (p (g • y))⟩).2 =
      (ρ g : F →L[𝕜] F) (((hp.associatedCore ρ).localTriv y ⟨p y, σ (p y)⟩).2) := by
  rw [hp.map_smul, VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply]
  exact hp.associatedCore_coordChange_smul ρ ((hp.associatedCore ρ).mem_baseSet_at _) g (σ (p y))

/-- Sections of the bundle associated with `ρ` are the same as `ρ`-equivariant functions on `E`.
The function attached to a section `σ` sends `y` to the coordinate of `σ (p y)` in the chart
through `y`. -/
noncomputable def associatedSectionEquiv :
    (∀ x, (hp.associatedCore ρ).Fiber x) ≃
      {f : E → F // ∀ (g : G) (y : E), f (g • y) = (ρ g : F →L[𝕜] F) (f y)} where
  toFun σ := ⟨fun y ↦ ((hp.associatedCore ρ).localTriv y ⟨p y, σ (p y)⟩).2,
    hp.localTriv_associatedCore_smul ρ σ⟩
  invFun f x := (f : E → F) ((hp.associatedCore ρ).indexAt x)
  left_inv σ := funext fun x ↦ by
    have hx : p ((hp.associatedCore ρ).indexAt x) = x := Function.surjInv_eq hp.surjective x
    simp only [VectorBundleCore.localTriv_apply]
    rw [hx]
    exact (hp.associatedCore ρ).coordChange_self _ x ((hp.associatedCore ρ).mem_baseSet_at x) (σ x)
  right_inv f := by
    obtain ⟨f, hf⟩ := f
    refine Subtype.ext (funext fun y ↦ ?_)
    simp only [VectorBundleCore.localTriv_apply, associatedCore_coordChange]
    have hz : p ((hp.associatedCore ρ).indexAt (p y)) = p y := Function.surjInv_eq hp.surjective _
    generalize (hp.associatedCore ρ).indexAt (p y) = z at hz ⊢
    obtain ⟨g, rfl⟩ := hp.apply_eq_iff_mem_orbit.1 hz.symm
    rw [hp.map_smul, deckChange_self_smul, hf]

/-- The equivariant function attached to a section sends `y` to the coordinate of the section at
`p y` in the chart through `y`. -/
@[simp]
theorem associatedSectionEquiv_apply_coe (σ : ∀ x, (hp.associatedCore ρ).Fiber x) (y : E) :
    (hp.associatedSectionEquiv ρ σ : E → F) y =
      ((hp.associatedCore ρ).localTriv y ⟨p y, σ (p y)⟩).2 :=
  (rfl)

/-- The section attached to an equivariant function `f` takes at `x` the value of `f` at the
point chosen over `x`, read in the preferred chart at `x`. -/
@[simp]
theorem associatedSectionEquiv_symm_apply
    (f : {f : E → F // ∀ (g : G) (y : E), f (g • y) = (ρ g : F →L[𝕜] F) (f y)}) (x : X) :
    (hp.associatedSectionEquiv ρ).symm f x = (f : E → F) ((hp.associatedCore ρ).indexAt x) :=
  (rfl)

/-- Over the domain of the chart through `y`, a section reads, in that chart, as the
corresponding equivariant function composed with the local section of `p` through `y`. -/
theorem localTriv_associatedCore_apply_snd (σ : ∀ x, (hp.associatedCore ρ).Fiber x) {y : E}
    {x : X} (hx : x ∈ (hp.isLocalHomeomorph.localInverseAt y).source) :
    ((hp.associatedCore ρ).localTriv y ⟨x, σ x⟩).2 =
      (hp.associatedSectionEquiv ρ σ : E → F) (hp.isLocalHomeomorph.localInverseAt y x) := by
  have hz := hp.isLocalHomeomorph.apply_localInverseAt_of_mem hx
  rw [associatedSectionEquiv_apply_coe, VectorBundleCore.localTriv_apply,
    VectorBundleCore.localTriv_apply, hz]
  exact (hp.associatedCore_coordChange_localInverseAt ρ ((hp.associatedCore ρ).mem_baseSet_at x)
    hx (σ x)).symm

/-- The section attached to an equivariant function `f` reads as `x ↦ f (localInverseAt y x)` in
the chart through `y`. -/
theorem localTriv_associatedSectionEquiv_symm_apply_snd
    (f : {f : E → F // ∀ (g : G) (y : E), f (g • y) = (ρ g : F →L[𝕜] F) (f y)}) {y : E} {x : X}
    (hx : x ∈ (hp.isLocalHomeomorph.localInverseAt y).source) :
    ((hp.associatedCore ρ).localTriv y ⟨x, (hp.associatedSectionEquiv ρ).symm f x⟩).2 =
      (f : E → F) (hp.isLocalHomeomorph.localInverseAt y x) := by
  rw [localTriv_associatedCore_apply_snd _ _ _ hx, Equiv.apply_symm_apply]

/-- The equivariant function attached to a section vanishes at `y` exactly when the section
vanishes at `p y`. -/
theorem associatedSectionEquiv_apply_eq_zero_iff (σ : ∀ x, (hp.associatedCore ρ).Fiber x)
    (y : E) : (hp.associatedSectionEquiv ρ σ : E → F) y = 0 ↔ σ (p y) = 0 := by
  have hy : p y ∈ ((hp.associatedCore ρ).localTriv y).baseSet := by
    rw [associatedCore_localTriv_baseSet]
    exact hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source
  rw [associatedSectionEquiv_apply_coe,
    Trivialization.apply_eq_prod_continuousLinearEquivAt 𝕜 _ _ hy]
  exact (((hp.associatedCore ρ).localTriv y).continuousLinearEquivAt 𝕜 (p y) hy).map_eq_zero_iff

/-! ### The total space as a quotient of `E × F` -/

/-- The point of the associated bundle `E ×_G F` represented by `(y, v) ∈ E × F`: the point over
`p y` whose coordinate in the chart through `y` is `v`
(`IsQuotientCoveringMap.localTriv_associatedMk_self`). Two pairs represent the same point exactly
when they lie in one orbit of `g • (y, v) = (g • y, ρ g v)`
(`IsQuotientCoveringMap.associatedMk_eq_associatedMk_iff`), and this map is an open quotient map
(`IsQuotientCoveringMap.isOpenQuotientMap_associatedMk`), so the total space is the quotient of
`E × F` by that action. -/
noncomputable def associatedMk (q : E × F) : (hp.associatedCore ρ).TotalSpace :=
  ⟨p q.1, (hp.associatedCore ρ).coordChange q.1 ((hp.associatedCore ρ).indexAt (p q.1)) (p q.1)
    q.2⟩

/-- The point represented by `(y, v)` lies over `p y`. -/
@[simp]
theorem associatedMk_proj (q : E × F) : (hp.associatedMk ρ q).proj = p q.1 :=
  (rfl)

/-- The point represented by `(y, v)` is the point with coordinates `(p y, v)` in the chart
through `y`. -/
theorem associatedMk_eq_localTriv_symm (y : E) (v : F) :
    hp.associatedMk ρ (y, v) =
      ((hp.associatedCore ρ).localTriv y).toOpenPartialHomeomorph.symm (p y, v) :=
  (rfl)

/-- In the chart through `e`, the point represented by `(y, v)` has coordinate
`coordChange y e (p y) v`. -/
theorem localTriv_associatedMk {e y : E} (he : p y ∈ (hp.associatedCore ρ).baseSet e) (v : F) :
    (hp.associatedCore ρ).localTriv e (hp.associatedMk ρ (y, v)) =
      (p y, (hp.associatedCore ρ).coordChange y e (p y) v) := by
  rw [VectorBundleCore.localTriv_apply]
  exact Prod.ext rfl ((hp.associatedCore ρ).coordChange_comp _ _ _ (p y)
    ⟨⟨hp.mem_associatedCore_baseSet_self ρ y, (hp.associatedCore ρ).mem_baseSet_at _⟩, he⟩ v)

/-- In the chart through `y`, the point represented by `(y, v)` has coordinate `v`. -/
theorem localTriv_associatedMk_self (y : E) (v : F) :
    (hp.associatedCore ρ).localTriv y (hp.associatedMk ρ (y, v)) = (p y, v) := by
  rw [hp.localTriv_associatedMk ρ (hp.mem_associatedCore_baseSet_self ρ y),
    (hp.associatedCore ρ).coordChange_self _ _ (hp.mem_associatedCore_baseSet_self ρ y)]

/-- Near `e`, along the local section of `p` through `e`, the chart through `e` reads the point
represented by `(y, v)` as `(p y, v)`. -/
theorem localTriv_associatedMk_of_mem_target {e y : E}
    (hy : y ∈ (hp.isLocalHomeomorph.localInverseAt e).target) (v : F) :
    (hp.associatedCore ρ).localTriv e (hp.associatedMk ρ (y, v)) = (p y, v) := by
  have he : p y ∈ (hp.associatedCore ρ).baseSet e := by
    simpa only [associatedCore_baseSet, IsLocalHomeomorph.localInverseAt_symm] using
      (hp.isLocalHomeomorph.localInverseAt e).map_target hy
  rw [hp.localTriv_associatedMk ρ he, associatedCore_coordChange,
    hp.deckChange_eq_one_of_mem_target hy, map_one, Units.val_one, one_apply_eq_self]

/-- Two points over the domain of the chart through `e` agree when the chart takes them to the
same point. -/
private theorem eq_of_localTriv_eq {e : E} {a b : (hp.associatedCore ρ).TotalSpace}
    (ha : a.proj ∈ (hp.associatedCore ρ).baseSet e) (hb : b.proj ∈ (hp.associatedCore ρ).baseSet e)
    (h : (hp.associatedCore ρ).localTriv e a = (hp.associatedCore ρ).localTriv e b) : a = b :=
  ((hp.associatedCore ρ).localTriv e).toOpenPartialHomeomorph.injOn ha hb h

/-- Two pairs with the same first component represent the same point only if they are equal. -/
@[simp]
theorem associatedMk_right_inj {y : E} {v v' : F} :
    hp.associatedMk ρ (y, v) = hp.associatedMk ρ (y, v') ↔ v = v' := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  simpa only [localTriv_associatedMk_self] using
    congrArg (fun z ↦ ((hp.associatedCore ρ).localTriv y z).2) h

/-- The pairs `(y, v)` and `g • (y, v) = (g • y, ρ g v)` represent the same point. -/
@[simp]
theorem associatedMk_smul (g : G) (y : E) (v : F) :
    hp.associatedMk ρ (g • y, (ρ g : F →L[𝕜] F) v) = hp.associatedMk ρ (y, v) := by
  have hy := hp.mem_associatedCore_baseSet_self ρ y
  have hgy : p (g • y) ∈ (hp.associatedCore ρ).baseSet y := by rwa [hp.map_smul]
  refine hp.eq_of_localTriv_eq ρ hgy hy ?_
  rw [hp.localTriv_associatedMk ρ hgy, localTriv_associatedMk_self, associatedCore_coordChange,
    hp.map_smul, deckChange_smul_self, map_inv, ← mul_apply_eq_comp, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, one_apply_eq_self]

/-- **The fibres of `E × F → E ×_G F` are the orbits** of `g • (y, v) = (g • y, ρ g v)`. -/
theorem associatedMk_eq_associatedMk_iff {y y' : E} {v v' : F} :
    hp.associatedMk ρ (y, v) = hp.associatedMk ρ (y', v') ↔
      ∃ g : G, g • y = y' ∧ (ρ g : F →L[𝕜] F) v = v' := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨g, rfl⟩ := hp.apply_eq_iff_mem_orbit.1 (congrArg Bundle.TotalSpace.proj h).symm
    refine ⟨g, rfl, ?_⟩
    have hv : v' = (ρ g : F →L[𝕜] F) ((ρ g⁻¹ : F →L[𝕜] F) v') := by
      rw [map_inv, ← mul_apply_eq_comp, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        one_apply_eq_self]
    rw [hv, associatedMk_smul, associatedMk_right_inj] at h
    rw [h]
    exact hv.symm
  · rintro ⟨g, rfl, rfl⟩
    exact (hp.associatedMk_smul ρ g y v).symm

/-- Every point of the associated bundle is represented by a pair in `E × F`. -/
theorem associatedMk_surjective : Function.Surjective (hp.associatedMk ρ) := by
  rintro ⟨x, (w : F)⟩
  have hx : p ((hp.associatedCore ρ).indexAt x) = x := Function.surjInv_eq hp.surjective x
  have hmem := (hp.associatedCore ρ).mem_baseSet_at x
  refine ⟨((hp.associatedCore ρ).indexAt x, w), hp.eq_of_localTriv_eq ρ (by rwa [associatedMk_proj,
    hx]) hmem ?_⟩
  rw [localTriv_associatedMk_self, VectorBundleCore.localTriv_apply, hx]
  exact Prod.ext rfl ((hp.associatedCore ρ).coordChange_self _ x hmem w).symm

/-- The pair `(y, f y)`, for the equivariant function `f` attached to a section `σ`, represents
the value of `σ` at `p y`. -/
theorem associatedMk_associatedSectionEquiv (σ : ∀ x, (hp.associatedCore ρ).Fiber x) (y : E) :
    hp.associatedMk ρ (y, (hp.associatedSectionEquiv ρ σ : E → F) y) = ⟨p y, σ (p y)⟩ := by
  have hy := hp.mem_associatedCore_baseSet_self ρ y
  refine hp.eq_of_localTriv_eq ρ hy hy ?_
  rw [localTriv_associatedMk_self, associatedSectionEquiv_apply_coe]
  rfl

/-- **The map `E × F → E ×_G F` is a local homeomorphism.** Near `(e, v)`, it is the inverse of
the chart through `e` composed with `p × id`, restricted to the image of the local section of `p`
through `e`. -/
theorem isLocalHomeomorph_associatedMk : IsLocalHomeomorph (hp.associatedMk ρ) := by
  refine IsLocalHomeomorph.mk _ fun q ↦ ?_
  set s := hp.isLocalHomeomorph.localInverseAt q.1
  set T := (hp.associatedCore ρ).localTriv q.1
  refine ⟨(s.symm.prod (OpenPartialHomeomorph.refl F)).trans T.toOpenPartialHomeomorph.symm,
    ?_, ?_⟩
  · refine ⟨⟨hp.isLocalHomeomorph.self_mem_localInverseAt_target, trivial⟩, (T.mem_target).2 ?_⟩
    simp only [s, OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.prod_apply,
      IsLocalHomeomorph.localInverseAt_symm]
    exact hp.mem_associatedCore_baseSet_self ρ q.1
  · rintro ⟨y, v⟩ ⟨⟨hy, -⟩, -⟩
    have hy' : y ∈ s.target := hy
    have hsrc : hp.associatedMk ρ (y, v) ∈ T.source := by
      have hs : p y ∈ s.source := by
        simpa only [s, IsLocalHomeomorph.localInverseAt_symm] using s.map_target hy'
      exact hs
    simp only [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.prod_apply,
      OpenPartialHomeomorph.refl_apply, id_eq, Function.comp_apply, s,
      IsLocalHomeomorph.localInverseAt_symm]
    rw [← hp.localTriv_associatedMk_of_mem_target ρ hy' v]
    exact (T.toOpenPartialHomeomorph.left_inv hsrc).symm

/-- **The total space of `E ×_G F` is the quotient of `E × F`** by `g • (y, v) = (g • y, ρ g v)`:
the map `E × F → E ×_G F` is an open quotient map, whose fibres are the orbits by
`IsQuotientCoveringMap.associatedMk_eq_associatedMk_iff`. -/
theorem isOpenQuotientMap_associatedMk : IsOpenQuotientMap (hp.associatedMk ρ) :=
  ⟨hp.associatedMk_surjective ρ, (hp.isLocalHomeomorph_associatedMk ρ).continuous,
    (hp.isLocalHomeomorph_associatedMk ρ).isOpenMap⟩

/-- The relation on `E × F` identifying `(y, v)` with `(g • y, ρ g v)` for every `g : G`. Its
quotient is the total space of the associated bundle
(`IsQuotientCoveringMap.associatedQuotientHomeomorph`). -/
def associatedOrbitRel : Setoid (E × F) where
  r q q' := ∃ g : G, g • q.1 = q'.1 ∧ (ρ g : F →L[𝕜] F) q.2 = q'.2
  -- By `associatedMk_eq_associatedMk_iff`, the relation says that both pairs represent the same
  -- point.
  iseqv.refl _ := (hp.associatedMk_eq_associatedMk_iff ρ).1 rfl
  iseqv.symm h := (hp.associatedMk_eq_associatedMk_iff ρ).1
    ((hp.associatedMk_eq_associatedMk_iff ρ).2 h).symm
  iseqv.trans h h' := (hp.associatedMk_eq_associatedMk_iff ρ).1
    (((hp.associatedMk_eq_associatedMk_iff ρ).2 h).trans
      ((hp.associatedMk_eq_associatedMk_iff ρ).2 h'))

/-- Two pairs are related by `associatedOrbitRel` when they differ by the action of an element of
`G`. -/
theorem associatedOrbitRel_iff {q q' : E × F} :
    hp.associatedOrbitRel ρ q q' ↔ ∃ g : G, g • q.1 = q'.1 ∧ (ρ g : F →L[𝕜] F) q.2 = q'.2 :=
  Iff.rfl

/-- The orbit relation is the kernel of `E × F → E ×_G F`. -/
theorem associatedOrbitRel_eq_ker : hp.associatedOrbitRel ρ = Setoid.ker (hp.associatedMk ρ) :=
  Setoid.ext fun _ _ ↦ (hp.associatedMk_eq_associatedMk_iff ρ).symm

/-- The total space of the associated bundle is homeomorphic to the quotient of `E × F` by the
orbit relation `(y, v) ∼ (g • y, ρ g v)`; the homeomorphism sends the class of `(y, v)` to the
point it represents (`IsQuotientCoveringMap.associatedQuotientHomeomorph_mk`). -/
noncomputable def associatedQuotientHomeomorph :
    Quotient (hp.associatedOrbitRel ρ) ≃ₜ (hp.associatedCore ρ).TotalSpace :=
  (Homeomorph.Quotient.congrRight (Setoid.ext_iff.1 (hp.associatedOrbitRel_eq_ker ρ))).trans
    (Topology.IsQuotientMap.homeomorph
      (f := ⟨_, (hp.isLocalHomeomorph_associatedMk ρ).continuous⟩)
      (hp.isOpenQuotientMap_associatedMk ρ).isQuotientMap)

/-- The homeomorphism `associatedQuotientHomeomorph` sends the class of `(y, v)` to the point it
represents. -/
@[simp]
theorem associatedQuotientHomeomorph_mk (q : E × F) :
    hp.associatedQuotientHomeomorph ρ (Quotient.mk _ q) = hp.associatedMk ρ q :=
  (rfl)

end IsQuotientCoveringMap
