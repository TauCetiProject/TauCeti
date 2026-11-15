/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.Monoidal

/-!
# Vector bundles associated with representations of a deck group

Let `p : E → X` present `X` as the quotient of `E` by a group `G` in the sense of Mathlib's
`IsQuotientCoveringMap p G`, and let `ρ : G →* (F →L[𝕜] F)ˣ` be a representation of `G` on a
normed space `F`. The associated vector bundle `E ×_G F` over `X` is the quotient of `E × F` by
`g • (y, v) = (g • y, ρ g v)`. Rather than forming that quotient, this file builds the bundle
from its transition functions, as a Mathlib `VectorBundleCore`,
`IsQuotientCoveringMap.associatedCore`.

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
Choosing a preimage over each base point presents the same line bundle as a point-indexed
rank-one core `IsQuotientCoveringMap.characterFiniteRankCore χ` in `TauCeti.FiniteRankBundleCore`,
homeomorphic on total spaces via `IsQuotientCoveringMap.characterFiniteRankCoreHomeomorph` and
compatible with the monoidal tensor product:
* `IsQuotientCoveringMap.characterFiniteRankCoreOneIso`: `L_1 ≅ 𝟙_`;
* `IsQuotientCoveringMap.characterFiniteRankCoreMulIso`: `L_χ ⊗ L_ψ ≅ L_{χ * ψ}`;
* `IsQuotientCoveringMap.characterFiniteRankCoreTensorPowerIso`: `L_χ^{\otimes m} ≅ L_{χ ^ m}`.

## Main definitions

* `IsQuotientCoveringMap.deckChange`: the deck transformation between two local sections.
* `IsQuotientCoveringMap.associatedCore`: the vector bundle associated with a representation.
* `IsQuotientCoveringMap.characterCore`: the line bundle associated with a character.
* `IsQuotientCoveringMap.associatedSectionEquiv`: sections of the associated bundle are
  equivariant functions upstairs.
* `IsQuotientCoveringMap.characterFiniteRankCore`: point-indexed rank-one core of a character,
  together with its monoidal multiplicativity and tensor-power isomorphisms.

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

end DeckChange

/-! ### The associated vector bundle -/

section AssociatedCore

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

/-- Near `y`, the coordinates in the chart through `y`, pulled back along `p`, agree with
the equivariant function of the section. -/
theorem eventuallyEq_localTriv_associatedSectionEquiv
    (σ : ∀ x, (hp.associatedCore ρ).Fiber x) (y : E) :
    ((fun x ↦ ((hp.associatedCore ρ).localTriv y ⟨x, σ x⟩).2) ∘ p) =ᶠ[𝓝 y]
      (hp.associatedSectionEquiv ρ σ : E → F) := by
  set s := hp.isLocalHomeomorph.localInverseAt y
  filter_upwards [s.open_target.mem_nhds (hp.isLocalHomeomorph.self_mem_localInverseAt_target)]
    with z hz
  have hsource := s.map_target hz
  have hinv := s.right_inv hz
  rw [hp.isLocalHomeomorph.localInverseAt_symm] at hsource hinv
  rw [Function.comp_apply, localTriv_associatedCore_apply_snd _ _ _ hsource, hinv]

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

end AssociatedCore

/-! ### Point-indexed finite-rank core of a character and tensor multiplicativity -/

section CharacterFiniteRank

open CategoryTheory MonoidalCategory TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The point-indexed rank-one vector-bundle core over `X` associated with a character
`χ : G →* 𝕜ˣ` of the deck group. Its chart at `x : X` is the chart of `hp.characterCore χ`
through `Function.surjInv hp.surjective x`, with model fibre `Fin 1 → 𝕜`. -/
@[expose]
noncomputable def characterFiniteRankCore (χ : G →* 𝕜ˣ) : FiniteRankBundleCore 𝕜 X where
  rank := 1
  core :=
    { baseSet x :=
        (hp.isLocalHomeomorph.localInverseAt (Function.surjInv hp.surjective x)).source
      isOpen_baseSet x :=
        (hp.isLocalHomeomorph.localInverseAt (Function.surjInv hp.surjective x)).open_source
      indexAt := id
      mem_baseSet_at x := by
        simpa only [id_eq, Function.surjInv_eq hp.surjective x] using
          hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source
            (x := Function.surjInv hp.surjective x)
      coordChange i j x :=
        (χ (hp.deckChange (Function.surjInv hp.surjective i)
          (Function.surjInv hp.surjective j) x) : 𝕜) •
          ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜)
      coordChange_self i x hx v := by
        rw [hp.deckChange_self hx, map_one, Units.val_one, one_smul,
          ContinuousLinearMap.id_apply]
      continuousOn_coordChange i j x hx :=
        ((continuousAt_const : ContinuousAt (fun _ : X ↦
          (χ (hp.deckChange (Function.surjInv hp.surjective i)
            (Function.surjInv hp.surjective j) x) : 𝕜) •
            ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜)) x).congr (by
          filter_upwards [hp.eventually_deckChange_eq hx] with x' hx'
          rw [hx'])).continuousWithinAt
      coordChange_comp i j k x hx v := by
        simp only [smul_apply, ContinuousLinearMap.id_apply, smul_smul]
        rw [← Units.val_mul, ← map_mul, hp.deckChange_mul_deckChange hx] }
  indexAt_eq _ := rfl

@[simp] theorem rank_characterFiniteRankCore (χ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ).rank = 1 := (rfl)

theorem characterFiniteRankCore_baseSet (χ : G →* 𝕜ˣ) (x : X) :
    (hp.characterFiniteRankCore χ).core.baseSet x =
      (hp.isLocalHomeomorph.localInverseAt (Function.surjInv hp.surjective x)).source := (rfl)

@[simp] theorem characterFiniteRankCore_localTriv_baseSet (χ : G →* 𝕜ˣ) (x : X) :
    ((hp.characterFiniteRankCore χ).core.localTriv x).baseSet =
      (hp.isLocalHomeomorph.localInverseAt (Function.surjInv hp.surjective x)).source := (rfl)

@[simp] theorem characterFiniteRankCore_coordChange (χ : G →* 𝕜ˣ) (i j x : X) :
    (hp.characterFiniteRankCore χ).core.coordChange i j x =
      (χ (hp.deckChange (Function.surjInv hp.surjective i)
        (Function.surjInv hp.surjective j) x) : 𝕜) •
        ContinuousLinearMap.id 𝕜 (Fin (hp.characterFiniteRankCore χ).rank → 𝕜) := (rfl)

/-- The transition functions of `hp.characterFiniteRankCore χ` are locally constant on chart
overlaps. -/
theorem eventually_characterFiniteRankCore_coordChange_eq (χ : G →* 𝕜ˣ) {i j x : X}
    (hx : x ∈ (hp.characterFiniteRankCore χ).core.baseSet i ∩
      (hp.characterFiniteRankCore χ).core.baseSet j) :
    ∀ᶠ x' in 𝓝 x, (hp.characterFiniteRankCore χ).core.coordChange i j x' =
      (hp.characterFiniteRankCore χ).core.coordChange i j x := by
  filter_upwards [hp.eventually_deckChange_eq hx] with x' hx'
  rw [characterFiniteRankCore_coordChange, characterFiniteRankCore_coordChange, hx']

/-- In preferred charts at `b : X`, evaluating a fibre vector of `hp.characterFiniteRankCore χ` at
its unique coordinate gives the fibre coordinate in `hp.characterCore χ`. -/
theorem trivializationAt_characterCore_snd (χ : G →* 𝕜ˣ) (b : X)
    (p₀ : (hp.characterFiniteRankCore χ).core.TotalSpace) :
    (trivializationAt 𝕜 (hp.characterCore χ).Fiber b
      ⟨p₀.1, (p₀.2 : Fin (hp.characterFiniteRankCore χ).rank → 𝕜) ⟨0, by simp⟩⟩).2 =
      (trivializationAt (Fin (hp.characterFiniteRankCore χ).rank → 𝕜)
        (hp.characterFiniteRankCore χ).core.Fiber b p₀).2 ⟨0, by simp⟩ := by
  let k₀ : Fin (hp.characterFiniteRankCore χ).rank := ⟨0, by simp⟩
  let v : Fin (hp.characterFiniteRankCore χ).rank → 𝕜 := p₀.2
  rw [(hp.characterCore χ).trivializationAt, ← (hp.characterCore χ).localTrivAt_def,
    (hp.characterFiniteRankCore χ).trivializationAt_core]
  change ((hp.characterCore χ).coordChange ((hp.characterCore χ).indexAt p₀.1)
      ((hp.characterCore χ).indexAt b) p₀.1 (v k₀)) =
    ((hp.characterFiniteRankCore χ).core.coordChange p₀.1 b p₀.1 v) k₀
  rw [characterCore_coordChange_apply, characterFiniteRankCore_coordChange]
  rfl

/-- In preferred charts at `b : X`, the constant coordinate vector of `q.2` in
`hp.characterFiniteRankCore χ` agrees in every coordinate with `q` in `hp.characterCore χ`. -/
theorem trivializationAt_characterFiniteRankCore_snd (χ : G →* 𝕜ˣ) (b : X)
    (q : (hp.characterCore χ).TotalSpace) (k : Fin (hp.characterFiniteRankCore χ).rank) :
    (trivializationAt (Fin (hp.characterFiniteRankCore χ).rank → 𝕜)
      (hp.characterFiniteRankCore χ).core.Fiber b
        ⟨q.1, (fun _ ↦ (q.2 : 𝕜) : Fin (hp.characterFiniteRankCore χ).rank → 𝕜)⟩).2 k =
      (trivializationAt 𝕜 (hp.characterCore χ).Fiber b q).2 := by
  rcases q with ⟨x, c⟩
  obtain rfl : k = ⟨0, by simp⟩ := Fin.ext (Nat.lt_one_iff.mp k.2)
  exact (hp.trivializationAt_characterCore_snd χ b ⟨x, fun _ ↦ (c : 𝕜)⟩).symm

/-- Total-space homeomorphism identifying `hp.characterFiniteRankCore χ` with
`hp.characterCore χ` over `X` by evaluating `Fin 1 → 𝕜` at its unique coordinate. -/
noncomputable def characterFiniteRankCoreHomeomorph (χ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ).core.TotalSpace ≃ₜ (hp.characterCore χ).TotalSpace where
  toFun p₀ := ⟨p₀.1, (p₀.2 : Fin (hp.characterFiniteRankCore χ).rank → 𝕜) ⟨0, by simp⟩⟩
  invFun q := ⟨q.1, (fun _ ↦ (q.2 : 𝕜) : Fin (hp.characterFiniteRankCore χ).rank → 𝕜)⟩
  left_inv p₀ := by
    rcases p₀ with ⟨x, v⟩
    refine TotalSpace.ext rfl (heq_of_eq ?_)
    let w : Fin (hp.characterFiniteRankCore χ).rank → 𝕜 := v
    change (fun _ : Fin (hp.characterFiniteRankCore χ).rank ↦ w ⟨0, by simp⟩) = w
    ext k; rw [show k = ⟨0, by simp⟩ from Fin.ext (Nat.lt_one_iff.mp k.2)]
  right_inv := fun ⟨_, _⟩ ↦ rfl
  continuous_toFun := continuous_iff_continuousAt.2 fun p₀ ↦ by
    let k₀ : Fin (hp.characterFiniteRankCore χ).rank := ⟨0, by simp⟩
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(FiberBundle.continuous_proj _ _).continuousAt,
      ((continuous_apply k₀).continuousAt.comp
        (((FiberBundle.continuousAt_totalSpace _ id).1 continuousAt_id).2)).congr
        (Eventually.of_forall fun z ↦ (hp.trivializationAt_characterCore_snd χ p₀.1 z).symm)⟩
  continuous_invFun := continuous_iff_continuousAt.2 fun q ↦ by
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(FiberBundle.continuous_proj _ _).continuousAt, continuousAt_pi.2 fun k ↦
      (((FiberBundle.continuousAt_totalSpace _ id).1 continuousAt_id).2).congr
        (Eventually.of_forall fun z ↦
          (hp.trivializationAt_characterFiniteRankCore_snd χ q.1 z k).symm)⟩

@[simp] theorem characterFiniteRankCoreHomeomorph_apply (χ : G →* 𝕜ˣ)
    (p₀ : (hp.characterFiniteRankCore χ).core.TotalSpace) :
    hp.characterFiniteRankCoreHomeomorph χ p₀ =
      ⟨p₀.1, (p₀.2 : Fin (hp.characterFiniteRankCore χ).rank → 𝕜) ⟨0, by simp⟩⟩ := (rfl)

@[simp] theorem characterFiniteRankCoreHomeomorph_symm_apply (χ : G →* 𝕜ˣ)
    (q : (hp.characterCore χ).TotalSpace) :
    (hp.characterFiniteRankCoreHomeomorph χ).symm q =
      ⟨q.1, (fun _ ↦ (q.2 : 𝕜) : Fin (hp.characterFiniteRankCore χ).rank → 𝕜)⟩ := (rfl)

/-- Equality of characters induces a canonical isomorphism between their point-indexed cores. -/
noncomputable def characterFiniteRankCoreCongr {χ ψ : G →* 𝕜ˣ} (h : χ = ψ) :
    hp.characterFiniteRankCore χ ≅ hp.characterFiniteRankCore ψ :=
  eqToIso (congrArg hp.characterFiniteRankCore h)

/-- The point-indexed core of the trivial character `1 : G →* 𝕜ˣ` is canonically isomorphic in
`FiniteRankBundleCore 𝕜 X` to the monoidal unit. -/
noncomputable def characterFiniteRankCoreOneIso :
    hp.characterFiniteRankCore (1 : G →* 𝕜ˣ) ≅ 𝟙_ (FiniteRankBundleCore 𝕜 X) :=
  FiniteRankBundleCore.isoTensorUnitOfCoordChangeEqId (hp.characterFiniteRankCore 1)
    (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜)) fun i j x _ _ ↦ by
      rw [characterFiniteRankCore_coordChange, MonoidHom.one_apply, Units.val_one, one_smul]

/-- Coordinate identification between the tensor-product fibre of `L_χ ⊗ L_ψ` and that of
`L_{χ * ψ}`. -/
noncomputable abbrev characterMulFibreEquiv (χ ψ : G →* 𝕜ˣ) :
    (Fin ((hp.characterFiniteRankCore χ).rank * (hp.characterFiniteRankCore ψ).rank) → 𝕜) ≃L[𝕜]
      (Fin (hp.characterFiniteRankCore (χ * ψ)).rank → 𝕜) :=
  ContinuousLinearEquiv.piCongrLeft 𝕜
    (fun _ : Fin (hp.characterFiniteRankCore (χ * ψ)).rank ↦ 𝕜) (finCongr rfl)

/-- Coordinate reindexing intertwines the Kronecker product of transitions of `L_χ` and `L_ψ`
with the transitions of `L_{χ * ψ}`. -/
theorem characterFiniteRankCore_mul_intertwine (χ ψ : G →* 𝕜ˣ) (i j x : X) :
    (hp.characterMulFibreEquiv χ ψ).toContinuousLinearMap.comp
      (((hp.characterFiniteRankCore χ).core.coordChange i j x).kronecker
        ((hp.characterFiniteRankCore ψ).core.coordChange i j x)) =
    ((hp.characterFiniteRankCore (χ * ψ)).core.coordChange i j x).comp
      (hp.characterMulFibreEquiv χ ψ).toContinuousLinearMap := by
  have hχ := hp.characterFiniteRankCore_coordChange χ i j x
  have hψ := hp.characterFiniteRankCore_coordChange ψ i j x
  have hχψ := hp.characterFiniteRankCore_coordChange (χ * ψ) i j x
  rw [MonoidHom.mul_apply, Units.val_mul] at hχψ
  change (hp.characterMulFibreEquiv χ ψ : _ →L[𝕜] _).comp
      (((hp.characterFiniteRankCore χ).core.coordChange i j x).kronecker
        ((hp.characterFiniteRankCore ψ).core.coordChange i j x)) =
    ((hp.characterFiniteRankCore (χ * ψ)).core.coordChange i j x).comp
      (hp.characterMulFibreEquiv χ ψ : _ →L[𝕜] _)
  rw [hχ, hψ, hχψ, ContinuousLinearMap.smul_kronecker, ContinuousLinearMap.kronecker_smul,
    smul_smul, ContinuousLinearMap.id_kronecker_id, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]

/-- **Tensor multiplicativity of character line bundles.** For characters `χ, ψ : G →* 𝕜ˣ` of the
deck group, `L_χ ⊗ L_ψ` is canonically isomorphic in `FiniteRankBundleCore 𝕜 X` to `L_{χ * ψ}`. -/
noncomputable def characterFiniteRankCoreMulIso (χ ψ : G →* 𝕜ˣ) :
    hp.characterFiniteRankCore χ ⊗ hp.characterFiniteRankCore ψ ≅
      hp.characterFiniteRankCore (χ * ψ) :=
  FiniteRankBundleCore.constIso (fun _ ↦ Set.inter_self _) (hp.characterMulFibreEquiv χ ψ)
    fun i j x _ _ ↦ hp.characterFiniteRankCore_mul_intertwine χ ψ i j x

/-- **Tensor powers of a character line bundle.** For every `m : ℕ`, the `m`-th tensor power of
`hp.characterFiniteRankCore χ` is canonically isomorphic to `hp.characterFiniteRankCore (χ ^ m)`. -/
noncomputable def characterFiniteRankCoreTensorPowerIso (χ : G →* 𝕜ˣ) :
    ∀ m : ℕ, (hp.characterFiniteRankCore χ).tensorPower m ≅
      hp.characterFiniteRankCore (χ ^ m)
  | 0 => hp.characterFiniteRankCoreOneIso.symm ≪≫
      hp.characterFiniteRankCoreCongr (pow_zero χ).symm
  | m + 1 => (characterFiniteRankCoreTensorPowerIso χ m ⊗ᵢ
        Iso.refl (hp.characterFiniteRankCore χ)) ≪≫
      hp.characterFiniteRankCoreMulIso (χ ^ m) χ ≪≫
      hp.characterFiniteRankCoreCongr (pow_succ χ m).symm

end CharacterFiniteRank

end IsQuotientCoveringMap
