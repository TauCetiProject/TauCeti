/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.Monoidal
public import TauCeti.Topology.VectorBundle.FiniteRank.Scalar

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

Choosing a preimage over each base point presents the associated bundle for a finite-rank
representation `ρ : G →* ((Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))ˣ` as a point-indexed core
`IsQuotientCoveringMap.associatedFiniteRankCore ρ` in `TauCeti.FiniteRankBundleCore`. For a
character `χ : G →* 𝕜ˣ` the associated bundle is the line bundle
`IsQuotientCoveringMap.characterCore χ`, whose transitions multiply by `χ (deckChange e e' x)`,
and its point-indexed rank-one specialization `IsQuotientCoveringMap.characterFiniteRankCore χ` is
homeomorphic on total spaces via `IsQuotientCoveringMap.characterFiniteRankCoreHomeomorph`,
canonically isomorphic to the generic scalar presentation
`TauCeti.FiniteRankBundleCore.ofScalarCore (hp.characterCore χ)` via
`IsQuotientCoveringMap.ofScalarCoreCharacterCoreIso`, and compatible with the monoidal tensor
product and `TauCeti.tensorPow`:
* `IsQuotientCoveringMap.characterFiniteRankCoreOneIso`: `L_1 ≅ 𝟙_`;
* `IsQuotientCoveringMap.characterFiniteRankCoreMulIso`: `L_χ ⊗ L_ψ ≅ L_{χ * ψ}`;
* `IsQuotientCoveringMap.characterFiniteRankCoreTensorPowerIso`: `L_χ^{\otimes m} ≅ L_{χ ^ m}`.

## Main definitions

* `IsQuotientCoveringMap.deckChange`: the deck transformation between two local sections.
* `IsQuotientCoveringMap.associatedCore`: the vector bundle associated with a representation.
* `IsQuotientCoveringMap.characterCore`: the line bundle associated with a character.
* `IsQuotientCoveringMap.associatedSectionEquiv`: sections of the associated bundle are
  equivariant functions upstairs.
* `IsQuotientCoveringMap.associatedFiniteRankCore`: point-indexed finite-rank core of a
  representation on `Fin r → 𝕜`.
* `IsQuotientCoveringMap.characterFiniteRankCore`: point-indexed rank-one core of a character,
  together with `IsQuotientCoveringMap.ofScalarCoreCharacterCoreIso` and its monoidal
  multiplicativity and tensor-power isomorphisms.
* `IsQuotientCoveringMap.characterCoreHomEquiv`: twisting cocycle morphisms between scalar
  character cores preserves all fibre maps, without completeness assumptions.

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

/-- Reversing the order of two local sections over a common point of their domains inverts the deck
transformation between them. -/
theorem deckChange_inv (h : x ∈ (hp.isLocalHomeomorph.localInverseAt e).source ∩
      (hp.isLocalHomeomorph.localInverseAt e').source) :
    hp.deckChange e' e x = (hp.deckChange e e' x)⁻¹ :=
  mul_eq_one_iff_eq_inv.1 <| by
    rw [hp.deckChange_mul_deckChange ⟨h, h.1⟩, hp.deckChange_self h.1]

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

/-- The chart domain of `hp.characterCore χ` through `e` is the domain of the local section of `p`
through `e`, independently of `χ`. -/
theorem characterCore_baseSet (χ : G →* 𝕜ˣ) (e : E) :
    (hp.characterCore χ).baseSet e = (hp.isLocalHomeomorph.localInverseAt e).source := by
  rw [characterCore_def, associatedCore_baseSet]

@[simp]
theorem characterCore_localTriv_baseSet (χ : G →* 𝕜ˣ) (e : E) :
    ((hp.characterCore χ).localTriv e).baseSet =
      (hp.isLocalHomeomorph.localInverseAt e).source := by
  rw [characterCore_def, associatedCore_localTriv_baseSet]

/-- The preferred chart index of `hp.characterCore χ` at `x` is `Function.surjInv hp.surjective x`,
independently of `χ`. -/
@[simp]
theorem characterCore_indexAt (χ : G →* 𝕜ˣ) (x : X) :
    (hp.characterCore χ).indexAt x = Function.surjInv hp.surjective x := by
  rw [characterCore_def, associatedCore_indexAt]

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

/-! ### Point-indexed finite-rank cores of representations and tensor multiplicativity -/

section CharacterFiniteRank

open CategoryTheory MonoidalCategory TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The point-indexed finite-rank vector-bundle core over `X` associated with a representation
`ρ : G →* ((Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))ˣ` of the deck group. Its chart at `x : X` is the chart
of `hp.associatedCore ρ` through `Function.surjInv hp.surjective x`. -/
-- Exposed so the rank `r` and coordinate model fibre `Fin r → 𝕜` reduce definitionally in
-- dependent fibre statements.
@[expose]
noncomputable def associatedFiniteRankCore {r : ℕ}
    (ρ : G →* ((Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))ˣ) : FiniteRankBundleCore 𝕜 X where
  rank := r
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
        ρ (hp.deckChange (Function.surjInv hp.surjective i)
          (Function.surjInv hp.surjective j) x)
      coordChange_self i x hx v := by
        rw [hp.deckChange_self hx, map_one, Units.val_one, one_apply_eq_self]
      continuousOn_coordChange i j x hx :=
        ((continuousAt_const : ContinuousAt (fun _ : X ↦
          (ρ (hp.deckChange (Function.surjInv hp.surjective i)
            (Function.surjInv hp.surjective j) x) : (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))) x).congr (by
          filter_upwards [hp.eventually_deckChange_eq hx] with x' hx'
          rw [hx'])).continuousWithinAt
      coordChange_comp i j k x hx v := by
        rw [← hp.deckChange_mul_deckChange hx, map_mul, Units.val_mul, mul_apply_eq_comp] }
  indexAt_eq _ := rfl

@[simp] theorem rank_associatedFiniteRankCore {r : ℕ}
    (ρ : G →* ((Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))ˣ) :
    (hp.associatedFiniteRankCore ρ).rank = r := (rfl)

theorem associatedFiniteRankCore_baseSet {r : ℕ}
    (ρ : G →* ((Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))ˣ) (x : X) :
    (hp.associatedFiniteRankCore ρ).core.baseSet x =
      (hp.isLocalHomeomorph.localInverseAt (Function.surjInv hp.surjective x)).source := (rfl)

@[simp] theorem associatedFiniteRankCore_localTriv_baseSet {r : ℕ}
    (ρ : G →* ((Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))ˣ) (x : X) :
    ((hp.associatedFiniteRankCore ρ).core.localTriv x).baseSet =
      (hp.isLocalHomeomorph.localInverseAt (Function.surjInv hp.surjective x)).source := (rfl)

@[simp] theorem associatedFiniteRankCore_coordChange {r : ℕ}
    (ρ : G →* ((Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))ˣ) (i j x : X) :
    (hp.associatedFiniteRankCore ρ).core.coordChange i j x =
      (ρ (hp.deckChange (Function.surjInv hp.surjective i)
        (Function.surjInv hp.surjective j) x) : (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜)) := (rfl)

/-- The transition functions of `hp.associatedFiniteRankCore ρ` are locally constant on chart
overlaps. -/
theorem eventually_associatedFiniteRankCore_coordChange_eq {r : ℕ}
    (ρ : G →* ((Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))ˣ) {i j x : X}
    (hx : x ∈ (hp.associatedFiniteRankCore ρ).core.baseSet i ∩
      (hp.associatedFiniteRankCore ρ).core.baseSet j) :
    ∀ᶠ x' in 𝓝 x, (hp.associatedFiniteRankCore ρ).core.coordChange i j x' =
      (hp.associatedFiniteRankCore ρ).core.coordChange i j x := by
  rw [associatedFiniteRankCore_baseSet, associatedFiniteRankCore_baseSet] at hx
  filter_upwards [hp.eventually_deckChange_eq hx] with x' hx'
  rw [associatedFiniteRankCore_coordChange, associatedFiniteRankCore_coordChange, hx']

/-- The point-indexed rank-one vector-bundle core over `X` associated with a character
`χ : G →* 𝕜ˣ` of the deck group. Its chart at `x : X` is the chart of `hp.characterCore χ`
through `Function.surjInv hp.surjective x`, with model fibre `Fin 1 → 𝕜`. -/
-- Exposed so the rank `1` and coordinate model fibre `Fin 1 → 𝕜` reduce definitionally in
-- dependent fibre statements.
@[expose]
noncomputable def characterFiniteRankCore (χ : G →* 𝕜ˣ) : FiniteRankBundleCore 𝕜 X :=
  hp.associatedFiniteRankCore
    ((Units.map (algebraMap 𝕜 ((Fin 1 → 𝕜) →L[𝕜] (Fin 1 → 𝕜))).toMonoidHom).comp χ)

/-- The point-indexed core of a character is the point-indexed associated core for scalar
multiplication on `Fin 1 → 𝕜`. -/
theorem characterFiniteRankCore_def (χ : G →* 𝕜ˣ) :
    hp.characterFiniteRankCore χ =
      hp.associatedFiniteRankCore
        ((Units.map (algebraMap 𝕜 ((Fin 1 → 𝕜) →L[𝕜] (Fin 1 → 𝕜))).toMonoidHom).comp χ) :=
  (rfl)

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
        ContinuousLinearMap.id 𝕜 (Fin (hp.characterFiniteRankCore χ).rank → 𝕜) := by
  rw [characterFiniteRankCore_def, associatedFiniteRankCore_coordChange]
  simp only [MonoidHom.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.one_def]
  rfl

/-- The transition functions of `hp.characterFiniteRankCore χ` are locally constant on chart
overlaps. -/
theorem eventually_characterFiniteRankCore_coordChange_eq (χ : G →* 𝕜ˣ) {i j x : X}
    (hx : x ∈ (hp.characterFiniteRankCore χ).core.baseSet i ∩
      (hp.characterFiniteRankCore χ).core.baseSet j) :
    ∀ᶠ x' in 𝓝 x, (hp.characterFiniteRankCore χ).core.coordChange i j x' =
      (hp.characterFiniteRankCore χ).core.coordChange i j x :=
  hp.eventually_associatedFiniteRankCore_coordChange_eq _ hx

/-- In preferred charts at `b : X`, evaluating a fibre vector of `hp.characterFiniteRankCore χ` at
its unique coordinate gives the fibre coordinate in `hp.characterCore χ`. -/
theorem trivializationAt_characterCore_snd (χ : G →* 𝕜ˣ) (b : X)
    (p₀ : (hp.characterFiniteRankCore χ).core.TotalSpace) :
    (trivializationAt 𝕜 (hp.characterCore χ).Fiber b
      ⟨p₀.proj, (p₀.snd : Fin (hp.characterFiniteRankCore χ).rank → 𝕜) ⟨0, by simp⟩⟩).2 =
      (trivializationAt (Fin (hp.characterFiniteRankCore χ).rank → 𝕜)
        (hp.characterFiniteRankCore χ).core.Fiber b p₀).2 ⟨0, by simp⟩ := by
  rw [(hp.characterCore χ).trivializationAt, ← (hp.characterCore χ).localTrivAt_def,
    (hp.characterFiniteRankCore χ).trivializationAt_core, VectorBundleCore.localTriv_apply,
    VectorBundleCore.localTriv_apply, (hp.characterFiniteRankCore χ).indexAt_eq,
    characterCore_coordChange_apply, characterFiniteRankCore_coordChange, characterCore_def,
    associatedCore_indexAt, associatedCore_indexAt]
  -- Reconcile `Fiber p₀.1` with the model fibre `Fin 1 → 𝕜` under scalar multiplication.
  rfl

/-- In preferred charts at `b : X`, the constant coordinate vector of `q.2` in
`hp.characterFiniteRankCore χ` agrees in every coordinate with `q` in `hp.characterCore χ`. -/
theorem trivializationAt_characterFiniteRankCore_snd (χ : G →* 𝕜ˣ) (b : X)
    (q : (hp.characterCore χ).TotalSpace) (k : Fin (hp.characterFiniteRankCore χ).rank) :
    (trivializationAt (Fin (hp.characterFiniteRankCore χ).rank → 𝕜)
      (hp.characterFiniteRankCore χ).core.Fiber b
        ⟨q.proj, (fun _ ↦ (q.snd : 𝕜) : Fin (hp.characterFiniteRankCore χ).rank → 𝕜)⟩).2 k =
      (trivializationAt 𝕜 (hp.characterCore χ).Fiber b q).2 := by
  rcases q with ⟨x, c⟩
  obtain rfl : k = ⟨0, by simp⟩ := Fin.ext (Nat.lt_one_iff.mp k.isLt)
  exact (hp.trivializationAt_characterCore_snd χ b ⟨x, fun _ ↦ (c : 𝕜)⟩).symm

/-- Total-space homeomorphism identifying `hp.characterFiniteRankCore χ` with
`hp.characterCore χ` over `X` by evaluating `Fin 1 → 𝕜` at its unique coordinate. -/
noncomputable def characterFiniteRankCoreHomeomorph (χ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ).core.TotalSpace ≃ₜ (hp.characterCore χ).TotalSpace where
  toFun p₀ := ⟨p₀.proj, (p₀.snd : Fin (hp.characterFiniteRankCore χ).rank → 𝕜) ⟨0, by simp⟩⟩
  invFun q := ⟨q.proj, (fun _ ↦ (q.snd : 𝕜) : Fin (hp.characterFiniteRankCore χ).rank → 𝕜)⟩
  left_inv p₀ := by
    rcases p₀ with ⟨x, v⟩
    refine TotalSpace.ext rfl (heq_of_eq ?_)
    exact funext fun k ↦ by
      obtain rfl : k = ⟨0, by simp⟩ := Fin.ext (Nat.lt_one_iff.mp k.isLt)
      rfl
  right_inv := fun ⟨_, _⟩ ↦ rfl
  continuous_toFun := continuous_iff_continuousAt.2 fun p₀ ↦ by
    let k₀ : Fin (hp.characterFiniteRankCore χ).rank := ⟨0, by simp⟩
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(FiberBundle.continuous_proj _ _).continuousAt,
      ((continuous_apply k₀).continuousAt.comp
        (((FiberBundle.continuousAt_totalSpace _ id).1 continuousAt_id).2)).congr
        (Eventually.of_forall fun z ↦ (hp.trivializationAt_characterCore_snd χ p₀.proj z).symm)⟩
  continuous_invFun := continuous_iff_continuousAt.2 fun q ↦ by
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(FiberBundle.continuous_proj _ _).continuousAt, continuousAt_pi.2 fun k ↦
      (((FiberBundle.continuousAt_totalSpace _ id).1 continuousAt_id).2).congr
        (Eventually.of_forall fun z ↦
          (hp.trivializationAt_characterFiniteRankCore_snd χ q.proj z k).symm)⟩

@[simp] theorem characterFiniteRankCoreHomeomorph_apply (χ : G →* 𝕜ˣ)
    (p₀ : (hp.characterFiniteRankCore χ).core.TotalSpace) :
    hp.characterFiniteRankCoreHomeomorph χ p₀ =
      ⟨p₀.proj, (p₀.snd : Fin (hp.characterFiniteRankCore χ).rank → 𝕜) ⟨0, by simp⟩⟩ := (rfl)

@[simp] theorem characterFiniteRankCoreHomeomorph_symm_apply (χ : G →* 𝕜ˣ)
    (q : (hp.characterCore χ).TotalSpace) :
    (hp.characterFiniteRankCoreHomeomorph χ).symm q =
      ⟨q.proj, (fun _ ↦ (q.snd : 𝕜) : Fin (hp.characterFiniteRankCore χ).rank → 𝕜)⟩ := (rfl)

/-- Chart domains of `FiniteRankBundleCore.ofScalarCore (hp.characterCore χ)` coincide with those
of `hp.characterFiniteRankCore χ`. -/
theorem baseSet_ofScalarCore_characterCore (χ : G →* 𝕜ˣ) (x : X) :
    (FiniteRankBundleCore.ofScalarCore (hp.characterCore χ)).core.baseSet x =
      (hp.characterFiniteRankCore χ).core.baseSet x := by
  rw [FiniteRankBundleCore.baseSet_ofScalarCore, characterCore_baseSet, characterCore_indexAt,
    characterFiniteRankCore_baseSet]

/-- Transitions of `FiniteRankBundleCore.ofScalarCore (hp.characterCore χ)` agree with those of
`hp.characterFiniteRankCore χ` under the identity equivalence on `Fin 1 → 𝕜`. -/
theorem coordChange_ofScalarCore_characterCore_intertwines (χ : G →* 𝕜ˣ) (i j x : X) :
    ((ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜) :
        (Fin (FiniteRankBundleCore.ofScalarCore (hp.characterCore χ)).rank → 𝕜) ≃L[𝕜]
          (Fin (hp.characterFiniteRankCore χ).rank → 𝕜)).toContinuousLinearMap).comp
        ((FiniteRankBundleCore.ofScalarCore (hp.characterCore χ)).core.coordChange i j x) =
      ((hp.characterFiniteRankCore χ).core.coordChange i j x).comp
        ((ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜) :
          (Fin (FiniteRankBundleCore.ofScalarCore (hp.characterCore χ)).rank → 𝕜) ≃L[𝕜]
            (Fin (hp.characterFiniteRankCore χ).rank → 𝕜)).toContinuousLinearMap) := by
  rw [FiniteRankBundleCore.coordChange_ofScalarCore_eq_smul, characterCore_indexAt,
    characterCore_indexAt, characterCore_coordChange_apply, mul_one,
    characterFiniteRankCore_coordChange]
  ext v k
  rfl

/-- Canonical isomorphism in `FiniteRankBundleCore 𝕜 X` identifying the generic scalar
presentation `FiniteRankBundleCore.ofScalarCore (hp.characterCore χ)` with
`hp.characterFiniteRankCore χ`. -/
noncomputable def ofScalarCoreCharacterCoreIso (χ : G →* 𝕜ˣ) :
    FiniteRankBundleCore.ofScalarCore (hp.characterCore χ) ≅ hp.characterFiniteRankCore χ :=
  FiniteRankBundleCore.constIso
    (A := FiniteRankBundleCore.ofScalarCore (hp.characterCore χ))
    (D := hp.characterFiniteRankCore χ)
    (hp.baseSet_ofScalarCore_characterCore χ)
    (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜))
    fun i j x _ _ ↦ hp.coordChange_ofScalarCore_characterCore_intertwines χ i j x

theorem ofScalarCoreCharacterCoreIso_def (χ : G →* 𝕜ˣ) :
    hp.ofScalarCoreCharacterCoreIso χ =
      FiniteRankBundleCore.constIso
        (A := FiniteRankBundleCore.ofScalarCore (hp.characterCore χ))
        (D := hp.characterFiniteRankCore χ)
        (hp.baseSet_ofScalarCore_characterCore χ)
        (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜))
        fun i j x _ _ ↦ hp.coordChange_ofScalarCore_characterCore_intertwines χ i j x := (rfl)

@[simp] theorem fiberMap_ofScalarCoreCharacterCoreIso_hom (χ : G →* 𝕜ˣ) (x : X) :
    (hp.ofScalarCoreCharacterCoreIso χ).hom.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜) :=
  FiniteRankBundleCore.fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_ofScalarCoreCharacterCoreIso_inv (χ : G →* 𝕜ˣ) (x : X) :
    (hp.ofScalarCoreCharacterCoreIso χ).inv.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜) :=
  FiniteRankBundleCore.fiberMap_constIso_inv _ _ _ x

/-- Equality of characters induces a canonical isomorphism between their point-indexed cores. -/
noncomputable def characterFiniteRankCoreCongr {χ ψ : G →* 𝕜ˣ} (h : χ = ψ) :
    hp.characterFiniteRankCore χ ≅ hp.characterFiniteRankCore ψ :=
  eqToIso (congrArg hp.characterFiniteRankCore h)

theorem characterFiniteRankCoreCongr_def {χ ψ : G →* 𝕜ˣ} (h : χ = ψ) :
    hp.characterFiniteRankCoreCongr h = eqToIso (congrArg hp.characterFiniteRankCore h) := (rfl)

@[simp] theorem characterFiniteRankCoreCongr_refl (χ : G →* 𝕜ˣ) :
    hp.characterFiniteRankCoreCongr (rfl : χ = χ) = Iso.refl _ := (rfl)

/-- The point-indexed core of the trivial character `1 : G →* 𝕜ˣ` is canonically isomorphic in
`FiniteRankBundleCore 𝕜 X` to the monoidal unit. -/
noncomputable def characterFiniteRankCoreOneIso :
    hp.characterFiniteRankCore (1 : G →* 𝕜ˣ) ≅ 𝟙_ (FiniteRankBundleCore 𝕜 X) :=
  FiniteRankBundleCore.isoTrivialOfCoordChangeEqId (hp.characterFiniteRankCore 1)
    (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜)) fun i j x _ _ ↦ by
      rw [characterFiniteRankCore_coordChange, MonoidHom.one_apply, Units.val_one, one_smul]

@[simp] theorem fiberMap_characterFiniteRankCoreOneIso_hom (x : X) :
    hp.characterFiniteRankCoreOneIso.hom.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin (hp.characterFiniteRankCore (1 : G →* 𝕜ˣ)).rank → 𝕜) :=
  FiniteRankBundleCore.fiberMap_isoTrivialOfCoordChangeEqId_hom _ _ _ x

@[simp] theorem fiberMap_characterFiniteRankCoreOneIso_inv (x : X) :
    hp.characterFiniteRankCoreOneIso.inv.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin (𝟙_ (FiniteRankBundleCore 𝕜 X)).rank → 𝕜) :=
  FiniteRankBundleCore.fiberMap_isoTrivialOfCoordChangeEqId_inv _ _ _ x

/-- Coordinate identification between the tensor-product fibre of `L_χ ⊗ L_ψ` and that of
`L_{χ * ψ}`. -/
noncomputable abbrev characterMulFiberEquiv (χ ψ : G →* 𝕜ˣ) :
    (Fin ((hp.characterFiniteRankCore χ).rank * (hp.characterFiniteRankCore ψ).rank) → 𝕜) ≃L[𝕜]
      (Fin (hp.characterFiniteRankCore (χ * ψ)).rank → 𝕜) :=
  ContinuousLinearEquiv.piCongrLeft 𝕜
    (fun _ : Fin (hp.characterFiniteRankCore (χ * ψ)).rank ↦ 𝕜) (finCongr rfl)

/-- Coordinate reindexing intertwines the Kronecker product of transitions of `L_χ` and `L_ψ`
with the transitions of `L_{χ * ψ}`. -/
theorem characterFiniteRankCore_mul_intertwine (χ ψ : G →* 𝕜ˣ) (i j x : X) :
    (hp.characterMulFiberEquiv χ ψ).toContinuousLinearMap.comp
      (((hp.characterFiniteRankCore χ).core.coordChange i j x).kronecker
        ((hp.characterFiniteRankCore ψ).core.coordChange i j x)) =
    ((hp.characterFiniteRankCore (χ * ψ)).core.coordChange i j x).comp
      (hp.characterMulFiberEquiv χ ψ).toContinuousLinearMap := by
  have hχ := hp.characterFiniteRankCore_coordChange χ i j x
  have hψ := hp.characterFiniteRankCore_coordChange ψ i j x
  have hχψ := hp.characterFiniteRankCore_coordChange (χ * ψ) i j x
  rw [MonoidHom.mul_apply, Units.val_mul] at hχψ
  rw [hχ, hψ, hχψ, ContinuousLinearMap.smul_kronecker, ContinuousLinearMap.kronecker_smul,
    smul_smul, ContinuousLinearMap.id_kronecker_id, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]

/-- **Tensor multiplicativity of character line bundles.** For characters `χ, ψ : G →* 𝕜ˣ` of the
deck group, `L_χ ⊗ L_ψ` is canonically isomorphic in `FiniteRankBundleCore 𝕜 X` to `L_{χ * ψ}`. -/
noncomputable def characterFiniteRankCoreMulIso (χ ψ : G →* 𝕜ˣ) :
    hp.characterFiniteRankCore χ ⊗ hp.characterFiniteRankCore ψ ≅
      hp.characterFiniteRankCore (χ * ψ) :=
  FiniteRankBundleCore.constIso (fun _ ↦ Set.inter_self _) (hp.characterMulFiberEquiv χ ψ)
    fun i j x _ _ ↦ hp.characterFiniteRankCore_mul_intertwine χ ψ i j x

@[simp] theorem fiberMap_characterFiniteRankCoreMulIso_hom (χ ψ : G →* 𝕜ˣ) (x : X) :
    (hp.characterFiniteRankCoreMulIso χ ψ).hom.fiberMap x =
      (hp.characterMulFiberEquiv χ ψ).toContinuousLinearMap :=
  FiniteRankBundleCore.fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_characterFiniteRankCoreMulIso_inv (χ ψ : G →* 𝕜ˣ) (x : X) :
    (hp.characterFiniteRankCoreMulIso χ ψ).inv.fiberMap x =
      (hp.characterMulFiberEquiv χ ψ).symm.toContinuousLinearMap :=
  FiniteRankBundleCore.fiberMap_constIso_inv _ _ _ x

/-- **Tensor powers of a character line bundle.** For every `m : ℕ`, the `m`-th tensor power of
`hp.characterFiniteRankCore χ` is canonically isomorphic to `hp.characterFiniteRankCore (χ ^ m)`. -/
noncomputable def characterFiniteRankCoreTensorPowerIso (χ : G →* 𝕜ˣ) :
    ∀ m : ℕ, tensorPow (hp.characterFiniteRankCore χ) m ≅
      hp.characterFiniteRankCore (χ ^ m)
  | 0 => hp.characterFiniteRankCoreOneIso.symm ≪≫
      hp.characterFiniteRankCoreCongr (pow_zero χ).symm
  | m + 1 => (Iso.refl (hp.characterFiniteRankCore χ) ⊗ᵢ
        characterFiniteRankCoreTensorPowerIso χ m) ≪≫
      hp.characterFiniteRankCoreMulIso χ (χ ^ m) ≪≫
      hp.characterFiniteRankCoreCongr (pow_succ' χ m).symm

@[simp] theorem characterFiniteRankCoreTensorPowerIso_zero (χ : G →* 𝕜ˣ) :
    hp.characterFiniteRankCoreTensorPowerIso χ 0 =
      hp.characterFiniteRankCoreOneIso.symm ≪≫
        hp.characterFiniteRankCoreCongr (pow_zero χ).symm := (rfl)

theorem characterFiniteRankCoreTensorPowerIso_succ (χ : G →* 𝕜ˣ) (m : ℕ) :
    hp.characterFiniteRankCoreTensorPowerIso χ (m + 1) =
      (Iso.refl (hp.characterFiniteRankCore χ) ⊗ᵢ
        hp.characterFiniteRankCoreTensorPowerIso χ m) ≪≫
        hp.characterFiniteRankCoreMulIso χ (χ ^ m) ≪≫
        hp.characterFiniteRankCoreCongr (pow_succ' χ m).symm := (rfl)

end CharacterFiniteRank

/-! ### Twisting cocycle morphisms between scalar character cores -/

section CharacterTwisting

open ContinuousLinearEquiv ContinuousLinearMap VectorBundleCore

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- On the common domain of charts `e` and `e'`, reading a family of fibre maps `ϕ` between
`hp.characterCore χ₁` and `hp.characterCore χ₂` differs from reading `ϕ` between
`hp.characterCore 1` and `hp.characterCore (χ₁⁻¹ * χ₂)` by the locally constant scalar
`χ₁ (hp.deckChange e e' x)`. -/
theorem inChartCoordinates_characterCore_eq_smul (χ₁ χ₂ : G →* 𝕜ˣ) (ϕ : X → 𝕜 →L[𝕜] 𝕜)
    (e e' : E) {x : X}
    (hx : x ∈ (hp.isLocalHomeomorph.localInverseAt e).source ∩
      (hp.isLocalHomeomorph.localInverseAt e').source) :
    (hp.characterCore χ₁).inChartCoordinates (hp.characterCore χ₂) e e' x (ϕ x) =
      (χ₁ (hp.deckChange e e' x) : 𝕜) •
        (hp.characterCore 1).inChartCoordinates (hp.characterCore (χ₁⁻¹ * χ₂)) e e' x (ϕ x) := by
  set i₀ := Function.surjInv hp.surjective x
  have hi₀ : x ∈ (hp.isLocalHomeomorph.localInverseAt i₀).source := by
    simpa only [i₀, Function.surjInv_eq hp.surjective x] using
      hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source (x := i₀)
  have hmul : χ₁ (hp.deckChange e e' x) * (χ₁ (hp.deckChange i₀ e' x))⁻¹ =
      χ₁ (hp.deckChange e i₀ x) := by
    rw [← hp.deckChange_mul_deckChange ⟨⟨hx.1, hi₀⟩, hx.2⟩, map_mul, mul_comm, inv_mul_cancel_left]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hmap : ∀ a b : 𝕜, (ϕ x) (a * b) = a * (ϕ x) b := fun a b ↦ (ϕ x).map_smul a b
  simp only [_root_.smul_apply, inChartCoordinates_apply, characterCore_indexAt,
    hp.characterCore_coordChange_apply, hp.characterCore_one_coordChange,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  rw [hmap, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, ← hmul, Units.val_mul]
  ring

/-- Twisting a cocycle morphism `a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)` by
`ψ`-multiplying its chart operators yields a cocycle morphism from `hp.characterCore χ₁'` to
`hp.characterCore χ₂'` with the same fibre maps whenever `ψ * χ₁ = χ₁'` and `ψ * χ₂ = χ₂'`. -/
private noncomputable def twistCharacterCoreHom {χ₁ χ₂ χ₁' χ₂' : G →* 𝕜ˣ} (ψ : G →* 𝕜ˣ)
    (h₁ : ψ * χ₁ = χ₁') (h₂ : ψ * χ₂ = χ₂')
    (a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)) :
    CoordinateHom (hp.characterCore χ₁') (hp.characterCore χ₂') where
  operator e e' :=
    let re : ↥((hp.characterCore χ₁').baseSet e ∩ (hp.characterCore χ₂').baseSet e') →
        ↥((hp.characterCore χ₁).baseSet e ∩ (hp.characterCore χ₂).baseSet e') :=
      fun x ↦ ⟨x.val, ⟨by simpa using x.property.1, by simpa using x.property.2⟩⟩
    ⟨fun x ↦ (ψ (hp.deckChange e e' x.val) : 𝕜) • a.operator e e' (re x),
      continuous_iff_continuousAt.2 fun x ↦ by
        have hx : x.val ∈ (hp.isLocalHomeomorph.localInverseAt e).source ∩
            (hp.isLocalHomeomorph.localInverseAt e').source := by simpa using x.property
        have hconst : ContinuousAt (fun y : ↥((hp.characterCore χ₁').baseSet e ∩
            (hp.characterCore χ₂').baseSet e') ↦ (ψ (hp.deckChange e e' y.val) : 𝕜)) x :=
          continuousAt_const.congr <| Filter.Eventually.mono
            (continuous_subtypeVal.continuousAt.eventually (hp.eventually_deckChange_eq hx))
            fun y hy ↦ congrArg (fun g ↦ (ψ g : 𝕜)) hy.symm
        exact hconst.smul ((a.operator e e').continuous.comp
          (continuous_subtypeVal.subtype_mk _)).continuousAt⟩
  compatible e₁ e₂ e₁' e₂' x he₁ he₂ he₁' he₂' v := by
    rw [characterCore_baseSet] at he₁ he₂ he₁' he₂'
    have hcompat := a.compatible e₁ e₂ e₁' e₂' x (by simpa using he₁) (by simpa using he₂)
      (by simpa using he₁') (by simpa using he₂') ((ψ (hp.deckChange e₁ e₂ x) : 𝕜) * v)
    rw [← smul_eq_mul, _root_.map_smul, smul_eq_mul, hp.characterCore_coordChange_apply,
      hp.characterCore_coordChange_apply] at hcompat
    have hc : (ψ (hp.deckChange e₁' e₂' x) : 𝕜) * (ψ (hp.deckChange e₁ e₁' x) : 𝕜) =
        (ψ (hp.deckChange e₂ e₂' x) : 𝕜) * (ψ (hp.deckChange e₁ e₂ x) : 𝕜) := by
      exact_mod_cast (by
        rw [← map_mul, ← map_mul, hp.deckChange_mul_deckChange ⟨⟨he₁, he₁'⟩, he₂'⟩,
          hp.deckChange_mul_deckChange ⟨⟨he₁, he₂⟩, he₂'⟩])
    have h₁x : (χ₁' (hp.deckChange e₁ e₂ x) : 𝕜) =
        (ψ (hp.deckChange e₁ e₂ x) : 𝕜) * (χ₁ (hp.deckChange e₁ e₂ x) : 𝕜) := by rw [← h₁]; simp
    have h₂x : (χ₂' (hp.deckChange e₁' e₂' x) : 𝕜) =
        (ψ (hp.deckChange e₁' e₂' x) : 𝕜) * (χ₂ (hp.deckChange e₁' e₂' x) : 𝕜) := by rw [← h₂]; simp
    simp only [ContinuousMap.coe_mk, _root_.smul_apply, smul_eq_mul,
      hp.characterCore_coordChange_apply, h₁x, h₂x]
    calc _ = (ψ (hp.deckChange e₁' e₂' x) : 𝕜) * (ψ (hp.deckChange e₁ e₁' x) : 𝕜) *
            ((χ₂ (hp.deckChange e₁' e₂' x) : 𝕜) * a.operator e₁ e₁' _ v) := by ring
      _ = (ψ (hp.deckChange e₂ e₂' x) : 𝕜) * ((χ₂ (hp.deckChange e₁' e₂' x) : 𝕜) *
            ((ψ (hp.deckChange e₁ e₂ x) : 𝕜) * a.operator e₁ e₁' _ v)) := by rw [hc]; ring
      _ = _ := by rw [hcompat]; congr 2; ring

private theorem fiberMap_twistCharacterCoreHom {χ₁ χ₂ χ₁' χ₂' : G →* 𝕜ˣ} (ψ : G →* 𝕜ˣ)
    (h₁ : ψ * χ₁ = χ₁') (h₂ : ψ * χ₂ = χ₂')
    (a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)) (x : X) :
    (hp.twistCharacterCoreHom ψ h₁ h₂ a).fiberMap x = a.fiberMap x := by
  rw [CoordinateHom.fiberMap_def]
  simp only [twistCharacterCoreHom, ContinuousMap.coe_mk, CoordinateHom.operator_eq]
  have hs : x ∈
      (hp.isLocalHomeomorph.localInverseAt (Function.surjInv hp.surjective x)).source := by
    simpa only [Function.surjInv_eq hp.surjective x] using
      hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source
        (x := Function.surjInv hp.surjective x)
  ext; simp [inChartCoordinates_apply, hp.deckChange_self hs]

/-- Cocycle morphisms between `hp.characterCore χ₁` and `hp.characterCore χ₂` correspond
additively to cocycle morphisms between `hp.characterCore 1` and `hp.characterCore (χ₁⁻¹ * χ₂)`
with the exact same fibre maps, without completeness assumptions on `𝕜`. -/
noncomputable def characterCoreHomEquiv (χ₁ χ₂ : G →* 𝕜ˣ) :
    CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂) ≃+
      CoordinateHom (hp.characterCore 1) (hp.characterCore (χ₁⁻¹ * χ₂)) where
  toFun := hp.twistCharacterCoreHom χ₁⁻¹ (inv_mul_cancel χ₁) rfl
  invFun := hp.twistCharacterCoreHom χ₁ (mul_one χ₁) (mul_inv_cancel_left χ₁ χ₂)
  left_inv _ := CoordinateHom.fiberMap_injective <| funext fun _ ↦ by
    rw [fiberMap_twistCharacterCoreHom, fiberMap_twistCharacterCoreHom]
  right_inv _ := CoordinateHom.fiberMap_injective <| funext fun _ ↦ by
    rw [fiberMap_twistCharacterCoreHom, fiberMap_twistCharacterCoreHom]
  map_add' _ _ := CoordinateHom.fiberMap_injective <| funext fun _ ↦ by
    simp [CoordinateHom.fiberMap_add, fiberMap_twistCharacterCoreHom]

@[simp] theorem fiberMap_characterCoreHomEquiv (χ₁ χ₂ : G →* 𝕜ˣ)
    (a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)) (x : X) :
    (hp.characterCoreHomEquiv χ₁ χ₂ a).fiberMap x = a.fiberMap x :=
  hp.fiberMap_twistCharacterCoreHom χ₁⁻¹ (inv_mul_cancel χ₁) rfl a x

@[simp] theorem fiberMap_characterCoreHomEquiv_symm (χ₁ χ₂ : G →* 𝕜ˣ)
    (b : CoordinateHom (hp.characterCore 1) (hp.characterCore (χ₁⁻¹ * χ₂))) (x : X) :
    ((hp.characterCoreHomEquiv χ₁ χ₂).symm b).fiberMap x = b.fiberMap x :=
  hp.fiberMap_twistCharacterCoreHom χ₁ (mul_one χ₁) (mul_inv_cancel_left χ₁ χ₂) b x

/-- Reading a fibrewise scalar-multiplication map `v ↦ v • s x` from `hp.characterCore 1` to
`hp.characterCore χ` in charts `(e, e')` gives scalar multiplication by the local coordinate of `s`
in the chart `e'`. -/
theorem inChartCoordinates_characterCore_one_smulRight (χ : G →* 𝕜ˣ)
    (s : X → 𝕜) (e e' : E) (x : X) :
    (hp.characterCore 1).inChartCoordinates (hp.characterCore χ) e e' x
        ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (s x)) =
      (ContinuousLinearMap.id 𝕜 𝕜).smulRight
        (((hp.characterCore χ).localTriv e' ⟨x, s x⟩).snd) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [inChartCoordinates_apply, hp.characterCore_one_coordChange, ContinuousLinearMap.id_apply,
    smulRight_apply, ContinuousLinearMap.id_apply, _root_.map_smul, localTriv_apply,
    smulRight_apply, ContinuousLinearMap.id_apply]

end CharacterTwisting

end IsQuotientCoveringMap
