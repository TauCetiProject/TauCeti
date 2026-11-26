/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Functions given by their values on the connected components of a set

A function `φ` on the connected components of a set `s` defines a function on the ambient space,
`TauCeti.componentFun φ`, equal to `φ c` on the component `c` of `s` and to `0` off `s`. It is
additive and homogeneous in `φ`. When `s` is open in a locally connected space, every component
of `s` is open, so `componentFun φ` is locally constant on `s`.

## Main declarations

* `TauCeti.componentFun`: the function equal to `φ c` on the component `c` of `s` and to `0` off
  `s`.
* `TauCeti.isLocallyConstant_componentFun`: on an open set of a locally connected space,
  `componentFun φ` is locally constant.
* `IsLocallyConstant.apply_eq_of_isPreconnected_of_subset`: a function that is locally constant
  on `s` is constant on every preconnected subset of `s`.
-/

public section

namespace TauCeti

open Set

variable {X β : Type*} [TopologicalSpace X] {s : Set X}

open scoped Classical in
/-- The function equal to `φ c` on the connected component `c` of `s`, and to `0` off `s`. -/
noncomputable def componentFun [Zero β] (φ : ConnectedComponents s → β) (x : X) : β :=
  if hx : x ∈ s then φ (ConnectedComponents.mk ⟨x, hx⟩) else 0

@[simp]
theorem componentFun_of_mem [Zero β] (φ : ConnectedComponents s → β) {x : X} (hx : x ∈ s) :
    componentFun φ x = φ (ConnectedComponents.mk ⟨x, hx⟩) := by
  simp [componentFun, hx]

@[simp]
theorem componentFun_of_notMem [Zero β] (φ : ConnectedComponents s → β) {x : X} (hx : x ∉ s) :
    componentFun φ x = 0 := by
  simp [componentFun, hx]

@[simp]
theorem componentFun_zero [Zero β] : componentFun (0 : ConnectedComponents s → β) = 0 := by
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

@[simp]
theorem componentFun_add [AddZeroClass β] (φ ψ : ConnectedComponents s → β) :
    componentFun (φ + ψ) = componentFun φ + componentFun ψ := by
  funext x
  by_cases hx : x ∈ s <;> simp [componentFun, hx]

@[simp]
theorem componentFun_smul {R : Type*} [Zero β] [SMulZeroClass R β] (c : R)
    (φ : ConnectedComponents s → β) :
    componentFun (c • φ) = c • componentFun φ := by
  funext x
  by_cases hx : x ∈ s <;> simp [componentFun, hx]

/-- On an open set `s` of a locally connected space, whose components are open,
`componentFun φ` is locally constant on `s`. -/
theorem isLocallyConstant_componentFun [LocallyConnectedSpace X] [Zero β] (hs : IsOpen s)
    (φ : ConnectedComponents s → β) : IsLocallyConstant (s.domRestrict (componentFun φ)) := by
  have := hs.locallyConnectedSpace
  refine IsLocallyConstant.of_constant_on_connected_components fun x y hy => ?_
  simp only [domRestrict_apply, componentFun_of_mem φ x.property, componentFun_of_mem φ y.property]
  exact congrArg φ (ConnectedComponents.coe_eq_coe'.2 hy)

/-- A function `g` that is locally constant on `s`, in the sense that `s.domRestrict g` is locally
constant, is constant on every preconnected subset `t` of `s`. -/
theorem _root_.IsLocallyConstant.apply_eq_of_isPreconnected_of_subset {g : X → β}
    (hg : IsLocallyConstant (s.domRestrict g)) {t : Set X} (ht : IsPreconnected t) (hts : t ⊆ s)
    {y z : X} (hy : y ∈ t) (hz : z ∈ t) : g y = g z := by
  have hpre : IsPreconnected (((↑) : s → X) ⁻¹' t) := by
    refine Topology.IsInducing.subtypeVal.isPreconnected_image.1 ?_
    rwa [image_preimage_eq_of_subset (Subtype.range_coe.symm ▸ hts)]
  exact hg.apply_eq_of_isPreconnected hpre (x := ⟨y, hts hy⟩) (y := ⟨z, hts hz⟩) hy hz

end TauCeti
