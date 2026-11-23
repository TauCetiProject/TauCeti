/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import TauCeti.Topology.Homeomorph.Pi
public import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Finite products of covering maps

A finite product of evenly covered points is evenly covered by the product map, with the product
of the sheet spaces as sheets. Consequently a finite product `Pi.map f` of covering maps
`f i : E i → X i` is a covering map. Finiteness is needed: the product of the evenly covered
neighbourhoods is open, and the product of the discrete sheet spaces is discrete, only for finitely
many factors. Surjectivity of the factors is not required. This is the finite-product counterpart of
`IsCoveringMap.prodMap`.
-/

public section

open Set Topology

variable {ι : Type*} [Finite ι] {E X A : ι → Type*} [∀ i, TopologicalSpace (E i)]
  [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (A i)] {f : ∀ i, E i → X i}

/-- A finite product of evenly covered points is evenly covered by the product map, with the
product of the sheet spaces. -/
theorem IsEvenlyCovered.piMap {x : ∀ i, X i} (h : ∀ i, IsEvenlyCovered (f i) (x i) (A i)) :
    IsEvenlyCovered (Pi.map f) x (∀ i, A i) := by
  choose hA U hx hU hfU H hH using h
  -- The sheet spaces are discrete, so their finite product is discrete.
  have := hA
  have hpre : Pi.map f ⁻¹' univ.pi U = univ.pi fun i ↦ f i ⁻¹' U i := by
    ext z
    simp
  refine ⟨inferInstance, univ.pi U, fun i _ ↦ hx i, isOpen_set_pi finite_univ fun i _ ↦ hU i,
    hpre ▸ isOpen_set_pi finite_univ fun i _ ↦ hfU i,
    (Homeomorph.setCongr hpre).trans ((Homeomorph.Set.univPi _).trans
      ((Homeomorph.piCongrRight H).trans ((Homeomorph.arrowProdHomeomorphProdArrow _ A).trans
        ((Homeomorph.Set.univPi U).symm.prodCongr (Homeomorph.refl _))))), fun z ↦ ?_⟩
  funext i
  simp [hH]

/-- A finite product of covering maps is a covering map. Surjectivity of the factors is not
required. -/
theorem IsCoveringMap.piMap (hf : ∀ i, IsCoveringMap (f i)) : IsCoveringMap (Pi.map f) :=
  fun x ↦ (IsEvenlyCovered.piMap fun i ↦ hf i (x i)).to_isEvenlyCovered_preimage
