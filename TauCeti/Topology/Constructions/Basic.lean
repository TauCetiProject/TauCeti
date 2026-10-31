/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.ContinuousMap.Defs

/-!
# Quotients by setoids and fibre products of topological spaces

This file adds to Mathlib's quotient-topology API for `Quotient.mk s`, where `s : Setoid X`, and to
the topology of the fibre product `Function.Pullback f g`, a subspace of the product.

## Main results

* `Setoid.image_quotient_mk_compl`: if `s` identifies only points of `t`, the quotient map sends
  the complement of `t` onto the complement of the image of `t`.
* `Setoid.isOpen_image_quotient_mk`: the image of an open set closed under `s` is open.
* `Setoid.isOpenEmbedding_domRestrict_quotient_mk_of_isOpen`: the quotient map restricted to an
  open set whose points are related only to themselves is an open embedding.
* `Function.Pullback.continuous_fst`, `Function.Pullback.continuous_snd`: the projections of the
  fibre product are continuous.
* `ContinuousMap.pullbackFst`, `ContinuousMap.pullbackSnd`: the projections of the fibre product,
  bundled as continuous maps.
-/

public section

open Set Topology

namespace Setoid

variable {X : Type*} (s : Setoid X)

/-- If an equivalence relation identifies only points of a set `t`, then the quotient map sends the
complement of `t` onto the complement of the image of `t`. -/
theorem image_quotient_mk_compl {t : Set X} (hst : ∀ ⦃x y⦄, s x y → x ≠ y → x ∈ t) :
    Quotient.mk s '' tᶜ = (Quotient.mk s '' t)ᶜ := by
  ext q
  induction q using Quotient.inductionOn with | h y => ?_
  simp only [mem_image, mem_compl_iff, Quotient.eq, not_exists, not_and]
  constructor
  · rintro ⟨x, hx, hxy⟩ z hz hzy
    by_cases hne : x = z
    · exact hx (hne ▸ hz)
    · exact hx (hst (s.trans hxy (s.symm hzy)) hne)
  · intro h
    exact ⟨y, fun hy => h y hy (s.refl y), s.refl y⟩

variable [TopologicalSpace X]

/-- The image in `Quotient s` of an open set closed under the relation `s` is open. -/
theorem isOpen_image_quotient_mk {U : Set X} (hU : IsOpen U)
    (hsat : ∀ ⦃x y⦄, x ∈ U → s x y → y ∈ U) : IsOpen (Quotient.mk s '' U) := by
  have hsatU : Quotient.mk s ⁻¹' (Quotient.mk s '' U) = U := by
    refine Subset.antisymm ?_ (subset_preimage_image _ _)
    rintro y ⟨x, hx, hxy⟩
    exact hsat hx (Quotient.exact hxy)
  have hq : IsQuotientMap (Quotient.mk s) := isQuotientMap_quotient_mk'
  rwa [← hq.isOpen_preimage, hsatU]

/-- If every point of an open set `U` is related by `s` only to itself, then the quotient map
restricted to `U` is an open embedding. -/
theorem isOpenEmbedding_domRestrict_quotient_mk_of_isOpen {U : Set X} (hU : IsOpen U)
    (hfix : ∀ ⦃x y⦄, x ∈ U → s x y → x = y) :
    IsOpenEmbedding (U.domRestrict (Quotient.mk s)) := by
  refine .of_continuous_injective_isOpenMap
    (continuous_quotient_mk'.comp continuous_subtype_val) (fun x y hxy => ?_) fun W hW => ?_
  · exact Subtype.ext (hfix x.2 (Quotient.exact hxy))
  · rw [domRestrict_eq, image_comp]
    refine isOpen_image_quotient_mk s (hU.isOpenMap_subtype_val W hW) ?_
    rintro _ y ⟨x, hx, rfl⟩ hxy
    exact hfix x.2 hxy ▸ mem_image_of_mem _ hx

end Setoid

section Pullback

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {f : X → Y} {g : Z → Y}

/-- The projection `X ×_Y Z → X` is continuous. -/
@[fun_prop]
theorem Function.Pullback.continuous_fst : Continuous (Pullback.fst : f.Pullback g → X) :=
  _root_.continuous_fst.comp continuous_subtype_val

/-- The projection `X ×_Y Z → Z` is continuous. -/
@[fun_prop]
theorem Function.Pullback.continuous_snd : Continuous (Pullback.snd : f.Pullback g → Z) :=
  _root_.continuous_snd.comp continuous_subtype_val

variable (f g)

/-- The projection `X ×_Y Z → X`, bundled as a continuous map. -/
def ContinuousMap.pullbackFst : C(f.Pullback g, X) :=
  ⟨Function.Pullback.fst, Function.Pullback.continuous_fst⟩

/-- The projection `X ×_Y Z → Z`, bundled as a continuous map. -/
def ContinuousMap.pullbackSnd : C(f.Pullback g, Z) :=
  ⟨Function.Pullback.snd, Function.Pullback.continuous_snd⟩

@[simp]
theorem ContinuousMap.coe_pullbackFst : ⇑(pullbackFst f g) = Function.Pullback.fst :=
  (rfl)

@[simp]
theorem ContinuousMap.coe_pullbackSnd : ⇑(pullbackSnd f g) = Function.Pullback.snd :=
  (rfl)

end Pullback
