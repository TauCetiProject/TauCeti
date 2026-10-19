/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions

/-!
# Quotients of topological spaces by setoids

This file adds to Mathlib's quotient-topology API for `Quotient.mk s`, where `s : Setoid X`.

## Main results

* `Setoid.isQuotientMap_quotient_mk`: `Quotient.mk s` is a quotient map.
* `Setoid.isOpen_image_quotient_mk`: the image of an open set closed under `s` is open.
* `Setoid.isOpenEmbedding_domRestrict_quotient_mk_of_isOpen`: the quotient map restricted to an
  open set whose points are related only to themselves is an open embedding.
-/

public section

open Set Topology

namespace Setoid

variable {X : Type*} [TopologicalSpace X] (s : Setoid X)

/-- `Quotient.mk s` is a quotient map; `isQuotientMap_quotient_mk'` states this for the
definitionally equal `Quotient.mk'`. -/
theorem isQuotientMap_quotient_mk : IsQuotientMap (Quotient.mk s) :=
  isQuotientMap_quotient_mk'

/-- The image in `Quotient s` of an open set closed under the relation `s` is open. -/
theorem isOpen_image_quotient_mk {U : Set X} (hU : IsOpen U)
    (hsat : ∀ ⦃x y⦄, x ∈ U → s x y → y ∈ U) : IsOpen (Quotient.mk s '' U) := by
  have hsatU : Quotient.mk s ⁻¹' (Quotient.mk s '' U) = U := by
    refine Subset.antisymm ?_ (subset_preimage_image _ _)
    rintro y ⟨x, hx, hxy⟩
    exact hsat hx (Quotient.exact hxy)
  rwa [← (isQuotientMap_quotient_mk s).isOpen_preimage, hsatU]

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
