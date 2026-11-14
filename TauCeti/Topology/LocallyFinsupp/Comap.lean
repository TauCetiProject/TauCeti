/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyFinsupp

/-!
# Pulling back functions with locally finite support along injective continuous maps

If `e : X' → X` is continuous and injective and `D : X → Y` has locally finite support, then
`D ∘ e` has locally finite support: a neighbourhood of `e x'` meeting finitely many points of the
support of `D` pulls back to a neighbourhood of `x'`, and injectivity keeps the intersection with
the support of `D ∘ e` finite. This is `Function.locallyFinsupp.comap`.

For an open or closed immersion of schemes it restricts an algebraic cycle to the subscheme.
-/

public section

open Set Filter Topology

namespace Function.locallyFinsupp

variable {X X' Y : Type*} [TopologicalSpace X] [TopologicalSpace X']

section Zero

variable [Zero Y]

/-- The pullback `D ∘ e` of a function with locally finite support along an injective continuous
map. -/
noncomputable def comap (e : X' → X) (he : Continuous e) (he' : Injective e)
    (D : locallyFinsupp X Y) : locallyFinsupp X' Y where
  toFun := D ∘ e
  supportWithinDomain' := subset_univ _
  supportLocallyFiniteWithinDomain' z _ := by
    obtain ⟨t, ht, hfin⟩ := D.supportLocallyFiniteWithinDomain' (e z) (mem_univ _)
    refine ⟨e ⁻¹' t, he.continuousAt.preimage_mem_nhds ht, ?_⟩
    refine (hfin.preimage he'.injOn).subset ?_
    rintro x ⟨hxt, hx⟩
    exact ⟨hxt, hx⟩

variable (e : X' → X) (he : Continuous e) (he' : Injective e)

@[simp]
lemma comap_apply (D : locallyFinsupp X Y) (x : X') : comap e he he' D x = D (e x) :=
  (rfl)

/-- The support of a pullback is the preimage of the support. -/
@[simp]
lemma support_comap (D : locallyFinsupp X Y) :
    (comap e he he' D).support = e ⁻¹' D.support :=
  (rfl)

end Zero

variable (e : X' → X) (he : Continuous e) (he' : Injective e)

@[simp]
lemma comap_zero [Zero Y] : comap e he he' (0 : locallyFinsupp X Y) = 0 :=
  (rfl)

@[simp]
lemma comap_add [AddMonoid Y] (D D' : locallyFinsupp X Y) :
    comap e he he' (D + D') = comap e he he' D + comap e he he' D' :=
  (rfl)

end Function.locallyFinsupp
