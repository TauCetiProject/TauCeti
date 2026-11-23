/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement

/-!
# Torsion elements in submonoids

A torsion-free submonoid `H : Submonoid G` contains no nontrivial element of finite order in the
ambient monoid `G`.

## Main results

* `Submonoid.eq_one_of_isOfFinOrder_mem`: a torsion-free submonoid contains no nontrivial ambient
  element of finite order.
-/

public section

namespace Submonoid

/-- If `H : Submonoid G` is torsion-free, every element of `H` that has finite order in `G` is
`1`. -/
theorem eq_one_of_isOfFinOrder_mem {G : Type*} [Monoid G] (H : Submonoid G) [IsMulTorsionFree H]
    {x : G} (hx : x ∈ H) (hfin : IsOfFinOrder x) : x = 1 :=
  congrArg Subtype.val (Submonoid.isOfFinOrder_coe.mp hfin : IsOfFinOrder (⟨x, hx⟩ : H)).eq_one'

end Submonoid
