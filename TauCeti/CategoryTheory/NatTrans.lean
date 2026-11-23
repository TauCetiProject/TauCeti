/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Range-saturation for natural transformations of `Type`-valued functors

If a natural transformation `φ : Y ⟶ X` between `Type`-valued functors on a category `C` has
objectwise image equal to the preimage of a subset `V` under a natural augmentation
`ε : X ⟶ (Functor.const C).obj Z`, then `φ` is saturated under morphisms of `C`: whenever
`X.map f x` lies in `Set.range (φ.app d)`, `x` already lies in `Set.range (φ.app c)`.

## Main declarations

* `CategoryTheory.NatTrans.mem_range_of_map_mem_range`: objectwise preimage characterization of
  `Set.range (φ.app c)` under an augmentation to a constant functor implies saturation under
  morphisms of `C`.
-/

public section

namespace CategoryTheory.NatTrans

universe w v u

variable {C : Type u} [Category.{v} C] {X Y : C ⥤ Type w} (φ : Y ⟶ X) {Z : Type w}
  (ε : X ⟶ (Functor.const C).obj Z) {V : Set Z}

/-- If the objectwise image of a natural transformation `φ : Y ⟶ X` between `Type`-valued
functors is the preimage of a set `V` under an augmentation `ε : X ⟶ (Functor.const C).obj Z`,
then `φ` is saturated under morphisms of `C`: whenever `X.map f x` lies in
`Set.range (φ.app d)`, `x` already lies in `Set.range (φ.app c)`. -/
theorem mem_range_of_map_mem_range (hrange : ∀ c, Set.range (φ.app c) = ε.app c ⁻¹' V)
    ⦃c d : C⦄ (f : c ⟶ d) (x : X.obj c) (hx : X.map f x ∈ Set.range (φ.app d)) :
    x ∈ Set.range (φ.app c) := by
  rw [hrange, Set.mem_preimage, NatTrans.naturality_apply] at hx
  rw [hrange]
  simpa using hx

end CategoryTheory.NatTrans
