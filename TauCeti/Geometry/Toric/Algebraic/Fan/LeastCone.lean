/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.Cone.Face.Exposed
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic
public import TauCeti.Geometry.Toric.Algebraic.Fan.Basic

/-!
# Characters on the least target cone

For a fan morphism, a character nonnegative on the least target cone of a source cone vanishes
on the image of the source cone exactly when it vanishes on the least target cone. Indeed, its
zero locus cuts out a face of the least target cone, and this face must contain the least cone.
This character criterion identifies the image of distinguished points and orbit strata under
toric maps without choosing coordinates.

## References

* W. Fulton, *Introduction to Toric Varieties*, §2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.3.
-/

public section

namespace TauCeti.Toric.FanHom

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

/-- A character nonnegative on the least target cone of `σ` vanishes on that cone exactly when
its pullback vanishes on `σ`. Neither fan needs to be regular. -/
theorem realCharacter_eq_zero_on_leastCone_iff (f : FanHom Φ Ψ) {σ : PointedCone ℝ V}
    (hσ : σ ∈ Φ.cones) {m : N' →+ ℤ}
    (hm : m ∈ dualSemigroup Ψ.lattice (f.leastCone hσ)) :
    (∀ y ∈ f.leastCone hσ, Ψ.lattice.realCharacter m y = 0) ↔
      ∀ x ∈ σ, Φ.lattice.realCharacter (m.comp f.latticeMap) x = 0 := by
  rw [Φ.lattice.realCharacter_comp Ψ.lattice f.latticeMap f.realMap f.map_lattice]
  constructor
  · intro h x hx
    exact h _ (f.mapsTo_leastCone hσ hx)
  · intro h
    have hface := PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup Ψ.lattice m).1 hm)
    have hle : f.leastCone hσ ≤
        f.leastCone hσ ⊓ PointedCone.ofSubmodule (LinearMap.ker (Ψ.lattice.realCharacter m)) :=
      f.leastCone_le hσ (Ψ.mem_of_isFaceOf (f.leastCone_mem hσ) hface) (by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨f.mapsTo_leastCone hσ hx, h x hx⟩)
    intro y hy
    exact (hle hy).2

end TauCeti.Toric.FanHom
