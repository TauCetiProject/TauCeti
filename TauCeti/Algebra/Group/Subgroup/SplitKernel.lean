/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Direct products from centralizing sections

A group homomorphism with a homomorphic section whose image centralizes the kernel identifies
its domain with the direct product of the kernel and the codomain. The second projection is
the given homomorphism, and the chosen section supplies the second factor of the inverse.
-/

public section

namespace MonoidHom

variable {G H : Type*} [Group G] [Group H] (f : G →* H) (s : H →* G)
  (hs : Function.RightInverse s f) (hc : ∀ (x : f.ker) y, Commute (s y) (x : G))

/-- A homomorphic section that centralizes the kernel gives a direct product decomposition. -/
def mulEquivKerProdOfRightInverse : G ≃* f.ker × H :=
  let lift := f.ker.subtype.noncommCoprod s fun x y ↦ (hc x y).symm
  have hlift (x : f.ker × H) : lift x = (x.1 : G) * s x.2 :=
    MonoidHom.noncommCoprod_apply _ _ _ x
  MulEquiv.symm
    { toFun := lift
      invFun := fun g ↦ (⟨g * (s (f g))⁻¹, by simp [MonoidHom.mem_ker, hs (f g)]⟩, f g)
      left_inv := by
        rintro ⟨x, y⟩
        apply Prod.ext (Subtype.ext ?_) <;>
          simp [hlift, hs y, f.mem_ker.mp x.property]
      right_inv := fun g ↦ by simp [hlift]
      map_mul' := lift.map_mul }

/-- The kernel coordinate removes the section of the image. -/
@[simp] theorem coe_mulEquivKerProdOfRightInverse_fst (g : G) :
    ((f.mulEquivKerProdOfRightInverse s hs hc g).1 : G) = g * (s (f g))⁻¹ := (rfl)

/-- The second coordinate is the original homomorphism. -/
@[simp] theorem mulEquivKerProdOfRightInverse_snd (g : G) :
    (f.mulEquivKerProdOfRightInverse s hs hc g).2 = f g := (rfl)

/-- The inverse multiplies the kernel element by the lift of the second coordinate. -/
@[simp] theorem mulEquivKerProdOfRightInverse_symm_apply (x : f.ker × H) :
    (f.mulEquivKerProdOfRightInverse s hs hc).symm x = (x.1 : G) * s x.2 := (rfl)

end MonoidHom
