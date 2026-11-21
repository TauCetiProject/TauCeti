/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import TauCeti.Analysis.CStarAlgebra.Ideal

/-!
# Unitization module action on closed ideals of C⋆-algebras

Left `Unitization ℂ A`-module structure `TwoSidedIdeal.unitizationModule` on a closed two-sided
ideal `I` of a nonunital C⋆-algebra `A`, induced by `TwoSidedIdeal.mulLeftEnd`.
-/

public section

namespace TwoSidedIdeal

section Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A] (I : TwoSidedIdeal A) [IsClosed (I : Set A)]

/-- Left multiplication by elements of `A` on a closed two-sided ideal `I`, as a nonunital algebra
homomorphism into the complex-linear endomorphisms of `I`. -/
def mulLeftEnd : A →ₙₐ[ℂ] Module.End ℂ I where
  toFun a :=
    { toFun x := ⟨a * x, I.mul_mem_left a x x.property⟩
      map_add' x y := Subtype.ext (mul_add a (x : A) y)
      map_smul' c x := Subtype.ext (mul_smul_comm c a (x : A)) }
  map_smul' c a := LinearMap.ext fun x ↦ Subtype.ext (smul_mul_assoc c a (x : A))
  map_zero' := LinearMap.ext fun x ↦ Subtype.ext (zero_mul (x : A))
  map_add' a b := LinearMap.ext fun x ↦ Subtype.ext (add_mul a b (x : A))
  map_mul' a b := LinearMap.ext fun x ↦ Subtype.ext (mul_assoc a b (x : A))

@[simp]
theorem coe_mulLeftEnd_apply (a : A) (x : I) : ((I.mulLeftEnd a x : I) : A) = a * x :=
  (rfl)

/-- The left action `(z, a) • x = z • x + a * x` of the unitization `Unitization ℂ A` on a closed
two-sided ideal `I`. -/
@[instance_reducible]
noncomputable def unitizationModule : Module (Unitization ℂ A) I :=
  Module.compHom I (Unitization.lift I.mulLeftEnd : Unitization ℂ A →+* Module.End ℂ I)

theorem unitizationModule_smul_def (u : Unitization ℂ A) (x : I) :
    letI := I.unitizationModule
    u • x = Unitization.lift I.mulLeftEnd u x :=
  (rfl)

@[simp]
theorem coe_unitizationModule_smul (u : Unitization ℂ A) (x : I) :
    letI := I.unitizationModule
    ((u • x : I) : A) = u.fst • (x : A) + u.snd * x := by
  let _ : Module (Unitization ℂ A) I := I.unitizationModule
  simp [unitizationModule_smul_def, Module.algebraMap_end_apply]

/-- Coercing `(r, a) • x` from `I` into `Unitization ℂ A` agrees with multiplication in
`Unitization ℂ A`. -/
theorem inr_coe_unitizationModule_smul (u : Unitization ℂ A) (x : I) :
    letI := I.unitizationModule
    (((u • x : I) : A) : Unitization ℂ A) = u * ((x : A) : Unitization ℂ A) := by
  let _ : Module (Unitization ℂ A) I := I.unitizationModule
  ext
  · simp
  · simp

/-- The left `Unitization ℂ A`-module structure on a closed two-sided ideal `I` is compatible with
its `ℂ`-module structure. -/
theorem isScalarTower_unitizationModule :
    letI := I.unitizationModule
    IsScalarTower ℂ (Unitization ℂ A) I := by
  let _ := I.unitizationModule
  exact ⟨fun r u x => Subtype.ext <| by simp [smul_add, mul_smul, smul_mul_assoc]⟩

end Unitization

end TwoSidedIdeal
