/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Module.ZMod

/-!
# Torsion in additive subgroups

Every additive subgroup `H` of a `ℤ`-torsion-free abelian group `G` inherits
`ℤ`-torsion-freeness along `H.subtype` (`AddSubgroup.instIsTorsionFree`), matching
`Submodule.instIsTorsionFree`.

If an additive subgroup `D` contains all the `n`-torsion of `A`, then its own `n`-torsion is
linearly equivalent to the ambient `n`-torsion over `ZMod n`, for any module structures on
these groups (`AddSubgroup.torsionByEquivOfLE`). This includes `n = 0`.
-/

public section

namespace AddSubgroup

/-- An additive subgroup of a torsion-free abelian group is torsion-free over `ℤ`. -/
instance instIsTorsionFree {G : Type*} [AddCommGroup G] [Module.IsTorsionFree ℤ G]
    (H : AddSubgroup G) : Module.IsTorsionFree ℤ H :=
  H.subtype_injective.moduleIsTorsionFree H.subtype fun _ _ ↦ rfl

/-- If `D` contains the ambient `n`-torsion, it has the same `n`-torsion as the ambient group.
The equivalence respects any supplied `ZMod n`-module structures, including when `n = 0`. -/
noncomputable def torsionByEquivOfLE {A : Type*} [AddCommGroup A] (D : AddSubgroup A)
    (n : ℕ) [Module (ZMod n) A[n]] [Module (ZMod n) D[n]]
    (hD : A[n] ≤ D) : A[n] ≃ₗ[ZMod n] D[n] := by
  let f : A[n] →+ D[n] :=
    { toFun := fun x ↦ ⟨⟨x, hD x.property⟩, torsionBy.nsmul_iff.mpr <|
        Subtype.ext (torsionBy.nsmul_iff.mp x.property)⟩
      map_zero' := Subtype.ext (Subtype.ext rfl)
      map_add' := fun _ _ ↦ Subtype.ext (Subtype.ext rfl) }
  exact LinearEquiv.ofBijective (f.toZModLinearMap n)
    ⟨fun _ _ h ↦ Subtype.ext (congrArg (fun x ↦ x.val.val) h),
      fun y ↦ ⟨⟨y.val.val, torsionBy.nsmul_iff.mpr <|
        congrArg Subtype.val (torsionBy.nsmul_iff.mp y.property)⟩, rfl⟩⟩

/-- The equivalence with torsion inside a subgroup preserves the underlying ambient element. -/
@[simp↓]
theorem torsionByEquivOfLE_apply_coe {A : Type*} [AddCommGroup A] (D : AddSubgroup A)
    (n : ℕ) [Module (ZMod n) A[n]] [Module (ZMod n) D[n]]
    (hD : A[n] ≤ D) (x : A[n]) : ((D.torsionByEquivOfLE n hD x : D) : A) = x := by
  unfold torsionByEquivOfLE
  erw [LinearEquiv.ofBijective_apply, AddMonoidHom.coe_toZModLinearMap]
  -- The remaining coercions project the subtype constructors in the additive homomorphism.
  rfl

/-- The inverse equivalence with torsion inside a subgroup preserves the ambient element. -/
@[simp↓]
theorem torsionByEquivOfLE_symm_apply_coe {A : Type*} [AddCommGroup A] (D : AddSubgroup A)
    (n : ℕ) [Module (ZMod n) A[n]] [Module (ZMod n) D[n]]
    (hD : A[n] ≤ D) (x : D[n]) : ((D.torsionByEquivOfLE n hD).symm x : A) = (x : D) := by
  simpa only [LinearEquiv.apply_symm_apply] using
    (D.torsionByEquivOfLE_apply_coe n hD ((D.torsionByEquivOfLE n hD).symm x)).symm

end AddSubgroup
