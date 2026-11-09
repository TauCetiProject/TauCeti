/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import TauCeti.Algebra.AddCircle

/-!
# Residue-ring forms of finite bilinear modules

On a finite bilinear module killed by `n`, the pairing takes values in the `n`-torsion of
`ℚ/ℤ`. Reading those values through `ZMod.toRatAddCircle` gives a symmetric bilinear form
with values in `ZMod n`. For prime `n` this lets finite-field linear algebra classify the
original pairing. The scalar action is any `ZMod n`-module structure on the given group;
additive maps are automatically linear for this action.

`zmodForm` is characterized by `toRatAddCircle_zmodForm`. Nondegeneracy, alternation and
isometry are preserved and reflected by this passage to the residue ring.
-/

public section

namespace TauCeti.FiniteBilinearModule

variable (A : FiniteBilinearModule) (n : ℕ) [NeZero n] [Module (ZMod n) A]

/-- The pairing of a module killed by `n`, read as a `ZMod n`-valued bilinear form. -/
noncomputable def zmodForm : LinearMap.BilinForm (ZMod n) A := by
  classical
  have h (x y : A) : ∃ a : ZMod n, ZMod.toRatAddCircle n a = A.pairing x y :=
    ZMod.exists_toRatAddCircle_eq_of_nsmul_eq_zero n (by
      rw [← pairing_nsmul_left, ZModModule.char_nsmul_eq_zero n, pairing_zero_left])
  let f (x y : A) : ZMod n := Classical.choose (h x y)
  have hf (x y : A) : ZMod.toRatAddCircle n (f x y) = A.pairing x y :=
    Classical.choose_spec (h x y)
  let g : A →+ A →+ ZMod n :=
    { toFun := fun x ↦
        { toFun := f x
          map_zero' := by
            apply ZMod.toRatAddCircle_injective n
            simp [hf]
          map_add' := fun y z ↦ by
            apply ZMod.toRatAddCircle_injective n
            simp [hf, pairing_add_right] }
      map_zero' := by
        ext y
        apply ZMod.toRatAddCircle_injective n
        simpa only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, hf,
          AddMonoidHom.zero_apply, map_zero] using A.pairing_zero_left y
      map_add' := fun x y ↦ by
        ext z
        apply ZMod.toRatAddCircle_injective n
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_add, hf,
          AddMonoidHom.add_apply]
        rfl }
  exact LinearMap.mk₂ (ZMod n) (fun x y ↦ g x y)
    (fun x y z ↦ DFunLike.congr_fun (g.map_add x y) z)
    (fun c x y ↦ by rw [ZMod.map_smul, AddMonoidHom.smul_apply, smul_eq_mul])
    (fun x y z ↦ (g x).map_add y z)
    (fun c x y ↦ by rw [ZMod.map_smul, smul_eq_mul])

/-- Reading a residue-ring pairing back in `ℚ/ℤ` recovers the original pairing. -/
@[simp] theorem toRatAddCircle_zmodForm (x y : A) :
    ZMod.toRatAddCircle n (A.zmodForm n x y) = A.pairing x y := by
  dsimp [zmodForm]
  exact Classical.choose_spec
    (ZMod.exists_toRatAddCircle_eq_of_nsmul_eq_zero n (v := A.pairing x y) (by
      rw [← pairing_nsmul_left, ZModModule.char_nsmul_eq_zero n, pairing_zero_left]))

/-- The residue-ring form is symmetric. -/
@[simp] theorem isSymm_zmodForm : (A.zmodForm n).IsSymm := by
  refine ⟨fun x y ↦ ?_⟩
  apply ZMod.toRatAddCircle_injective n
  simp only [toRatAddCircle_zmodForm]
  exact A.pairing_comm x y

/-- Nondegeneracy of the residue-ring form is equivalent to perfection of the original
finite pairing. -/
@[simp] theorem nondegenerate_zmodForm_iff :
    (A.zmodForm n).Nondegenerate ↔ A.IsNondegenerate := by
  constructor
  · intro h
    apply A.isNondegenerate_of_injective
    intro x y hxy
    have hzero : x - y = 0 := h.1 _ fun z ↦ by
      apply ZMod.toRatAddCircle_injective n
      simp only [map_sub, LinearMap.sub_apply, toRatAddCircle_zmodForm, map_zero]
      rw [DFunLike.congr_fun hxy z, sub_self]
    exact sub_eq_zero.mp hzero
  · intro h
    have hl : (A.zmodForm n).SeparatingLeft := fun x hx ↦
      IsNondegenerate.eq_zero_of_forall_pairing_eq_zero A h fun y ↦ by
        rw [← toRatAddCircle_zmodForm A n, hx y, map_zero]
    exact ⟨hl, fun x hx ↦ hl x fun y ↦ (A.isSymm_zmodForm n).eq x y |>.trans (hx y)⟩

/-- Alternation can be tested before or after reading the pairing in the residue ring. -/
@[simp] theorem isAlt_zmodForm_iff :
    (A.zmodForm n).IsAlt ↔ ∀ x : A, A.pairing x x = 0 := by
  constructor
  · intro h x
    rw [← toRatAddCircle_zmodForm A n, h.self_eq_zero, map_zero]
  · intro h
    exact fun x ↦ (ZMod.toRatAddCircle_eq_zero n).mp (by simp [h])

/-- Isometry of the finite pairings is equivalent to isometry of their residue-ring forms. -/
theorem nonempty_isometry_iff_equivalent_zmodForm (B : FiniteBilinearModule)
    [Module (ZMod n) B] :
    Nonempty (Isometry A B) ↔ (A.zmodForm n).Equivalent (B.zmodForm n) := by
  constructor
  · rintro ⟨f⟩
    exact ⟨{ toLinearEquiv := { f.toAddEquiv with map_smul' := ZMod.map_smul f.toAddEquiv }
             map_app' := fun x y ↦ ZMod.toRatAddCircle_injective n (by
               simp only [toRatAddCircle_zmodForm, AddEquiv.toFun_eq_coe,
                 Isometry.coe_toAddEquiv, f.map_pairing]) }⟩
  · rintro ⟨f⟩
    exact ⟨{ toAddEquiv := f.toLinearEquiv.toAddEquiv
             map_pairing' := fun x y ↦ by
               rw [← toRatAddCircle_zmodForm A n, ← toRatAddCircle_zmodForm B n]
               exact congrArg (ZMod.toRatAddCircle n) (f.map_app' x y) }⟩

end TauCeti.FiniteBilinearModule
