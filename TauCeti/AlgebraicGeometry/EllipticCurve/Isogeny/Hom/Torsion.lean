/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
public import TauCeti.Algebra.Module.Torsion.Snake
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure
import Mathlib.Algebra.Module.ZMod

/-!
# The action of an elliptic-curve morphism on torsion

A morphism of elliptic curves sends `N`-torsion points to `N`-torsion points. This file packages
that action as a `ZMod N`-linear map, the restriction `TauCeti.torsionByMap` of the morphism's
point map. The construction is functorial in the morphism: it respects zero, identities, addition,
negation, subtraction, integer multiples and composition.

The finite-level action is the bridge from the intrinsic endomorphism ring to matrices. Whenever
`E[N]` is free over `ZMod N` (for instance of rank two, when `F` is separably closed and `N` is
invertible in `F`), `LinearMap.toMatrix` turns each value of `Hom.torsionRepresentation` into a
matrix after a basis is chosen; this is the matrix representation used in the Weil-pairing proof
of the Hasse bound. There, `Hom.torsionLinearMap_apply` supplies the point-map hypotheses of
`TauCeti.Isogeny.weilPairing_eq_degree_nsmul_weilPairing`, which says that an isogeny scales the
Weil pairing by its degree.

## Main definitions

* `TauCeti.Isogeny.Hom.torsionLinearMap`: the `ZMod N`-linear action of a morphism on `N`-torsion.
* `TauCeti.Isogeny.Hom.torsionRepresentation`: the resulting ring representation of `End(E)`.

## Main results

* `TauCeti.Isogeny.Hom.torsionLinearMap_comp`: the torsion action is functorial.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and III.8.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

namespace Hom

variable {W₁ W₂ W₃ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **The action of a morphism on `N`-torsion**, as a `ZMod N`-linear map.

The underlying additive map is `TauCeti.torsionByMap` applied to `Hom.pointMapHom`: the point map
restricted to the torsion submodules, which lands in the target torsion because it is additive. -/
noncomputable def torsionLinearMap (f : Hom W₁ W₂) (N : ℕ) :
    AddSubgroup.torsionBy W₁.Point (N : ℤ) →ₗ[ZMod N]
      AddSubgroup.torsionBy W₂.Point (N : ℤ) :=
  AddMonoidHom.toZModLinearMap N (M := AddSubgroup.torsionBy W₁.Point (N : ℤ))
    (M₁ := AddSubgroup.torsionBy W₂.Point (N : ℤ))
    (torsionByMap (N : ℤ) f.pointMapHom.toIntLinearMap).toAddMonoidHom

/-- The torsion action is the morphism's point map on underlying points. -/
@[simp]
theorem torsionLinearMap_apply (f : Hom W₁ W₂) (N : ℕ)
    (P : AddSubgroup.torsionBy W₁.Point (N : ℤ)) :
    (f.torsionLinearMap N P : W₂.Point) = f.pointMap P :=
  (coe_torsionByMap_apply (N : ℤ) f.pointMapHom.toIntLinearMap P).trans (f.pointMapHom_apply _)

/-- The zero morphism acts as the zero map on torsion. -/
@[simp]
theorem torsionLinearMap_zero (N : ℕ) :
    (0 : Hom W₁ W₂).torsionLinearMap N = 0 := by
  ext P
  simp

/-- The identity morphism acts as the identity map on torsion. -/
@[simp]
theorem torsionLinearMap_id (N : ℕ) :
    (id W₁).torsionLinearMap N = LinearMap.id := by
  ext P
  simp

/-- The torsion action is additive in the morphism. -/
@[simp]
theorem torsionLinearMap_add (f g : Hom W₁ W₂) (N : ℕ) :
    (f + g).torsionLinearMap N = f.torsionLinearMap N + g.torsionLinearMap N := by
  ext P
  simp

/-- Negating a morphism negates its action on torsion. -/
@[simp]
theorem torsionLinearMap_neg (f : Hom W₁ W₂) (N : ℕ) :
    (-f).torsionLinearMap N = -f.torsionLinearMap N := by
  ext P
  simp

/-- Subtraction of morphisms becomes subtraction of their actions on torsion. -/
@[simp]
theorem torsionLinearMap_sub (f g : Hom W₁ W₂) (N : ℕ) :
    (f - g).torsionLinearMap N = f.torsionLinearMap N - g.torsionLinearMap N := by
  rw [sub_eq_add_neg, torsionLinearMap_add, torsionLinearMap_neg, sub_eq_add_neg]

/-- Integer multiples of a morphism act by the same integer multiple on torsion. -/
@[simp]
theorem torsionLinearMap_zsmul (f : Hom W₁ W₂) (N : ℕ) (n : ℤ) :
    (n • f).torsionLinearMap N = n • f.torsionLinearMap N := by
  ext P
  simp

/-- Natural multiples of a morphism act by the same natural multiple on torsion. -/
@[simp]
theorem torsionLinearMap_nsmul (f : Hom W₁ W₂) (N n : ℕ) :
    (n • f).torsionLinearMap N = n • f.torsionLinearMap N := by
  ext P
  simp

/-- **The torsion action is functorial**: the action of a composite is the composite of the
actions. -/
@[simp]
theorem torsionLinearMap_comp [W₃.IsElliptic] (g : Hom W₂ W₃) (f : Hom W₁ W₂) (N : ℕ) :
    (g.comp f).torsionLinearMap N = (g.torsionLinearMap N).comp (f.torsionLinearMap N) := by
  ext P
  simp

/-- **The action of the endomorphism ring on `N`-torsion.** This packages additivity and
functoriality of `torsionLinearMap` as a ring homomorphism, ready to be written as matrices after
choosing a basis of the torsion module whenever it is free. -/
noncomputable def torsionRepresentation (W : WeierstrassCurve.Affine F) [W.IsElliptic] (N : ℕ) :
    Hom W W →+* Module.End (ZMod N) (AddSubgroup.torsionBy W.Point (N : ℤ)) where
  toFun f := f.torsionLinearMap N
  map_zero' := torsionLinearMap_zero N
  map_one' := by rw [one_def, torsionLinearMap_id, Module.End.one_eq_id]
  map_add' f g := torsionLinearMap_add f g N
  map_mul' f g := by rw [mul_def, Module.End.mul_eq_comp, torsionLinearMap_comp]

/-- The torsion representation sends an endomorphism to its torsion linear map. -/
@[simp]
theorem torsionRepresentation_apply (W : WeierstrassCurve.Affine F) [W.IsElliptic] (N : ℕ)
    (f : Hom W W) : torsionRepresentation W N f = f.torsionLinearMap N :=
  (rfl)

end Hom

end TauCeti.Isogeny

end
