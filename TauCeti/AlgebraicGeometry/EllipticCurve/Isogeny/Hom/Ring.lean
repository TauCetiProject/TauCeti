/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.PointMap
-- Proof-only: base change to a separable closure, on points and on morphisms.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
-- Proof-only: an elliptic curve has infinitely many points over a separably closed field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed
-- Proof-only: every isogeny is a separable isogeny after a Frobenius power.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
-- Proof-only: relative Frobenius acts on points by powering the coordinates.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Point

/-!
# The endomorphism ring of an elliptic curve

Composition of morphisms of elliptic curves is additive in the outer morphism by construction
(`TauCeti.Isogeny.Hom.add_comp`), the sum of morphisms being computed on their tautological points.
This file proves that it is additive in the inner morphism as well, over every field, so that
composition is biadditive and the endomorphisms `Hom W W` of an elliptic curve form a ring
(Silverman III.4).

Additivity in the inner morphism is a statement about points: two morphisms are equal once they
agree on infinitely many points, so over a separably closed field `h ∘ (f + g) = h ∘ f + h ∘ g`
follows once `h` acts additively on points (`TauCeti.Isogeny.Hom.comp_add_of_pointMap_add`). That
every morphism acts additively on points is Silverman III.4.8. A separable isogeny over a
separably closed field acts through the class-group point map, which is additive by construction
(`TauCeti.Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom`). Every isogeny factors as a separable one
after a Frobenius power `F^r : W → W⁽ᵖʳ⁾` (Silverman II.2.12), and `F^r` sends `(x, y)` to
`(x ^ p ^ r, y ^ p ^ r)` (`TauCeti.Isogeny.pointMap_iterateRelativeFrobeniusIsogeny`), which is
additive because the Frobenius of the field is a ring homomorphism. Over an arbitrary field, both
additivity statements are compared after base change to a separable closure: on points, which embed
additively and compatibly with the action of morphisms (`TauCeti.Isogeny.Hom.pointMap_map`), and on
morphisms, along the faithful, additive base change (`TauCeti.Isogeny.Hom.map_injective`).

## Main results

* `TauCeti.Isogeny.Hom.pointMap_add`: every morphism acts additively on points, over any field
  (Silverman III.4.8), with `pointMap_neg`, `pointMap_sub`, `pointMap_nsmul` and `pointMap_zsmul`.
* `TauCeti.Isogeny.Hom.comp_add`: composition is additive in the inner morphism, over any field.
* `TauCeti.Isogeny.Hom.compLeftHom`: postcomposition by a morphism, as an additive homomorphism.
* The `Ring (Hom W W)` and `IsDomain (Hom W W)` instances.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.11–12 and III.4.
-/

public section

open WeierstrassCurve.Affine

namespace TauCeti.Isogeny.Hom

variable {F : Type*} [Field F] {W₁ W₂ W₃ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic]

section PointMap

variable [DecidableEq F]

-- The separable case of `pointMap_add`: the action is the additive class-group point map.
private theorem pointMap_ofIsogeny_add_of_isSeparable [IsSepClosed F] (φ : Isogeny W₁ W₂)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] (P Q : W₁.Point) :
    (ofIsogeny φ).pointMap (P + Q) = (ofIsogeny φ).pointMap P + (ofIsogeny φ).pointMap Q := by
  have := W₂.isIntegrallyClosed_coordinateRing
  rw [pointMap_ofIsogeny_eq_toPointHom, _root_.map_add, ← pointMap_ofIsogeny_eq_toPointHom,
    ← pointMap_ofIsogeny_eq_toPointHom]

-- `pointMap_add` over a separably closed field, where `φ` factors as a separable isogeny after a
-- Frobenius power.
private theorem pointMap_add_of_isSepClosed [IsSepClosed F] (f : Hom W₁ W₂) (P Q : W₁.Point) :
    f.pointMap (P + Q) = f.pointMap P + f.pointMap Q := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp only [zero_pointMap, add_zero]
  -- `φ = χ ∘ F^r` with `χ` separable and `F^r` the `r`-fold relative Frobenius
  obtain ⟨r, χ, hχ, rfl⟩ :=
    exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq (ringExpChar F) φ
  simp only [← ofIsogeny_comp_ofIsogeny, comp_pointMap, pointMap_iterateRelativeFrobeniusIsogeny,
    Point.mapAlong_add, pointMap_ofIsogeny_add_of_isSeparable]

/-- **Every morphism of elliptic curves acts additively on points** (Silverman III.4.8). -/
@[simp]
theorem pointMap_add (f : Hom W₁ W₂) (P Q : W₁.Point) :
    f.pointMap (P + Q) = f.pointMap P + f.pointMap Q := by
  classical
  -- compare both sides over a separable closure, into which points embed additively
  let ι := algebraMap F (SeparableClosure F)
  apply Point.mapAlong_injective ι ι.injective
  rw [Point.mapAlong_add, ← pointMap_map, ← pointMap_map, ← pointMap_map, Point.mapAlong_add,
    pointMap_add_of_isSepClosed]

/-- **The action of a morphism on points, as a homomorphism of point groups.** -/
noncomputable def pointMapHom (f : Hom W₁ W₂) : W₁.Point →+ W₂.Point :=
  AddMonoidHom.mk' f.pointMap (pointMap_add f)

@[simp]
theorem pointMapHom_apply (f : Hom W₁ W₂) (P : W₁.Point) : f.pointMapHom P = f.pointMap P :=
  (rfl)

@[simp]
theorem pointMap_neg (f : Hom W₁ W₂) (P : W₁.Point) : f.pointMap (-P) = -f.pointMap P :=
  f.pointMapHom.map_neg P

@[simp]
theorem pointMap_sub (f : Hom W₁ W₂) (P Q : W₁.Point) :
    f.pointMap (P - Q) = f.pointMap P - f.pointMap Q :=
  f.pointMapHom.map_sub P Q

/-- **Every morphism commutes with natural multiples of points.** -/
@[simp]
theorem pointMap_nsmul (f : Hom W₁ W₂) (n : ℕ) (P : W₁.Point) :
    f.pointMap (n • P) = n • f.pointMap P :=
  f.pointMapHom.map_nsmul n P

/-- **Every morphism commutes with integer multiples of points.** -/
@[simp]
theorem pointMap_zsmul (f : Hom W₁ W₂) (n : ℤ) (P : W₁.Point) :
    f.pointMap (n • P) = n • f.pointMap P :=
  f.pointMapHom.map_zsmul n P

end PointMap

/-- **Composition is additive in the inner morphism**, over any field. -/
@[simp]
theorem comp_add [W₃.IsElliptic] (h : Hom W₂ W₃) (f g : Hom W₁ W₂) :
    h.comp (f + g) = h.comp f + h.comp g := by
  classical
  -- compare both sides over a separable closure, where `h` acts additively on the infinitely
  -- many points of `W₁`
  refine map_injective (algebraMap F (SeparableClosure F)) ?_
  simp only [comp_map, map_add]
  exact comp_add_of_pointMap_add _ (pointMap_add _) _ _

/-- **Postcomposition by `h`, as a homomorphism of the additive groups of morphisms.** -/
noncomputable def compLeftHom [W₃.IsElliptic] (h : Hom W₂ W₃) :
    Hom W₁ W₂ →+ Hom W₁ W₃ :=
  AddMonoidHom.mk' h.comp (comp_add h)

@[simp]
theorem compLeftHom_apply [W₃.IsElliptic] (h : Hom W₂ W₃) (f : Hom W₁ W₂) :
    compLeftHom h f = h.comp f := (rfl)

/-- **Composition commutes with negation in the inner morphism.** -/
@[simp]
theorem comp_neg [W₃.IsElliptic] (h : Hom W₂ W₃) (f : Hom W₁ W₂) :
    h.comp (-f) = -h.comp f :=
  (compLeftHom h).map_neg f

/-- **Composition respects subtraction in the inner morphism.** -/
@[simp]
theorem comp_sub [W₃.IsElliptic] (h : Hom W₂ W₃) (f g : Hom W₁ W₂) :
    h.comp (f - g) = h.comp f - h.comp g :=
  (compLeftHom h).map_sub f g

/-- **Composition is `ℤ`-linear in the inner morphism.** -/
@[simp]
theorem comp_zsmul [W₃.IsElliptic] (h : Hom W₂ W₃) (n : ℤ) (f : Hom W₁ W₂) :
    h.comp (n • f) = n • h.comp f :=
  (compLeftHom h).map_zsmul n f

/-- **Composition is `ℕ`-linear in the inner morphism**, the rule for a natural scalar. -/
@[simp]
theorem comp_nsmul [W₃.IsElliptic] (h : Hom W₂ W₃) (n : ℕ) (f : Hom W₁ W₂) :
    h.comp (n • f) = n • h.comp f :=
  (compLeftHom h).map_nsmul n f

/-- **The endomorphisms of an elliptic curve form a ring**, with addition the group law on
morphisms and multiplication composition (Silverman III.4). -/
noncomputable instance : Ring (Hom W₁ W₁) where
  __ := (inferInstance : MonoidWithZero (Hom W₁ W₁))
  __ := (inferInstance : AddCommGroup (Hom W₁ W₁))
  left_distrib := comp_add
  right_distrib g g' f := add_comp g g' f

/-- **The endomorphism ring of an elliptic curve is a domain**: a composite of isogenies is an
isogeny. -/
instance : IsDomain (Hom W₁ W₁) :=
  NoZeroDivisors.to_isDomain _

end TauCeti.Isogeny.Hom

end
