/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.LinearAlgebra.Pi

/-!
# Connections along derivations on right modules

A right connection along a derivation `D` of a possibly noncommutative algebra satisfies
`∇(ξa) = (∇ξ)a + ξD(a)`. Right modules use the native `Module Aᵐᵒᵖ E` interface, and
algebra derivations use `TauCeti.derivationLieAlgebra`.

Connections along a fixed derivation differ by right-module endomorphisms. For two commuting
derivations, the commutator of connections is a right-module endomorphism: their curvature.
The coordinate connection on a coordinate product supplies concrete flat connections and the
ambient connections from which Grassmann connections are obtained by projection. For finite
coordinate sets, these products are free right modules.

## References

* A. Connes, *Noncommutative Geometry*, Chapter IV, §6, connections on smooth modules.
-/

public section

namespace TauCeti

open MulOpposite

variable {k A E : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup E] [Module k E] [Module Aᵐᵒᵖ E]

/-- A connection along `D` on a right `A`-module: a `k`-linear map satisfying the right
Leibniz rule. No continuity or Hermitian compatibility is imposed here. -/
structure RightConnection (D : derivationLieAlgebra k A) extends E →ₗ[k] E where
  leibniz' (a : A) (x : E) :
    toLinearMap (op a • x) = op a • toLinearMap x + op ((D : Module.End k A) a) • x

namespace RightConnection

variable {D D₁ D₂ : derivationLieAlgebra k A}

instance : FunLike (RightConnection (E := E) D) E E where
  coe c := c.toLinearMap
  coe_injective c c' h := by
    cases c
    cases c'
    congr 1
    exact DFunLike.coe_injective h

instance : LinearMapClass (RightConnection (E := E) D) k E E where
  map_add c := c.toLinearMap.map_add
  map_smulₛₗ c := c.toLinearMap.map_smul

@[simp]
theorem coe_mk (f : E →ₗ[k] E) (h) :
    ⇑(RightConnection.mk (D := D) f h) = f := (rfl)

/-- Two connections are equal when they agree on every vector. -/
@[ext]
theorem ext {c c' : RightConnection (E := E) D} (h : ∀ x, c x = c' x) : c = c' :=
  DFunLike.ext _ _ h

@[simp]
theorem toLinearMap_apply (c : RightConnection (E := E) D) (x : E) :
    c.toLinearMap x = c x := (rfl)

/-- The right Leibniz rule. -/
@[simp]
theorem leibniz (c : RightConnection (E := E) D) (a : A) (x : E) :
    c (op a • x) = op a • c x + op ((D : Module.End k A) a) • x :=
  c.leibniz' a x

/-- The difference of two connections along the same derivation is right `A`-linear. -/
def difference (c c' : RightConnection (E := E) D) : E →ₗ[Aᵐᵒᵖ] E where
  toFun x := c x - c' x
  map_add' x y := by simp only [map_add]; abel
  map_smul' a x := by
    have h := congrArg₂ (· - ·) (c.leibniz a.unop x) (c'.leibniz a.unop x)
    simpa only [op_unop, add_sub_add_right_eq_sub, smul_sub, RingHom.id_apply] using h

@[simp]
theorem difference_apply (c c' : RightConnection (E := E) D) (x : E) :
    difference c c' x = c x - c' x := (rfl)

@[simp]
theorem difference_self (c : RightConnection (E := E) D) : difference c c = 0 := by
  ext x
  simp

theorem neg_difference (c c' : RightConnection (E := E) D) :
    -difference c c' = difference c' c := by
  ext x
  simp

/-- The induced derivative on right-module endomorphisms, given by `[c,T]`. -/
def derivativeEnd (c : RightConnection (E := E) D) (T : E →ₗ[Aᵐᵒᵖ] E) :
    E →ₗ[Aᵐᵒᵖ] E where
  toFun x := c (T x) - T (c x)
  map_add' x y := by simp only [map_add]; abel
  map_smul' a x := by
    have h₁ := c.leibniz a.unop (T x)
    have h₂ := congrArg T (c.leibniz a.unop x)
    simp only [op_unop, LinearMap.map_add, LinearMap.map_smul] at h₁ h₂
    simp only [LinearMap.map_smul, RingHom.id_apply, h₁, h₂, smul_sub]
    abel

@[simp]
theorem derivativeEnd_apply (c : RightConnection (E := E) D) (T : E →ₗ[Aᵐᵒᵖ] E) (x : E) :
    derivativeEnd c T x = c (T x) - T (c x) := (rfl)

theorem derivativeEnd_add (c : RightConnection (E := E) D) (T S : E →ₗ[Aᵐᵒᵖ] E) :
    derivativeEnd c (T + S) = derivativeEnd c T + derivativeEnd c S := by
  ext x
  simp only [derivativeEnd_apply, LinearMap.add_apply, map_add]
  abel

theorem derivativeEnd_sub (c : RightConnection (E := E) D) (T S : E →ₗ[Aᵐᵒᵖ] E) :
    derivativeEnd c (T - S) = derivativeEnd c T - derivativeEnd c S := by
  ext x
  simp only [derivativeEnd_apply, LinearMap.sub_apply, map_sub]
  abel

@[simp]
theorem derivativeEnd_one (c : RightConnection (E := E) D) : derivativeEnd c 1 = 0 := by
  ext x
  simp

/-- The induced derivative satisfies the Leibniz rule for composition of endomorphisms. -/
theorem derivativeEnd_mul (c : RightConnection (E := E) D) (T S : E →ₗ[Aᵐᵒᵖ] E) :
    derivativeEnd c (T * S) = derivativeEnd c T * S + T * derivativeEnd c S := by
  ext x
  simp only [derivativeEnd_apply, mul_apply_eq_comp, LinearMap.add_apply, map_sub]
  abel

variable [IsScalarTower k Aᵐᵒᵖ E]

/-- Adding a right-module endomorphism to a connection gives a connection along the same
algebra derivation. -/
def addEnd (c : RightConnection (E := E) D) (T : E →ₗ[Aᵐᵒᵖ] E) :
    RightConnection (E := E) D where
  toLinearMap := c.toLinearMap + T.restrictScalars k
  leibniz' a x := by
    simp only [LinearMap.add_apply, LinearMap.restrictScalars_apply, c.leibniz',
      LinearMap.map_smul, smul_add]
    abel

@[simp]
theorem addEnd_apply (c : RightConnection (E := E) D) (T : E →ₗ[Aᵐᵒᵖ] E) (x : E) :
    addEnd c T x = c x + T x := (rfl)

@[simp]
theorem addEnd_zero (c : RightConnection (E := E) D) : addEnd c 0 = c := by
  ext x
  simp

theorem addEnd_addEnd (c : RightConnection (E := E) D) (T S : E →ₗ[Aᵐᵒᵖ] E) :
    addEnd (addEnd c T) S = addEnd c (T + S) := by
  ext x
  simp only [addEnd_apply, LinearMap.add_apply, add_assoc]

/-- Every connection is obtained from any other by adding its difference. -/
@[simp]
theorem addEnd_difference (c c' : RightConnection (E := E) D) :
    addEnd c' (difference c c') = c := by
  ext x
  simp

/-- Adding an endomorphism changes a connection by exactly that endomorphism. -/
@[simp]
theorem difference_addEnd (c : RightConnection (E := E) D) (T : E →ₗ[Aᵐᵒᵖ] E) :
    difference (addEnd c T) c = T := by
  ext x
  simp

omit [IsScalarTower k Aᵐᵒᵖ E] in
/-- For commuting algebra derivations the commutator of connections is right `A`-linear. -/
def curvature (c₁ : RightConnection (E := E) D₁) (c₂ : RightConnection (E := E) D₂)
    (hD : Commute (D₁ : Module.End k A) (D₂ : Module.End k A)) : E →ₗ[Aᵐᵒᵖ] E where
  toFun x := c₁ (c₂ x) - c₂ (c₁ x)
  map_add' x y := by simp only [map_add]; abel
  map_smul' a x := by
    have h := LinearMap.congr_fun hD.eq a.unop
    simp only [mul_apply_eq_comp] at h
    rw [← op_unop a]
    simp only [leibniz, map_add, RingHom.id_apply, smul_sub, h]
    abel

omit [IsScalarTower k Aᵐᵒᵖ E] in
/-- Curvature acts by the commutator of the two covariant derivatives. -/
@[simp]
theorem curvature_apply (c₁ : RightConnection (E := E) D₁)
    (c₂ : RightConnection (E := E) D₂)
    (hD : Commute (D₁ : Module.End k A) (D₂ : Module.End k A)) (x : E) :
    curvature c₁ c₂ hD x = c₁ (c₂ x) - c₂ (c₁ x) := (rfl)

omit [IsScalarTower k Aᵐᵒᵖ E] in
/-- Swapping the connections negates their curvature. -/
theorem curvature_swap (c₁ : RightConnection (E := E) D₁)
    (c₂ : RightConnection (E := E) D₂)
    (hD : Commute (D₁ : Module.End k A) (D₂ : Module.End k A)) :
    curvature c₂ c₁ hD.symm = -curvature c₁ c₂ hD := by
  ext x
  simp

/-- The coordinate connection on a coordinate product differentiates each coordinate.
For finite `ι`, this is a connection on a free right module. -/
def coordinate (D : derivationLieAlgebra k A) (ι : Type*) :
    RightConnection (E := ι → A) D where
  toLinearMap := LinearMap.piMap fun _ ↦ (D : Module.End k A)
  leibniz' a x := by
    ext i
    simpa only [LinearMap.coe_piMap, Pi.map_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul_unop, unop_op, add_comm] using
      derivationLieAlgebra.leibniz D (x i) a

@[simp]
theorem coordinate_apply (D : derivationLieAlgebra k A) {ι : Type*} (x : ι → A) (i : ι) :
    coordinate D ι x i = (D : Module.End k A) (x i) := (rfl)

/-- Coordinate connections along commuting derivations are flat. -/
@[simp]
theorem curvature_coordinate (ι : Type*)
    (hD : Commute (D₁ : Module.End k A) (D₂ : Module.End k A)) :
    curvature (coordinate D₁ ι) (coordinate D₂ ι) hD = 0 := by
  ext x i
  simp only [curvature_apply, coordinate_apply, LinearMap.zero_apply, Pi.sub_apply,
    Pi.zero_apply, sub_eq_zero]
  exact LinearMap.congr_fun hD.eq (x i)

end RightConnection

end TauCeti
