/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Connection.Right.Basic
public import Mathlib.LinearAlgebra.Projection

/-!
# Grassmann connections and their curvature

An idempotent right-module endomorphism `p` projects an ambient connection `c` to the
connection `x ↦ p(c x)` on its range. Applied to a coordinate connection on a finite free
module, this is the Grassmann connection on a projective module.

The derivative of an endomorphism is the commutator `[c,T]`. The curvature of the projected
connection is the projected ambient curvature plus `p [[c₁,p],[c₂,p]]` on the range of `p`.
For a flat ambient connection this is the familiar formula `p (dp ∧ dp)` used to compare
curvature traces with cyclic cocycles. No choice of matrix coordinates, self-adjointness of
`p`, or analytic structure is needed for these algebraic identities.

## References

* A. Connes, *Noncommutative Geometry*, Chapter IV, §6, connections and curvature on
  finite projective smooth modules.
-/

public section

namespace TauCeti.RightConnection

open MulOpposite

variable {k A E : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup E] [Module k E] [Module Aᵐᵒᵖ E]
  {D D₁ D₂ : derivationLieAlgebra k A}

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

variable [IsScalarTower k Aᵐᵒᵖ E]

/-- Projecting a connection by an idempotent gives a connection on its range. In particular,
projecting `coordinate D ι` gives the Grassmann connection on a summand of a free module. -/
def project (c : RightConnection (E := E) D) (p : E →ₗ[Aᵐᵒᵖ] E)
    (hp : IsIdempotentElem p) : RightConnection (E := LinearMap.range p) D where
  toLinearMap := (p.rangeRestrict.restrictScalars k).comp
    (c.toLinearMap.comp ((LinearMap.range p).subtype.restrictScalars k))
  leibniz' a x := by
    apply Subtype.ext
    have hx := (LinearMap.IsIdempotentElem.mem_range_iff hp).mp x.property
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.codRestrict_apply, Submodule.coe_smul_of_tower,
      Submodule.subtype_apply, Submodule.coe_add, c.leibniz', LinearMap.map_add,
      LinearMap.map_smul, hx]

/-- The projected connection is the ambient derivative followed by projection. -/
@[simp]
theorem coe_project_apply (c : RightConnection (E := E) D) (p : E →ₗ[Aᵐᵒᵖ] E)
    (hp : IsIdempotentElem p) (x : LinearMap.range p) :
    (project c p hp x : E) = p (c x) := (rfl)

omit [IsScalarTower k Aᵐᵒᵖ E] in
/-- On the range of an idempotent, its derivative is the component of the ambient derivative
in the complementary kernel. -/
theorem derivativeEnd_apply_of_mem_range (c : RightConnection (E := E) D)
    {p : E →ₗ[Aᵐᵒᵖ] E} (hp : IsIdempotentElem p) (x : LinearMap.range p) :
    derivativeEnd c p x = c x - p (c x) := by
  rw [derivativeEnd_apply, (LinearMap.IsIdempotentElem.mem_range_iff hp).mp x.property]

omit [IsScalarTower k Aᵐᵒᵖ E] in
/-- The derivative of an idempotent has no range-to-range component. -/
theorem project_derivativeEnd_apply (c : RightConnection (E := E) D)
    {p : E →ₗ[Aᵐᵒᵖ] E} (hp : IsIdempotentElem p) (x : LinearMap.range p) :
    p (derivativeEnd c p x) = 0 := by
  rw [derivativeEnd_apply_of_mem_range c hp x, LinearMap.map_sub,
    (LinearMap.IsIdempotentElem.mem_range_iff hp).mp (LinearMap.mem_range_self p (c x)), sub_self]

/-- Curvature of a projected connection is projected ambient curvature plus `p (dp ∧ dp)`.
The order of the connections fixes the orientation of the commutator. -/
theorem coe_curvature_project (c₁ : RightConnection (E := E) D₁)
    (c₂ : RightConnection (E := E) D₂)
    (hD : Commute (D₁ : Module.End k A) (D₂ : Module.End k A))
    (p : E →ₗ[Aᵐᵒᵖ] E) (hp : IsIdempotentElem p) (x : LinearMap.range p) :
    (curvature (project c₁ p hp) (project c₂ p hp) hD x : E) =
      p (curvature c₁ c₂ hD x) +
        p (derivativeEnd c₁ p (derivativeEnd c₂ p x) -
          derivativeEnd c₂ p (derivativeEnd c₁ p x)) := by
  have hterm {D D' : derivationLieAlgebra k A}
      (c : RightConnection (E := E) D) (c' : RightConnection (E := E) D') :
      p (derivativeEnd c p (derivativeEnd c' p x)) =
        p (c (p (c' x))) - p (c (c' x)) := by
    have hpp (y : E) : p (p y) = p y := LinearMap.congr_fun hp y
    rw [derivativeEnd_apply, project_derivativeEnd_apply c' hp x,
      map_zero, zero_sub, LinearMap.map_neg,
      derivativeEnd_apply_of_mem_range c' hp x, map_sub]
    simp only [LinearMap.map_sub, hpp]
    abel
  simp only [curvature_apply, Submodule.coe_sub, coe_project_apply, LinearMap.map_sub,
    hterm c₁ c₂, hterm c₂ c₁]
  abel

/-- For flat ambient connections, only the `p (dp ∧ dp)` curvature term remains. -/
theorem coe_curvature_project_of_flat (c₁ : RightConnection (E := E) D₁)
    (c₂ : RightConnection (E := E) D₂)
    (hD : Commute (D₁ : Module.End k A) (D₂ : Module.End k A))
    (hflat : curvature c₁ c₂ hD = 0)
    (p : E →ₗ[Aᵐᵒᵖ] E) (hp : IsIdempotentElem p) (x : LinearMap.range p) :
    (curvature (project c₁ p hp) (project c₂ p hp) hD x : E) =
      p (derivativeEnd c₁ p (derivativeEnd c₂ p x) -
        derivativeEnd c₂ p (derivativeEnd c₁ p x)) := by
  rw [coe_curvature_project, hflat, LinearMap.zero_apply, LinearMap.map_zero, zero_add]

end TauCeti.RightConnection
