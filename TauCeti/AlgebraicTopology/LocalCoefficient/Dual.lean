/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import TauCeti.AlgebraicTopology.LocalCoefficient

/-!
# The dual of a local coefficient system

Let `L` be a local coefficient system of modules over a commutative ring `R` on a space `X`, a
functor from the fundamental groupoid of `X` to `R`-modules. Its **dual** `L^∨`
(`TauCeti.LocalCoefficientSystem.dual`) has fibre `Hom_R(L(x), R)` at `x`, and transports a linear
form along a path class `γ` from `x` to `y` by precomposing it with transport in `L` along the
reversed path:

`transport L^∨ γ = ((transport L γ)⁻¹)^*` (`TauCeti.LocalCoefficientSystem.transport_dual`).

Equivalently, transport in `L^∨` and in `L` preserve the evaluation pairing
`Hom_R(L(x), R) × L(x) → R`. Since the fundamental groupoid is a groupoid, reversing paths turns
the contravariant functor `x ↦ Hom_R(L(x), R)` back into a covariant one.

The dual system is the coefficient system of the cochains dual to the chains with coefficients in
`L`. In Morse theory, the Morse complex of `-f` with coefficients in `L^∨` is the signed dual of the
Morse complex of `f` with coefficients in `L` on an oriented manifold
(`TauCeti.Geometry.Manifold.Morse.Boundary.TwistedDual`).

## Main definitions

* `TauCeti.LocalCoefficientSystem.dual`: the dual `x ↦ Hom_R(L(x), R)` of a local coefficient
  system.

## Main results

* `TauCeti.LocalCoefficientSystem.transport_dual`: transport in the dual system is the dual map of
  the inverse of transport, that is, of transport along the reversed path.
* `TauCeti.LocalCoefficientSystem.transport_dual_symm`: transport in the dual system along a
  reversed path is the dual map of transport along the path.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §3.H (local coefficients).
-/

public section

universe u v

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [CommRing R] {X : TopCat.{v}}

/-- **The dual of a local coefficient system.** Its fibre at `x` is the dual module
`Hom_R(L(x), R)`, and a path class `γ` acts by the dual map of transport along the reversed
path. -/
-- The body is exposed: statements about the dual system read its fibres as the dual modules.
@[expose]
noncomputable def dual (L : LocalCoefficientSystem.{u, v, u} R X) :
    LocalCoefficientSystem.{u, v, u} R X where
  obj x := ModuleCat.of R (Module.Dual R (L.obj x))
  map γ := ModuleCat.ofHom (transport L γ.symm).toLinearMap.dualMap
  map_id x := by
    ext φ a
    rw [FundamentalGroupoid.id_eq_path_refl]
    simp
  map_comp γ δ := by
    ext φ a
    rw [FundamentalGroupoid.comp_eq]
    simp

variable (L : LocalCoefficientSystem.{u, v, u} R X)

/-- The fibre of the dual system at `x` is the dual of the fibre of `L` at `x`. -/
theorem dual_obj (x : FundamentalGroupoid X) :
    L.dual.obj x = ModuleCat.of R (Module.Dual R (L.obj x)) :=
  (rfl)

/-- **Transport in the dual system** along `γ` is the dual map of the inverse of transport in `L`
along `γ`. -/
@[simp]
theorem transport_dual {x y : X} (γ : Path.Homotopic.Quotient x y) :
    transport L.dual γ = (transport L γ).symm.dualMap := by
  rw [← transport_symm]
  -- Transport is the action of the path class, which for the dual system is this dual map.
  exact LinearEquiv.ext fun φ ↦ transport_apply L.dual γ φ

/-- Transport in the dual system along the reversed path `γ⁻¹` is the dual map of transport in `L`
along `γ`. -/
theorem transport_dual_symm {x y : X} (γ : Path.Homotopic.Quotient x y) :
    transport L.dual γ.symm = (transport L γ).dualMap := by
  refine LinearEquiv.ext fun φ ↦ LinearMap.ext fun a ↦ ?_
  simp only [transport_dual, transport_symm]
  -- Both sides evaluate `φ` on `(transport L γ).symm.symm a`, which is `transport L γ a`.
  rfl

end TauCeti.LocalCoefficientSystem
