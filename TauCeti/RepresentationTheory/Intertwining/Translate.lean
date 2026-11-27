/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Algebra.Module.Submodule.Pointwise

/-!
# Translated images under equivariant maps

A linear map into a representation can be translated before applying an equivariant operator.
The resulting family is obtained by translating a single map in the target representation.
A unit normalization changes the vectors in the family, but not their image submodules.
In particular, one can compare normalized Poincaré maps with the unnormalized projections
when selecting translates whose images span a large subspace.

The application to normalized Poincaré maps follows `New.Data.coe_normalizedPoincare` and
`New.Data.range_normalizedPoincare` in `grh/src/New/Reduction/ShortAndEnough.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
For a central group-algebra operator, Mathlib's `IntertwiningMap.centralAlgebraMul` gives the
intertwiner used below.
-/

public section

namespace Representation.IntertwiningMap

variable {A G U V W : Type*} [CommSemiring A] [Monoid G]
  [AddCommMonoid U] [Module A U] [AddCommMonoid V] [Module A V]
  [AddCommMonoid W] [Module A W] {ρ : Representation A G V} {σ : Representation A G W}

/-- Translate the values of `P` by `g`, then apply the equivariant map `f` and scale by `c`.
The source of `P` need not carry a group action. -/
def translateComp (f : IntertwiningMap ρ σ) (c : A) (P : U →ₗ[A] V) (g : G) : U →ₗ[A] W :=
  c • (f.toLinearMap.comp ((ρ g).comp P))

/-- Evaluation of the translated and scaled composite. -/
@[simp] theorem translateComp_apply (f : IntertwiningMap ρ σ) (c : A) (P : U →ₗ[A] V)
    (g : G) (u : U) : f.translateComp c P g u = c • f (ρ g (P u)) := (rfl)

/-- A translate indexed by `g * h` is obtained by acting by `g` on the `h`-translate. -/
theorem translateComp_mul (f : IntertwiningMap ρ σ) (c : A) (P : U →ₗ[A] V) (g h : G) :
    f.translateComp c P (g * h) = (σ g).comp (f.translateComp c P h) := by
  ext u
  simp [map_mul, f.isIntertwining, map_smul]

/-- The identity translate is just the scaled composite. -/
@[simp] theorem translateComp_one (f : IntertwiningMap ρ σ) (c : A) (P : U →ₗ[A] V) :
    f.translateComp c P 1 = c • f.toLinearMap.comp P := by
  ext u
  simp

open scoped Pointwise in
/-- The image of each translated map is the translate of the unscaled composite's image,
provided that the scale is a unit. -/
theorem range_translateComp_of_isUnit (f : IntertwiningMap ρ σ) {c : A} (hc : IsUnit c)
    (P : U →ₗ[A] V) (g : G) :
    (f.translateComp c P g).range = (f.toLinearMap.comp P).range.map (σ g) := by
  have htranslate : f.translateComp c P g = (σ g).comp (f.translateComp c P 1) := by
    simpa only [mul_one] using f.translateComp_mul c P g 1
  rw [htranslate, LinearMap.range_comp, translateComp_one]
  have hscale : c • f.toLinearMap.comp P =
      (DistribSMul.toLinearMap A W c).comp (f.toLinearMap.comp P) := by
    ext u
    simp
  rw [hscale, LinearMap.range_comp, ← Submodule.pointwise_smul_def,
    Submodule.smul_eq_self_of_isUnit hc]

end Representation.IntertwiningMap
