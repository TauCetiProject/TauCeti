/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Fixed
public import TauCeti.Algebra.HopfAlgebra.Cointegral.Basic
public import Mathlib.LinearAlgebra.Projection

/-!
# Projecting a comodule onto its invariants

Applying a left cointegral to the coalgebra factor of a right coaction gives an invariant
vector. For a normalized cointegral this is the Reynolds projection onto the fixed submodule.
Mathlib's `LinearMap.IsProj` then supplies the retraction, its kernel complement over rings,
and the characterization of invariants as the vectors fixed by the projection.

For the coordinate algebra of a linearly reductive group, this is averaging a rational
representation against the invariant integral (J. S. Milne, *Algebraic Groups*, §12.l).
-/

public section

open scoped TensorProduct

namespace TauCeti.IsLeftCointegral

open Comodule

variable {R H : Type*} [CommSemiring R] [AddCommMonoid H] [One H] [Module R H] [Coalgebra R H]
variable {I : H →ₗ[R] R} {M : Type*} [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- Averaging a right coaction against a left cointegral gives a fixed vector, for any value
of the integral on the unit. -/
theorem coactComponent_mem_fixedSubcomodule (hI : IsLeftCointegral I) (m : M) :
    coactComponent I m ∈ fixedSubcomodule R H M := by
  rw [mem_fixedSubcomodule, coact_coactComponent, coactComponent_apply]
  induction coact (R := R) (C := H) m using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
  | tmul x a =>
    simp only [LinearMap.lTensor_tmul, LinearMap.comp_apply, LinearMap.tensorComponent_tmul]
    rw [LinearMap.tensorComponent_def, LinearMap.comp_apply, LinearEquiv.coe_coe,
      (isLeftCointegral_def I).mp hI a, TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/-- The Reynolds projection of a comodule for a normalized left cointegral. -/
theorem isProj_coactComponent (hI : IsLeftCointegral I) (h1 : I 1 = 1) (M : Type*)
    [AddCommMonoid M] [Module R M] [Comodule R H M] :
    LinearMap.IsProj (fixedSubcomodule R H M).toSubmodule (coactComponent I) where
  map_mem := hI.coactComponent_mem_fixedSubcomodule
  map_id m hm := by
    rw [coactComponent_apply, mem_fixedSubcomodule.mp hm, LinearMap.tensorComponent_tmul,
      h1, one_smul]

end TauCeti.IsLeftCointegral
