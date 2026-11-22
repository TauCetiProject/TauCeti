/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

/-!
# Clifford relations along algebra homomorphisms and on Clifford modules

For an algebra homomorphism `ρ : CliffordAlgebra Q →ₐ[K] A` (in particular a `CliffordAlgebra Q`-
module representation `ρ : CliffordAlgebra Q →ₐ[K] Module.End K W`), Mathlib's
`CliffordAlgebra.comp_ι_sq_scalar` records the fundamental squaring relation
`ρ (ι Q v) * ρ (ι Q v) = algebraMap K A (Q v)`. This file collects its direct consequences for
module actions, vectors with `Q v = -1`, and polarized / orthogonal anticommutators.

## Main results

* `AlgHom.map_cliffordAlgebraι_apply_self`: applying `ρ (ι Q v)` twice on a Clifford module scales
  by `Q v`.
* `AlgHom.map_cliffordAlgebraι_mul_self_of_eq_neg_one`,
  `AlgHom.map_cliffordAlgebraι_apply_self_of_eq_neg_one`: a vector with `Q v = -1` squares to `-1`
  and acts as negation when applied twice.
* `AlgHom.map_cliffordAlgebraι_mul_add_swap`,
  `AlgHom.map_cliffordAlgebraι_anticommute_of_isOrtho`,
  `AlgHom.map_cliffordAlgebraι_apply_anticommute_of_isOrtho`: the polarized anticommutator relation
  and anticommutation of `Q`-orthogonal vectors along `ρ`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1.
-/

public section

open CliffordAlgebra

namespace AlgHom

variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M] {Q : QuadraticForm K M}

section Semiring

variable {A W : Type*} [Semiring A] [Algebra K A] [AddCommMonoid W] [Module K W]

/-- In a `CliffordAlgebra Q`-module, applying a vector `v` twice scales by `Q v`. -/
@[simp]
theorem map_cliffordAlgebraι_apply_self (ρ : CliffordAlgebra Q →ₐ[K] Module.End K W)
    (v : M) (w : W) :
    ρ (ι Q v) (ρ (ι Q v) w) = Q v • w := by
  rw [← mul_apply_eq_comp, comp_ι_sq_scalar, Module.algebraMap_end_apply]

/-- Under any algebra homomorphism out of `CliffordAlgebra Q`, the anticommutator of two vectors is
the scalar `polar Q u v`. -/
theorem map_cliffordAlgebraι_mul_add_swap (ρ : CliffordAlgebra Q →ₐ[K] A) (u v : M) :
    ρ (ι Q u) * ρ (ι Q v) + ρ (ι Q v) * ρ (ι Q u) = algebraMap K A (QuadraticMap.polar Q u v) := by
  rw [← map_mul ρ, ← map_mul ρ, ← map_add ρ, ι_mul_ι_add_swap, AlgHom.commutes]

/-- Orthogonal vectors anticommute under any algebra homomorphism out of `CliffordAlgebra Q`. -/
theorem map_cliffordAlgebraι_anticommute_of_isOrtho (ρ : CliffordAlgebra Q →ₐ[K] A)
    {u v : M} (huv : Q.IsOrtho u v) :
    ρ (ι Q u) * ρ (ι Q v) + ρ (ι Q v) * ρ (ι Q u) = 0 := by
  rw [← map_mul ρ, ← map_mul ρ, ← map_add ρ, ι_mul_ι_add_swap_of_isOrtho huv, map_zero]

/-- Orthogonal vectors act as anticommuting endomorphisms on any `CliffordAlgebra Q`-module. -/
theorem map_cliffordAlgebraι_apply_anticommute_of_isOrtho
    (ρ : CliffordAlgebra Q →ₐ[K] Module.End K W) {u v : M} (huv : Q.IsOrtho u v) (w : W) :
    ρ (ι Q u) (ρ (ι Q v) w) + ρ (ι Q v) (ρ (ι Q u) w) = 0 := by
  have h := congrArg (fun T : Module.End K W ↦ T w)
    (ρ.map_cliffordAlgebraι_anticommute_of_isOrtho huv)
  simpa only [LinearMap.add_apply, mul_apply_eq_comp, LinearMap.zero_apply] using h

end Semiring

section Ring

variable {A W : Type*} [Ring A] [Algebra K A] [AddCommGroup W] [Module K W]

/-- A vector with `Q v = -1` maps to a square root of `-1` under any algebra homomorphism out of
`CliffordAlgebra Q`. -/
theorem map_cliffordAlgebraι_mul_self_of_eq_neg_one (ρ : CliffordAlgebra Q →ₐ[K] A)
    {v : M} (hv : Q v = -1) :
    ρ (ι Q v) * ρ (ι Q v) = -1 := by
  simp [hv]

/-- In a `CliffordAlgebra Q`-module, applying a vector with `Q v = -1` twice negates every
element. -/
theorem map_cliffordAlgebraι_apply_self_of_eq_neg_one
    (ρ : CliffordAlgebra Q →ₐ[K] Module.End K W) {v : M} (hv : Q v = -1) (w : W) :
    ρ (ι Q v) (ρ (ι Q v) w) = -w := by
  simp [hv]

end Ring

end AlgHom
