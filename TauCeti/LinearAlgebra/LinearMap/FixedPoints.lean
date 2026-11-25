/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The span of the fixed vectors of a semilinear map

For a `σ`-semilinear endomorphism `F` of a module, the fixed vectors `fixedPoints F` form only an
additive subgroup, not a submodule, when `σ` is not the identity. Their span is still mapped into
itself by `F`, so `F` induces a semilinear map on the quotient by this span. When `F` is injective
and `σ` is surjective, `F` maps the span onto itself, and the induced map on the quotient is
injective. This is how fixed vectors of Frobenius-semilinear maps are shown to span: a fixed vector
of the quotient lifts to an almost fixed vector.

## Main results

* `LinearMap.span_fixedPoints_le_comap`: the span of the fixed vectors is `F`-stable.
* `LinearMap.injective_mapQ_span_fixedPoints`: for `F` injective and `σ` surjective, the map
  induced on the quotient by that span is injective.
-/

public section

open Function Submodule

namespace LinearMap

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {σ : R →+* R}

/-- The span of the fixed vectors of a semilinear map is mapped into itself. -/
theorem span_fixedPoints_le_comap (F : M →ₛₗ[σ] M) :
    span R (fixedPoints F) ≤ (span R (fixedPoints F)).comap F :=
  mapsTo_span fun _ hx ↦ hx.apply

end Semiring

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {σ : R →+* R}

/-- For an injective `σ`-semilinear map `F` with `σ` surjective, the map induced on the quotient by
the span of the fixed vectors is injective. -/
theorem injective_mapQ_span_fixedPoints (hσ : Surjective σ) {F : M →ₛₗ[σ] M}
    (hF : Injective F) :
    Injective ((span R (fixedPoints F)).mapQ _ F (span_fixedPoints_le_comap F)) := by
  have : RingHomSurjective σ := ⟨hσ⟩
  set U := span R (fixedPoints F)
  have hmap : U.map F = U := by
    rw [Submodule.map_span, Set.EqOn.image_eq_self (f := F) fun _ hx ↦ hx]
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective U y
  rw [mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨u', hu', hFu⟩ := Submodule.mem_map.1 (hmap.ge hy)
  rw [Submodule.Quotient.mk_eq_zero, ← hF hFu]
  exact hu'

end Ring

end LinearMap
