/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Real-linear extension from a full lattice

A full lattice `L` in a finite-dimensional real normed space `E` spans `E`, and a `ℤ`-basis of `L`
is a real basis of `E` (`Module.Basis.ofZLatticeBasis`). So every `ℤ`-linear map `g : L → F` to a
real vector space extends to exactly one real-linear map `E → F`:
`ZLattice.linearExtension L g` extends it (`ZLattice.linearExtension_apply`), and real-linear maps
agreeing on `L` are equal (`ZLattice.linearMap_ext`).

## Main definitions

* `ZLattice.linearExtension`: the real-linear extension of a `ℤ`-linear map on a full lattice.

## Main results

* `ZLattice.linearExtension_apply`: the extension agrees with the map on the lattice.
* `ZLattice.linearMap_ext`: real-linear maps agreeing on a full lattice are equal.
-/

public section

noncomputable section

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- The real-linear extension of a `ℤ`-linear map on a full lattice `L`, along the real basis of
`E` given by a `ℤ`-basis of `L`. -/
def linearExtension (g : L →ₗ[ℤ] F) : E →ₗ[ℝ] F :=
  have := ZLattice.module_free ℝ L
  (Module.Basis.ofZLatticeBasis ℝ L (Module.Free.chooseBasis ℤ L)).constr ℝ
    fun i ↦ g (Module.Free.chooseBasis ℤ L i)

/-- The real-linear extension of `g` agrees with `g` on the lattice. -/
@[simp]
theorem linearExtension_apply (g : L →ₗ[ℤ] F) (x : L) : linearExtension L g x = g x := by
  have := ZLattice.module_free ℝ L
  let b := Module.Free.chooseBasis ℤ L
  -- Both sides are `ℤ`-linear in `x ∈ L` and agree on the basis `b`.
  have h := b.ext (f₁ := ((linearExtension L g).restrictScalars ℤ).comp L.subtype) (f₂ := g)
    fun i ↦ by
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.subtype_apply]
      rw [linearExtension, ← Module.Basis.ofZLatticeBasis_apply ℝ L, Module.Basis.constr_basis]
  exact LinearMap.congr_fun h x

omit [FiniteDimensional ℝ E] in
variable {L} in
/-- Real-linear maps that agree on a full lattice are equal. -/
theorem linearMap_ext {f₁ f₂ : E →ₗ[ℝ] F} (h : ∀ x ∈ L, f₁ x = f₂ x) : f₁ = f₂ :=
  LinearMap.ext_on (IsZLattice.span_top (K := ℝ) (L := L)) h

end ZLattice
