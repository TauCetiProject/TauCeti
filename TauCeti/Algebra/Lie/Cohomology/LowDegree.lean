/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Cochain

/-!
# Low-degree Lie algebra cohomology

This file completes the degree-zero and degree-one part of Mathlib's low-degree
Chevalley--Eilenberg cochain API.  It defines the differential from module elements to linear
one-cochains, packages one-cocycles and one-coboundaries, and constructs first cohomology as their
quotient.

The quotient interface reduces vanishing of first cohomology to the concrete statement that every
one-cocycle is a principal cocycle.  This is the form used by proofs of the first Whitehead lemma
and by normalization arguments for Lie algebra two-cocycles.

## Main definitions

* `TauCeti.LieModule.Cohomology.d₀₁`: the degree-zero Chevalley--Eilenberg differential.
* `TauCeti.LieModule.Cohomology.oneCocycle`: the kernel of Mathlib's `d₁₂`.
* `TauCeti.LieModule.Cohomology.d₀₁Cocycle`: the differential with codomain restricted to cocycles.
* `TauCeti.LieModule.Cohomology.oneCoboundary`: the principal one-cocycles inside the cocycles.
* `TauCeti.LieModule.Cohomology.firstCohomology`: first Lie algebra cohomology.
* `TauCeti.LieModule.Cohomology.firstCohomologyLift`: descend a linear map from cocycles to first
  cohomology.

## References

* [N. Jacobson, *Lie Algebras*][jacobson1979], Chapter III, §7.
-/

public section

namespace TauCeti.LieModule.Cohomology

open _root_.LieModule.Cohomology

variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L]
variable (M : Type*) [AddCommGroup M] [Module R M]
variable [LieRingModule L M] [LieModule R L M]

/-- The degree-zero Chevalley--Eilenberg differential, sending `m` to the principal cocycle
`x ↦ ⁅x, m⁆`. -/
def d₀₁ : M →ₗ[R] oneCochain R L M :=
  (LieModule.toEnd R L M : L →ₗ[R] Module.End R M).flip

@[simp]
theorem d₀₁_apply (m : M) (x : L) : d₀₁ R L M m x = ⁅x, m⁆ := (rfl)

/-- Consecutive low-degree Chevalley--Eilenberg differentials compose to zero. -/
theorem d₁₂_comp_d₀₁ :
    (d₁₂ R L M).comp (d₀₁ R L M) = 0 := by
  ext m x y
  simp

/-- Lie algebra one-cocycles: linear maps annihilated by the differential `d₁₂`. -/
def oneCocycle : Submodule R (oneCochain R L M) := LinearMap.ker (d₁₂ R L M)

/-- A linear map is a one-cocycle exactly when it satisfies the cocycle identity. -/
theorem mem_oneCocycle_iff {f : oneCochain R L M} :
    f ∈ oneCocycle R L M ↔
      ∀ x y, f ⁅x, y⁆ = ⁅x, f y⁆ - ⁅y, f x⁆ := by
  rw [oneCocycle, LinearMap.mem_ker, ← Submodule.coe_eq_zero, LinearMap.ext_iff]
  simp [LinearMap.ext_iff, sub_eq_zero, eq_comm (a := f _)]

/-- The cocycle identity for a bundled one-cocycle. -/
theorem oneCocycle_apply_lie (f : oneCocycle R L M) (x y : L) :
    f.val ⁅x, y⁆ = ⁅x, f.val y⁆ - ⁅y, f.val x⁆ :=
  (mem_oneCocycle_iff R L M).1 f.property x y

/-- The degree-zero differential, with codomain restricted to one-cocycles. -/
def d₀₁Cocycle : M →ₗ[R] oneCocycle R L M :=
  (d₀₁ R L M).codRestrict (oneCocycle R L M) fun m ↦ by
    simpa [oneCocycle] using LinearMap.congr_fun (d₁₂_comp_d₀₁ R L M) m

@[simp]
theorem d₀₁Cocycle_coe (m : M) :
    (d₀₁Cocycle R L M m : oneCochain R L M) = d₀₁ R L M m := (rfl)

/-- Lie algebra one-coboundaries, regarded as a submodule of the one-cocycles. -/
def oneCoboundary : Submodule R (oneCocycle R L M) :=
  LinearMap.range (d₀₁Cocycle R L M)

/-- A cocycle is a coboundary exactly when it is principal. -/
theorem mem_oneCoboundary_iff {f : oneCocycle R L M} :
    f ∈ oneCoboundary R L M ↔ ∃ m : M, d₀₁Cocycle R L M m = f := by
  simp only [oneCoboundary, LinearMap.mem_range]

/-- First Lie algebra cohomology, the quotient of one-cocycles by principal cocycles. -/
abbrev firstCohomology := oneCocycle R L M ⧸ oneCoboundary R L M

/-- The quotient map from one-cocycles to first cohomology. -/
def firstCohomologyMk : oneCocycle R L M →ₗ[R] firstCohomology R L M :=
  (oneCoboundary R L M).mkQ

/-- Every first cohomology class has a cocycle representative. -/
theorem firstCohomologyMk_surjective :
    Function.Surjective (firstCohomologyMk R L M) :=
  (oneCoboundary R L M).mkQ_surjective

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- Descend a linear map on one-cocycles that vanishes on principal cocycles to first
cohomology. -/
def firstCohomologyLift (f : oneCocycle R L M →ₗ[R] N)
    (h : ∀ m, f (d₀₁Cocycle R L M m) = 0) : firstCohomology R L M →ₗ[R] N :=
  (oneCoboundary R L M).liftQ f fun x hx ↦ by
    obtain ⟨m, rfl⟩ := (mem_oneCoboundary_iff R L M).1 hx
    exact LinearMap.mem_ker.2 (h m)

@[simp]
theorem firstCohomologyLift_mk (f : oneCocycle R L M →ₗ[R] N)
    (h : ∀ m, f (d₀₁Cocycle R L M m) = 0) (x : oneCocycle R L M) :
    firstCohomologyLift R L M f h (firstCohomologyMk R L M x) = f x := (rfl)

/-- A linear map from first cohomology is determined by its values on cocycle representatives. -/
theorem firstCohomologyLift_unique (f : oneCocycle R L M →ₗ[R] N)
    (h : ∀ m, f (d₀₁Cocycle R L M m) = 0) (g : firstCohomology R L M →ₗ[R] N)
    (hg : g.comp (firstCohomologyMk R L M) = f) :
    g = firstCohomologyLift R L M f h :=
  LinearMap.ext fun q ↦ by
    obtain ⟨x, rfl⟩ := firstCohomologyMk_surjective R L M q
    rw [firstCohomologyLift_mk, ← hg, LinearMap.comp_apply]

@[simp]
theorem firstCohomologyMk_eq_zero_iff (f : oneCocycle R L M) :
    firstCohomologyMk R L M f = 0 ↔ ∃ m : M, d₀₁Cocycle R L M m = f := by
  rw [firstCohomologyMk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    mem_oneCoboundary_iff]

@[simp]
theorem firstCohomologyMk_d₀₁Cocycle (m : M) :
    firstCohomologyMk R L M (d₀₁Cocycle R L M m) = 0 :=
  (firstCohomologyMk_eq_zero_iff R L M _).2 ⟨m, rfl⟩

/-- Two cocycles represent the same first cohomology class exactly when their difference is
principal. -/
theorem firstCohomologyMk_eq_iff (f g : oneCocycle R L M) :
    firstCohomologyMk R L M f = firstCohomologyMk R L M g ↔
      ∃ m : M, d₀₁Cocycle R L M m = f - g := by
  rw [← sub_eq_zero, ← map_sub, firstCohomologyMk_eq_zero_iff]

/-- First cohomology is trivial exactly when every one-cocycle is principal. -/
theorem subsingleton_firstCohomology_iff :
    Subsingleton (firstCohomology R L M) ↔
      ∀ f : oneCocycle R L M, ∃ m : M, d₀₁Cocycle R L M m = f := by
  simp only [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff', mem_oneCoboundary_iff]

end TauCeti.LieModule.Cohomology
