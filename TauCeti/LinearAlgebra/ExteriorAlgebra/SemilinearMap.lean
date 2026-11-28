/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Semilinear maps on exterior algebras

For a ring homomorphism `σ : R →+* S` between commutative rings and a `σ`-semilinear map
`f : M →ₛₗ[σ] N`, the universal property of the exterior algebra induces a ring homomorphism
`ExteriorAlgebra.mapSemilinear f : ExteriorAlgebra R M →+* ExteriorAlgebra S N` sending scalars
through `σ` and generators `ι R m` to `ι S (f m)`. Its interaction with the constant-term
homomorphism `ExteriorAlgebra.algebraMapInv` is given by
`ExteriorAlgebra.algebraMapInv_mapSemilinear`:
`algebraMapInv (mapSemilinear f x) = σ (algebraMapInv x)`.

## Main definitions and results

* `ExteriorAlgebra.mapSemilinear`: the ring homomorphism
  `ExteriorAlgebra R M →+* ExteriorAlgebra S N` induced by a `σ`-semilinear map `f : M →ₛₗ[σ] N`.
* `ExteriorAlgebra.mapSemilinear_ι`, `ExteriorAlgebra.mapSemilinear_smul`,
  `ExteriorAlgebra.mapSemilinear_algebraMap`: action on generators, scalars, and embedded scalars.
* `ExteriorAlgebra.algebraMapInv_mapSemilinear`: `mapSemilinear f` acts on the degree-zero part
  through `σ`.

## Provenance

Generalized from `grh-lean` (https://github.com/lsernau/grh-lean at commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC), files
`src/Lib/Cohomology/Hodge/Site.lean` (`exteriorMap`) and
`src/Lib/PadicComparison/HodgeTate/ExtCocycles.lean` (`algebraMapInv_exteriorMap`).
-/

public section

namespace ExteriorAlgebra

universe u v w z

variable {R : Type u} {S : Type v} {M : Type w} {N : Type z}
  [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
  {σ : R →+* S}

/-- The ring homomorphism `ExteriorAlgebra R M →+* ExteriorAlgebra S N` induced by a
`σ`-semilinear map `f : M →ₛₗ[σ] N`, extending `σ` on scalars and `f` on generators. -/
noncomputable def mapSemilinear (f : M →ₛₗ[σ] N) :
    ExteriorAlgebra R M →+* ExteriorAlgebra S N :=
  letI : Algebra R (ExteriorAlgebra S N) := Algebra.compHom (ExteriorAlgebra S N) σ
  (lift R ⟨⟨(ι S ∘ₛₗ f).toAddHom, (ι S ∘ₛₗ f).map_smul'⟩, fun _ ↦ ι_sq_zero _⟩).toRingHom

/-- `mapSemilinear f` sends a generator `ι R m` to `ι S (f m)`. -/
@[simp]
theorem mapSemilinear_ι (f : M →ₛₗ[σ] N) (m : M) :
    mapSemilinear f (ι R m) = ι S (f m) := by
  simp [mapSemilinear]

/-- `mapSemilinear f` is `σ`-semilinear with respect to scalar multiplication. -/
@[simp]
theorem mapSemilinear_smul (f : M →ₛₗ[σ] N) (r : R) (x : ExteriorAlgebra R M) :
    mapSemilinear f (r • x) = σ r • mapSemilinear f x := by
  let : Algebra R (ExteriorAlgebra S N) := Algebra.compHom (ExteriorAlgebra S N) σ
  exact map_smul (lift R ⟨⟨(ι S ∘ₛₗ f).toAddHom, (ι S ∘ₛₗ f).map_smul'⟩, fun _ ↦ ι_sq_zero _⟩) r x

/-- `mapSemilinear f` restricts to `σ` on embedded scalars. -/
@[simp]
theorem mapSemilinear_algebraMap (f : M →ₛₗ[σ] N) (r : R) :
    mapSemilinear f (algebraMap R (ExteriorAlgebra R M) r) =
      algebraMap S (ExteriorAlgebra S N) (σ r) := by
  rw [Algebra.algebraMap_eq_smul_one, mapSemilinear_smul, map_one, ← Algebra.algebraMap_eq_smul_one]

/-- `mapSemilinear f` acts on the degree-zero (scalar) component through `σ`. -/
theorem algebraMapInv_mapSemilinear (f : M →ₛₗ[σ] N) (x : ExteriorAlgebra R M) :
    algebraMapInv (mapSemilinear f x) = σ (algebraMapInv x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [mapSemilinear_algebraMap, algebraMap_leftInverse, algebraMap_leftInverse]
  | ι m =>
    rw [mapSemilinear_ι, algebraMapInv, algebraMapInv, lift_ι_apply, lift_ι_apply,
      LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  | mul x y hx hy =>
    rw [map_mul, map_mul, map_mul, map_mul, hx, hy]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add, hx, hy]

end ExteriorAlgebra
