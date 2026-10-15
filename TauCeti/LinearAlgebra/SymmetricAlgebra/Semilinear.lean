/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous

/-!
# Semilinear functoriality of symmetric algebras

Let `φ : R →+* S` be a morphism of commutative semirings, `M` an `R`-module and `N` an
`S`-module. A `φ`-semilinear map `f : M →ₛₗ[φ] N` induces a ring homomorphism
`SymmetricAlgebra R M →+* SymmetricAlgebra S N`, which is `φ` on scalars and sends the generator
of `m` to the generator of `f m`. It preserves the homogeneous pieces.

This is the change-of-rings version of `SymmetricAlgebra.map`. For a presheaf of modules over a
presheaf of rings, the restriction maps are semilinear over the restriction maps of the rings, so
this construction is what makes the sectionwise symmetric algebras and symmetric powers of a
presheaf of modules into presheaves.

## Main declarations

* `SymmetricAlgebra.mapₛₗ`: the ring homomorphism induced by a semilinear map;
* `SymmetricAlgebra.mapₛₗ_comp_mapₛₗ` and `SymmetricAlgebra.mapₛₗ_eq_id`: functoriality, with the
  ring homomorphisms and semilinear maps related by pointwise equations, so that they apply to
  maps that only agree propositionally (as for the restriction maps of a presheaf);
* `TauCeti.SymmetricAlgebra.mapₛₗ_mem_homogeneousSubmodule` and
  `TauCeti.SymmetricAlgebra.map_mem_homogeneousSubmodule`: the induced maps preserve degrees;
* `TauCeti.SymmetricAlgebra.homogeneousSubmoduleMapₛₗ`: the induced semilinear map between
  homogeneous pieces of the same degree.
-/

public section

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace SymmetricAlgebra

variable {R : Type u₁} {S : Type u₂} {T : Type u₃}
variable [CommSemiring R] [CommSemiring S] [CommSemiring T]
variable {M : Type v₁} {N : Type v₂} {P : Type v₃}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N] [AddCommMonoid P]
  [Module T P]
variable {φ : R →+* S} {ψ : S →+* T} {χ : R →+* T}

/-- The ring homomorphism between symmetric algebras induced by a semilinear map `f : M →ₛₗ[φ] N`:
it is `φ` on scalars and sends the generator of `m` to the generator of `f m`. -/
noncomputable def mapₛₗ (f : M →ₛₗ[φ] N) : SymmetricAlgebra R M →+* SymmetricAlgebra S N :=
  letI : Algebra R (SymmetricAlgebra S N) :=
    ((algebraMap S (SymmetricAlgebra S N)).comp φ).toAlgebra
  (lift
    { toFun m := ι S N (f m)
      map_add' m m' := by rw [map_add, map_add]
      map_smul' r m := by
        rw [f.map_smulₛₗ, map_smul, RingHom.id_apply, Algebra.smul_def, Algebra.smul_def]
        rfl }).toRingHom

/-- The map induced by a semilinear map is the original ring homomorphism on scalars. -/
@[simp]
theorem mapₛₗ_algebraMap (f : M →ₛₗ[φ] N) (r : R) :
    mapₛₗ f (algebraMap R _ r) = algebraMap S (SymmetricAlgebra S N) (φ r) := by
  let : Algebra R (SymmetricAlgebra S N) :=
    ((algebraMap S (SymmetricAlgebra S N)).comp φ).toAlgebra
  exact AlgHom.commutes _ r

/-- The map induced by a semilinear map sends a generator to the generator of its image. -/
@[simp]
theorem mapₛₗ_ι (f : M →ₛₗ[φ] N) (m : M) :
    mapₛₗ f (ι R M m) = ι S N (f m) := by
  let : Algebra R (SymmetricAlgebra S N) :=
    ((algebraMap S (SymmetricAlgebra S N)).comp φ).toAlgebra
  exact lift_ι_apply _ m

/-- The map induced by a semilinear map is semilinear. -/
theorem mapₛₗ_smul (f : M →ₛₗ[φ] N) (r : R) (x : SymmetricAlgebra R M) :
    mapₛₗ f (r • x) = φ r • mapₛₗ f x := by
  rw [Algebra.smul_def, map_mul, mapₛₗ_algebraMap, ← Algebra.smul_def]

/-- For a linear map, the induced ring homomorphism underlies `SymmetricAlgebra.map`. -/
theorem mapₛₗ_eq_map {N' : Type*} [AddCommMonoid N'] [Module R N'] (f : M →ₗ[R] N') :
    mapₛₗ f = (map R f : SymmetricAlgebra R M →+* SymmetricAlgebra R N') := by
  ext x <;> simp

/-- The map induced by a semilinear map which is the identity on elements, over a ring
homomorphism which is the identity, is the identity. -/
theorem mapₛₗ_eq_id {φ : R →+* R} (hφ : ∀ r, φ r = r) {f : M →ₛₗ[φ] M} (hf : ∀ m, f m = m) :
    mapₛₗ f = RingHom.id _ := by
  ext x <;> simp [hφ, hf]

/-- Composition of semilinear maps becomes composition of the induced ring homomorphisms. The
composites are related by pointwise equations, so that this applies to composites which only
agree propositionally. -/
theorem mapₛₗ_comp_mapₛₗ (f : M →ₛₗ[φ] N) (g : N →ₛₗ[ψ] P) (h : M →ₛₗ[χ] P)
    (hχ : ∀ r, ψ (φ r) = χ r) (hh : ∀ m, g (f m) = h m) :
    (mapₛₗ g).comp (mapₛₗ f) = mapₛₗ h := by
  ext x <;> simp [hχ, hh]

end SymmetricAlgebra

namespace TauCeti.SymmetricAlgebra

open _root_.SymmetricAlgebra (mapₛₗ mapₛₗ_algebraMap mapₛₗ_ι)

variable {R : Type u₁} {S : Type u₂} [CommSemiring R] [CommSemiring S]
variable {M : Type v₁} {N : Type v₂} [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module S N]
variable {φ : R →+* S}

/-- The ring homomorphism induced by a semilinear map preserves the homogeneous pieces. -/
theorem mapₛₗ_mem_homogeneousSubmodule (f : M →ₛₗ[φ] N) {n : ℕ}
    {x : _root_.SymmetricAlgebra R M} (hx : x ∈ homogeneousSubmodule R M n) :
    mapₛₗ f x ∈ homogeneousSubmodule S N n := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
      rw [mapₛₗ_algebraMap, homogeneousSubmodule, pow_zero]
      exact Submodule.algebraMap_mem _
  | add x y i _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | mem_mul m hm i x _ ih =>
      obtain ⟨y, rfl⟩ := hm
      rw [map_mul, mapₛₗ_ι, Nat.succ_eq_add_one, Nat.add_comm]
      exact SetLike.mul_mem_graded (ι_mem_homogeneousSubmodule S N (f y)) ih

/-- The semilinear map between degree-`n` homogeneous pieces induced by a semilinear map: the
restriction of `SymmetricAlgebra.mapₛₗ`. -/
noncomputable def homogeneousSubmoduleMapₛₗ (f : M →ₛₗ[φ] N) (n : ℕ) :
    homogeneousSubmodule R M n →ₛₗ[φ] homogeneousSubmodule S N n where
  toFun x := ⟨mapₛₗ f x, mapₛₗ_mem_homogeneousSubmodule f x.2⟩
  map_add' x y := Subtype.ext (map_add (mapₛₗ f) x.1 y.1)
  map_smul' r x := Subtype.ext (_root_.SymmetricAlgebra.mapₛₗ_smul f r x.1)

/-- The map between homogeneous pieces induced by a semilinear map is computed in the symmetric
algebra by `SymmetricAlgebra.mapₛₗ`. -/
@[simp]
theorem coe_homogeneousSubmoduleMapₛₗ_apply (f : M →ₛₗ[φ] N) (n : ℕ)
    (x : homogeneousSubmodule R M n) :
    (homogeneousSubmoduleMapₛₗ f n x : _root_.SymmetricAlgebra S N) = mapₛₗ f x :=
  (rfl)

/-- The algebra homomorphism induced by a linear map preserves the homogeneous pieces. -/
theorem map_mem_homogeneousSubmodule {N' : Type*} [AddCommMonoid N'] [Module R N']
    (f : M →ₗ[R] N') {n : ℕ} {x : _root_.SymmetricAlgebra R M}
    (hx : x ∈ homogeneousSubmodule R M n) :
    _root_.SymmetricAlgebra.map R f x ∈ homogeneousSubmodule R N' n := by
  simpa only [_root_.SymmetricAlgebra.mapₛₗ_eq_map, RingHom.coe_coe] using
    mapₛₗ_mem_homogeneousSubmodule f hx

end TauCeti.SymmetricAlgebra
