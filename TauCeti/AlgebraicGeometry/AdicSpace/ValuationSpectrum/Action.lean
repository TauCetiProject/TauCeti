/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Basic

/-!
# Group actions on the valuation spectrum

A group `G` acting on a ring `A` by ring automorphisms acts on `Spv A` by transport of structure,
`(g • v)(a) = v(g⁻¹ • a)`, that is `g • v = comap (g⁻¹ • ·) v`, by homeomorphisms. This matches
Mathlib's action on `PrimeSpectrum A`.

Pullback along a `G`-equivariant ring map is `G`-equivariant
(`TauCeti.ValuationSpectrum.comap_smul`), and pullback along a ring map whose image is fixed by
`G`, such as `algebraMap R A` when `G` acts by `R`-algebra automorphisms, is constant on orbits
(`TauCeti.ValuationSpectrum.comap_smul_eq_comap`,
`TauCeti.ValuationSpectrum.comap_algebraMap_smul`).

## Main definitions

* The `MulAction G (Spv A)` and `ContinuousConstSMul G (Spv A)` instances.

## Main results

* `TauCeti.ValuationSpectrum.smul_def`: `g • v = comap (g⁻¹ • ·) v`.
* `TauCeti.ValuationSpectrum.comap_smul`: pullback along an equivariant ring map is equivariant.
* `TauCeti.ValuationSpectrum.comap_smul_eq_comap`: pullback along a ring map with `G`-fixed image
  is constant on `G`-orbits.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {G A : Type*} [Group G] [CommRing A] [MulSemiringAction G A]

/-- A group acting on `A` by ring automorphisms acts on `Spv A` by transport of structure,
`(g • v)(a) = v(g⁻¹ • a)`, that is `g • v = comap (g⁻¹ • ·) v`. This matches Mathlib's action on
`PrimeSpectrum A`. -/
instance : SMul G (Spv A) :=
  ⟨fun g v ↦ comap (MulSemiringAction.toRingHom G A g⁻¹) v⟩

/-- `g • v` is the pullback of `v` along the ring automorphism `g⁻¹ • ·`. -/
theorem smul_def (g : G) (v : Spv A) : g • v = comap (MulSemiringAction.toRingHom G A g⁻¹) v :=
  (rfl)

/-- The action of `G` on `Spv A` by transport of structure is a group action. -/
instance : MulAction G (Spv A) where
  one_smul v := by
    have h : MulSemiringAction.toRingHom G A 1 = RingHom.id A := RingHom.ext (one_smul G)
    rw [smul_def, inv_one, h, comap_id, id]
  mul_smul g h v := by
    rw [smul_def, smul_def, smul_def, comap_comap]
    congr 1
    exact RingHom.ext fun a ↦ by simp [mul_smul]

/-- `G` acts on `Spv A` by homeomorphisms. -/
instance : ContinuousConstSMul G (Spv A) :=
  ⟨fun _ ↦ continuous_comap _⟩

/-- **Pullback along an equivariant ring map is equivariant.** If `f : R → A` commutes with the
actions of `G`, then `comap f (g • v) = g • comap f v`. -/
theorem comap_smul {R : Type*} [CommRing R] [MulSemiringAction G R] (f : R →+* A)
    (hf : ∀ (g : G) (r : R), f (g • r) = g • f r) (g : G) (v : Spv A) :
    comap f (g • v) = g • comap f v := by
  rw [smul_def, smul_def, comap_comap, comap_comap]
  congr 1
  exact RingHom.ext fun r ↦ (hf g⁻¹ r).symm

/-- **Pullback along a ring map with `G`-fixed image is constant on orbits.** If `g • f r = f r`
for all `g` and `r`, then `comap f (g • v) = comap f v`. No finiteness hypothesis is needed. -/
theorem comap_smul_eq_comap {R : Type*} [CommRing R] (f : R →+* A)
    (hf : ∀ (g : G) (r : R), g • f r = f r) (g : G) (v : Spv A) :
    comap f (g • v) = comap f v := by
  rw [smul_def, comap_comap]
  congr 1
  exact RingHom.ext fun r ↦ hf g⁻¹ r

/-- Acting by `g ∈ G` does not change the image in `Spv R`, since `G` acts by `R`-algebra
automorphisms. No finiteness or invariance hypothesis is needed. -/
@[simp]
theorem comap_algebraMap_smul {R : Type*} [CommRing R] [Algebra R A] [SMulCommClass G R A]
    (g : G) (y : Spv A) : comap (algebraMap R A) (g • y) = comap (algebraMap R A) y :=
  comap_smul_eq_comap _ (fun g r ↦ smul_algebraMap g r) g y

end TauCeti.ValuationSpectrum
