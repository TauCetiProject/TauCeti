/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Invariant
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Action

/-!
# Group actions on the adic spectrum

Let a group `G` act on a topological ring `A` by continuous ring automorphisms preserving a
subring `A⁺` (`IsInvariantSubring G A⁺`). The action `(g • v)(a) = v(g⁻¹ • a)` of `G` on `Spv A`
then preserves `Spa(A, A⁺)` (`TauCeti.ValuationSpectrum.smul_mem_spa_iff`), so `G` acts on
`Spa(A, A⁺)` by homeomorphisms.

For a morphism of Huber pairs `φ : (R, R⁺) → (A, A⁺)`, the induced map `Spa(A, A⁺) → Spa(R, R⁺)`
is equivariant when `φ` is (`TauCeti.Huber.Pair.Hom.spaComap_smul`), and constant on `G`-orbits
when the image of `φ` is fixed by `G` (`TauCeti.Huber.Pair.Hom.spaComap_smul_eq_spaComap`).

## Main definitions

* The `MulAction G (spa A⁺)` and `ContinuousConstSMul G (spa A⁺)` instances.

## Main results

* `TauCeti.ValuationSpectrum.smul_mem_spa_iff`: `G` preserves `Spa(A, A⁺)` when it preserves
  `A⁺`.
* `TauCeti.Huber.Pair.Hom.spaComap_smul`: the map of adic spectra induced by an equivariant
  morphism of Huber pairs is equivariant.
* `TauCeti.Huber.Pair.Hom.spaComap_smul_eq_spaComap`: the map of adic spectra induced by a
  morphism of Huber pairs with `G`-fixed image is constant on `G`-orbits.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {G A : Type*} [Group G] [CommRing A] [TopologicalSpace A] [MulSemiringAction G A]
  [ContinuousConstSMul G A] {Aplus : Subring A} [IsInvariantSubring G Aplus]

/-- A group acting on `A` by continuous ring automorphisms preserving `A⁺` preserves
`Spa(A, A⁺)`. -/
theorem smul_mem_spa_iff (g : G) {v : Spv A} : g • v ∈ spa Aplus ↔ v ∈ spa Aplus := by
  have key (g : G) {v : Spv A} (hv : v ∈ spa Aplus) : g • v ∈ spa Aplus :=
    comap_mem_spa (continuous_const_smul g⁻¹) (fun _ ha ↦ IsInvariantSubring.smul_mem g⁻¹ ha) hv
  exact ⟨fun h ↦ inv_smul_smul g v ▸ key g⁻¹ h, key g⟩

/-- The action of `G` on `Spa(A, A⁺)` for an action on `A` by continuous ring automorphisms
preserving `A⁺`: `(g • v)(a) = v(g⁻¹ • a)`. -/
instance : SMul G (spa Aplus) :=
  ⟨fun g v ↦ ⟨g • v.val, (smul_mem_spa_iff g).mpr v.property⟩⟩

/-- The underlying point of `g • v` in `Spv A`. -/
@[simp]
theorem val_smul (g : G) (v : spa Aplus) : (g • v : spa Aplus).val = g • v.val :=
  (rfl)

/-- The action of `G` on `Spa(A, A⁺)` is the restriction of its action on `Spv A`. -/
instance : MulAction G (spa Aplus) :=
  Subtype.val_injective.mulAction _ val_smul

/-- `G` acts on `Spa(A, A⁺)` by homeomorphisms. -/
instance : ContinuousConstSMul G (spa Aplus) :=
  Topology.IsInducing.subtypeVal.continuousConstSMul id fun {g v} ↦ val_smul g v

end TauCeti.ValuationSpectrum

namespace TauCeti.Huber.Pair.Hom

open ValuationSpectrum

variable {R A : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsHuberRing R]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {G : Type*} [Group G] [MulSemiringAction G A] [ContinuousConstSMul G A]
  {S : Pair R} {T : Pair A} [IsInvariantSubring G T.plus]

/-- **Restriction along a morphism with `G`-fixed image is constant on orbits.** If every element
in the image of `φ : (R, R⁺) → (A, A⁺)` is fixed by `G`, then `φ.spaComap (g • x) = φ.spaComap x`.
No finiteness hypothesis is needed. -/
theorem spaComap_smul_eq_spaComap (φ : Hom S T)
    (hφ : ∀ (g : G) (r : R), g • φ.toRingHom r = φ.toRingHom r) (g : G) (x : spa T.plus) :
    φ.spaComap (g • x) = φ.spaComap x :=
  Subtype.ext <| by rw [spaComap_val, spaComap_val, val_smul, comap_smul_eq_comap _ hφ]

/-- **Restriction along an equivariant morphism is equivariant.** If `G` acts on both Huber pairs
and `φ : (R, R⁺) → (A, A⁺)` commutes with the actions, then
`φ.spaComap (g • x) = g • φ.spaComap x`. -/
theorem spaComap_smul [MulSemiringAction G R] [ContinuousConstSMul G R]
    [IsInvariantSubring G S.plus] (φ : Hom S T)
    (hφ : ∀ (g : G) (r : R), φ.toRingHom (g • r) = g • φ.toRingHom r) (g : G) (x : spa T.plus) :
    φ.spaComap (g • x) = g • φ.spaComap x :=
  Subtype.ext <| by rw [spaComap_val, val_smul, val_smul, spaComap_val, comap_smul _ hφ]

end TauCeti.Huber.Pair.Hom
