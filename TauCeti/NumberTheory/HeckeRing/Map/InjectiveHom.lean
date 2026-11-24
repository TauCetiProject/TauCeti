/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Defs
public import TauCeti.NumberTheory.HeckeRing.Associativity
public import TauCeti.NumberTheory.HeckeRing.Degree

import TauCeti.NumberTheory.HeckeRing.LinearExtension
import TauCeti.NumberTheory.HeckeRing.Multiplicity.Equiv

/-!
# Transporting Hecke coset modules and rings along injective group homomorphisms

Building on the low-level triple and double-coset pushforward in
`TauCeti.NumberTheory.HeckeRing.Basic` (`IsHeckeTriple.map`, `HeckeCoset.mapHom`,
`HeckeCoset.mapEquivOfInjective`, and `HeckeCoset.degree_mapHom_of_injective`), an injective group
homomorphism `φ : G →* K` induces an `R`-linear isomorphism
`HeckeCosetModule.mapInjectiveLinearEquiv` of bimodules that intertwines `HeckeCosetModule.mul` and
specializes on the diagonal to a degree-preserving ring isomorphism
`HeckeCosetModule.mapInjectiveRingEquiv : 𝕋 Δ H R ≃+* 𝕋 (Δ.map φ) (H.map φ) R`.

## Main definitions and results

* `HeckeCosetModule.mapInjectiveLinearEquiv`, `HeckeCosetModule.mapInjectiveLinearEquiv_mul`:
  the induced `R`-linear isomorphism on `HeckeCosetModule` bimodules intertwining
  `HeckeCosetModule.mul`.
* `HeckeCosetModule.mapInjectiveRingEquiv`, `HeckeCosetModule.deg_mapInjectiveRingEquiv`: the
  induced degree-preserving ring isomorphism `𝕋 Δ H R ≃+* 𝕋 (Δ.map φ) (H.map φ) R`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.1–3.2.
-/

public section

open DoubleCoset
open scoped HeckeCosetModule

section InjectiveHom

variable {G K : Type*} [Group G] [Group K]

namespace HeckeCosetModule

variable (R : Type*) [Semiring R] {Δ : Submonoid G} {H₁ H₂ H₃ H : Subgroup G}

/-- `R`-linear equivalence of Hecke coset bimodules induced by an injective group homomorphism
`φ : G →* K`. -/
noncomputable def mapInjectiveLinearEquiv (φ : G →* K) (hφ : Function.Injective φ) :
    HeckeCosetModule Δ H₁ H₂ R ≃ₗ[R] HeckeCosetModule (Δ.map φ) (H₁.map φ) (H₂.map φ) R :=
  Finsupp.mapDomain.linearEquiv R R (HeckeCoset.mapEquivOfInjective φ hφ)

/-- Evaluating `mapInjectiveLinearEquiv` at `D.mapHom φ` recovers the coefficient at `D`. -/
@[simp]
theorem mapInjectiveLinearEquiv_apply_mapHom (φ : G →* K) (hφ : Function.Injective φ)
    (f : HeckeCosetModule Δ H₁ H₂ R) (D : HeckeCoset Δ H₁ H₂) :
    mapInjectiveLinearEquiv R φ hφ f (D.mapHom φ) = f D := by
  rw [← HeckeCoset.mapEquivOfInjective_apply φ hφ D]
  exact Finsupp.mapDomain_apply_of_injective (HeckeCoset.mapEquivOfInjective φ hφ).injective f D

/-- `mapInjectiveLinearEquiv` sends each basis element to the mapped basis element. -/
@[simp]
theorem mapInjectiveLinearEquiv_single (φ : G →* K) (hφ : Function.Injective φ)
    (D : HeckeCoset Δ H₁ H₂) (b : R) :
    mapInjectiveLinearEquiv R φ hφ (single R D b) = single R (D.mapHom φ) b := by
  rw [← HeckeCoset.mapEquivOfInjective_apply φ hφ D]
  exact mapDomain_single R (HeckeCoset.mapEquivOfInjective φ hφ) D b

/-- `mapInjectiveLinearEquiv` sends structure constants on `(H₁, H₂, H₃)` to structure constants on
`(H₁.map φ, H₂.map φ, H₃.map φ)`. -/
theorem mapInjectiveLinearEquiv_structureConstants (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (D₁ : HeckeCoset Δ H₁ H₂) (D₂ : HeckeCoset Δ H₂ H₃) :
    mapInjectiveLinearEquiv R φ hφ (structureConstants R H₁ H₂ H₃ D₁.rep D₂.rep) =
      structureConstants R (H₁.map φ) (H₂.map φ) (H₃.map φ)
        (D₁.mapHom φ).rep (D₂.mapHom φ).rep := by
  ext E
  obtain ⟨D, rfl⟩ := (HeckeCoset.mapHom_bijective hφ).2 E
  rw [mapInjectiveLinearEquiv_apply_mapHom, structureConstants_apply, structureConstants_apply,
    multiplicity_doubleCoset_congr_first (H₁.map φ) (H₂.map φ) (H₃.map φ) _ _
      (HeckeCoset.rep_mapHom_mem_doubleCoset φ D₁),
    multiplicity_doubleCoset_congr_second (H₁.map φ) (H₂.map φ) (H₃.map φ) _ _
      (HeckeCoset.rep_mapHom_mem_doubleCoset φ D₂),
    multiplicity_doubleCoset_congr _ _ (HeckeCoset.rep_mapHom_mem_doubleCoset φ D),
    multiplicity_map_of_injective φ hφ H₁ H₂ H₃ (D₁.rep : G) (D₂.rep : G) (D.rep : G)]

/-- `mapInjectiveLinearEquiv` intertwines the bimodule convolution product
`HeckeCosetModule.mul`. -/
theorem mapInjectiveLinearEquiv_mul (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (f : HeckeCosetModule Δ H₁ H₂ R) (g : HeckeCosetModule Δ H₂ H₃ R) :
    mapInjectiveLinearEquiv R φ hφ (mul R f g) =
      mul R (mapInjectiveLinearEquiv R φ hφ f) (mapInjectiveLinearEquiv R φ hφ g) :=
  map_mul_of_structureConstants_of_map R (HeckeCoset.mapHom φ) (HeckeCoset.mapHom φ)
    (mapInjectiveLinearEquiv R φ hφ).toLinearMap (mapInjectiveLinearEquiv R φ hφ).toLinearMap
    (mapInjectiveLinearEquiv R φ hφ).toLinearMap (mapInjectiveLinearEquiv_single R φ hφ)
    (mapInjectiveLinearEquiv_single R φ hφ)
    (mapInjectiveLinearEquiv_structureConstants R φ hφ) f g

/-- **Injective-homomorphism isomorphism for Hecke rings**: an injective group homomorphism
`φ : G →* K` induces a ring isomorphism `𝕋 Δ H R ≃+* 𝕋 (Δ.map φ) (H.map φ) R` over any coefficient
semiring `R`. -/
noncomputable def mapInjectiveRingEquiv (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H H] :
    𝕋 Δ H R ≃+* 𝕋 (Δ.map φ) (H.map φ) R :=
  { mapInjectiveLinearEquiv R φ hφ with
    map_mul' := mapInjectiveLinearEquiv_mul R φ hφ }

/-- `mapInjectiveRingEquiv` coerces to `mapInjectiveLinearEquiv`. -/
-- Deliberately not `@[simp]`: rewriting `⇑(mapInjectiveRingEquiv …)` to a `LinearEquiv` prevents
-- generic ring-homomorphism simp lemmas (`map_mul`, `map_one`) from firing.
theorem coe_mapInjectiveRingEquiv (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H H] :
    ⇑(mapInjectiveRingEquiv R (Δ := Δ) (H := H) φ hφ) =
      mapInjectiveLinearEquiv R φ hφ := (rfl)

/-- `mapInjectiveRingEquiv` sends each basis element `single R D b` to `single R (D.mapHom φ) b`. -/
@[simp]
theorem mapInjectiveRingEquiv_single (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H H]
    (D : HeckeCoset Δ H H) (b : R) :
    mapInjectiveRingEquiv R φ hφ (single R D b) = single R (D.mapHom φ) b :=
  mapInjectiveLinearEquiv_single R φ hφ D b

/-- The inverse of `mapInjectiveRingEquiv` sends `single R (D.mapHom φ) b` back to
`single R D b`. -/
@[simp]
theorem mapInjectiveRingEquiv_symm_single_mapHom (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H H]
    (D : HeckeCoset Δ H H) (b : R) :
    (mapInjectiveRingEquiv R φ hφ).symm (single R (D.mapHom φ) b) = single R D b :=
  (mapInjectiveRingEquiv R φ hφ).injective (by simp)

/-- `mapInjectiveRingEquiv` preserves the degree homomorphism `LeftCosetModule.deg`. -/
@[simp]
theorem deg_mapInjectiveRingEquiv (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H H]
    (f : 𝕋 Δ H R) :
    LeftCosetModule.deg (Δ.map φ) (H.map φ) R (mapInjectiveRingEquiv R φ hφ f) =
      LeftCosetModule.deg Δ H R f := by
  induction f using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | hsingle D b => simp [HeckeCoset.degree_mapHom_of_injective hφ]

/-- Precomposing `LeftCosetModule.deg` with `mapInjectiveRingEquiv` recovers
`LeftCosetModule.deg`. -/
@[simp]
theorem deg_comp_mapInjectiveRingEquiv (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H H] :
    (LeftCosetModule.deg (Δ.map φ) (H.map φ) R).comp
        ↑(mapInjectiveRingEquiv R (Δ := Δ) (H := H) φ hφ) =
      LeftCosetModule.deg Δ H R :=
  RingHom.ext (deg_mapInjectiveRingEquiv R φ hφ)

end HeckeCosetModule

end InjectiveHom

end
