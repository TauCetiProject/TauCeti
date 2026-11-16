/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Defs
public import TauCeti.NumberTheory.HeckeRing.Associativity
public import TauCeti.NumberTheory.HeckeRing.Degree
public import TauCeti.NumberTheory.HeckeRing.Multiplicity.Equiv

import TauCeti.Algebra.Group.Subgroup.Pointwise
import TauCeti.NumberTheory.HeckeRing.LinearExtension

/-!
# Transporting Hecke coset modules and rings along group homomorphisms

Pushing a Hecke triple `(Δ, H₁, H₂)` forward along an arbitrary group homomorphism `φ : G →* K`
yields a Hecke triple `(Δ.map φ, H₁.map φ, H₂.map φ)` (`IsHeckeTriple.map`) and a double-coset map
`HeckeCoset.mapHom φ`. When `φ` is injective, `HeckeCoset.mapHom φ` is bijective and preserves
double-coset degrees, inducing an `R`-linear isomorphism
`HeckeCosetModule.mapInjectiveLinearEquiv` of bimodules that intertwines `HeckeCosetModule.mul` and
specializes on the diagonal to a degree-preserving ring isomorphism
`HeckeCosetModule.mapInjectiveRingEquiv : 𝕋 Δ H R ≃+* 𝕋 (Δ.map φ) (H.map φ) R`.

## Main definitions and results

* `IsHeckeTriple.map`: any group homomorphism transports a Hecke triple `(Δ, H₁, H₂)` to
  `(Δ.map φ, H₁.map φ, H₂.map φ)`.
* `HeckeCoset.mapHom`, `HeckeCoset.mapEquivOfInjective`, `HeckeCoset.degree_mapHom_of_injective`:
  pushforward of Hecke cosets along a group homomorphism, its functor laws, and its bijectivity and
  degree preservation under injectivity.
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

open Subgroup Subgroup.Commensurable DoubleCoset
open scoped Pointwise HeckeCosetModule

section InjectiveHom

variable {G K : Type*} [Group G] [Group K]

namespace IsHeckeTriple

/-- Pushing a Hecke triple `(Δ, H₁, H₂)` forward along a group homomorphism `φ : G →* K` yields a
Hecke triple `(Δ.map φ, H₁.map φ, H₂.map φ)`. -/
theorem map {Δ : Submonoid G} {H₁ H₂ : Subgroup G} [IsHeckeTriple Δ H₁ H₂] (φ : G →* K) :
    IsHeckeTriple (Δ.map φ) (H₁.map φ) (H₂.map φ) where
  left_le := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, IsHeckeTriple.mem_of_mem_left H₂ hx, rfl⟩
  right_le := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, IsHeckeTriple.mem_of_mem_right H₁ hx, rfl⟩
  commensurable := (IsHeckeTriple.commensurable (Δ := Δ)).map φ
  le_commensurator_right := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_toSubmonoid, commensurator_mem_iff, ← TauCeti.map_conj_eq_conj_smul,
      ← MulEquiv.toMonoidHom_eq_coe, ← Subgroup.map_map_conj, MulEquiv.toMonoidHom_eq_coe,
      TauCeti.map_conj_eq_conj_smul]
    exact ((commensurator_mem_iff H₂ g).mp (IsHeckeTriple.mem_commensurator_right H₁ ⟨g, hg⟩)).map φ

end IsHeckeTriple

namespace HeckeCoset

variable {Δ : Submonoid G} {H₁ H₂ H : Subgroup G}

/-- Push a Hecke double coset forward along a group homomorphism `φ : G →* K`. -/
def mapHom (φ : G →* K) (D : HeckeCoset Δ H₁ H₂) :
    HeckeCoset (Δ.map φ) (H₁.map φ) (H₂.map φ) :=
  Quotient.map (fun g : Δ ↦ (⟨φ g, ⟨g, g.2, rfl⟩⟩ : ↥(Δ.map φ)))
    (fun a b hab ↦ by
      obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hb⟩ := DoubleCoset.rel_iff.mp hab
      refine DoubleCoset.rel_iff.mpr ⟨φ γ₁, ⟨γ₁, hγ₁, rfl⟩, φ γ₂, ⟨γ₂, hγ₂, rfl⟩, ?_⟩
      simpa [mul_assoc] using congrArg φ hb) D

/-- Computation rule for `HeckeCoset.mapHom` on an explicit coset `mk H₁ H₂ g`. -/
@[simp]
theorem mapHom_mk (φ : G →* K) (g : Δ) :
    (mk H₁ H₂ g).mapHom φ = mk (H₁.map φ) (H₂.map φ) (⟨φ g, ⟨g, g.2, rfl⟩⟩ : ↥(Δ.map φ)) := (rfl)

/-- `HeckeCoset.mapHom` along `MonoidHom.id G` agrees with the identity up to `HeckeCoset.map`
along `Submonoid.map_id` and `Subgroup.map_id`. -/
@[simp]
theorem mapHom_id (D : HeckeCoset Δ H₁ H₂)
    (hΔ : Δ.map (MonoidHom.id G) ≤ Δ := (Submonoid.map_id Δ).le)
    (h₁ : H₁.map (MonoidHom.id G) ≤ H₁ := (Subgroup.map_id H₁).le)
    (h₂ : H₂.map (MonoidHom.id G) ≤ H₂ := (Subgroup.map_id H₂).le) :
    (D.mapHom (MonoidHom.id G)).map hΔ h₁ h₂ = D := by
  induction D using HeckeCoset.induction with | h g =>
  rw [mapHom_mk, map_mk]
  exact mk_congr_val rfl

/-- `HeckeCoset.mapHom` composes functorially along `φ : G →* K` and `ψ : K →* L` up to
`HeckeCoset.map` along `Submonoid.map_map` and `Subgroup.map_map`. -/
@[simp]
theorem mapHom_mapHom {L : Type*} [Group L] (φ : G →* K) (ψ : K →* L) (D : HeckeCoset Δ H₁ H₂)
    (hΔ : (Δ.map φ).map ψ ≤ Δ.map (ψ.comp φ) := (Δ.map_map ψ φ).le)
    (h₁ : (H₁.map φ).map ψ ≤ H₁.map (ψ.comp φ) := (H₁.map_map ψ φ).le)
    (h₂ : (H₂.map φ).map ψ ≤ H₂.map (ψ.comp φ) := (H₂.map_map ψ φ).le) :
    ((D.mapHom φ).mapHom ψ).map hΔ h₁ h₂ = D.mapHom (ψ.comp φ) := by
  induction D using HeckeCoset.induction with | h g =>
  rw [mapHom_mk, mapHom_mk, map_mk, mapHom_mk]
  exact mk_congr_val rfl

/-- `HeckeCoset.mapHom` sends the identity coset to the identity coset. -/
@[simp]
theorem mapHom_one (φ : G →* K) :
    (1 : HeckeCoset Δ H H).mapHom φ = (1 : HeckeCoset (Δ.map φ) (H.map φ) (H.map φ)) := by
  rw [one_def, one_def, mapHom_mk]
  exact mk_congr_val (_root_.map_one φ)

/-- The chosen representative of `D.mapHom φ` lies in the `(H₁.map φ, H₂.map φ)`-double coset of
`φ D.rep`. -/
theorem rep_mapHom_mem_doubleCoset (φ : G →* K) (D : HeckeCoset Δ H₁ H₂) :
    (((D.mapHom φ).rep : ↥(Δ.map φ)) : K) ∈
      doubleCoset (φ (D.rep : G)) (H₁.map φ) (H₂.map φ) := by
  let w : ↥(Δ.map φ) := ⟨φ (D.rep : G), ⟨D.rep, D.rep.2, rfl⟩⟩
  have hmap : D.mapHom φ = mk (H₁.map φ) (H₂.map φ) w := by
    conv_lhs => rw [← mk_rep D, mapHom_mk]
  simpa only [hmap] using rep_mk_mem_doubleCoset (H₁ := H₁.map φ) (H₂ := H₂.map φ) w

/-- When `φ : G →* K` is injective, `HeckeCoset.mapHom φ` is bijective. -/
theorem mapHom_bijective {φ : G →* K} (hφ : Function.Injective φ) :
    Function.Bijective (mapHom (Δ := Δ) (H₁ := H₁) (H₂ := H₂) φ) := by
  refine ⟨fun D₁ D₂ hEq ↦ ?_, fun E ↦ ?_⟩
  · induction D₁ using HeckeCoset.induction with | h g₁ =>
    induction D₂ using HeckeCoset.induction with | h g₂ =>
    rw [mapHom_mk, mapHom_mk, eq_iff] at hEq
    obtain ⟨_, ⟨γ₁, hγ₁, rfl⟩, _, ⟨γ₂, hγ₂, rfl⟩, hmul⟩ :=
      mem_doubleCoset.mp (hEq ▸ mem_doubleCoset_self (H₁.map φ) (H₂.map φ) _)
    exact mk_eq_mk_of_mem (mem_doubleCoset.mpr ⟨γ₁, hγ₁, γ₂, hγ₂,
      hφ (by simpa [mul_assoc] using hmul)⟩)
  · induction E using HeckeCoset.induction with | h y =>
    obtain ⟨g, hg, hy⟩ := y.2
    refine ⟨mk H₁ H₂ ⟨g, hg⟩, ?_⟩
    rw [mapHom_mk]
    exact mk_congr_val hy

/-- Equivalence of Hecke double cosets induced by an injective group homomorphism `φ : G →* K`. -/
noncomputable def mapEquivOfInjective (φ : G →* K) (hφ : Function.Injective φ) :
    HeckeCoset Δ H₁ H₂ ≃ HeckeCoset (Δ.map φ) (H₁.map φ) (H₂.map φ) :=
  Equiv.ofBijective (mapHom φ) (mapHom_bijective hφ)

/-- `mapEquivOfInjective` computes as `HeckeCoset.mapHom`. -/
@[simp]
theorem mapEquivOfInjective_apply (φ : G →* K) (hφ : Function.Injective φ)
    (D : HeckeCoset Δ H₁ H₂) :
    mapEquivOfInjective φ hφ D = D.mapHom φ := (rfl)

/-- An injective group homomorphism preserves the degree of every double coset. -/
@[simp]
theorem degree_mapHom_of_injective {φ : G →* K} (hφ : Function.Injective φ)
    (D : HeckeCoset Δ H₁ H₂) :
    (D.mapHom φ).degree = D.degree := by
  induction D using HeckeCoset.induction with | h g =>
  rw [mapHom_mk, degree_mk, degree_mk]
  exact (Nat.card_congr (decompQuotientEquivMapOfInjective φ hφ H₁ H₂ (g : G))).symm

end HeckeCoset

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
    mapInjectiveLinearEquiv R φ hφ f (D.mapHom φ) = f D :=
  Finsupp.mapDomain_apply_of_injective (HeckeCoset.mapHom_bijective hφ).1 f D

/-- `mapInjectiveLinearEquiv` sends each basis element to the mapped basis element. -/
@[simp]
theorem mapInjectiveLinearEquiv_single (φ : G →* K) (hφ : Function.Injective φ)
    (D : HeckeCoset Δ H₁ H₂) (b : R) :
    mapInjectiveLinearEquiv R φ hφ (single R D b) = single R (D.mapHom φ) b :=
  mapDomain_single R _ D b

/-- `mapInjectiveLinearEquiv` sends structure constants on `(H₁, H₂, H₃)` to structure constants on
`(H₁.map φ, H₂.map φ, H₃.map φ)`. -/
theorem mapInjectiveLinearEquiv_structureConstants (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    [IsHeckeTriple (Δ.map φ) (H₁.map φ) (H₂.map φ)]
    [IsHeckeTriple (Δ.map φ) (H₂.map φ) (H₃.map φ)]
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
    [IsHeckeTriple (Δ.map φ) (H₁.map φ) (H₂.map φ)]
    [IsHeckeTriple (Δ.map φ) (H₂.map φ) (H₃.map φ)]
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
    [IsHeckeTriple Δ H H] [IsHeckeTriple (Δ.map φ) (H.map φ) (H.map φ)] :
    𝕋 Δ H R ≃+* 𝕋 (Δ.map φ) (H.map φ) R :=
  { mapInjectiveLinearEquiv R φ hφ with
    map_mul' := mapInjectiveLinearEquiv_mul R φ hφ }

/-- `mapInjectiveRingEquiv` coerces to `mapInjectiveLinearEquiv`. -/
-- Deliberately not `@[simp]`: rewriting `⇑(mapInjectiveRingEquiv …)` to a `LinearEquiv` prevents
-- generic ring-homomorphism simp lemmas (`map_mul`, `map_one`) from firing.
theorem coe_mapInjectiveRingEquiv (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H H] [IsHeckeTriple (Δ.map φ) (H.map φ) (H.map φ)] :
    ⇑(mapInjectiveRingEquiv R (Δ := Δ) (H := H) φ hφ) =
      mapInjectiveLinearEquiv R φ hφ := (rfl)

/-- `mapInjectiveRingEquiv` sends each basis element `single R D b` to `single R (D.mapHom φ) b`. -/
@[simp]
theorem mapInjectiveRingEquiv_single (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H H] [IsHeckeTriple (Δ.map φ) (H.map φ) (H.map φ)]
    (D : HeckeCoset Δ H H) (b : R) :
    mapInjectiveRingEquiv R φ hφ (single R D b) = single R (D.mapHom φ) b :=
  mapInjectiveLinearEquiv_single R φ hφ D b

/-- The inverse of `mapInjectiveRingEquiv` sends `single R (D.mapHom φ) b` back to
`single R D b`. -/
@[simp]
theorem mapInjectiveRingEquiv_symm_single_mapHom (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H H] [IsHeckeTriple (Δ.map φ) (H.map φ) (H.map φ)]
    (D : HeckeCoset Δ H H) (b : R) :
    (mapInjectiveRingEquiv R φ hφ).symm (single R (D.mapHom φ) b) = single R D b :=
  (mapInjectiveRingEquiv R φ hφ).injective (by simp)

/-- `mapInjectiveRingEquiv` preserves the degree homomorphism `LeftCosetModule.deg`. -/
@[simp]
theorem deg_mapInjectiveRingEquiv (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H H] [IsHeckeTriple (Δ.map φ) (H.map φ) (H.map φ)]
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
    [IsHeckeTriple Δ H H] [IsHeckeTriple (Δ.map φ) (H.map φ) (H.map φ)] :
    (LeftCosetModule.deg (Δ.map φ) (H.map φ) R).comp
        ↑(mapInjectiveRingEquiv R (Δ := Δ) (H := H) φ hφ) =
      LeftCosetModule.deg Δ H R :=
  RingHom.ext (deg_mapInjectiveRingEquiv R φ hφ)

end HeckeCosetModule

end InjectiveHom

end
