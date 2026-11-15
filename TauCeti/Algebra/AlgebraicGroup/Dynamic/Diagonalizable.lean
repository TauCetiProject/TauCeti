/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Tangent
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Centralizer
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Weights
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Maximal

/-!
# Dynamic subgroups of cocharacters through a diagonalizable subgroup

Let `π : H →ₐc[R] R[X]` present a group morphism `D(X) → G = Spec H` from the diagonalizable
group of a commutative group `X`, for instance a chosen split maximal torus `T`. A cocharacter
`ψ : X →* Multiplicative ℤ` of `D(X)` gives the cocharacter `λ = π.cocharacter ψ` of `G`.

The `λ`-weights of the adjoint representation are read off from the `D(X)`-weights through the
pairing: the `λ`-weight space of weight `n` is the sum of the `D(X)`-weight spaces `𝔤_χ` with
`⟨χ, ψ⟩ = n`. Consequently, with finite projective cotangent module,

* `Lie P_G(λ)` is the sum of the `𝔤_χ` with `⟨χ, ψ⟩ ≥ 0`;
* `Lie U_G(λ)` is the sum of the `𝔤_χ` with `⟨χ, ψ⟩ > 0`;
* `Lie Z_G(λ)` is the sum of the `𝔤_χ` with `⟨χ, ψ⟩ = 0`.

When `π` is surjective, so that `D(X)` is a closed subgroup of `G`, it is contained in the
dynamic Levi `Z_G(λ)`. None of these statements needs a field, smoothness, reductivity or
maximality of the diagonalizable subgroup.

## Main declarations

* `BialgHom.adjointWeightSpace_cocharacter` and `BialgHom.iSup_adjointWeightSpace_cocharacter`:
  the `λ`-weight spaces and their sums in terms of the `D(X)`-weight spaces.
* `BialgHom.lieSubalgebra_parabolicDefiningHopfIdeal_cocharacter_toSubmodule`,
  `BialgHom.lieSubalgebra_unipotentDefiningHopfIdeal_cocharacter_toSubmodule` and
  `BialgHom.lieSubalgebra_leviDefiningHopfIdeal_cocharacter_toSubmodule`: the Lie algebras of
  `P_G(λ)`, `U_G(λ)` and `Z_G(λ)` in `D(X)`-weight spaces.
* `BialgHom.leviDefiningHopfIdeal_cocharacter_le_kerOfSurjective`: a closed diagonalizable
  subgroup lies in `Z_G(λ)`.
* `TauCeti.SplitMaximalTorus.leviDefiningHopfIdeal_cocharacter_le_definingIdeal`: the case of a
  chosen split maximal torus `T`, with `π = T.coordinateMap.hom`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
-/

public section

namespace BialgHom

open TauCeti

universe u v w

section Levi

variable {R : Type u} {H : Type v} {X : Type w} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [CommGroup X] (π : H →ₐc[R] MonoidAlgebra R X)

/-- A closed diagonalizable subgroup lies in the dynamic Levi subgroup of each of its
cocharacters. -/
theorem leviDefiningHopfIdeal_cocharacter_le_kerOfSurjective (hπ : Function.Surjective π)
    (ψ : X →* Multiplicative ℤ) :
    Cocharacter.leviDefiningHopfIdeal (π.cocharacter ψ) ≤ HopfIdeal.kerOfSurjective π hπ := by
  rw [BialgHom.leviDefiningHopfIdeal_eq_centralizerHopfIdeal,
    BialgEquiv.toBialgHom_eq_coe, toMultiplicativeBialgEquiv_comp_cocharacter]
  exact BialgHom.centralizerHopfIdeal_comp_le_kerOfSurjective _ hπ _

end Levi

/-! ### Lie algebras -/

section Tangent

variable {R H : Type u} {X : Type w} [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]
  [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)] (π : H →ₐc[R] MonoidAlgebra R X)

/-- The weight-`n` space of the adjoint action of the cocharacter of `ψ` is the sum of the
`D(X)`-weight spaces of the characters `χ` with `⟨χ, ψ⟩ = n`. -/
theorem adjointWeightSpace_cocharacter (ψ : X →* Multiplicative ℤ) (n : ℤ) :
    Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp (π.cocharacter ψ))
        (Multiplicative.ofAdd n) =
      ⨆ (χ) (_ : DiagonalizableGroup.pairing χ ψ = n), Derivation.adjointWeightSpace π χ := by
  rw [BialgEquiv.toBialgHom_eq_coe, toMultiplicativeBialgEquiv_comp_cocharacter,
    Derivation.adjointWeightSpace_mapDomainBialgHom_comp]
  refine iSup_congr fun χ ↦ iSup_congr_Prop ?_ fun _ ↦ rfl
  rw [Set.mem_preimage, Set.mem_singleton_iff, DiagonalizableGroup.pairing_def]
  exact ⟨fun h ↦ by rw [h, toAdd_ofAdd], fun h ↦ by rw [← h, ofAdd_toAdd]⟩

/-- The sum of the adjoint weight spaces of the cocharacter of `ψ` over the weights satisfying
`p` is the sum of the `D(X)`-weight spaces of the characters `χ` with `p ⟨χ, ψ⟩`. -/
theorem iSup_adjointWeightSpace_cocharacter (ψ : X →* Multiplicative ℤ) (p : ℤ → Prop) :
    ⨆ (n : ℤ) (_ : p n), Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp (π.cocharacter ψ))
        (Multiplicative.ofAdd n) =
      ⨆ (χ) (_ : p (DiagonalizableGroup.pairing χ ψ)), Derivation.adjointWeightSpace π χ := by
  simp_rw [adjointWeightSpace_cocharacter]
  refine le_antisymm (iSup₂_le fun n hn ↦ iSup₂_le fun χ hχ ↦ ?_)
    (iSup₂_le fun χ hχ ↦ ?_)
  · exact le_iSup₂_of_le (f := fun χ (_ : p (DiagonalizableGroup.pairing χ ψ)) ↦
      Derivation.adjointWeightSpace π χ) χ (hχ ▸ hn) le_rfl
  · exact le_iSup₂_of_le (DiagonalizableGroup.pairing χ ψ) hχ (le_iSup₂_of_le χ rfl le_rfl)

/-- The Lie algebra of the dynamic parabolic subgroup of the cocharacter of `ψ` is the sum of the
`D(X)`-weight spaces of the characters `χ` with `⟨χ, ψ⟩ ≥ 0`. -/
theorem lieSubalgebra_parabolicDefiningHopfIdeal_cocharacter_toSubmodule
    (ψ : X →* Multiplicative ℤ) :
    ((Cocharacter.parabolicDefiningHopfIdeal (π.cocharacter ψ)).lieSubalgebra
        (B := R)).toSubmodule =
      (⨆ (χ) (_ : 0 ≤ DiagonalizableGroup.pairing χ ψ), Derivation.adjointWeightSpace π χ).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).toLinearMap := by
  rw [BialgHom.lieSubalgebra_parabolicDefiningHopfIdeal_toSubmodule,
    iSup_adjointWeightSpace_cocharacter π ψ (0 ≤ ·)]

/-- The Lie algebra of the dynamic unipotent subgroup of the cocharacter of `ψ` is the sum of the
`D(X)`-weight spaces of the characters `χ` with `⟨χ, ψ⟩ > 0`. -/
theorem lieSubalgebra_unipotentDefiningHopfIdeal_cocharacter_toSubmodule
    (ψ : X →* Multiplicative ℤ) :
    ((π.cocharacter ψ).unipotentDefiningHopfIdeal.lieSubalgebra (B := R)).toSubmodule =
      (⨆ (χ) (_ : 0 < DiagonalizableGroup.pairing χ ψ), Derivation.adjointWeightSpace π χ).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).toLinearMap := by
  rw [BialgHom.lieSubalgebra_unipotentDefiningHopfIdeal_toSubmodule,
    iSup_adjointWeightSpace_cocharacter π ψ (0 < ·)]

end Tangent

section LeviTangent

variable {R H X : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]
  [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)] (π : H →ₐc[R] MonoidAlgebra R X)

/-- The Lie algebra of the dynamic Levi subgroup of the cocharacter of `ψ` is the sum of the
`D(X)`-weight spaces of the characters `χ` with `⟨χ, ψ⟩ = 0`. -/
theorem lieSubalgebra_leviDefiningHopfIdeal_cocharacter_toSubmodule
    (ψ : X →* Multiplicative ℤ) :
    ((Cocharacter.leviDefiningHopfIdeal (π.cocharacter ψ)).lieSubalgebra (B := R)).toSubmodule =
      (⨆ (χ) (_ : DiagonalizableGroup.pairing χ ψ = 0), Derivation.adjointWeightSpace π χ).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).toLinearMap := by
  -- Lift the character group of `𝔾ₘ` to the universe of `H`, where the Lie algebra of a
  -- centralizer is computed.
  let q : X →* ULift.{u} (Multiplicative ℤ) := MulEquiv.ulift.symm.toMonoidHom.comp ψ
  have hq : MonoidAlgebra.mapDomainBialgHom R q =
      (MonoidAlgebra.mapDomainBialgHom R MulEquiv.ulift.symm.toMonoidHom).comp
        (MonoidAlgebra.mapDomainBialgHom R ψ) :=
    MonoidAlgebra.mapDomainBialgHom_comp _ _
  have hψ : MonoidAlgebra.mapDomainBialgHom R ψ =
      (MonoidAlgebra.mapDomainBialgHom R MulEquiv.ulift.toMonoidHom).comp
        (MonoidAlgebra.mapDomainBialgHom R q) := by
    rw [← MonoidAlgebra.mapDomainBialgHom_comp]
    congr 1
  have hZ : BialgHom.centralizerHopfIdeal ((MonoidAlgebra.mapDomainBialgHom R ψ).comp π) =
      BialgHom.centralizerHopfIdeal ((MonoidAlgebra.mapDomainBialgHom R q).comp π) := by
    apply le_antisymm
    · rw [hψ, BialgHom.comp_assoc]
      exact BialgHom.centralizerHopfIdeal_comp_le _ _
    · rw [hq, BialgHom.comp_assoc]
      exact BialgHom.centralizerHopfIdeal_comp_le _ _
  rw [BialgHom.leviDefiningHopfIdeal_eq_centralizerHopfIdeal,
    BialgEquiv.toBialgHom_eq_coe, toMultiplicativeBialgEquiv_comp_cocharacter, hZ,
    BialgHom.lieSubalgebra_centralizerHopfIdeal_mapDomainBialgHom_comp_toSubmodule]
  congr 1
  refine iSup_congr fun χ ↦ iSup_congr_Prop ?_ fun _ ↦ rfl
  rw [MonoidHom.mem_ker, DiagonalizableGroup.pairing_def]
  simp [q]

end LeviTangent

end BialgHom

namespace TauCeti.SplitMaximalTorus

universe u

variable {R : Type u} [CommRing R] {H : CommHopfAlgCat.{u} R} [Algebra.FiniteType R H] {r : ℕ}

/-- A chosen split maximal torus lies in the dynamic Levi subgroup of each of its
cocharacters. -/
theorem leviDefiningHopfIdeal_cocharacter_le_definingIdeal (T : SplitMaximalTorus R H r)
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) :
    Cocharacter.leviDefiningHopfIdeal (T.coordinateMap.hom.cocharacter ψ) ≤ T.definingIdeal :=
  fun _ hx ↦ (T.mem_definingIdeal _).mpr <| (HopfIdeal.mem_kerOfSurjective _ T.surjective).mp <|
    BialgHom.leviDefiningHopfIdeal_cocharacter_le_kerOfSurjective _ T.surjective ψ hx

end TauCeti.SplitMaximalTorus
