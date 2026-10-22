/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Centralizer
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Weights
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Maximal

/-!
# Dynamic subgroups of cocharacters of a split maximal torus

Let `T` be a chosen split maximal torus of rank `r` of an affine group `G = Spec H` over a
commutative ring `R`, with character lattice `X = Multiplicative (ULift (Fin r) →₀ ℤ)`. A
cocharacter `ψ : X →* Multiplicative ℤ` of `T` gives the cocharacter `λ = T.cocharacter ψ`
of `G`, the composite `𝔾ₘ → T → G`. On points it sends a unit `u` to the image in `G` of the
point of `T` whose character is `χ ↦ u ^ ⟨χ, ψ⟩`.

The `λ`-weights of the adjoint representation are read off from the `T`-weights through the
pairing: the `λ`-weight space of weight `n` is the sum of the `T`-weight spaces `𝔤_χ` with
`⟨χ, ψ⟩ = n`. Consequently, with finite projective cotangent module,

* `Lie P_G(λ)` is the sum of the `𝔤_χ` with `⟨χ, ψ⟩ ≥ 0`;
* `Lie U_G(λ)` is the sum of the `𝔤_χ` with `⟨χ, ψ⟩ > 0`;
* `Lie Z_G(λ)` is the sum of the `𝔤_χ` with `⟨χ, ψ⟩ = 0`.

The torus is contained in the dynamic Levi `Z_G(λ)`. None of these statements needs a field,
smoothness or reductivity.

## Main declarations

* `TauCeti.SplitMaximalTorus.cocharacter`: the cocharacter `𝔾ₘ → T → G` of a cocharacter of the
  chosen torus, with point formula `TauCeti.SplitMaximalTorus.pointsHom_cocharacter`.
* `TauCeti.SplitMaximalTorus.pointsHom_cocharacter_mul` and
  `TauCeti.SplitMaximalTorus.cocharacter_pow`: products and powers of torus cocharacters.
* `TauCeti.SplitMaximalTorus.adjointWeightSpace_cocharacter` and
  `TauCeti.SplitMaximalTorus.iSup_adjointWeightSpace_cocharacter`: the `λ`-weight spaces and
  their sums in terms of the `T`-weight spaces.
* `TauCeti.SplitMaximalTorus.lieSubalgebra_parabolicDefiningHopfIdeal_cocharacter_toSubmodule`,
  `TauCeti.SplitMaximalTorus.lieSubalgebra_unipotentDefiningHopfIdeal_cocharacter_toSubmodule`
  and `TauCeti.SplitMaximalTorus.lieSubalgebra_leviDefiningHopfIdeal_cocharacter_toSubmodule`:
  the Lie algebras of `P_G(λ)`, `U_G(λ)` and `Z_G(λ)` in `T`-weight spaces.
* `TauCeti.SplitMaximalTorus.leviDefiningHopfIdeal_cocharacter_le_definingIdeal`: `T` lies in
  `Z_G(λ)`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
-/

public section

open WithConv

namespace TauCeti.SplitMaximalTorus

universe u v

variable {R : Type u} [CommRing R] {H : CommHopfAlgCat.{u} R} [Algebra.FiniteType R H] {r : ℕ}
  (T : SplitMaximalTorus R H r)

/-- The cocharacter `𝔾ₘ → T → G` of the ambient group given by a cocharacter `ψ` of the
chosen split maximal torus. -/
noncomputable def cocharacter (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) :
    H →ₐc[R] LaurentPolynomial R :=
  (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).symm.toBialgHom.comp
    ((MonoidAlgebra.mapDomainBialgHom R ψ).comp T.coordinateMap.hom)

/-- In the group-algebra presentation of `𝔾ₘ`, the cocharacter of `ψ` is restriction to the
torus followed by the map of group algebras induced by `ψ`. -/
@[simp]
theorem toMultiplicativeBialgEquiv_comp_cocharacter
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) :
    (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ :
        LaurentPolynomial R →ₐc[R] MonoidAlgebra R (Multiplicative ℤ)).comp (T.cocharacter ψ) =
      (MonoidAlgebra.mapDomainBialgHom R ψ).comp T.coordinateMap.hom := by
  ext h
  simp [cocharacter]

/-! ### Points -/

section Points

variable {A : Type v} [CommRing A] [Algebra R A]

/-- The cocharacter of `ψ` sends a unit `u` to the image in `G` of the torus point
`DiagonalizableGroup.cocharPoints ψ` at `u`, whose character is `χ ↦ u ^ ⟨χ, ψ⟩`. -/
theorem pointsHom_cocharacter
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) (u : Aˣ) :
    Cocharacter.pointsHom A (T.cocharacter ψ) u =
      BialgHom.mapDomain T.coordinateMap.hom
        (DiagonalizableGroup.cocharPoints ψ
          ((DiagonalizableGroup.pointsMulEquiv (R := R)).symm (zpowersHom Aˣ u))) := by
  have hT (m : Multiplicative ℤ) : (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R ℤ).symm
      (MonoidAlgebra.single m 1) = LaurentPolynomial.T m.toAdd := by
    rw [AlgEquiv.symm_apply_eq, LaurentPolynomial.T,
      AddMonoidAlgebra.toMultiplicativeAlgEquiv_single, ofAdd_toAdd]
  have hQ : DiagonalizableGroup.cocharPoints ψ
      ((DiagonalizableGroup.pointsMulEquiv (R := R)).symm (zpowersHom Aˣ u)) =
        toConv (((laurentEval (R := R) u).comp
          (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R ℤ).symm.toAlgHom).comp
            (MonoidAlgebra.mapDomainAlgHom R R ψ)) := by
    apply (DiagonalizableGroup.pointsMulEquiv (R := R) (A := A)).injective
    refine MonoidHom.ext fun χ ↦ Units.ext ?_
    rw [DiagonalizableGroup.pointsMulEquiv_cocharPoints, MulEquiv.apply_symm_apply,
      DiagonalizableGroup.pointsMulEquiv_apply, DiagonalizableGroup.charOfPoint_apply_coe]
    simp [hT]
  rw [hQ, Cocharacter.pointsHom_apply, BialgHom.mapDomain_apply, BialgHom.mapDomain_apply]
  rfl

/-- The product of two torus cocharacters acts on points as the product of their actions. -/
theorem pointsHom_cocharacter_mul
    (ψ ψ' : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) (u : Aˣ) :
    Cocharacter.pointsHom A (T.cocharacter (ψ * ψ')) u =
      Cocharacter.pointsHom A (T.cocharacter ψ) u *
        Cocharacter.pointsHom A (T.cocharacter ψ') u := by
  rw [pointsHom_cocharacter, pointsHom_cocharacter, pointsHom_cocharacter, ← map_mul]
  congr 1
  apply (DiagonalizableGroup.pointsMulEquiv (R := R) (A := A)).injective
  refine MonoidHom.ext fun χ ↦ ?_
  rw [map_mul, MonoidHom.mul_apply, DiagonalizableGroup.pointsMulEquiv_cocharPoints,
    DiagonalizableGroup.pointsMulEquiv_cocharPoints,
    DiagonalizableGroup.pointsMulEquiv_cocharPoints, MonoidHom.mul_apply, toAdd_mul, zpow_add]

end Points

/-- The `n`-th power of a torus cocharacter is the `n`-th power `t ↦ λ(tⁿ)` of its
cocharacter. -/
theorem cocharacter_pow (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ)
    (n : ℤ) : T.cocharacter (ψ ^ n) = (T.cocharacter ψ).powCocharacter n := by
  have hs (m : Multiplicative ℤ) (a : R) :
      (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).symm (MonoidAlgebra.single m a) =
        AddMonoidAlgebra.single m.toAdd a := by
    apply EquivLike.injective (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ)
    rw [BialgEquiv.apply_symm_apply, AddMonoidAlgebra.toMultiplicativeBialgEquiv_single,
      ofAdd_toAdd]
  ext h : 1
  rw [BialgHom.powCocharacter_apply]
  simp only [cocharacter, BialgHom.comp_apply]
  induction T.coordinateMap.hom h using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, AddMonoidAlgebra.mapDomain_add]
  | single χ a =>
    simp only [MonoidAlgebra.mapDomainBialgHom_single, BialgEquiv.toBialgHom_eq_coe,
      BialgEquiv.coe_toBialgHom, hs, MonoidHom.zpow_apply, AddMonoidAlgebra.mapDomain_single,
      toAdd_zpow, smul_eq_mul]
    rw [mul_comm]

/-- The torus lies in the dynamic Levi subgroup of each of its cocharacters. -/
theorem leviDefiningHopfIdeal_cocharacter_le_definingIdeal
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) :
    Cocharacter.leviDefiningHopfIdeal (T.cocharacter ψ) ≤ T.definingIdeal := by
  rw [BialgHom.leviDefiningHopfIdeal_eq_centralizerHopfIdeal,
    BialgEquiv.toBialgHom_eq_coe, toMultiplicativeBialgEquiv_comp_cocharacter]
  intro x hx
  rw [mem_definingIdeal]
  exact (HopfIdeal.mem_kerOfSurjective _ T.surjective).mp
    (BialgHom.centralizerHopfIdeal_comp_le_kerOfSurjective _ T.surjective _ hx)

/-! ### Lie algebras -/

section Tangent

variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]

/-- The weight-`n` space of the adjoint action of the cocharacter of `ψ` is the sum of the
`T`-weight spaces of the characters `χ` with `⟨χ, ψ⟩ = n`. -/
theorem adjointWeightSpace_cocharacter
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) (n : ℤ) :
    Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp (T.cocharacter ψ))
        (Multiplicative.ofAdd n) =
      ⨆ (χ) (_ : DiagonalizableGroup.pairing χ ψ = n),
        Derivation.adjointWeightSpace T.coordinateMap.hom χ := by
  rw [BialgEquiv.toBialgHom_eq_coe, toMultiplicativeBialgEquiv_comp_cocharacter,
    Derivation.adjointWeightSpace_mapDomainBialgHom_comp]
  refine iSup_congr fun χ ↦ iSup_congr_Prop ?_ fun _ ↦ rfl
  rw [Set.mem_preimage, Set.mem_singleton_iff, DiagonalizableGroup.pairing_def]
  exact ⟨fun h ↦ by rw [h, toAdd_ofAdd], fun h ↦ by rw [← h, ofAdd_toAdd]⟩

/-- The sum of the adjoint weight spaces of the cocharacter of `ψ` over the weights satisfying
`p` is the sum of the `T`-weight spaces of the characters `χ` with `p ⟨χ, ψ⟩`. -/
theorem iSup_adjointWeightSpace_cocharacter
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) (p : ℤ → Prop) :
    ⨆ (n : ℤ) (_ : p n), Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp (T.cocharacter ψ))
        (Multiplicative.ofAdd n) =
      ⨆ (χ) (_ : p (DiagonalizableGroup.pairing χ ψ)),
        Derivation.adjointWeightSpace T.coordinateMap.hom χ := by
  simp_rw [adjointWeightSpace_cocharacter]
  refine le_antisymm (iSup₂_le fun n hn ↦ iSup₂_le fun χ hχ ↦ ?_)
    (iSup₂_le fun χ hχ ↦ ?_)
  · exact le_iSup₂_of_le (f := fun χ (_ : p (DiagonalizableGroup.pairing χ ψ)) ↦
      Derivation.adjointWeightSpace T.coordinateMap.hom χ) χ (hχ ▸ hn) le_rfl
  · exact le_iSup₂_of_le (DiagonalizableGroup.pairing χ ψ) hχ (le_iSup₂_of_le χ rfl le_rfl)

/-- The Lie algebra of the dynamic parabolic subgroup of the cocharacter of `ψ` is the sum of the
`T`-weight spaces of the characters `χ` with `⟨χ, ψ⟩ ≥ 0`. -/
theorem lieSubalgebra_parabolicDefiningHopfIdeal_cocharacter_toSubmodule
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) :
    ((Cocharacter.parabolicDefiningHopfIdeal (T.cocharacter ψ)).lieSubalgebra
        (B := R)).toSubmodule =
      (⨆ (χ) (_ : 0 ≤ DiagonalizableGroup.pairing χ ψ),
        Derivation.adjointWeightSpace T.coordinateMap.hom χ).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).toLinearMap := by
  rw [BialgHom.lieSubalgebra_parabolicDefiningHopfIdeal_toSubmodule,
    iSup_adjointWeightSpace_cocharacter T ψ (0 ≤ ·)]

/-- The Lie algebra of the dynamic unipotent subgroup of the cocharacter of `ψ` is the sum of the
`T`-weight spaces of the characters `χ` with `⟨χ, ψ⟩ > 0`. -/
theorem lieSubalgebra_unipotentDefiningHopfIdeal_cocharacter_toSubmodule
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) :
    ((T.cocharacter ψ).unipotentDefiningHopfIdeal.lieSubalgebra (B := R)).toSubmodule =
      (⨆ (χ) (_ : 0 < DiagonalizableGroup.pairing χ ψ),
        Derivation.adjointWeightSpace T.coordinateMap.hom χ).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).toLinearMap := by
  rw [BialgHom.lieSubalgebra_unipotentDefiningHopfIdeal_toSubmodule,
    iSup_adjointWeightSpace_cocharacter T ψ (0 < ·)]

/-- The Lie algebra of the dynamic Levi subgroup of the cocharacter of `ψ` is the sum of the
`T`-weight spaces of the characters `χ` with `⟨χ, ψ⟩ = 0`. -/
theorem lieSubalgebra_leviDefiningHopfIdeal_cocharacter_toSubmodule
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) :
    ((Cocharacter.leviDefiningHopfIdeal (T.cocharacter ψ)).lieSubalgebra (B := R)).toSubmodule =
      (⨆ (χ) (_ : DiagonalizableGroup.pairing χ ψ = 0),
        Derivation.adjointWeightSpace T.coordinateMap.hom χ).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).toLinearMap := by
  -- Lift the character group of `𝔾ₘ` to the universe of `H`, where the Lie algebra of a
  -- centralizer is computed.
  let q : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* ULift.{u} (Multiplicative ℤ) :=
    MulEquiv.ulift.symm.toMonoidHom.comp ψ
  have hq : MonoidAlgebra.mapDomainBialgHom R q =
      (MonoidAlgebra.mapDomainBialgHom R MulEquiv.ulift.symm.toMonoidHom).comp
        (MonoidAlgebra.mapDomainBialgHom R ψ) :=
    MonoidAlgebra.mapDomainBialgHom_comp _ _
  have hψ : MonoidAlgebra.mapDomainBialgHom R ψ =
      (MonoidAlgebra.mapDomainBialgHom R MulEquiv.ulift.toMonoidHom).comp
        (MonoidAlgebra.mapDomainBialgHom R q) := by
    rw [← MonoidAlgebra.mapDomainBialgHom_comp]
    congr 1
  have hZ : BialgHom.centralizerHopfIdeal
        ((MonoidAlgebra.mapDomainBialgHom R ψ).comp T.coordinateMap.hom) =
      BialgHom.centralizerHopfIdeal
        ((MonoidAlgebra.mapDomainBialgHom R q).comp T.coordinateMap.hom) := by
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

end Tangent

end TauCeti.SplitMaximalTorus
