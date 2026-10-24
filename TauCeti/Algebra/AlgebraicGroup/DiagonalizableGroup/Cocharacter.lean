/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Points
public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv

/-!
# Cocharacters through a diagonalizable subgroup

Let `π : H →ₐc[R] R[X]` present a group morphism `D(X) → G = Spec H` from the diagonalizable
group of a commutative group `X`, for instance a chosen split maximal torus. A cocharacter
`ψ : X →* Multiplicative ℤ` of `D(X)` gives the cocharacter `λ = π.cocharacter ψ` of `G`, the
composite `𝔾ₘ → D(X) → G`. On points it sends a unit `u` to the image in `G` of the point of
`D(X)` whose character is `χ ↦ u ^ ⟨χ, ψ⟩`.

## Main declarations

* `BialgHom.cocharacter`: the cocharacter `𝔾ₘ → D(X) → G` of a cocharacter of `D(X)`, with
  point formula `BialgHom.pointsHom_cocharacter`.
* `BialgHom.pointsHom_cocharacter_mul` and `BialgHom.cocharacter_pow`: products and powers of
  cocharacters of `D(X)`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
-/

public section

open WithConv

namespace BialgHom

open TauCeti

universe u v w x

variable {R : Type u} {H : Type v} {X : Type w} [CommRing R] [CommRing H] [Bialgebra R H]
  [CommGroup X] (π : H →ₐc[R] MonoidAlgebra R X)

/-- The cocharacter `𝔾ₘ → D(X) → G` given by a cocharacter `ψ` of the diagonalizable group
`D(X)`, where `π` presents the group morphism `D(X) → G`. -/
noncomputable def cocharacter (ψ : X →* Multiplicative ℤ) : H →ₐc[R] LaurentPolynomial R :=
  (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).symm.toBialgHom.comp
    ((MonoidAlgebra.mapDomainBialgHom R ψ).comp π)

/-- In the group-algebra presentation of `𝔾ₘ`, the cocharacter of `ψ` is `π` followed by the map
of group algebras induced by `ψ`. -/
@[simp]
theorem toMultiplicativeBialgEquiv_comp_cocharacter (ψ : X →* Multiplicative ℤ) :
    (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ :
        LaurentPolynomial R →ₐc[R] MonoidAlgebra R (Multiplicative ℤ)).comp (π.cocharacter ψ) =
      (MonoidAlgebra.mapDomainBialgHom R ψ).comp π := by
  ext h
  simp [cocharacter]

/-! ### Points -/

section Points

variable {A : Type x} [CommRing A] [Algebra R A]

/-- The cocharacter of `ψ` sends a unit `u` to the image in `G` of the point
`DiagonalizableGroup.cocharPoints ψ` of `D(X)` at `u`, whose character is `χ ↦ u ^ ⟨χ, ψ⟩`. -/
theorem pointsHom_cocharacter (ψ : X →* Multiplicative ℤ) (u : Aˣ) :
    Cocharacter.pointsHom A (π.cocharacter ψ) u =
      BialgHom.mapDomain π
        (DiagonalizableGroup.cocharPoints ψ
          ((DiagonalizableGroup.pointsMulEquiv (R := R)).symm (zpowersHom Aˣ u))) := by
  -- The Laurent point `T ↦ u` of `𝔾ₘ` is the group-algebra point with character `zpowersHom u`.
  have hG : BialgHom.mapDomain (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).symm.toBialgHom
      (toConv (laurentEval (R := R) u)) =
        (DiagonalizableGroup.pointsMulEquiv (R := R)).symm (zpowersHom Aˣ u) := by
    apply (DiagonalizableGroup.pointsMulEquiv (R := R) (A := A)).injective
    refine MonoidHom.ext_mint (Units.ext ?_)
    simp [BialgHom.mapDomain_apply]
  -- The cocharacter `ψ` of `D(X)` acts on points by precomposition with `R[ψ]`.
  have hP : DiagonalizableGroup.cocharPoints ψ
      ((DiagonalizableGroup.pointsMulEquiv (R := R)).symm (zpowersHom Aˣ u)) =
        BialgHom.mapDomain (MonoidAlgebra.mapDomainBialgHom R ψ)
          ((DiagonalizableGroup.pointsMulEquiv (R := R)).symm (zpowersHom Aˣ u)) := by
    apply (DiagonalizableGroup.pointsMulEquiv (R := R) (A := A)).injective
    refine MonoidHom.ext fun χ ↦ ?_
    rw [DiagonalizableGroup.pointsMulEquiv_cocharPoints, ← DiagonalizableGroup.pointsMap,
      DiagonalizableGroup.pointsMulEquiv_pointsMap]
    simp
  rw [Cocharacter.pointsHom_apply, cocharacter, BialgHom.mapDomain_comp, BialgHom.mapDomain_comp,
    MonoidHom.comp_apply, MonoidHom.comp_apply, hG, hP]

/-- The product of two cocharacters of `D(X)` acts on points as the product of their actions. -/
theorem pointsHom_cocharacter_mul (ψ ψ' : X →* Multiplicative ℤ) (u : Aˣ) :
    Cocharacter.pointsHom A (π.cocharacter (ψ * ψ')) u =
      Cocharacter.pointsHom A (π.cocharacter ψ) u *
        Cocharacter.pointsHom A (π.cocharacter ψ') u := by
  rw [pointsHom_cocharacter, pointsHom_cocharacter, pointsHom_cocharacter, ← map_mul]
  congr 1
  apply (DiagonalizableGroup.pointsMulEquiv (R := R) (A := A)).injective
  refine MonoidHom.ext fun χ ↦ ?_
  simp only [map_mul, MonoidHom.mul_apply, DiagonalizableGroup.pointsMulEquiv_cocharPoints,
    toAdd_mul, zpow_add]

end Points

/-- The `n`-th power of a cocharacter of `D(X)` gives the `n`-th power `t ↦ λ(tⁿ)` of its
cocharacter. -/
theorem cocharacter_pow (ψ : X →* Multiplicative ℤ) (n : ℤ) :
    π.cocharacter (ψ ^ n) = (π.cocharacter ψ).powCocharacter n := by
  ext h : 1
  rw [BialgHom.powCocharacter_apply]
  simp only [cocharacter, BialgHom.comp_apply]
  induction π h using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, AddMonoidAlgebra.mapDomain_add]
  | single χ a =>
    simp only [MonoidAlgebra.mapDomainBialgHom_single, BialgEquiv.toBialgHom_eq_coe,
      BialgEquiv.coe_toBialgHom, AddMonoidAlgebra.toMultiplicativeBialgEquiv_symm_single,
      MonoidHom.zpow_apply, AddMonoidAlgebra.mapDomain_single,
      toAdd_zpow, smul_eq_mul]
    rw [mul_comm]

end BialgHom
