/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.HeckeComparison.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Star
public import TauCeti.Algebra.TypeAHeckeAlgebra.Star
public import TauCeti.Algebra.TypeAHeckeAlgebra.UnitaryStar

/-!
# Star-algebra comparisons with the type-A Hecke algebra

Whenever `τ * (q + q⁻¹) ^ 2 = 1`, `BalancedProjectionAlgebra.heckeEquiv` upgrades to a
`⋆`-algebra isomorphism `BalancedProjectionAlgebra R τ ≃⋆ₐ[R] InfiniteTypeAHeckeAlgebra R q` in
both involutive parameter fibers:
* **real-parameter fiber** (`Fact (IsSelfAdjoint (q : R))`, `star (T i) = T i`);
* **unit-circle fiber** (`Fact ((q : R) ∈ unitary R)`, `star (T i) = T i⁻¹ = T i - (q - q⁻¹)`).

## Main definitions and results

* `TauCeti.BalancedProjectionAlgebra.heckeEquiv_star`,
  `TauCeti.BalancedProjectionAlgebra.heckeStarAlgEquiv`: real-fiber `⋆`-isomorphism with
  `InfiniteTypeAHeckeAlgebra R q`.
* `TauCeti.BalancedProjectionAlgebra.UnitCircle.heckeEquiv_star`,
  `TauCeti.BalancedProjectionAlgebra.UnitCircle.heckeStarAlgEquiv`: unit-circle `⋆`-isomorphism
  with `InfiniteTypeAHeckeAlgebra R q`.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§4, 5, 11.
-/

public section

namespace TauCeti

namespace BalancedProjectionAlgebra

private theorem heckeEquiv_star_of_eigenprojection {R : Type*} [CommRing R] [StarRing R]
    {τ : R} [Fact (IsSelfAdjoint τ)] {q : Rˣ}
    [StarRing (InfiniteTypeAHeckeAlgebra R q)] [StarModule R (InfiniteTypeAHeckeAlgebra R q)]
    (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (hP : ∀ s : Rˣ, (s : R) = q + ↑q⁻¹ →
      ∀ i, IsSelfAdjoint ((↑s⁻¹ : R) • (InfiniteTypeAHeckeAlgebra.T q i + algebraMap R _ ↑q⁻¹)))
    (x : BalancedProjectionAlgebra R τ) :
    heckeEquiv q hτ (star x) = star (heckeEquiv q hτ x) :=
  map_star_iff (F := (heckeEquiv q hτ).toAlgHom) |>.mpr (fun i ↦ by
    simpa only [AlgEquiv.toAlgHom_apply, heckeEquiv_e, ← val_inv_addInvUnit hτ] using
      hP (addInvUnit hτ) (val_addInvUnit hτ) i) x

end BalancedProjectionAlgebra

/-! ### Real-parameter Hecke star compatibility -/

section RealHecke

open InfiniteTypeAHeckeAlgebra (T)

variable {R : Type*} [CommRing R] [StarRing R] {q : Rˣ} [hq : Fact (IsSelfAdjoint (q : R))]

namespace BalancedProjectionAlgebra

variable {τ : R} [Fact (IsSelfAdjoint τ)]

/-- In the real-parameter fiber, `heckeEquiv` commutes with the involutions. -/
@[simp]
theorem heckeEquiv_star (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : BalancedProjectionAlgebra R τ) :
    heckeEquiv q hτ (star x) = star (heckeEquiv q hτ x) :=
  heckeEquiv_star_of_eigenprojection hτ
    (fun s hs i ↦ (InfiniteTypeAHeckeAlgebra.isStarProjection_eigenprojection s hs i).isSelfAdjoint)
    x

@[simp]
theorem heckeEquiv_symm_star (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : InfiniteTypeAHeckeAlgebra R q) :
    (heckeEquiv q hτ).symm (star x) = star ((heckeEquiv q hτ).symm x) :=
  (heckeEquiv q hτ).injective <| by simp

variable (q) in
/-- In the real-parameter fiber, `BalancedProjectionAlgebra R τ` and
`InfiniteTypeAHeckeAlgebra R q` are isomorphic as `⋆`-algebras whenever `τ * (q + q⁻¹) ^ 2 = 1`. -/
def heckeStarAlgEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) :
    BalancedProjectionAlgebra R τ ≃⋆ₐ[R] InfiniteTypeAHeckeAlgebra R q :=
  StarAlgEquiv.ofAlgEquiv (heckeEquiv q hτ) (heckeEquiv_star hτ)

@[simp]
theorem toAlgEquiv_heckeStarAlgEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) :
    (heckeStarAlgEquiv q hτ).toAlgEquiv = heckeEquiv q hτ := (rfl)

@[simp]
theorem heckeStarAlgEquiv_e (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    heckeStarAlgEquiv q hτ (e τ i) =
      (τ * ((q : R) + ↑q⁻¹)) • (T q i + algebraMap R _ ↑q⁻¹) := heckeEquiv_e hτ i

@[simp]
theorem heckeStarAlgEquiv_symm_T (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    (heckeStarAlgEquiv q hτ).symm (T q i) =
      ((q : R) + ↑q⁻¹) • e τ i - algebraMap R _ ↑q⁻¹ := heckeEquiv_symm_T hτ i

end BalancedProjectionAlgebra

end RealHecke

/-! ### Unit-circle Hecke star compatibility -/

section UnitCircleHecke

open InfiniteTypeAHeckeAlgebra (T)

variable {R : Type*} [CommRing R] [StarRing R] {q : Rˣ} [hq : Fact ((q : R) ∈ unitary R)]

namespace BalancedProjectionAlgebra.UnitCircle

variable {τ : R} [Fact (IsSelfAdjoint τ)]

/-- In the unit-circle fiber, `heckeEquiv` commutes with the involutions. -/
@[simp]
theorem heckeEquiv_star (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : BalancedProjectionAlgebra R τ) :
    heckeEquiv q hτ (star x) = star (heckeEquiv q hτ x) :=
  heckeEquiv_star_of_eigenprojection hτ
    (fun s hs i ↦
      (InfiniteTypeAHeckeAlgebra.UnitCircle.isStarProjection_eigenprojection s hs i).isSelfAdjoint)
    x

@[simp]
theorem heckeEquiv_symm_star (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : InfiniteTypeAHeckeAlgebra R q) :
    (heckeEquiv q hτ).symm (star x) = star ((heckeEquiv q hτ).symm x) :=
  (heckeEquiv q hτ).injective <| by simp

variable (q) in
/-- In the unit-circle fiber, `BalancedProjectionAlgebra R τ` and
`InfiniteTypeAHeckeAlgebra R q` are isomorphic as `⋆`-algebras whenever `τ * (q + q⁻¹) ^ 2 = 1`. -/
def heckeStarAlgEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) :
    BalancedProjectionAlgebra R τ ≃⋆ₐ[R] InfiniteTypeAHeckeAlgebra R q :=
  StarAlgEquiv.ofAlgEquiv (heckeEquiv q hτ) (heckeEquiv_star hτ)

@[simp]
theorem toAlgEquiv_heckeStarAlgEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) :
    (heckeStarAlgEquiv q hτ).toAlgEquiv = heckeEquiv q hτ := (rfl)

@[simp]
theorem heckeStarAlgEquiv_e (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    heckeStarAlgEquiv q hτ (e τ i) =
      (τ * ((q : R) + ↑q⁻¹)) • (T q i + algebraMap R _ ↑q⁻¹) := heckeEquiv_e hτ i

@[simp]
theorem heckeStarAlgEquiv_symm_T (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    (heckeStarAlgEquiv q hτ).symm (T q i) =
      ((q : R) + ↑q⁻¹) • e τ i - algebraMap R _ ↑q⁻¹ := heckeEquiv_symm_T hτ i

end BalancedProjectionAlgebra.UnitCircle

end UnitCircleHecke

end TauCeti
