/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Basic
public import Mathlib.Algebra.Algebra.RestrictScalars

/-!
# Restriction of crossed products to an intermediate scalar ring

For a scalar tower from commutative semirings `K` and `L` to a commutative ring `E`,
restricting a cocycle of `Aut_K(E)` to `Aut_L(E)` embeds its crossed product in the original
crossed product. The embedding sends each coefficient to itself and each basis element
`u_σ` to `u_{σ|K}`. Its image consists exactly of the elements whose supported automorphisms
fix the image of `algebraMap L E`. When `E` has no zero divisors, this image is the centralizer
of the image of `L` under `inc c ∘ algebraMap L E`.

This identifies the algebra of a restricted cocycle, the algebraic ingredient in comparing
scalar extension of Brauer classes with restriction in Galois cohomology. Neither finiteness
nor a Galois hypothesis is needed for the embedding or its centralizer description.

## References

* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X, §5.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
-/

public section

noncomputable section

namespace TauCeti

variable {K L E : Type*} [CommSemiring K] [CommSemiring L] [CommRing E]
  [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]

namespace TwoCocycle

/-- Restrict a cocycle to the automorphisms fixing the intermediate scalar ring `L`. -/
def restrict (c : TwoCocycle K E) (L : Type*) [CommSemiring L]
    [Algebra K L] [Algebra L E] [IsScalarTower K L E] : TwoCocycle L E where
  toFun σ τ := c.toFun (σ.restrictScalars K) (τ.restrictScalars K)
  isMulCocycle₂ σ τ ρ :=
    c.isMulCocycle₂ (σ.restrictScalars K) (τ.restrictScalars K) (ρ.restrictScalars K)

/-- Restriction evaluates the original cocycle on the underlying `K`-automorphisms. -/
@[simp]
theorem restrict_toFun (c : TwoCocycle K E) (σ τ : E ≃ₐ[L] E) :
    (c.restrict L).toFun σ τ = c.toFun (σ.restrictScalars K) (τ.restrictScalars K) :=
  (rfl)

/-- Restriction preserves the trivial cocycle. -/
@[simp]
theorem restrict_one : (1 : TwoCocycle K E).restrict L = 1 :=
  TwoCocycle.ext (funext₂ fun _ _ => by simp)

/-- Restriction preserves multiplication of cocycles. -/
@[simp]
theorem restrict_mul (c d : TwoCocycle K E) :
    (c * d).restrict L = c.restrict L * d.restrict L :=
  TwoCocycle.ext (funext₂ fun _ _ => by simp)

/-- Restriction preserves inversion of cocycles. -/
@[simp]
theorem restrict_inv (c : TwoCocycle K E) : c⁻¹.restrict L = (c.restrict L)⁻¹ :=
  TwoCocycle.ext (funext₂ fun _ _ => by simp)

/-- Restriction preserves division of cocycles. -/
@[simp]
theorem restrict_div (c d : TwoCocycle K E) :
    (c / d).restrict L = c.restrict L / d.restrict L :=
  TwoCocycle.ext (funext₂ fun _ _ => by simp)

/-- Restriction preserves natural powers of cocycles. -/
@[simp]
theorem restrict_pow (c : TwoCocycle K E) (n : ℕ) :
    (c ^ n).restrict L = c.restrict L ^ n :=
  TwoCocycle.ext (funext₂ fun _ _ => by simp)

/-- Restriction preserves integer powers of cocycles. -/
@[simp]
theorem restrict_zpow (c : TwoCocycle K E) (n : ℤ) :
    (c ^ n).restrict L = c.restrict L ^ n :=
  TwoCocycle.ext (funext₂ fun _ _ => by simp)

end TwoCocycle

namespace CrossedProduct

variable (c : TwoCocycle K E)

/-- Extend coordinates by zero from `Aut_L(E)` to `Aut_K(E)`. -/
private def restrictionLinearMap : CrossedProduct (c.restrict L) →ₗ[E] CrossedProduct c :=
  (basis c).repr.symm.toLinearMap ∘ₗ
    Finsupp.lmapDomain E E (AlgEquiv.restrictScalars K) ∘ₗ (basis (c.restrict L)).repr.toLinearMap

private theorem restrictionLinearMap_smul_basis (σ : E ≃ₐ[L] E) (x : E) :
    restrictionLinearMap (L := L) c (x • basis (c.restrict L) σ) =
      x • basis c (σ.restrictScalars K) := by
  simp [restrictionLinearMap]

/-- The restricted crossed product is a `K`-algebra through its `L`-algebra structure. -/
instance (priority := 100) instAlgebraRestrict : Algebra K (CrossedProduct (c.restrict L)) :=
  Algebra.restrictScalars K L _

/-- The restricted crossed product carries a scalar tower from `K` through `L`. -/
instance (priority := 100) instIsScalarTowerRestrictBase :
    IsScalarTower K L (CrossedProduct (c.restrict L)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The induced `K`-action is compatible with the left coefficient action of `E`. -/
instance (priority := 100) instIsScalarTowerRestrict :
    IsScalarTower K E (CrossedProduct (c.restrict L)) :=
  IsScalarTower.of_algebraMap_smul fun r a => by
    rw [IsScalarTower.algebraMap_apply K L E, algebraMap_smul E, algebraMap_smul L]

/-- The embedding of the crossed product of the restricted cocycle, compatible with the
`K`-algebra structure induced by its `L`-algebra structure. -/
def restrictHom : CrossedProduct (c.restrict L) →ₐ[K] CrossedProduct c :=
  AlgHom.ofLinearMap ((restrictionLinearMap c).restrictScalars K)
    (by
      simp only [LinearMap.restrictScalars_apply, one_def, restrictionLinearMap_smul_basis,
        TwoCocycle.restrict_toFun, ← AlgEquiv.restrictScalarsHom_apply, map_one])
    (by
      intro a b
      induction a using induction_on with
      | zero => simp
      | add a b ha hb => simp only [add_mul, map_add, ha, hb]
      | smul_basis σ x =>
        induction b using induction_on with
        | zero => simp
        | add a b ha hb => simp only [mul_add, map_add, ha, hb]
        | smul_basis τ y =>
          simp only [LinearMap.restrictScalars_apply, smul_basis_mul_smul_basis,
            restrictionLinearMap_smul_basis, TwoCocycle.restrict_toFun,
            ← AlgEquiv.restrictScalarsHom_apply, map_mul]
          simp only [AlgEquiv.restrictScalarsHom_apply, AlgEquiv.restrictScalars_apply])

/-- The embedding preserves a coefficient times a basis element. -/
@[simp]
theorem restrictHom_smul_basis (σ : E ≃ₐ[L] E) (x : E) :
    restrictHom (L := L) c (x • basis (c.restrict L) σ) =
      x • basis c (σ.restrictScalars K) :=
  restrictionLinearMap_smul_basis c σ x

/-- The embedding sends each basis element to the basis element of the underlying automorphism. -/
@[simp]
theorem restrictHom_basis (σ : E ≃ₐ[L] E) :
    restrictHom (L := L) c (basis (c.restrict L) σ) = basis c (σ.restrictScalars K) := by
  simpa using restrictHom_smul_basis c σ 1

/-- The embedding preserves the coefficient ring. -/
@[simp]
theorem restrictHom_inc (x : E) :
    restrictHom (L := L) c (inc (c.restrict L) x) = inc c x := by
  simp only [inc_apply, restrictHom_smul_basis, TwoCocycle.restrict_toFun,
    ← AlgEquiv.restrictScalarsHom_apply, map_one]

/-- Coordinates of the embedding are extended by zero along restriction of scalars. -/
@[simp]
theorem repr_restrictHom (a : CrossedProduct (c.restrict L)) :
    (basis c).repr (restrictHom (L := L) c a) =
      Finsupp.mapDomain (AlgEquiv.restrictScalars K) ((basis (c.restrict L)).repr a) := by
  simp only [restrictHom, AlgHom.ofLinearMap_apply, LinearMap.restrictScalars_apply,
    restrictionLinearMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Finsupp.lmapDomain_apply]

/-- Restriction of crossed products is injective. -/
theorem restrictHom_injective : Function.Injective (restrictHom (L := L) c) := by
  intro a b h
  apply (basis (c.restrict L)).repr.injective
  apply Finsupp.mapDomain_injective (AlgEquiv.restrictScalars_injective K)
  have hrepr := congrArg (basis c).repr h
  rw [repr_restrictHom, repr_restrictHom] at hrepr
  exact hrepr

/-- An element is in the restricted crossed product exactly when its coefficients vanish
outside the automorphisms fixing `L`. -/
theorem mem_range_restrictHom_iff (a : CrossedProduct c) :
    a ∈ (restrictHom (L := L) c).range ↔
      ∀ σ ∉ Set.range (AlgEquiv.restrictScalars K : (E ≃ₐ[L] E) → E ≃ₐ[K] E),
        (basis c).repr a σ = 0 := by
  have hr : a ∈ (restrictHom (L := L) c).range ↔
      (basis c).repr a ∈ Set.range
        (Finsupp.mapDomain (AlgEquiv.restrictScalars K : (E ≃ₐ[L] E) → E ≃ₐ[K] E)) := by
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨(basis (c.restrict L)).repr b, (repr_restrictHom c b).symm⟩
    · rintro ⟨f, hf⟩
      refine ⟨(basis (c.restrict L)).repr.symm f, ?_⟩
      apply (basis c).repr.injective
      exact (repr_restrictHom c ((basis (c.restrict L)).repr.symm f)).trans
        (by rw [LinearEquiv.apply_symm_apply, hf])
  exact hr.trans (Finsupp.mem_range_mapDomain_iff (AlgEquiv.restrictScalars K)
    (AlgEquiv.restrictScalars_injective K) _)

/-- The image of the restricted crossed product is the centralizer of the image of `L`
under `inc c ∘ algebraMap L E`. This holds for any scalar tower with no zero divisors in `E`,
without finiteness or Galois assumptions. -/
theorem range_restrictHom_eq_centralizer [NoZeroDivisors E] :
    (restrictHom (L := L) c).range =
      Subalgebra.centralizer K (Set.range fun x : L => inc c (algebraMap L E x)) := by
  ext a
  rw [mem_range_restrictHom_iff, Subalgebra.mem_centralizer_iff]
  constructor
  · intro ha y hy
    obtain ⟨x, rfl⟩ := hy
    apply (basis c).repr.injective
    ext σ
    simp only [← smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, repr_mul_inc]
    by_cases hσ : σ ∈ Set.range (AlgEquiv.restrictScalars K : (E ≃ₐ[L] E) → E ≃ₐ[K] E)
    · obtain ⟨τ, rfl⟩ := hσ
      rw [AlgEquiv.restrictScalars_apply, τ.commutes]
      exact mul_comm _ _
    · simp [ha σ hσ]
  · intro ha σ hσ
    by_contra hn
    have hfix (x : L) : σ (algebraMap L E x) = algebraMap L E x := by
      have h := congrArg (fun b => (basis c).repr b σ) (ha _ ⟨x, rfl⟩)
      simp only [← smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, repr_mul_inc] at h
      exact mul_left_cancel₀ hn (h.symm.trans (mul_comm _ _))
    exact hσ ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hfix,
      AlgEquiv.ext fun _ => rfl⟩

/-- The restricted crossed product is canonically equivalent as a `K`-algebra to the
centralizer of the image of `L` under `inc c ∘ algebraMap L E`. -/
def restrictAlgEquivCentralizer [NoZeroDivisors E] :
    CrossedProduct (c.restrict L) ≃ₐ[K]
      Subalgebra.centralizer K (Set.range fun x : L => inc c (algebraMap L E x)) :=
  (AlgEquiv.ofInjective (restrictHom (L := L) c) (restrictHom_injective c)).trans
    (Subalgebra.equivOfEq _ _ (range_restrictHom_eq_centralizer c))

/-- The centralizer equivalence has the same underlying value as the restriction embedding. -/
@[simp]
theorem coe_restrictAlgEquivCentralizer_apply [NoZeroDivisors E]
    (a : CrossedProduct (c.restrict L)) :
    (restrictAlgEquivCentralizer c a : CrossedProduct c) = restrictHom (L := L) c a :=
  (rfl)

end CrossedProduct

end TauCeti
