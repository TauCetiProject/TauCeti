/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified
public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.ArtinMap

/-!
# The geometric normalization of the absolute local Artin map

The absolute local Artin map `artinMap K : Kˣ →* G_K^ab` of a nonarchimedean local field `K` is
normalized by arithmetic Frobenius: a uniformizer maps to the class of an arithmetic Frobenius
lift (`isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer`). Part of the literature, following
Deligne, uses the opposite normalization, in which a uniformizer maps to a *geometric* Frobenius,
the inverse of an arithmetic one. This file defines that map,

```text
geometricArtinMap K : Kˣ →* G_K^ab,    geometricArtinMap K x = (artinMap K x)⁻¹,
```

as the arithmetic map followed by inversion in the commutative group `G_K^ab`, so that both
normalizations are the same reciprocity map and no second one is constructed. Its properties are
those of `artinMap K` read through inversion.

* It is continuous (`continuous_geometricArtinMap`), has the same image as `artinMap K`
  (`range_geometricArtinMap`), hence dense image (`denseRange_geometricArtinMap`), and the same
  kernel (`ker_geometricArtinMap`); in characteristic zero it is injective
  (`injective_geometricArtinMap`).
* Its unramified coordinate is the inverse, in the multiplicatively written `ℤ̂`, of the
  normalized valuation (`unramifiedCoordinate_geometricArtinMap`). So every lift of the geometric
  Artin symbol of a uniformizer is the inverse of an arithmetic Frobenius lift
  (`isArithFrobeniusLift_inv_of_mk_eq_geometricArtinMap_uniformizer`), and every lift of the
  geometric Artin symbol of a unit lies in inertia
  (`mem_inertiaSubgroup_of_mk_eq_geometricArtinMap`).
* Its finite restrictions are the inverses of the finite local Artin maps
  (`geometricArtinMap_restrict`), it is functorial for the norm of a finite extension
  (`geometricArtinMap_norm`), and it is natural in the local field (`geometricArtinMap_congr`).

## Main definitions

* `TauCeti.ClassFieldTheory.geometricArtinMap K`: the absolute local Artin map normalized by
  geometric Frobenius.

## References

* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §1, for the two normalizations of the
  reciprocity map.
* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), §2.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The **geometric local Artin map** `Kˣ →* G_K^ab` of a nonarchimedean local field `K`: the
absolute local Artin map `artinMap K` followed by inversion in `G_K^ab`. It sends a uniformizer to
the class of a geometric Frobenius, the inverse of an arithmetic Frobenius lift
(`isArithFrobeniusLift_inv_of_mk_eq_geometricArtinMap_uniformizer`). -/
def geometricArtinMap : Kˣ →* Field.absoluteGaloisGroupAbelianization K :=
  (artinMap K)⁻¹

@[simp]
theorem geometricArtinMap_apply (x : Kˣ) : geometricArtinMap K x = (artinMap K x)⁻¹ := by
  rw [geometricArtinMap, MonoidHom.inv_apply]

/-- The geometric local Artin map is continuous. -/
theorem continuous_geometricArtinMap : Continuous (geometricArtinMap K) :=
  (continuous_artinMap K).inv

/-- **The geometric and arithmetic local Artin maps have the same image.** -/
theorem range_geometricArtinMap : (geometricArtinMap K).range = (artinMap K).range := by
  ext y
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x⁻¹, ?_⟩, fun ⟨x, hx⟩ ↦ ⟨x⁻¹, ?_⟩⟩ <;> simpa using hx

/-- The geometric local Artin map has dense image. -/
theorem denseRange_geometricArtinMap : DenseRange (geometricArtinMap K) := by
  rw [DenseRange, ← MonoidHom.coe_range, range_geometricArtinMap, MonoidHom.coe_range]
  exact denseRange_artinMap K

/-- **The geometric and arithmetic local Artin maps have the same kernel**, the intersection of the
norm subgroups (`ker_artinMap_eq_iInf`). -/
theorem ker_geometricArtinMap : (geometricArtinMap K).ker = (artinMap K).ker := by
  ext x
  simp

/-- The geometric local Artin map is injective in characteristic zero, in particular for a finite
extension of `ℚ_p`. -/
theorem injective_geometricArtinMap [CharZero K] : Function.Injective (geometricArtinMap K) :=
  inv_injective.comp (injective_artinMap K)

/-! ### The geometric Frobenius normalization -/

/-- **The unramified coordinate of the geometric local Artin map is inverse normalized
valuation**: the coordinate of the geometric Artin symbol of `x` is the inverse of the image of
`v_K(x)` in the multiplicatively written profinite integers. -/
theorem unramifiedCoordinate_geometricArtinMap (x : Kˣ) :
    unramifiedCoordinate K (geometricArtinMap K x) = (zHat.ofInt (normalizedValuation K x))⁻¹ := by
  simp

/-- Every lift of the geometric Artin symbol of a valuation-zero unit lies in inertia. -/
theorem mem_inertiaSubgroup_of_mk_eq_geometricArtinMap (u : Kˣ)
    (hu : ValuativeRel.valuation K (u : K) = 1) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = geometricArtinMap K u) :
    σ ∈ inertiaSubgroup K :=
  inv_mem_iff.1 <| mem_inertiaSubgroup_of_mk_eq_artinMap K u hu σ⁻¹ <| by
    rw [QuotientGroup.mk_inv, hσ, geometricArtinMap_apply, inv_inv]

/-- **Geometric Frobenius normalization.** Every lift of the geometric Artin symbol of a
uniformizer is a geometric Frobenius: its inverse is an arithmetic Frobenius lift. -/
theorem isArithFrobeniusLift_inv_of_mk_eq_geometricArtinMap_uniformizer {π : Kˣ}
    (hπ : IsUniformizer K π) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = geometricArtinMap K π) :
    IsArithFrobeniusLift K σ⁻¹ :=
  isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer K hπ σ⁻¹ <| by
    rw [QuotientGroup.mk_inv, hσ, geometricArtinMap_apply, inv_inv]

/-! ### Finite restrictions, norm functoriality and naturality -/

/-- **The finite restrictions of the geometric local Artin map are the inverses of the finite local
Artin maps.** If `σ ∈ Gal(AlgebraicClosure K/K)` represents the geometric Artin symbol of `x ∈ Kˣ`,
then for every finite Galois extension `L/K` embedded in the separable closure by `ι`, the Artin
symbol of `x` in `Gal(L/K)^ab` is the inverse of the class of the restriction of `σ` to `L`. -/
theorem geometricArtinMap_restrict (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (ι : L →ₐ[K] SeparableClosure K) (x : Kˣ) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = geometricArtinMap K x) :
    localArtinMap K L ι (Additive.ofMul x) =
      -Additive.ofMul
        (Abelianization.of (ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ))) := by
  rw [artinMap_restrict K L ι x σ⁻¹ (by rw [QuotientGroup.mk_inv, hσ, geometricArtinMap_apply,
    inv_inv]), map_inv, map_inv, map_inv, ofMul_inv]

section Norm

variable {K} (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L]
  (iota : L →ₐ[K] SeparableClosure K) [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

/-- **Norm functoriality of the geometric local Artin map.** Let `L/K` be a finite extension of
nonarchimedean local fields, embedded in `Kˢ` by `iota`. If `τ ∈ Gal(AlgebraicClosure L/L)`
represents the geometric Artin symbol of `x ∈ Lˣ`, then its image under
`absoluteGaloisGroupExtend K L iota : G_L → G_K` represents the geometric Artin symbol of
`N_{L/K} x`. -/
theorem geometricArtinMap_norm (x : Lˣ) (τ : Field.absoluteGaloisGroup L)
    (hτ : (τ : Field.absoluteGaloisGroupAbelianization L) = geometricArtinMap L x) :
    (absoluteGaloisGroupExtend K L iota τ : Field.absoluteGaloisGroupAbelianization K) =
      geometricArtinMap K (Algebra.normUnits K x) := by
  rw [geometricArtinMap_apply, ← artinMap_norm L iota x τ⁻¹ (by
    rw [QuotientGroup.mk_inv, hτ, geometricArtinMap_apply, inv_inv]), map_inv,
    QuotientGroup.mk_inv, inv_inv]

end Norm

section Congr

variable {K} {K' : Type} [Field K'] [ValuativeRel K'] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K']

/-- **The geometric local Artin map is natural in the local field.** Let `e : K ≃+* K'` be a
continuous isomorphism of nonarchimedean local fields and `e'` an extension of `e` to the algebraic
closures. If `σ ∈ G_K` represents the geometric Artin symbol of `x ∈ Kˣ`, then its conjugate
`σ' = e' ∘ σ ∘ e'⁻¹ ∈ G_{K'}` represents the geometric Artin symbol of `e x`. -/
theorem geometricArtinMap_congr (e : K ≃+* K') (he : Continuous e)
    (e' : AlgebraicClosure K ≃+* AlgebraicClosure K')
    (he' : ∀ c : K, e' (algebraMap K (AlgebraicClosure K) c) =
      algebraMap K' (AlgebraicClosure K') (e c))
    (x : Kˣ) (σ : Field.absoluteGaloisGroup K) (σ' : Field.absoluteGaloisGroup K')
    (hσσ' : ∀ y : AlgebraicClosure K, e' (σ.toRingEquiv y) = σ'.toRingEquiv (e' y))
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = geometricArtinMap K x) :
    (σ' : Field.absoluteGaloisGroupAbelianization K') =
      geometricArtinMap K' (Units.map e.toMonoidHom x) := by
  -- The inverses `σ⁻¹` and `σ'⁻¹` correspond under `e'` and represent the arithmetic symbols.
  have hinv : ∀ y : AlgebraicClosure K, e' (σ⁻¹.toRingEquiv y) = σ'⁻¹.toRingEquiv (e' y) :=
    fun y ↦ by
      apply σ'.toRingEquiv.injective
      -- In `Gal(AlgebraicClosure K/K)`, the inverse `σ⁻¹` is `σ.symm` by definition.
      have h₁ : σ.toRingEquiv (σ⁻¹.toRingEquiv y) = y := σ.apply_symm_apply y
      have h₂ : σ'.toRingEquiv (σ'⁻¹.toRingEquiv (e' y)) = e' y := σ'.apply_symm_apply (e' y)
      rw [← hσσ', h₁, h₂]
  rw [geometricArtinMap_apply, ← artinMap_congr e he e' he' x σ⁻¹ σ'⁻¹ hinv (by
    rw [QuotientGroup.mk_inv, hσ, geometricArtinMap_apply, inv_inv]), QuotientGroup.mk_inv,
    inv_inv]

end Congr

end TauCeti.ClassFieldTheory
