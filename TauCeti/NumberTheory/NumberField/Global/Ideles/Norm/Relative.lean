/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Norm
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Extension
public import TauCeti.RingTheory.Norm.Units

/-!
# The norm map of ideles and idele classes

Let `L / K` be an extension of number fields. The norm map of adeles `adeleNorm` is
multiplicative, so it restricts to a homomorphism of idele groups

`ideleNormMap K L : 𝕀_L →* 𝕀_K`.

Its coordinate at a place `v` of `K` is the product, over the places `w ∣ v` of `L`, of the local
norms `N_{L_w/K_v}` of the coordinates at `w`. It sends the principal idele of `x ∈ Lˣ` to the
principal idele of `N_{L/K}(x)`, so it descends to a homomorphism of idele class groups

`ideleClassNormMap K L : C_L →* C_K`.

Composed with extension of ideles from `K` to `L`, both maps are the `[L : K]`-th power map.

This is the norm in the direction `L → K`, opposite to the extension maps `ideleExtension` and
`ideleClassExtension`. It is not to be confused with the absolute idele norm `ideleNorm`, a
homomorphism to `ℝ≥0ˣ`.

## Main definitions

* `TauCeti.GlobalNumberFields.ideleNormMap`: the norm map `𝕀_L →* 𝕀_K` of idele groups.
* `TauCeti.GlobalNumberFields.ideleClassNormMap`: the induced norm map `C_L →* C_K` of idele
  class groups.

## Main results

* `TauCeti.GlobalNumberFields.ideleFiniteCoord_ideleNormMap`,
  `TauCeti.GlobalNumberFields.ideleInfiniteCoord_ideleNormMap`: the coordinate of the norm of an
  idele at a place `v` of `K` is the product of the local norms of its coordinates at the places
  above `v`.
* `TauCeti.GlobalNumberFields.ideleNormMap_unitEmbedding`: the norm of a principal idele is the
  principal idele of the global norm.
* `TauCeti.GlobalNumberFields.ideleNormMap_ideleExtension`,
  `TauCeti.GlobalNumberFields.ideleClassNormMap_ideleClassExtension`: the norm of an idele, or of
  an idele class, extended from `K` is its `[L : K]`-th power.
* `TauCeti.GlobalNumberFields.ideleNormMap_comp`,
  `TauCeti.GlobalNumberFields.ideleClassNormMap_comp`: norm maps compose in towers.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter VI, §2.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped AdicCompletionExtension NumberField.LiesOver

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The norm map of ideles** `N_{L/K} : 𝕀_L →* 𝕀_K`, the restriction of the multiplicative
norm map of adeles `adeleNorm` to units. -/
def ideleNormMap : IdeleGroup (𝓞 L) L →* IdeleGroup (𝓞 K) K :=
  Units.map (adeleNorm K L)

variable {K L} in
/-- The underlying adele of the norm of an idele is the adele norm of its underlying adele. -/
@[simp]
theorem coe_ideleNormMap (x : IdeleGroup (𝓞 L) L) :
    (ideleNormMap K L x : AdeleRing (𝓞 K) K) = adeleNorm K L x :=
  (rfl)

variable {K L} in
/-- **The finite coordinates of the idele norm.** The coordinate of `N_{L/K}(x)` at a finite place
`v` of `K` is the product over the places `w ∣ v` of `N_{L_w/K_v}(x_w)`. -/
@[simp]
theorem ideleFiniteCoord_ideleNormMap (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup (𝓞 L) L) :
    v.ideleFiniteCoord (ideleNormMap K L x) =
      ∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.normUnits (v.adicCompletion K) (w.1.ideleFiniteCoord x) := by
  apply Units.ext
  rw [← Units.coeHom_apply, ← Units.coeHom_apply, map_finprod _ (Set.toFinite _)]
  simp

variable {K L} in
/-- **The infinite coordinates of the idele norm.** The coordinate of `N_{L/K}(x)` at an infinite
place `v` of `K` is the product over the places `w ∣ v` of `N_{L_w/K_v}(x_w)`. -/
@[simp]
theorem ideleInfiniteCoord_ideleNormMap (v : InfinitePlace K) (x : IdeleGroup (𝓞 L) L) :
    v.ideleInfiniteCoord (ideleNormMap K L x) =
      ∏ᶠ w : {w : InfinitePlace L // w.LiesOver v},
        Algebra.normUnits v.Completion (w.1.ideleInfiniteCoord x) := by
  apply Units.ext
  rw [← Units.coeHom_apply, ← Units.coeHom_apply, map_finprod _ (Set.toFinite _)]
  simp

/-- The norm of a principal idele is the principal idele of the norm of `L / K`. -/
@[simp]
theorem ideleNormMap_unitEmbedding (x : Lˣ) :
    ideleNormMap K L (IdeleGroup.unitEmbedding (𝓞 L) L x) =
      IdeleGroup.unitEmbedding (𝓞 K) K (Algebra.normUnits K x) := by
  apply Units.ext
  simp [ideleNormMap]

/-- The norm of an idele extended from `K` is its `[L : K]`-th power. -/
@[simp]
theorem ideleNormMap_ideleExtension (x : IdeleGroup (𝓞 K) K) :
    ideleNormMap K L (ideleExtension K L x) = x ^ Module.finrank K L := by
  apply Units.ext
  simp [ideleNormMap]

/-- Norm maps of ideles compose in a tower of number fields. -/
@[simp]
theorem ideleNormMap_comp (M : Type*) [Field M] [NumberField M] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] :
    (ideleNormMap K L).comp (ideleNormMap L M) = ideleNormMap K M := by
  apply MonoidHom.ext
  intro x
  apply Units.ext
  simpa only [MonoidHom.comp_apply, coe_ideleNormMap] using
    DFunLike.congr_fun (adeleNorm_comp K L M) (x : AdeleRing (𝓞 M) M)

/-- The norm map of ideles sends principal ideles to principal ideles. -/
theorem principalSubgroup_le_comap_ideleNormMap :
    IdeleGroup.principalSubgroup (𝓞 L) L ≤
      (IdeleGroup.principalSubgroup (𝓞 K) K).comap (ideleNormMap K L) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨Algebra.normUnits K x, (ideleNormMap_unitEmbedding K L x).symm⟩

/-- **The norm map of idele classes** `N_{L/K} : C_L →* C_K`, induced by the norm map of ideles. -/
def ideleClassNormMap : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K :=
  QuotientGroup.map _ _ (ideleNormMap K L) (principalSubgroup_le_comap_ideleNormMap K L)

variable {K L} in
/-- On an idele class, the norm is represented by the norm of a representing idele. -/
@[simp]
theorem ideleClassNormMap_mk (x : IdeleGroup (𝓞 L) L) :
    ideleClassNormMap K L (x : IdeleClassGroup (𝓞 L) L) =
      (ideleNormMap K L x : IdeleClassGroup (𝓞 K) K) :=
  (rfl)

/-- The norm of an idele class extended from `K` is its `[L : K]`-th power. -/
@[simp]
theorem ideleClassNormMap_ideleClassExtension (x : IdeleClassGroup (𝓞 K) K) :
    ideleClassNormMap K L (ideleClassExtension K L x) = x ^ Module.finrank K L := by
  induction x using QuotientGroup.induction_on with
  | H x => simp [← QuotientGroup.mk_pow]

/-- Norm maps of idele classes compose in a tower of number fields. -/
@[simp]
theorem ideleClassNormMap_comp (M : Type*) [Field M] [NumberField M] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] :
    (ideleClassNormMap K L).comp (ideleClassNormMap L M) = ideleClassNormMap K M := by
  unfold ideleClassNormMap
  simpa only [ideleNormMap_comp] using
    QuotientGroup.map_comp_map (IdeleGroup.principalSubgroup (𝓞 M) M)
      (IdeleGroup.principalSubgroup (𝓞 L) L) (IdeleGroup.principalSubgroup (𝓞 K) K)
      (ideleNormMap L M) (ideleNormMap K L)
      (principalSubgroup_le_comap_ideleNormMap L M)
      (principalSubgroup_le_comap_ideleNormMap K L)

end TauCeti.GlobalNumberFields
