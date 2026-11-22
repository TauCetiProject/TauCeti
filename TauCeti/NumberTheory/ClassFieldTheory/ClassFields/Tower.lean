/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Norm.Transitivity
public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
public import TauCeti.NumberTheory.NumberField.Global.RayClass.PurelyFinite
import TauCeti.NumberTheory.NumberField.Global.RayClass.ClassNumber

/-!
# Relative Galois groups, degrees, and norms in ray class field towers

Let `K` be a number field and `𝔪 ∣ 𝔫` moduli of `K`. By `rayClassField_mono`, the ray class field
`rayClassField 𝔪` is a subextension of `rayClassField 𝔫`; in particular the Hilbert class field
`hilbertClassField K = rayClassField (Modulus.one K)` lies in every ray class field.

This file reads the relative Galois theory of `rayClassField 𝔫 / rayClassField 𝔪` and of
`rayClassField 𝔪 / hilbertClassField K` off tower compatibility of the global Artin map:

* By tower compatibility of `rayClassArtinMap` (`restrictNormalHom_rayClassArtinMap` in
  `Global.AdmissibleModulus.Reciprocity`), restriction
  `Gal(rayClassField 𝔫 / K) →* Gal(rayClassField 𝔪 / K)` corresponds under `rayClassArtinEquiv` to
  the transition map `classMap h : Cl_𝔫 →* Cl_𝔪` (`restrictNormalHom_rayClassArtinEquiv`), and
  restriction to `hilbertClassField K` corresponds to `rayClassToClassGroup 𝔪`
  (`restrictNormalHom_hilbertClassField_rayClassArtinEquiv`).
* Restricting scalars identifies `Gal(rayClassField 𝔫 / rayClassField 𝔪)` with the kernel of
  restriction to `rayClassField 𝔪`, yielding the canonical relative Artin isomorphisms
  `kerClassMapArtinEquiv : (classMap h).ker ≃* Gal(rayClassField 𝔫 / rayClassField 𝔪)` and
  `kerRayClassToClassGroupArtinEquiv : (rayClassToClassGroup 𝔪).ker ≃*
  Gal(rayClassField 𝔪 / hilbertClassField K)`. When `𝔪.infinitePart = ∅`, composing with
  `residueUnitsQuotientEquivKerRayClassToClassGroup` gives the residue-unit quotient presentation
  `residueUnitsQuotientArtinEquiv` of `Gal(rayClassField 𝔪 / hilbertClassField K)`.
* Consequently `[rayClassField 𝔫 : rayClassField 𝔪] = #(classMap h).ker`
  (`finrank_rayClassField_rayClassField`), `[rayClassField 𝔪 : hilbertClassField K]` satisfies the
  relative ray class degree formula (`finrank_hilbertClassField_rayClassField_mul_index`),
  degrees multiply cleanly across towers through `hilbertClassField K`
  (`classNumber_mul_finrank_hilbertClassField_rayClassField`,
  `finrank_hilbertClassField_mul_finrank_rayClassField`),
  and the relative field norm is the product of Galois conjugates indexed by these kernels or
  residue-unit quotients (`algebraMap_norm_rayClassField`,
  `algebraMap_norm_hilbertClassField_rayClassField`,
  `algebraMap_norm_hilbertClassField_of_infinitePart_eq_empty`).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§5–7.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2.
-/

public noncomputable section

open IsDedekindDomain NumberField TauCeti.GlobalNumberFields
open scoped nonZeroDivisors

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

/-! ### Restriction compatibility between ray class fields -/

/-- **Restriction between ray class fields is the transition map on ray class groups**: for
`h : 𝔪 ∣ 𝔫`, restricting `rayClassArtinEquiv 𝔫 x` to `rayClassField 𝔪` gives
`rayClassArtinEquiv 𝔪 (classMap h x)`. -/
theorem restrictNormalHom_rayClassArtinEquiv {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫)
    [Algebra (rayClassField 𝔪) (rayClassField 𝔫)]
    [IsScalarTower K (rayClassField 𝔪) (rayClassField 𝔫)] (x : RayClassGroup 𝔫) :
    AlgEquiv.restrictNormalHom (rayClassField 𝔪) (rayClassArtinEquiv 𝔫 x) =
      rayClassArtinEquiv 𝔪 (classMap h x) := by
  rw [rayClassArtinEquiv_apply, rayClassArtinEquiv_apply]
  exact restrictNormalHom_rayClassArtinMap (rayClassField 𝔪) h
    (isAdmissibleModulus_rayClassField 𝔪) (isAdmissibleModulus_rayClassField 𝔫) x

/-- **Restriction from a ray class field to the Hilbert class field** sends the Artin symbol of a
ray class `x` to the Hilbert-class Artin symbol of its ordinary ideal class
`rayClassToClassGroup 𝔪 x`. -/
theorem restrictNormalHom_hilbertClassField_rayClassArtinEquiv (𝔪 : Modulus K)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)] (x : RayClassGroup 𝔪) :
    AlgEquiv.restrictNormalHom (hilbertClassField K) (rayClassArtinEquiv 𝔪 x) =
      hilbertClassArtinEquiv K (rayClassToClassGroup 𝔪 x) := by
  rw [restrictNormalHom_rayClassArtinEquiv (Modulus.one_dvd 𝔪),
    rayClassToClassGroup_eq_oneEquivClassGroup_comp_classMap, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, hilbertClassArtinEquiv_oneEquivClassGroup]

/-! ### Relative Galois groups in ray class field towers -/

/-- Under `rayClassArtinEquiv 𝔫`, the kernel of `classMap h` maps onto the range of scalar
restriction `Gal(rayClassField 𝔫 / rayClassField 𝔪) →* Gal(rayClassField 𝔫 / K)`. -/
private theorem map_ker_classMap_rayClassArtinEquiv {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫)
    [Algebra (rayClassField 𝔪) (rayClassField 𝔫)]
    [IsScalarTower K (rayClassField 𝔪) (rayClassField 𝔫)] :
    (classMap h).ker.map (rayClassArtinEquiv 𝔫 : RayClassGroup 𝔫 →* Gal(rayClassField 𝔫/K)) =
      (AlgEquiv.restrictScalarsHom (S := rayClassField 𝔪) (A := rayClassField 𝔫) K).range := by
  rw [AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K (rayClassField 𝔪)
    (rayClassField 𝔫)]
  ext σ
  obtain ⟨x, rfl⟩ := (rayClassArtinEquiv 𝔫).surjective σ
  rw [Subgroup.mem_map, MonoidHom.mem_ker, restrictNormalHom_rayClassArtinEquiv h]
  refine ⟨fun ⟨y, hy, hyx⟩ ↦ ?_, fun hx ↦ ⟨x, ?_, rfl⟩⟩
  · obtain rfl := (rayClassArtinEquiv 𝔫).injective hyx
    simp [MonoidHom.mem_ker.mp hy]
  · exact MonoidHom.mem_ker.mpr ((rayClassArtinEquiv 𝔪).injective (by simpa using hx))

/-- **Relative reciprocity for a pair of ray class fields**: for `h : 𝔪 ∣ 𝔫`, the Artin map of
`rayClassField 𝔫` identifies `(classMap h).ker` with the relative Galois group
`Gal(rayClassField 𝔫 / rayClassField 𝔪)`. -/
def kerClassMapArtinEquiv {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫)
    [Algebra (rayClassField 𝔪) (rayClassField 𝔫)]
    [IsScalarTower K (rayClassField 𝔪) (rayClassField 𝔫)] :
    (classMap h).ker ≃* Gal(rayClassField 𝔫/rayClassField 𝔪) :=
  (((rayClassArtinEquiv 𝔫).subgroupMap (classMap h).ker).trans
    (MulEquiv.subgroupCongr (map_ker_classMap_rayClassArtinEquiv h))).trans
    (MonoidHom.ofInjective
      (AlgEquiv.restrictScalarsHom_injective
        (S := rayClassField 𝔪) (A := rayClassField 𝔫) K)).symm

/-- Restricting scalars of `kerClassMapArtinEquiv h x` to `K` recovers `rayClassArtinEquiv 𝔫 x`. -/
@[simp]
theorem restrictScalars_kerClassMapArtinEquiv {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫)
    [Algebra (rayClassField 𝔪) (rayClassField 𝔫)]
    [IsScalarTower K (rayClassField 𝔪) (rayClassField 𝔫)] (x : (classMap h).ker) :
    (kerClassMapArtinEquiv h x).restrictScalars K = rayClassArtinEquiv 𝔫 x := by
  rw [← AlgEquiv.restrictScalarsHom_apply K]; simp [kerClassMapArtinEquiv]

/-- Pointwise evaluation of `kerClassMapArtinEquiv` agrees with `rayClassArtinEquiv 𝔫`. -/
@[simp]
theorem kerClassMapArtinEquiv_apply {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫)
    [Algebra (rayClassField 𝔪) (rayClassField 𝔫)]
    [IsScalarTower K (rayClassField 𝔪) (rayClassField 𝔫)] (x : (classMap h).ker)
    (y : rayClassField 𝔫) : kerClassMapArtinEquiv h x y = rayClassArtinEquiv 𝔫 x y := by
  rw [← AlgEquiv.restrictScalars_apply K, restrictScalars_kerClassMapArtinEquiv]

/-- The kernel of transition to the trivial modulus is the kernel of `rayClassToClassGroup`. -/
private theorem ker_rayClassToClassGroup_eq_ker_classMap_one_dvd (𝔪 : Modulus K) :
    (rayClassToClassGroup 𝔪).ker = (classMap (Modulus.one_dvd 𝔪)).ker := by
  ext x; simp [rayClassToClassGroup_eq_oneEquivClassGroup_comp_classMap]

/-- **Relative reciprocity over the Hilbert class field**: the Artin map of `rayClassField 𝔪`
identifies `(rayClassToClassGroup 𝔪).ker` with `Gal(rayClassField 𝔪 / hilbertClassField K)`. -/
def kerRayClassToClassGroupArtinEquiv (𝔪 : Modulus K)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)] :
    (rayClassToClassGroup 𝔪).ker ≃* Gal(rayClassField 𝔪/hilbertClassField K) :=
  (MulEquiv.subgroupCongr (ker_rayClassToClassGroup_eq_ker_classMap_one_dvd 𝔪)).trans
    (kerClassMapArtinEquiv (Modulus.one_dvd 𝔪))

/-- Restricting scalars of `kerRayClassToClassGroupArtinEquiv 𝔪 x` to `K` recovers
`rayClassArtinEquiv 𝔪 x`. -/
@[simp]
theorem restrictScalars_kerRayClassToClassGroupArtinEquiv (𝔪 : Modulus K)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)]
    (x : (rayClassToClassGroup 𝔪).ker) :
    (kerRayClassToClassGroupArtinEquiv 𝔪 x).restrictScalars K = rayClassArtinEquiv 𝔪 x := by
  rw [kerRayClassToClassGroupArtinEquiv, MulEquiv.trans_apply,
    restrictScalars_kerClassMapArtinEquiv, MulEquiv.subgroupCongr_apply]

/-- Pointwise evaluation of `kerRayClassToClassGroupArtinEquiv` agrees with
`rayClassArtinEquiv 𝔪`. -/
@[simp]
theorem kerRayClassToClassGroupArtinEquiv_apply (𝔪 : Modulus K)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)]
    (x : (rayClassToClassGroup 𝔪).ker) (y : rayClassField 𝔪) :
    kerRayClassToClassGroupArtinEquiv 𝔪 x y = rayClassArtinEquiv 𝔪 x y := by
  rw [← AlgEquiv.restrictScalars_apply K, restrictScalars_kerRayClassToClassGroupArtinEquiv]

/-- **Residue-unit reciprocity over the Hilbert class field**: when `𝔪.infinitePart = ∅`, the
quotient of `(𝓞 K ⧸ 𝔪.finitePart)ˣ` by the image of `(𝓞 K)ˣ` maps isomorphically onto
`Gal(rayClassField 𝔪 / hilbertClassField K)`. -/
def residueUnitsQuotientArtinEquiv {𝔪 : Modulus K} (h : 𝔪.infinitePart = ∅)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)] :
    (𝓞 K ⧸ 𝔪.finitePart)ˣ ⧸
        (Units.map (Ideal.Quotient.mk 𝔪.finitePart : 𝓞 K →* 𝓞 K ⧸ 𝔪.finitePart)).range ≃*
      Gal(rayClassField 𝔪/hilbertClassField K) :=
  (residueUnitsQuotientEquivKerRayClassToClassGroup h).trans
    (kerRayClassToClassGroupArtinEquiv 𝔪)

/-- Restricting scalars of `residueUnitsQuotientArtinEquiv h u` to `K` gives
`rayClassArtinEquiv 𝔪 (residueRayClass 𝔪 u)`. -/
@[simp]
theorem restrictScalars_residueUnitsQuotientArtinEquiv_mk {𝔪 : Modulus K}
    (h : 𝔪.infinitePart = ∅)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)] (u : (𝓞 K ⧸ 𝔪.finitePart)ˣ) :
    (residueUnitsQuotientArtinEquiv h u).restrictScalars K =
      rayClassArtinEquiv 𝔪 (residueRayClass 𝔪 u) := by
  rw [residueUnitsQuotientArtinEquiv, MulEquiv.trans_apply,
    restrictScalars_kerRayClassToClassGroupArtinEquiv,
    coe_residueUnitsQuotientEquivKerRayClassToClassGroup_mk]

/-- Pointwise evaluation of `residueUnitsQuotientArtinEquiv` on the coset of `u` agrees with
`rayClassArtinEquiv 𝔪 (residueRayClass 𝔪 u)`. -/
@[simp]
theorem residueUnitsQuotientArtinEquiv_mk_apply {𝔪 : Modulus K} (h : 𝔪.infinitePart = ∅)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)]
    (u : (𝓞 K ⧸ 𝔪.finitePart)ˣ) (y : rayClassField 𝔪) :
    residueUnitsQuotientArtinEquiv h u y = rayClassArtinEquiv 𝔪 (residueRayClass 𝔪 u) y := by
  rw [← AlgEquiv.restrictScalars_apply K, restrictScalars_residueUnitsQuotientArtinEquiv_mk]

/-! ### Relative degrees and Galois norms -/

section RelativeDegreesAndNorms

private theorem isGalois_rayClassField_of_tower (M : Type*) [Field M] [Algebra K M]
    {𝔫 : Modulus K} [Algebra M (rayClassField 𝔫)] [IsScalarTower K M (rayClassField 𝔫)] :
    IsGalois M (rayClassField 𝔫) :=
  IsGalois.tower_top_of_isGalois K M (rayClassField 𝔫)

private theorem finiteDimensional_rayClassField_of_tower (M : Type*) [Field M] [Algebra K M]
    {𝔫 : Modulus K} [Algebra M (rayClassField 𝔫)] [IsScalarTower K M (rayClassField 𝔫)] :
    FiniteDimensional M (rayClassField 𝔫) :=
  FiniteDimensional.right K M (rayClassField 𝔫)

private theorem finrank_mul_finrank_rayClassField (M : Type*) [Field M] [Algebra K M]
    (𝔫 : Modulus K) [Algebra M (rayClassField 𝔫)] [IsScalarTower K M (rayClassField 𝔫)] :
    Module.finrank K M * Module.finrank M (rayClassField 𝔫) =
      Module.finrank K (rayClassField 𝔫) := by
  have : Module.Free K M := .of_divisionRing K M
  have : Module.Free M (rayClassField 𝔫) := .of_divisionRing M (rayClassField 𝔫)
  exact Module.finrank_mul_finrank K M (rayClassField 𝔫)

/-- **Relative degree of ray class fields**: for `h : 𝔪 ∣ 𝔫`,
`[rayClassField 𝔫 : rayClassField 𝔪] = #(classMap h).ker`. -/
theorem finrank_rayClassField_rayClassField {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫)
    [Algebra (rayClassField 𝔪) (rayClassField 𝔫)]
    [IsScalarTower K (rayClassField 𝔪) (rayClassField 𝔫)] :
    Module.finrank (rayClassField 𝔪) (rayClassField 𝔫) = Nat.card (classMap h).ker := by
  have := isGalois_rayClassField_of_tower (K := K) (rayClassField 𝔪) (𝔫 := 𝔫)
  have := finiteDimensional_rayClassField_of_tower (K := K) (rayClassField 𝔪) (𝔫 := 𝔫)
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr (kerClassMapArtinEquiv h).symm.toEquiv]

/-- Whenever `rayClassField 𝔫` is a `K`-tower over `rayClassField 𝔪`,
`[rayClassField 𝔫 : rayClassField 𝔪] * #Cl_𝔪 = #Cl_𝔫`. -/
theorem finrank_rayClassField_mul_card (𝔪 𝔫 : Modulus K)
    [Algebra (rayClassField 𝔪) (rayClassField 𝔫)]
    [IsScalarTower K (rayClassField 𝔪) (rayClassField 𝔫)] :
    Module.finrank (rayClassField 𝔪) (rayClassField 𝔫) * Nat.card (RayClassGroup 𝔪) =
      Nat.card (RayClassGroup 𝔫) := by
  rw [← finrank_rayClassField 𝔪, ← finrank_rayClassField 𝔫, mul_comm,
    finrank_mul_finrank_rayClassField (rayClassField 𝔪) 𝔫]

/-- **Degree of a ray class field over the Hilbert class field**:
`[rayClassField 𝔪 : hilbertClassField K] = #(rayClassToClassGroup 𝔪).ker`. -/
theorem finrank_hilbertClassField_rayClassField (𝔪 : Modulus K)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)] :
    Module.finrank (hilbertClassField K) (rayClassField 𝔪) =
      Nat.card (rayClassToClassGroup 𝔪).ker := by
  rw [finrank_rayClassField_rayClassField (Modulus.one_dvd 𝔪),
    ker_rayClassToClassGroup_eq_ker_classMap_one_dvd]

/-- The degree of a ray class field over `K` factors through the Hilbert class field:
`classNumber K * [rayClassField 𝔪 : hilbertClassField K] = [rayClassField 𝔪 : K]`. -/
theorem classNumber_mul_finrank_hilbertClassField_rayClassField (𝔪 : Modulus K)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)] :
    classNumber K * Module.finrank (hilbertClassField K) (rayClassField 𝔪) =
      Module.finrank K (rayClassField 𝔪) := by
  rw [← finrank_hilbertClassField K, finrank_mul_finrank_rayClassField (hilbertClassField K) 𝔪]

/-- Degree multiplicativity over the Hilbert class field: for any `K`-tower
`hilbertClassField K ⊆ rayClassField 𝔪 ⊆ rayClassField 𝔫`,
`[rayClassField 𝔪 : hilbertClassField K] * [rayClassField 𝔫 : rayClassField 𝔪] =
[rayClassField 𝔫 : hilbertClassField K]`. -/
theorem finrank_hilbertClassField_mul_finrank_rayClassField (𝔪 𝔫 : Modulus K)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)]
    [Algebra (hilbertClassField K) (rayClassField 𝔫)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔫)]
    [Algebra (rayClassField 𝔪) (rayClassField 𝔫)]
    [IsScalarTower K (rayClassField 𝔪) (rayClassField 𝔫)] :
    Module.finrank (hilbertClassField K) (rayClassField 𝔪) *
        Module.finrank (rayClassField 𝔪) (rayClassField 𝔫) =
      Module.finrank (hilbertClassField K) (rayClassField 𝔫) := by
  have hmul := finrank_mul_finrank_rayClassField (K := K) (rayClassField 𝔪) 𝔫
  rw [← classNumber_mul_finrank_hilbertClassField_rayClassField 𝔪,
    ← classNumber_mul_finrank_hilbertClassField_rayClassField 𝔫, mul_assoc] at hmul
  exact Nat.mul_left_cancel (NumberField.classNumber_pos K) hmul

/-- **Relative ray class degree formula** over the Hilbert class field:
`[rayClassField 𝔪 : hilbertClassField K] * [(𝓞 K)ˣ : unitsCongruenceSubgroup 𝔪] =
#(𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ #𝔪.infinitePart`. -/
theorem finrank_hilbertClassField_rayClassField_mul_index (𝔪 : Modulus K)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)] :
    Module.finrank (hilbertClassField K) (rayClassField 𝔪) * (unitsCongruenceSubgroup 𝔪).index =
      Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ 𝔪.infinitePart.card := by
  rw [finrank_hilbertClassField_rayClassField, card_ker_rayClassToClassGroup_mul_index]

/-- Purely finite specialization of `finrank_hilbertClassField_rayClassField_mul_index`. -/
theorem finrank_hilbertClassField_rayClassField_mul_index_of_infinitePart_eq_empty
    {𝔪 : Modulus K} (h : 𝔪.infinitePart = ∅)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)] :
    Module.finrank (hilbertClassField K) (rayClassField 𝔪) * (unitsCongruenceSubgroup 𝔪).index =
      Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ := by
  rw [finrank_hilbertClassField_rayClassField,
    card_ker_rayClassToClassGroup_mul_index_of_infinitePart_eq_empty h]

/-- **Norm in a ray class field tower as a product over `(classMap h).ker`.** -/
theorem algebraMap_norm_rayClassField {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫)
    [Algebra (rayClassField 𝔪) (rayClassField 𝔫)]
    [IsScalarTower K (rayClassField 𝔪) (rayClassField 𝔫)] (y : rayClassField 𝔫) :
    algebraMap (rayClassField 𝔪) (rayClassField 𝔫) (Algebra.norm (rayClassField 𝔪) y) =
      ∏ᶠ x : (classMap h).ker, rayClassArtinEquiv 𝔫 x y := by
  classical
  have := isGalois_rayClassField_of_tower (K := K) (rayClassField 𝔪) (𝔫 := 𝔫)
  have := finiteDimensional_rayClassField_of_tower (K := K) (rayClassField 𝔪) (𝔫 := 𝔫)
  rw [Algebra.norm_eq_prod_automorphisms, ← finprod_eq_prod_of_fintype,
    ← finprod_comp_equiv (kerClassMapArtinEquiv h).toEquiv]
  simp

/-- **Norm from a ray class field to the Hilbert class field** as a product over
`(rayClassToClassGroup 𝔪).ker`. -/
theorem algebraMap_norm_hilbertClassField_rayClassField (𝔪 : Modulus K)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)] (y : rayClassField 𝔪) :
    algebraMap (hilbertClassField K) (rayClassField 𝔪) (Algebra.norm (hilbertClassField K) y) =
      ∏ᶠ x : (rayClassToClassGroup 𝔪).ker, rayClassArtinEquiv 𝔪 x y := by
  rw [algebraMap_norm_rayClassField (Modulus.one_dvd 𝔪),
    ← finprod_comp_equiv (MulEquiv.subgroupCongr
      (ker_rayClassToClassGroup_eq_ker_classMap_one_dvd 𝔪)).toEquiv]
  simp

/-- **Norm from a purely finite ray class field to the Hilbert class field** as a product over the
quotient of `(𝓞 K ⧸ 𝔪.finitePart)ˣ` by the image of `(𝓞 K)ˣ`. -/
theorem algebraMap_norm_hilbertClassField_of_infinitePart_eq_empty {𝔪 : Modulus K}
    (h : 𝔪.infinitePart = ∅)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)] (y : rayClassField 𝔪) :
    algebraMap (hilbertClassField K) (rayClassField 𝔪) (Algebra.norm (hilbertClassField K) y) =
      ∏ᶠ g : (𝓞 K ⧸ 𝔪.finitePart)ˣ ⧸
        (Units.map (Ideal.Quotient.mk 𝔪.finitePart : 𝓞 K →* 𝓞 K ⧸ 𝔪.finitePart)).range,
          residueUnitsQuotientArtinEquiv h g y := by
  rw [algebraMap_norm_hilbertClassField_rayClassField 𝔪,
    ← finprod_comp_equiv (residueUnitsQuotientEquivKerRayClassToClassGroup h).toEquiv]
  simp [residueUnitsQuotientArtinEquiv]

end RelativeDegreesAndNorms

end TauCeti.ClassFieldTheory
