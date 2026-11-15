/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Norm.Transitivity
public import TauCeti.FieldTheory.Galois.Restriction
public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
public import TauCeti.NumberTheory.NumberField.Global.RayClass.PurelyFinite

/-!
# Relative Galois groups, degrees, and norms in ray class field towers

Let `K` be a number field and `𝔪 ∣ 𝔫` moduli of `K`. By `rayClassField_mono`, the ray class field
`rayClassField 𝔪` is a subextension of `rayClassField 𝔫`; in particular the Hilbert class field
`hilbertClassField K = rayClassField (Modulus.one K)` lies in every ray class field.

This file reads the relative Galois theory of `rayClassField 𝔫 / rayClassField 𝔪` and of
`rayClassField 𝔪 / hilbertClassField K` off tower compatibility of the global Artin map:

* For any `K`-embedding `f : M →ₐ[K] L` between finite abelian extensions of `K`, restricting the
  Artin symbol `ideleClassArtinMap K L c` along `f` recovers `ideleClassArtinMap K M c`
  (`restrictNormalHom_ideleClassArtinMap`). Passing to ray class groups shows that restriction
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
  relative ray class degree formula (`finrank_hilbertClassField_rayClassField_mul_index`), and the
  relative field norm is the product of Galois conjugates indexed by these kernels or residue-unit
  quotients (`algebraMap_norm_rayClassField`, `algebraMap_norm_hilbertClassField_rayClassField`,
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

/-! ### Tower compatibility of abelian Artin maps -/

open scoped IsMulCommutative in
/-- **Tower compatibility of the global Artin map of abelian extensions**: for any `K`-embedding
`f : M →ₐ[K] L` of finite abelian extensions of `K`, restricting the Artin symbol in `Gal(L/K)`
along `f` yields the Artin symbol in `Gal(M/K)`. -/
theorem restrictNormalHom_ideleClassArtinMap
    {M L : Type*} [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M]
    [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (f : M →ₐ[K] L) (c : IdeleClassGroup (𝓞 K) K) :
    f.restrictNormalHom (ideleClassArtinMap K L c) = ideleClassArtinMap K M c := by
  apply (Group.Abelianization.equivOfComm (H := Gal(M/K))).injective
  change Group.Abelianization.of (f.restrictNormalHom (ideleClassArtinMap K L c)) =
    Group.Abelianization.of (ideleClassArtinMap K M c)
  have h := DFunLike.congr_fun
    (globalArtinMap_comp K L f IsSepClosed.lift) (Additive.ofMul c)
  have hL := of_ideleClassArtinMap K L IsSepClosed.lift c
  have hM := of_ideleClassArtinMap K M (IsSepClosed.lift.comp f) c
  have h' : Group.Abelianization.map f.restrictNormalHom
      (globalArtinMap K L IsSepClosed.lift (.ofMul c)).toMul =
      (globalArtinMap K M (IsSepClosed.lift.comp f) (.ofMul c)).toMul :=
    congrArg Additive.toMul h
  rw [← hL, Group.Abelianization.map_of, ← hM] at h'
  exact h'

/-- Scalar-tower form of `restrictNormalHom_ideleClassArtinMap`. -/
@[simp]
theorem restrictNormal_ideleClassArtinMap
    (M : Type*) {L : Type*} [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M]
    [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    [Algebra M L] [IsScalarTower K M L] (c : IdeleClassGroup (𝓞 K) K) :
    AlgEquiv.restrictNormalHom M (ideleClassArtinMap K L c) = ideleClassArtinMap K M c := by
  rw [← AlgHom.restrictNormalHom_toAlgHom (F := K), restrictNormalHom_ideleClassArtinMap]

/-- **Tower compatibility of ray-class Artin maps**: for `h : 𝔪 ∣ 𝔫` and admissible extensions
`f : M →ₐ[K] L`, restriction along `f` intertwines `rayClassArtinMap` with `classMap h`. -/
theorem restrictNormalHom_rayClassArtinMap
    {M L : Type} [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M]
    [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) (hM : IsAdmissibleModulus K M 𝔪)
    (hL : IsAdmissibleModulus K L 𝔫) (f : M →ₐ[K] L) (x : RayClassGroup 𝔫) :
    f.restrictNormalHom (rayClassArtinMap 𝔫 hL x) = rayClassArtinMap 𝔪 hM (classMap h x) := by
  obtain ⟨c, rfl⟩ := rayClassQuotient_surjective 𝔫 x
  rw [rayClassArtinMap_rayClassQuotient, classMap_rayClassQuotient,
    rayClassArtinMap_rayClassQuotient, restrictNormalHom_ideleClassArtinMap]

/-- Scalar-tower form of `restrictNormalHom_rayClassArtinMap`. -/
theorem restrictNormal_rayClassArtinMap
    (M : Type) {L : Type} [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M]
    [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    [Algebra M L] [IsScalarTower K M L] {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫)
    (hM : IsAdmissibleModulus K M 𝔪) (hL : IsAdmissibleModulus K L 𝔫) (x : RayClassGroup 𝔫) :
    AlgEquiv.restrictNormalHom M (rayClassArtinMap 𝔫 hL x) =
      rayClassArtinMap 𝔪 hM (classMap h x) := by
  rw [← AlgHom.restrictNormalHom_toAlgHom (F := K), restrictNormalHom_rayClassArtinMap h hM hL]

/-- **Restriction between ray class fields is the transition map on ray class groups**: for
`h : 𝔪 ∣ 𝔫`, restricting `rayClassArtinEquiv 𝔫 x` to `rayClassField 𝔪` gives
`rayClassArtinEquiv 𝔪 (classMap h x)`. -/
theorem restrictNormalHom_rayClassArtinEquiv {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫)
    [Algebra (rayClassField 𝔪) (rayClassField 𝔫)]
    [IsScalarTower K (rayClassField 𝔪) (rayClassField 𝔫)] (x : RayClassGroup 𝔫) :
    AlgEquiv.restrictNormalHom (rayClassField 𝔪) (rayClassArtinEquiv 𝔫 x) =
      rayClassArtinEquiv 𝔪 (classMap h x) := by
  rw [rayClassArtinEquiv_apply, rayClassArtinEquiv_apply]
  exact restrictNormal_rayClassArtinMap (rayClassField 𝔪) h
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
  change AlgEquiv.restrictScalarsHom K (kerClassMapArtinEquiv h x) = rayClassArtinEquiv 𝔫 x
  simp [kerClassMapArtinEquiv]

/-- Pointwise evaluation of `kerClassMapArtinEquiv` agrees with `rayClassArtinEquiv 𝔫`. -/
@[simp]
theorem kerClassMapArtinEquiv_apply {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫)
    [Algebra (rayClassField 𝔪) (rayClassField 𝔫)]
    [IsScalarTower K (rayClassField 𝔪) (rayClassField 𝔫)] (x : (classMap h).ker)
    (y : rayClassField 𝔫) :
    kerClassMapArtinEquiv h x y = rayClassArtinEquiv 𝔫 x y := by
  rw [← AlgEquiv.restrictScalars_apply K, restrictScalars_kerClassMapArtinEquiv]

/-- The kernel of transition to the trivial modulus is the kernel of `rayClassToClassGroup`. -/
private theorem ker_rayClassToClassGroup_eq_ker_classMap_one_dvd (𝔪 : Modulus K) :
    (rayClassToClassGroup 𝔪).ker = (classMap (Modulus.one_dvd 𝔪)).ker := by
  ext x
  simp [rayClassToClassGroup_eq_oneEquivClassGroup_comp_classMap]

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

/-- **Relative degree of ray class fields**: for `h : 𝔪 ∣ 𝔫`,
`[rayClassField 𝔫 : rayClassField 𝔪] = #(classMap h).ker`. -/
theorem finrank_rayClassField_rayClassField {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫)
    [Algebra (rayClassField 𝔪) (rayClassField 𝔫)]
    [IsScalarTower K (rayClassField 𝔪) (rayClassField 𝔫)] :
    Module.finrank (rayClassField 𝔪) (rayClassField 𝔫) = Nat.card (classMap h).ker := by
  have : IsGalois (rayClassField 𝔪) (rayClassField 𝔫) :=
    IsGalois.tower_top_of_isGalois K (rayClassField 𝔪) (rayClassField 𝔫)
  have : FiniteDimensional (rayClassField 𝔪) (rayClassField 𝔫) :=
    FiniteDimensional.right K (rayClassField 𝔪) (rayClassField 𝔫)
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr (kerClassMapArtinEquiv h).symm.toEquiv]

/-- Whenever `rayClassField 𝔫` is a `K`-tower over `rayClassField 𝔪`,
`[rayClassField 𝔫 : rayClassField 𝔪] * #Cl_𝔪 = #Cl_𝔫`. -/
theorem finrank_rayClassField_mul_card (𝔪 𝔫 : Modulus K)
    [Algebra (rayClassField 𝔪) (rayClassField 𝔫)]
    [IsScalarTower K (rayClassField 𝔪) (rayClassField 𝔫)] :
    Module.finrank (rayClassField 𝔪) (rayClassField 𝔫) * Nat.card (RayClassGroup 𝔪) =
      Nat.card (RayClassGroup 𝔫) := by
  have : Module.Free K (rayClassField 𝔪) := .of_divisionRing K (rayClassField 𝔪)
  have : Module.Free (rayClassField 𝔪) (rayClassField 𝔫) :=
    .of_divisionRing (rayClassField 𝔪) (rayClassField 𝔫)
  rw [← finrank_rayClassField 𝔪, ← finrank_rayClassField 𝔫, mul_comm,
    Module.finrank_mul_finrank K (rayClassField 𝔪) (rayClassField 𝔫)]

/-- **Degree of a ray class field over the Hilbert class field**:
`[rayClassField 𝔪 : hilbertClassField K] = #(rayClassToClassGroup 𝔪).ker`. -/
theorem finrank_hilbertClassField_rayClassField (𝔪 : Modulus K)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)] :
    Module.finrank (hilbertClassField K) (rayClassField 𝔪) =
      Nat.card (rayClassToClassGroup 𝔪).ker := by
  rw [finrank_rayClassField_rayClassField (Modulus.one_dvd 𝔪),
    ker_rayClassToClassGroup_eq_ker_classMap_one_dvd]

/-- **Relative ray class degree formula** over the Hilbert class field:
`[rayClassField 𝔪 : hilbertClassField K] * [(𝓞 K)ˣ : unitsCongruenceSubgroup 𝔪] =
#(𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ #𝔪.infinitePart`. -/
theorem finrank_hilbertClassField_rayClassField_mul_index (𝔪 : Modulus K)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)] :
    Module.finrank (hilbertClassField K) (rayClassField 𝔪) *
        (unitsCongruenceSubgroup 𝔪).index =
      Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ 𝔪.infinitePart.card := by
  rw [finrank_hilbertClassField_rayClassField, card_ker_rayClassToClassGroup_mul_index]

/-- Purely finite specialization of `finrank_hilbertClassField_rayClassField_mul_index`. -/
theorem finrank_hilbertClassField_rayClassField_mul_index_of_infinitePart_eq_empty
    {𝔪 : Modulus K} (h : 𝔪.infinitePart = ∅)
    [Algebra (hilbertClassField K) (rayClassField 𝔪)]
    [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)] :
    Module.finrank (hilbertClassField K) (rayClassField 𝔪) *
        (unitsCongruenceSubgroup 𝔪).index =
      Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ := by
  simpa [h] using finrank_hilbertClassField_rayClassField_mul_index 𝔪

/-- **Norm in a ray class field tower as a product over `(classMap h).ker`.** -/
theorem algebraMap_norm_rayClassField {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫)
    [Algebra (rayClassField 𝔪) (rayClassField 𝔫)]
    [IsScalarTower K (rayClassField 𝔪) (rayClassField 𝔫)] (y : rayClassField 𝔫) :
    algebraMap (rayClassField 𝔪) (rayClassField 𝔫) (Algebra.norm (rayClassField 𝔪) y) =
      ∏ᶠ x : (classMap h).ker, rayClassArtinEquiv 𝔫 x y := by
  classical
  have : IsGalois (rayClassField 𝔪) (rayClassField 𝔫) :=
    IsGalois.tower_top_of_isGalois K (rayClassField 𝔪) (rayClassField 𝔫)
  have : FiniteDimensional (rayClassField 𝔪) (rayClassField 𝔫) :=
    FiniteDimensional.right K (rayClassField 𝔪) (rayClassField 𝔫)
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
  classical
  have : IsGalois (hilbertClassField K) (rayClassField 𝔪) :=
    IsGalois.tower_top_of_isGalois K (hilbertClassField K) (rayClassField 𝔪)
  have : FiniteDimensional (hilbertClassField K) (rayClassField 𝔪) :=
    FiniteDimensional.right K (hilbertClassField K) (rayClassField 𝔪)
  rw [Algebra.norm_eq_prod_automorphisms, ← finprod_eq_prod_of_fintype,
    ← finprod_comp_equiv (kerRayClassToClassGroupArtinEquiv 𝔪).toEquiv]
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
  classical
  have : IsGalois (hilbertClassField K) (rayClassField 𝔪) :=
    IsGalois.tower_top_of_isGalois K (hilbertClassField K) (rayClassField 𝔪)
  have : FiniteDimensional (hilbertClassField K) (rayClassField 𝔪) :=
    FiniteDimensional.right K (hilbertClassField K) (rayClassField 𝔪)
  rw [Algebra.norm_eq_prod_automorphisms, ← finprod_eq_prod_of_fintype,
    ← finprod_comp_equiv (residueUnitsQuotientArtinEquiv h).toEquiv]
  rfl

end TauCeti.ClassFieldTheory
