/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.FieldArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormSubgroup
import TauCeti.GroupTheory.Abelianization.Basic

/-!
# The absolute global Artin map

For a number field `K`, `absoluteGlobalArtinMap` maps the idele class group `C_K` to the
topological abelianization of the absolute Galois group. It specializes
`ClassFormation.absoluteArtinMap` to the global class formation. Its finite restrictions
recover `globalArtinMap` and, for abelian extensions, `ideleClassArtinMap`.
The finite restriction equation `abelianizationRestrictNormalHom_comp_absoluteGlobalArtinMap`
characterizes the map by `eq_absoluteGlobalArtinMap_of_forall_abelianizationRestrictNormalHom`.
`OpenSubgroup.exists_absoluteGlobalArtinMap_mem_iff` identifies open subgroup preimages with
global norm subgroups using `ClassFormation.exists_absoluteArtinMap_mem_iff`. Its kernel corollary
`OpenNormalSubgroup.exists_ker_mk'_comp_absoluteGlobalArtinMap_eq` and
`isOpen_globalNormSubgroup` give `continuous_absoluteGlobalArtinMap`. By continuity,
`absoluteGlobalArtinMap_eq_one_of_mem_connectedComponent` shows that the map kills the identity
component of `C_K`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, §5.
* B. Lawrence and A. Venkatesh, *Diophantine problems and p-adic period mappings*, §2.4.
-/

public noncomputable section

open NumberField

namespace TauCeti.ClassFieldTheory

/-- The absolute global Artin map `C_K → G_K^ab` of a number field, obtained from the inverse
limit of finite Artin maps in the global class formation. -/
def absoluteGlobalArtinMap (K : Type) [Field K] [NumberField K] :
    IdeleClassGroup (𝓞 K) K →* Field.absoluteGaloisGroupAbelianization K :=
  (absoluteGaloisGroupRestrictEquiv K).symm.topologicalAbelianizationCongr.toMonoidHom.comp
    (MonoidHom.toAdditive.symm
      ((globalClassFormation K).absoluteArtinMap.comp (globalGroundEquiv K).toAddMonoidHom))

-- Do not put this expansion in simp. It hides the absolute symbol from the restriction API.
/-- The absolute global Artin symbol is the symbol of the global class formation, transported
from the separable closure to Mathlib's algebraic closure. -/
theorem absoluteGlobalArtinMap_apply (K : Type) [Field K] [NumberField K]
    (c : IdeleClassGroup (𝓞 K) K) :
    absoluteGlobalArtinMap K c =
      (absoluteGaloisGroupRestrictEquiv K).symm.topologicalAbelianizationCongr
        ((globalClassFormation K).absoluteArtinMap (globalGroundEquiv K (.ofMul c))).toMul := (rfl)

/-- On the separable-closure model of `G_K^ab`, the absolute global Artin symbol is the
symbol of the global class formation. -/
@[simp]
theorem topologicalAbelianizationCongr_absoluteGlobalArtinMap (K : Type) [Field K] [NumberField K]
    (c : IdeleClassGroup (𝓞 K) K) :
    (absoluteGaloisGroupRestrictEquiv K).topologicalAbelianizationCongr
        (absoluteGlobalArtinMap K c) =
      ((globalClassFormation K).absoluteArtinMap (globalGroundEquiv K (.ofMul c))).toMul := by
  rw [absoluteGlobalArtinMap_apply, ← ContinuousMulEquiv.topologicalAbelianizationCongr_symm,
    ContinuousMulEquiv.apply_symm_apply]

/-- Transport membership of an absolute global Artin symbol to the separable-closure model:
membership in the original open subgroup is equivalent to membership of the formation symbol
in the comapped subgroup, without expanding either model's Artin map. -/
theorem absoluteGlobalArtinMap_mem_iff_mem_comap {K : Type}
    [Field K] [NumberField K] {U : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K)}
    {c : IdeleClassGroup (𝓞 K) K} :
    absoluteGlobalArtinMap K c ∈ U ↔
      ((globalClassFormation K).absoluteArtinMap (globalGroundEquiv K (.ofMul c))).toMul ∈
        U.comap (↑(absoluteGaloisGroupRestrictEquiv K).symm.topologicalAbelianizationCongr)
          (map_continuous
            (absoluteGaloisGroupRestrictEquiv K).symm.topologicalAbelianizationCongr) := by
  rw [OpenSubgroup.mem_comap, MonoidHom.coe_ofClass, absoluteGlobalArtinMap_apply]

-- Use this existence theorem to choose a layer, not as a simp rule for membership.
/-- The preimage of any open subgroup of `G_K^ab` is the norm subgroup of a finite Galois layer. -/
theorem _root_.OpenSubgroup.exists_absoluteGlobalArtinMap_mem_iff {K : Type}
    [Field K] [NumberField K] (U : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    ∃ V : OpenNormalSubgroup (AbsoluteGaloisGroup K), ∀ c : IdeleClassGroup (𝓞 K) K,
      absoluteGlobalArtinMap K c ∈ U ↔ c ∈ globalNormSubgroup K V := by
  let e := (absoluteGaloisGroupRestrictEquiv K).symm.topologicalAbelianizationCongr
  obtain ⟨V, hV⟩ := (globalClassFormation K).exists_absoluteArtinMap_mem_iff
    (U.comap (↑e) (map_continuous e))
  exact ⟨V, fun c ↦ absoluteGlobalArtinMap_mem_iff_mem_comap.trans
    ((hV (globalGroundEquiv K (.ofMul c))).trans mem_globalNormSubgroup_iff.symm)⟩

/-- The kernel of the absolute global Artin map modulo an open normal subgroup of `G_K^ab`
is the norm subgroup of a finite Galois layer. -/
theorem _root_.OpenNormalSubgroup.exists_ker_mk'_comp_absoluteGlobalArtinMap_eq {K : Type}
    [Field K] [NumberField K] (U : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    ∃ V : OpenNormalSubgroup (AbsoluteGaloisGroup K),
      ((QuotientGroup.mk' U.toSubgroup).comp (absoluteGlobalArtinMap K)).ker =
        globalNormSubgroup K V := by
  obtain ⟨V, hV⟩ := U.toOpenSubgroup.exists_absoluteGlobalArtinMap_mem_iff
  refine ⟨V, Subgroup.ext fun c ↦ ?_⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hV c

variable (K : Type) [Field K] [NumberField K]

/-- The absolute global Artin map of a number field is continuous. -/
theorem continuous_absoluteGlobalArtinMap : Continuous (absoluteGlobalArtinMap K) := by
  refine continuous_iff_forall_continuous_mk.mpr fun U ↦ ?_
  obtain ⟨V, hV⟩ := U.exists_ker_mk'_comp_absoluteGlobalArtinMap_eq
  let f := (QuotientGroup.mk' U.toSubgroup).comp (absoluteGlobalArtinMap K)
  have hopen : IsOpen (f.ker : Set (IdeleClassGroup (𝓞 K) K)) :=
    hV ▸ isOpen_globalNormSubgroup K V
  simpa only [f, MonoidHom.coe_comp, Function.comp_def, QuotientGroup.mk'_apply] using
    f.continuous_of_isOpen_ker hopen

/-- The absolute global Artin map kills the connected component of the identity of `C_K`. -/
theorem absoluteGlobalArtinMap_eq_one_of_mem_connectedComponent {c : IdeleClassGroup (𝓞 K) K}
    (hc : c ∈ connectedComponent (1 : IdeleClassGroup (𝓞 K) K)) :
    absoluteGlobalArtinMap K c = 1 := by
  have hmem : absoluteGlobalArtinMap K c ∈
      absoluteGlobalArtinMap K '' connectedComponent (1 : IdeleClassGroup (𝓞 K) K) :=
    Set.mem_image_of_mem _ hc
  rwa [(continuous_absoluteGlobalArtinMap K).image_connectedComponent_eq_singleton,
    Set.mem_singleton_iff, map_one] at hmem

section Finite

open scoped IsMulCommutative

variable (L : Type*) [Field L] [NumberField L] [Algebra K L]

/-- The restriction of the absolute global Artin map to a finite Galois extension of number
fields is the finite global Artin map, with both maps written additively. -/
@[simp]
theorem abelianizationRestrictNormalHom_comp_absoluteGlobalArtinMap [IsGalois K L]
    (ι : L →ₐ[K] SeparableClosure K) :
    ι.abelianizationRestrictNormalHom.comp (MonoidHom.toAdditive (absoluteGlobalArtinMap K)) =
      globalArtinMap K L ι := by
  refine AddMonoidHom.ext fun c ↦ ?_
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
  -- Compare on the separable-closure model, where the formation restriction equation applies.
  rw [AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply, toMul_ofMul,
    ι.abelianizationRestrictNormalHom_apply, topologicalAbelianizationCongr_absoluteGlobalArtinMap,
    ofMul_toMul, ClassFormation.abelianizationRestrict_absoluteArtinMap, globalArtinMap_apply,
    globalArtinEquiv_mk]

/-- Restricting a representative of an absolute global Artin symbol to a finite Galois extension
gives the finite Artin symbol in the abelianization of its Galois group. -/
theorem globalArtinMap_eq_of_mk_eq_absoluteGlobalArtinMap [IsGalois K L]
    (ι : L →ₐ[K] SeparableClosure K)
    {c : IdeleClassGroup (𝓞 K) K} {g : Field.absoluteGaloisGroup K}
    (hg : (g : Field.absoluteGaloisGroupAbelianization K) = absoluteGlobalArtinMap K c) :
    globalArtinMap K L ι (.ofMul c) =
      .ofMul (Group.Abelianization.of
        (ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K g))) := by
  apply globalArtinMap_eq_of_mk_eq_absoluteArtinMap K L ι
  -- Transport the representative back to the separable closure used by the class formation.
  rw [← ContinuousMulEquiv.topologicalAbelianizationCongr_mk, hg,
    topologicalAbelianizationCongr_absoluteGlobalArtinMap, ofMul_toMul]

/-- Over a finite abelian extension, the restriction of an absolute global Artin symbol is the
finite Artin symbol in the Galois group itself. -/
theorem ideleClassArtinMap_eq_of_mk_eq_absoluteGlobalArtinMap [IsAbelianGalois K L]
    (ι : L →ₐ[K] SeparableClosure K) {c : IdeleClassGroup (𝓞 K) K} {g : Field.absoluteGaloisGroup K}
    (hg : (g : Field.absoluteGaloisGroupAbelianization K) = absoluteGlobalArtinMap K c) :
    ideleClassArtinMap K L c = ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K g) := by
  apply Group.Abelianization.of_injective
  rw [of_ideleClassArtinMap K L ι,
    globalArtinMap_eq_of_mk_eq_absoluteGlobalArtinMap K L ι hg, toMul_ofMul]

end Finite

/-- A homomorphism from `C_K` to `G_K^ab` is the absolute global Artin map if its restriction
to every finite Galois layer is the finite global Artin map. -/
theorem eq_absoluteGlobalArtinMap_of_forall_abelianizationRestrictNormalHom
    {φ : IdeleClassGroup (𝓞 K) K →* Field.absoluteGaloisGroupAbelianization K}
    (hφ : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
      (ι : L →ₐ[K] SeparableClosure K),
      ι.abelianizationRestrictNormalHom.comp (MonoidHom.toAdditive φ) = globalArtinMap K L ι) :
    φ = absoluteGlobalArtinMap K := by
  refine MonoidHom.ext fun c ↦ ?_
  apply (absoluteGaloisGroupRestrictEquiv K).topologicalAbelianizationCongr.injective
  refine Additive.ofMul.injective (NormalLayer.eq_of_forall_abelianizationRestrict_eq fun V ↦ ?_)
  let ι := (classField K V).val
  have h := DFunLike.congr_fun ((hφ (classField K V) ι).trans
    (abelianizationRestrictNormalHom_comp_absoluteGlobalArtinMap K (classField K V) ι).symm)
    (Additive.ofMul c)
  simp only [AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply, toMul_ofMul,
    AlgHom.abelianizationRestrictNormalHom_apply] at h
  rw [← fixingOpenNormalSubgroup_classField V]
  exact (MulEquiv.toAdditive (layerGalEquiv ι).abelianizationCongr).injective h

end TauCeti.ClassFieldTheory
