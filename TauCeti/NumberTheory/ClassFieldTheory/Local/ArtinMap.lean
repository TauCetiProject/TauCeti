/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.AbsoluteArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Restriction
public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.NormSubgroup
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.ConjugateSubgroups
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# The absolute local Artin map

Let `K` be a nonarchimedean local field. The local class formation
`TauCeti.ClassFieldTheory.localClassFormation K` lives on the formation of `(Kˢ)ˣ` over the
absolute Galois group `G_K = Gal(Kˢ/K)`. Its ground level is `Kˣ`. Its absolute Artin map
`ClassFormation.absoluteArtinMap` is the inverse limit of the finite Artin maps. Reading it
through these identifications gives the **absolute local Artin map**

```text
artinMap K : Kˣ →* G_K^ab,
```

normalized, like the finite local Artin maps, by arithmetic Frobenius. Its target is
`Field.absoluteGaloisGroupAbelianization K`, the topological abelianization of Mathlib's
absolute Galois group `Gal(AlgebraicClosure K/K)`, taken at the algebraic closure. The comparison
between the two closures is `TauCeti.absoluteGaloisGroupRestrictEquiv`, restriction to the
separable closure.

The finite restrictions of `artinMap K` are the finite local Artin maps (`artinMap_restrict`): if
`σ ∈ Gal(AlgebraicClosure K/K)` represents the absolute Artin symbol of `x ∈ Kˣ`, then for every
finite Galois extension `L/K` embedded in `Kˢ` by `ι`, the Artin symbol of `x` in `Gal(L/K)^ab` is
the class of the restriction of `σ` to `L`. The image of `artinMap K` is dense
(`denseRange_artinMap`), but it is not all of `G_K^ab`, so no statement about `G_K^ab` follows from
one about the image alone.

The norm subgroups of `Kˣ` are the preimages of the open subgroups of `G_K^ab`: every open
subgroup of `G_K^ab` is cut out by some finite Galois extension `L/K`, and its preimage under
`artinMap K` is the norm group `N_{L/K}(Lˣ)` (`exists_artinMap_mem_iff`), the kernel of the finite
local Artin map. Conversely every norm subgroup is such a preimage
(`exists_openSubgroup_artinMap_mem_iff`). Since norm groups of finite separable extensions are
open, `artinMap K` is continuous (`continuous_artinMap`), and its kernel is the intersection of
all norm subgroups (`ker_artinMap_eq_iInf`).

The absolute Artin map is functorial for the norm (`artinMap_norm`). For a finite extension `L/K`
embedded in `Kˢ` by `iota`, `TauCeti.absoluteGaloisGroupExtend K L iota` embeds `G_L` in `G_K` as
`Gal(Kˢ/iota(L))`, and it carries the Artin symbol of `x ∈ Lˣ` to that of `N_{L/K} x`. The proof
compares the two local class formations on corresponding layers
(`TauCeti.ClassFieldTheory.artinMap_localFormationLayerEquiv`) and then uses the Artin–Tate
diagram for the norm inside the formation of `K`
(`TauCeti.ClassFieldTheory.ClassFormation.artinMap_groundNorm`). On ground levels, that norm is
the field norm `N_{L/K}` (`TauCeti.ClassFieldTheory.groundNorm_layerRestriction_localFormationMap`).

The absolute Artin map is natural in the local field (`artinMap_congr`). A continuous isomorphism
`e : K ≃+* K'`, extended to the algebraic closures by `e'`, carries `Art_K(x)` to `Art_{K'}(e x)`.
Conjugation by `e'` is determined only up to an inner automorphism of `G_{K'}`, which is
invisible in `G_{K'}^ab`. This transports Artin symbols across identifications of local fields,
for instance from a completion of a number field to a concrete model such as `ℚ_[p]`.

## Main definitions

* `TauCeti.ClassFieldTheory.artinMap K`: the absolute local Artin map `Kˣ →* G_K^ab`.

## Main results

* `TauCeti.ClassFieldTheory.artinMap_apply`: `artinMap K` is the absolute Artin map of the local
  class formation, read through the identification of its ground level with `Kˣ` and the
  comparison of absolute Galois groups.
* `TauCeti.ClassFieldTheory.artinMap_restrict`: the finite restrictions of the absolute local
  Artin map are the finite local Artin maps.
* `TauCeti.ClassFieldTheory.denseRange_artinMap`: the absolute local Artin map has dense image.
* `TauCeti.ClassFieldTheory.exists_artinMap_mem_iff`: the preimage of an open subgroup of
  `G_K^ab` is a norm subgroup.
* `TauCeti.ClassFieldTheory.exists_openSubgroup_artinMap_mem_iff`: every norm subgroup is the
  preimage of an open subgroup of `G_K^ab`.
* `TauCeti.ClassFieldTheory.continuous_artinMap`: the absolute local Artin map is continuous.
* `TauCeti.ClassFieldTheory.ker_artinMap_eq_iInf`: its kernel is the intersection of all norm
  subgroups.
* `TauCeti.ClassFieldTheory.artinMap_norm`: the absolute local Artin map is functorial for the
  norm of a finite extension.
* `TauCeti.ClassFieldTheory.artinMap_congr`: the absolute local Artin map is natural for
  continuous isomorphisms of local fields.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter V, §1.
* J.-P. Serre, *Local class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VI, §2.
* J.-P. Serre, *Local Fields*, Chapter XI, §3 (functoriality of the reciprocity map).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open NormalLayer

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The **absolute local Artin map** `Kˣ →* G_K^ab` of a nonarchimedean local field `K`, into the
topological abelianization of the absolute Galois group `Gal(AlgebraicClosure K/K)`. It is the
absolute Artin map of the local class formation (`artinMap_apply`), the inverse limit of the finite
local Artin maps (`artinMap_restrict`). It has dense image (`denseRange_artinMap`). -/
def artinMap : Kˣ →* Field.absoluteGaloisGroupAbelianization K :=
  (absoluteGaloisGroupRestrictEquiv K).symm.topologicalAbelianizationCongr.toMonoidHom.comp
    (MonoidHom.toAdditive.symm
      ((localClassFormation K).absoluteArtinMap.comp
        (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
          (fixedField_toSubgroup_top K)).toAddMonoidHom))

/-- **The absolute local Artin map is the absolute Artin map of the local class formation**: the
absolute Artin symbol of `x ∈ Kˣ`, regarded as an element of the ground level `((Kˢ)ˣ)^{G_K}`,
carried from `Gal(Kˢ/K)^ab` to `Gal(AlgebraicClosure K/K)^ab`. -/
theorem artinMap_apply (x : Kˣ) :
    artinMap K x = (absoluteGaloisGroupRestrictEquiv K).symm.topologicalAbelianizationCongr
      ((localClassFormation K).absoluteArtinMap
        (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K)) (fixedField_toSubgroup_top K)
          (Additive.ofMul x))).toMul := by
  rw [artinMap, MonoidHom.comp_apply, MonoidHom.toAdditive_symm_apply_apply]
  rfl

/-- If `σ ∈ Gal(AlgebraicClosure K/K)` represents the absolute local Artin symbol of `x ∈ Kˣ`, then
the absolute Artin symbol of `x` for the local class formation is the class of the restriction of
`σ` to the separable closure. -/
private theorem absoluteArtinMap_eq_of_mk_eq_artinMap (x : Kˣ) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = artinMap K x) :
    (localClassFormation K).absoluteArtinMap
        (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K)) (fixedField_toSubgroup_top K)
          (Additive.ofMul x)) =
      Additive.ofMul ((absoluteGaloisGroupRestrictEquiv K σ : AbsoluteGaloisGroup K) :
        TopologicalAbelianization (AbsoluteGaloisGroup K)) := by
  rw [← ContinuousMulEquiv.topologicalAbelianizationCongr_mk, hσ, artinMap_apply,
    ← ContinuousMulEquiv.topologicalAbelianizationCongr_symm,
    ContinuousMulEquiv.apply_symm_apply, ofMul_toMul]

/-- **The finite restrictions of the absolute local Artin map are the finite local Artin maps.**
If `σ ∈ Gal(AlgebraicClosure K/K)` represents the absolute Artin symbol of `x ∈ Kˣ`, then for
every finite Galois extension `L/K` embedded in the separable closure by `ι`, the Artin symbol of
`x` in `Gal(L/K)^ab` is the class of the restriction of `σ` to `L`. -/
theorem artinMap_restrict (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (ι : L →ₐ[K] SeparableClosure K) (x : Kˣ) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = artinMap K x) :
    localArtinMap K L ι (Additive.ofMul x) =
      Additive.ofMul
        (Abelianization.of (ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ))) := by
  set V := fixingOpenNormalSubgroup K L
  set a := unitsLevelEquiv (Algebra.ofId K (SeparableClosure K)) (fixedField_toSubgroup_top K)
    (Additive.ofMul x)
  -- The absolute Artin symbol of `x` for the local class formation is the class of the
  -- restriction of `σ` to the separable closure.
  have habs : (localClassFormation K).absoluteArtinMap a =
      Additive.ofMul ((absoluteGaloisGroupRestrictEquiv K σ : AbsoluteGaloisGroup K) :
        TopologicalAbelianization (AbsoluteGaloisGroup K)) :=
    absoluteArtinMap_eq_of_mk_eq_artinMap K x σ hσ
  have hground : groundEquivOfOpenNormal (unitsFormation K) V a =
      unitsLevelEquiv (Algebra.ofId K (SeparableClosure K)) (fixedField_ground_ofOpenNormal K V)
        (Additive.ofMul x) :=
    Subtype.ext (by simp [a])
  have hmem : (absoluteGaloisGroupRestrictEquiv K σ : AbsoluteGaloisGroup K) ∈
      (ofOpenNormal V).ground := by
    simp
  rw [localArtinMap_apply, localArtinEquiv_mk, ← hground,
    ← (localClassFormation K).abelianizationRestrict_absoluteArtinMap, habs,
    abelianizationRestrict_mk V ⟨_, hmem⟩, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
    abelianizationCongr_of, layerGalEquiv_mk]

/-- **The absolute local Artin map has dense image**: it reaches every finite quotient of
`G_K^ab`, because every finite local Artin map is surjective. -/
theorem denseRange_artinMap : DenseRange (artinMap K) := by
  have hfun : ⇑(artinMap K) =
      ⇑(absoluteGaloisGroupRestrictEquiv K).symm.topologicalAbelianizationCongr ∘
      (fun a ↦ ((localClassFormation K).absoluteArtinMap a).toMul) ∘
      ⇑(unitsLevelEquiv (Algebra.ofId K (SeparableClosure K)) (fixedField_toSubgroup_top K)) ∘
      Additive.ofMul :=
    funext (artinMap_apply K)
  rw [hfun, DenseRange, ← Function.comp_assoc,
    ((unitsLevelEquiv _ _).surjective.comp Additive.ofMul.surjective).range_comp]
  exact (ContinuousMulEquiv.surjective _).denseRange.comp
    (localClassFormation K).denseRange_absoluteArtinMap (map_continuous _)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The unit `x ∈ Kˣ`, as an element of the ground level of the top layer, read in the ground level
of the layer `V ◁ G_K`, is `localGroundEquiv K V x`. -/
private theorem groundEquivOfOpenNormal_unitsLevelEquiv
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) (x : Kˣ) :
    groundEquivOfOpenNormal (unitsFormation K) V
        (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K)) (fixedField_toSubgroup_top K)
          (Additive.ofMul x)) =
      localGroundEquiv K V (Additive.ofMul x) :=
  Subtype.ext (by simp)

/-- **The preimage of an open subgroup under the absolute local Artin map is a norm subgroup.**
For every open subgroup `U` of `G_K^ab` there is an open normal subgroup `V` of `G_K`, cutting out
the finite Galois extension `classField K V`, such that the Artin symbol of `x ∈ Kˣ` lies in `U`
exactly when `x` is a norm from `classField K V`. -/
theorem exists_artinMap_mem_iff
    (U : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    ∃ V : OpenNormalSubgroup (AbsoluteGaloisGroup K), ∀ x : Kˣ,
      artinMap K x ∈ U ↔ x ∈ localNormSubgroup K V := by
  set e := (absoluteGaloisGroupRestrictEquiv K).symm.topologicalAbelianizationCongr
  obtain ⟨V, hV⟩ := (localClassFormation K).exists_absoluteArtinMap_mem_iff
    (U.comap (e : TopologicalAbelianization (AbsoluteGaloisGroup K) →* _) (map_continuous e))
  refine ⟨V, fun x ↦ ?_⟩
  rw [← localGroundEquiv_mem_normSubgroup_iff, ← groundEquivOfOpenNormal_unitsLevelEquiv, ← hV,
    OpenSubgroup.mem_comap, MonoidHom.coe_ofClass, artinMap_apply]

/-- **Every local norm subgroup is the preimage of an open subgroup under the absolute local Artin
map.** For every open normal subgroup `V` of `G_K` there is an open subgroup `U` of `G_K^ab`, the
kernel of the projection `G_K^ab → Gal(classField K V/K)^ab`, such that the Artin symbol of
`x ∈ Kˣ` lies in `U` exactly when `x` is a norm from `classField K V`. This is the converse of
`exists_artinMap_mem_iff`. -/
theorem exists_openSubgroup_artinMap_mem_iff (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    ∃ U : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K), ∀ x : Kˣ,
      artinMap K x ∈ U ↔ x ∈ localNormSubgroup K V := by
  set e := (absoluteGaloisGroupRestrictEquiv K).symm.topologicalAbelianizationCongr
  -- the kernel of the projection onto `(G_K/V)^ab` contains the open image of `V`
  let ρ := MonoidHom.toAdditive.symm (abelianizationRestrict V)
  have hmem (y : TopologicalAbelianization (AbsoluteGaloisGroup K)) :
      y ∈ ρ.ker ↔ abelianizationRestrict V (Additive.ofMul y) = 0 :=
    MonoidHom.mem_ker.trans toMul_eq_one
  have hρ : IsOpen (ρ.ker : Set (TopologicalAbelianization (AbsoluteGaloisGroup K))) := by
    refine Subgroup.isOpen_mono (H₁ := V.toSubgroup.map (QuotientGroup.mk' _)) ?_
      (QuotientGroup.isOpenMap_coe _ V.isOpen)
    rintro _ ⟨g, hgV, rfl⟩
    have hg : g ∈ (ofOpenNormal V).ground := by simp
    rw [QuotientGroup.mk'_apply, hmem, abelianizationRestrict_mk V ⟨g, hg⟩, ofMul_eq_zero,
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hgV)),
      map_one]
  refine ⟨(⟨ρ.ker, hρ⟩ : OpenSubgroup _).comap (e.symm : _ →* _) (map_continuous e.symm),
    fun x ↦ ?_⟩
  rw [OpenSubgroup.mem_comap, ← OpenSubgroup.mem_toSubgroup, MonoidHom.coe_ofClass,
    artinMap_apply, ContinuousMulEquiv.symm_apply_apply, hmem, ofMul_toMul,
    (localClassFormation K).abelianizationRestrict_absoluteArtinMap_eq_zero_iff,
    groundEquivOfOpenNormal_unitsLevelEquiv, localGroundEquiv_mem_normSubgroup_iff]

/-- **The absolute local Artin map is continuous.** The preimage of an open subgroup of `G_K^ab`
is a norm subgroup (`exists_artinMap_mem_iff`), and norm subgroups of finite separable extensions
are open in `Kˣ`. -/
theorem continuous_artinMap : Continuous (artinMap K) := by
  refine continuous_of_continuousAt_one (artinMap K) fun N hN ↦ ?_
  rw [map_one] at hN
  obtain ⟨W, hWN, hWo, hW1⟩ := mem_nhds_iff.mp hN
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo hW1
  obtain ⟨V, hV⟩ := exists_artinMap_mem_iff K U.toOpenSubgroup
  exact Filter.mem_map.mpr <| Filter.mem_of_superset
    ((isOpen_localNormSubgroup K V).mem_nhds (one_mem _)) fun x hx ↦ hWN (hU ((hV x).mpr hx))

/-- **The kernel of the absolute local Artin map is the intersection of all norm subgroups**: the
Artin symbol of `x ∈ Kˣ` is trivial exactly when `x` is a norm from every finite Galois extension
of `K`. This says nothing about whether that intersection is trivial. -/
theorem ker_artinMap_eq_iInf :
    (artinMap K).ker = ⨅ V : OpenNormalSubgroup (AbsoluteGaloisGroup K), localNormSubgroup K V := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_iInf, artinMap_apply,
    map_eq_one_iff _ (ContinuousMulEquiv.injective _), toMul_eq_one,
    ClassFormation.absoluteArtinMap_eq_zero_iff]
  refine forall_congr' fun V ↦ ?_
  rw [groundEquivOfOpenNormal_unitsLevelEquiv, localGroundEquiv_mem_normSubgroup_iff]

/-! ### Norm functoriality -/

section Norm

variable {K} (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L]
  (iota : L →ₐ[K] SeparableClosure K) [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

/-- The norm functoriality of the absolute Artin maps of the local class formations of `L` and
`K`, read in the finite quotient of `G_K^ab` cut out by an open normal subgroup
`V ≤ Gal(Kˢ/iota(L))`. -/
private theorem abelianizationRestrict_absoluteArtinMap_normUnits
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    (hV : V ≤ (galoisSubgroup K L iota).toSubgroup) (x : Lˣ) (τ : AbsoluteGaloisGroup L)
    (hτ : (localClassFormation L).absoluteArtinMap
        (unitsLevelEquiv (Algebra.ofId L (SeparableClosure L)) (fixedField_toSubgroup_top L)
          (Additive.ofMul x)) =
      Additive.ofMul (τ : TopologicalAbelianization (AbsoluteGaloisGroup L))) :
    abelianizationRestrict V ((localClassFormation K).absoluteArtinMap
        (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K)) (fixedField_toSubgroup_top K)
          (Additive.ofMul (Algebra.normUnits K x)))) =
      abelianizationRestrict V (Additive.ofMul ((localFormationHom K L iota τ :
        AbsoluteGaloisGroup K) : TopologicalAbelianization (AbsoluteGaloisGroup K))) := by
  let V' := V.comap (localFormationHom K L iota) (continuous_localFormationHom K L iota)
  have T := layerRestriction_localFormationMap K L iota V hV
  have hτs :
      localFormationHom K L iota τ ∈ ((ofOpenNormal V').localFormationMap K L iota).ground := by
    rw [← OpenSubgroup.mem_toSubgroup, localFormationMap_ofOpenNormal_ground_toSubgroup K L iota,
      ← range_localFormationHom]
    exact ⟨τ, rfl⟩
  have hτV' : τ ∈ (ofOpenNormal V').ground := by simp
  -- The steps below are written with `Eq.trans` and `congrArg`: rewriting in these goals is slow.
  -- In the layer `V ◁ G_K`, `N x` is the norm of `iota x` from the restricted layer
  -- `V ◁ Gal(Kˢ/iota(L))`, which corresponds to the layer `V' ◁ G_L` over `L`.
  have hNx : localGroundEquiv K V (Additive.ofMul (Algebra.normUnits K x)) =
      T.groundNorm (unitsFormation K)
        ((localFormationLayerEquiv K L iota (ofOpenNormal V')).groundEquiv
          (localGroundEquiv L V' (Additive.ofMul x))) :=
    (groundNorm_layerRestriction_localFormationMap K L iota V hV _).symm.trans
      (congrArg (T.groundNorm (unitsFormation K))
        (groundEquiv_localFormationLayerEquiv_localGroundEquiv K L iota V' _).symm)
  -- In the layer `V' ◁ G_L`, the finite Artin symbol of `x` is the class of `τ`.
  have hL : (localClassFormation L).artinMap (ofOpenNormal V')
        (localGroundEquiv L V' (Additive.ofMul x)) =
      Additive.ofMul (Abelianization.of
        ((⟨τ, hτV'⟩ : (ofOpenNormal V').ground) : (ofOpenNormal V').Gal)) :=
    (congrArg _ (groundEquivOfOpenNormal_unitsLevelEquiv L V' x).symm).trans
      (((localClassFormation L).abelianizationRestrict_absoluteArtinMap V' _).symm.trans
        ((congrArg _ hτ).trans (abelianizationRestrict_mk V' ⟨τ, hτV'⟩)))
  -- Pass to the layer `V ◁ G_K`, apply the Artin-Tate norm diagram to `hNx`, and compare the two
  -- local class formations to reach `hL`.
  refine ((localClassFormation K).abelianizationRestrict_absoluteArtinMap V _).trans ?_
  refine (congrArg ((localClassFormation K).artinMap (ofOpenNormal V))
    ((groundEquivOfOpenNormal_unitsLevelEquiv K V _).trans hNx)).trans ?_
  refine ((localClassFormation K).artinMap_groundNorm T _).trans ?_
  refine (congrArg T.inclusionHom ((artinMap_localFormationLayerEquiv K L iota _ _).trans
    (congrArg _ hL))).trans ?_
  refine Eq.trans ?_ (abelianizationRestrict_mk V ⟨localFormationHom K L iota τ, by simp⟩).symm
  rw [MulEquiv.toAdditive_apply_apply, toMul_ofMul, abelianizationCongr_of,
    localFormationLayerEquiv_galEquiv_mk K L iota _ _ ⟨_, hτs⟩ rfl,
    LayerRestriction.inclusionHom_of, LayerRestriction.galHom_mk]
  exact congrArg (fun w ↦ Additive.ofMul (Abelianization.of
    (QuotientGroup.mk w : (ofOpenNormal V).Gal))) (Subtype.ext (Subgroup.coe_inclusion _ _))

/-- **Norm functoriality of the absolute local Artin map.** Let `L/K` be a finite extension of
nonarchimedean local fields, embedded in `Kˢ` by `iota`. If `τ ∈ Gal(AlgebraicClosure L/L)`
represents the absolute Artin symbol of `x ∈ Lˣ`, then its image under the embedding
`absoluteGaloisGroupExtend K L iota : G_L → G_K` represents the absolute Artin symbol of the norm
`N_{L/K} x`: in `G_K^ab`,

```text
Art_K (N_{L/K} x) = absoluteGaloisGroupExtend K L iota (Art_L x).
```
-/
theorem artinMap_norm (x : Lˣ) (τ : Field.absoluteGaloisGroup L)
    (hτ : (τ : Field.absoluteGaloisGroupAbelianization L) = artinMap L x) :
    (absoluteGaloisGroupExtend K L iota τ : Field.absoluteGaloisGroupAbelianization K) =
      artinMap K (Algebra.normUnits K x) := by
  -- On the separable closures the absolute Artin symbol of `x` is the class of the restriction
  -- `τ'` of `τ`, and `absoluteGaloisGroupExtend` is `localFormationHom`.
  set τ' := absoluteGaloisGroupRestrictEquiv L τ
  have habs := absoluteArtinMap_eq_of_mk_eq_artinMap L x τ hτ
  -- It suffices to compare the two symbols in the quotients cut out by the open normal subgroups
  -- of `G_K` contained in `Gal(Kˢ/iota(L))`.
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (galoisSubgroup K L iota).isOpen (one_mem _)
  have key : (localClassFormation K).absoluteArtinMap
      (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K)) (fixedField_toSubgroup_top K)
        (Additive.ofMul (Algebra.normUnits K x))) =
      Additive.ofMul ((localFormationHom K L iota τ' : AbsoluteGaloisGroup K) :
        TopologicalAbelianization (AbsoluteGaloisGroup K)) :=
    eq_of_forall_le_abelianizationRestrict_eq N fun V hV ↦
      abelianizationRestrict_absoluteArtinMap_normUnits L iota V
        ((OpenNormalSubgroup.toSubgroup_le.mpr hV).trans hN) x τ' habs
  rw [artinMap_apply, key, toMul_ofMul, ContinuousMulEquiv.topologicalAbelianizationCongr_mk]
  congr 1
  rw [ContinuousMulEquiv.eq_symm_apply, absoluteGaloisGroupRestrictEquiv_absoluteGaloisGroupExtend,
    localFormationHom_apply]

end Norm

/-! ### Naturality in the local field -/

section Congr

variable {K} {K' : Type} [Field K'] [ValuativeRel K'] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K']

/-- **The absolute local Artin map is natural in the local field.** Let `e : K ≃+* K'` be a
continuous isomorphism of nonarchimedean local fields and `e'` an extension of `e` to the algebraic
closures. If `σ ∈ G_K` represents the absolute Artin symbol of `x ∈ Kˣ`, then its conjugate
`σ' = e' ∘ σ ∘ e'⁻¹ ∈ G_{K'}` represents the absolute Artin symbol of `e x`:

```text
Art_{K'} (e x) = e' ∘ Art_K (x) ∘ e'⁻¹.
```

Two extensions of `e` differ by an element of `G_{K'}`, and conjugation by it is invisible in
`G_{K'}^ab`, so every extension `e'` is allowed. Continuity of `e` is what makes it compatible
with the valuations of `K` and `K'`. -/
theorem artinMap_congr (e : K ≃+* K') (he : Continuous e)
    (e' : AlgebraicClosure K ≃+* AlgebraicClosure K')
    (he' : ∀ c : K, e' (algebraMap K (AlgebraicClosure K) c) =
      algebraMap K' (AlgebraicClosure K') (e c))
    (x : Kˣ) (σ : Field.absoluteGaloisGroup K) (σ' : Field.absoluteGaloisGroup K')
    (hσσ' : ∀ y : AlgebraicClosure K, e' (σ.toRingEquiv y) = σ'.toRingEquiv (e' y))
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = artinMap K x) :
    (σ' : Field.absoluteGaloisGroupAbelianization K') =
      artinMap K' (Units.map e.toMonoidHom x) := by
  -- Regard `K` as an extension of degree one of `K'` along `e⁻¹`.
  let _ : Algebra K' K := e.symm.toRingHom.toAlgebra
  let eA : K' ≃ₐ[K'] K := AlgEquiv.ofRingEquiv (f := e.symm) fun _ ↦ rfl
  have : FiniteDimensional K' K := eA.toLinearEquiv.finiteDimensional
  have : ValuativeExtension K' K := ⟨fun a b ↦ by
    rw [RingHom.algebraMap_toAlgebra, ← e.toRingHom.map_vle_map_iff_of_continuous he]
    simp⟩
  let iota : K →ₐ[K'] SeparableClosure K' := (Algebra.ofId K' (SeparableClosure K')).comp eA.symm
  -- Along `iota`, `absoluteGaloisGroupExtend` is conjugation by `e'` up to an inner automorphism,
  -- and the norm of `K/K'` is `e`, so `artinMap_norm` gives the claim.
  obtain ⟨γ, hγ⟩ := exists_absoluteGaloisGroupExtend_eq_conj K' K iota e' he'
  have hnorm : Algebra.normUnits K' x = Units.map e.toMonoidHom x := by
    ext
    rw [Algebra.coe_normUnits, ← eA.apply_symm_apply (x : K), Algebra.norm_eq_of_algEquiv,
      Algebra.norm_self, MonoidHom.id_apply, Units.coe_map]
    -- `eA⁻¹` is `e` as a function.
    rfl
  rw [← hnorm, ← artinMap_norm K iota x σ hσ, hγ σ σ' hσσ', QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_cancel_comm]

end Congr

end TauCeti.ClassFieldTheory
