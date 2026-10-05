/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.AbsoluteArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.NormSubgroup
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization

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
local Artin map. Since norm groups of finite separable extensions are open, `artinMap K` is
continuous (`continuous_artinMap`), and its kernel is the intersection of all norm subgroups
(`ker_artinMap_eq_iInf`).

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
* `TauCeti.ClassFieldTheory.continuous_artinMap`: the absolute local Artin map is continuous.
* `TauCeti.ClassFieldTheory.ker_artinMap_eq_iInf`: its kernel is the intersection of all norm
  subgroups.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter V, §1.
* J.-P. Serre, *Local class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VI, §2.
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
        TopologicalAbelianization (AbsoluteGaloisGroup K)) := by
    rw [← ContinuousMulEquiv.topologicalAbelianizationCongr_mk, hσ, artinMap_apply,
      ← ContinuousMulEquiv.topologicalAbelianizationCongr_symm,
      ContinuousMulEquiv.apply_symm_apply, ofMul_toMul]
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

end TauCeti.ClassFieldTheory
