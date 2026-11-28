/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.Topology.Algebra.PointTopology.Scheme.Functoriality
import Mathlib.Analysis.Normed.Field.Lemmas
import TauCeti.Topology.Algebra.PointTopology.Smooth.Basic

/-!
# Smooth morphisms are open on field-valued points

A smooth morphism of schemes over a commutative ring is open on points valued in a complete
nontrivially normed field algebra over that ring. Around each source point, take
affine charts in which the morphism is standard smooth and use the implicit function
theorem on the relative presentation.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, §4, p. 11.
-/

public section

open AlgebraicGeometry CategoryTheory Topology
open scoped TauCeti.PointTopology TauCeti.SchemePointTopology

universe u

namespace TauCeti.SchemePointTopology

variable {k K : Type u} [CommRing k] [NontriviallyNormedField K] [CompleteSpace K]
  [Algebra k K]
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}

/-- A smooth morphism over a commutative ring is open on points valued in a complete
nontrivially normed field algebra, with the chart topology. -/
theorem isOpenMap_map_of_smooth (g : X ⟶ Y) (hg : g ≫ fY = fX)
    [Smooth g] : IsOpenMap (map (R := K) g hg) := by
  refine IsOpenMap.of_nhds_le fun x ↦ ?_
  obtain ⟨U, hU, V, hV, hxV, hVU, hstd⟩ :=
    Smooth.exists_isStandardSmooth g (x.val (IsLocalRing.closedPoint K))
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let q : R →+* S := (g.appLE U V hVU).hom
  let a : k →+* R := (Spec.preimage (hU.fromSpec ≫ fY)).hom
  let : Algebra k R := a.toAlgebra
  let : Algebra R S := q.toAlgebra
  let : Algebra k S := (q.comp a).toAlgebra
  let : IsScalarTower k R S := .of_algebraMap_eq' rfl
  let φ := IsScalarTower.toAlgHom k R S
  let A := CommAlgCat.of k R
  let B := CommAlgCat.of k S
  have ha : algebraMap k R = a := RingHom.algebraMap_toAlgebra a
  have hq : algebraMap R S = q := RingHom.algebraMap_toAlgebra q
  have hφq : φ.toRingHom = q := (IsScalarTower.coe_toAlgHom k R S).trans hq
  have hA : hU.fromSpec ≫ fY = Spec.algebraMap k A := by
    change _ = Spec.map (CommRingCat.ofHom (algebraMap k R))
    rw [ha]
    exact (Spec.map_preimage _).symm
  have hcomm :
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hU.fromSpec = hV.fromSpec ≫ g := by
    simpa only [hφq, q, CommRingCat.ofHom_hom] using
      IsAffineOpen.SpecMap_appLE_fromSpec g hU hV hVU
  have hB : hV.fromSpec ≫ fX = Spec.algebraMap k B := by
    rw [← hg, ← Category.assoc, ← hcomm, Category.assoc, hA, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (φ.toRingHom.comp (algebraMap k R))) =
      Spec.map (CommRingCat.ofHom (algebraMap k S))
    rw [ha, hφq, RingHom.algebraMap_toAlgebra]
  have hφ : IsOpenMap (fun z : S →ₐ[k] K ↦ z.comp φ) := by
    have : Algebra.IsStandardSmooth R S := RingHom.isStandardSmooth_algebraMap.mp
      (by rwa [hq])
    exact PointTopology.isOpenMap_comap_of_isStandardSmooth
  obtain ⟨z, rfl⟩ : x ∈ Set.range (chartPoint fX B hV.fromSpec hB) := by
    apply (mem_range_chartPoint_iff_closedPoint fX B hV.fromSpec hB x).2
    simpa only [IsAffineOpen.opensRange_fromSpec] using hxV
  have hmap (z' : S →ₐ[k] K) :
      map g hg (chartPoint fX B hV.fromSpec hB z') =
        chartPoint fY A hU.fromSpec hA (z'.comp φ) := by
    simpa only [map_chartPoint, hcomm] using
      chartPoint_spec_map_comp (A := B) (C := A) fY hU.fromSpec hA φ
        (by rw [hcomm, Category.assoc, hg, hB]) z'
  have hw := (isOpenEmbedding_chartPoint (R := K) fY A hU.fromSpec hA).isOpenMap.comp hφ
  rw [← (isOpenEmbedding_chartPoint (R := K) fX B hV.fromSpec hB).map_nhds_eq z,
    Filter.map_map]
  have heq : map (R := K) g hg ∘ chartPoint fX B hV.fromSpec hB =
      chartPoint fY A hU.fromSpec hA ∘ (fun z' : S →ₐ[k] K ↦ z'.comp φ) := funext hmap
  rw [heq, hmap]
  exact hw.nhds_le z

end TauCeti.SchemePointTopology

namespace AlgHom

/-- A smooth algebra map induces an open map on points valued in a complete nontrivially
normed field algebra over the base ring. -/
theorem isOpenMap_comap_of_smooth {k K A B : Type u} [CommRing k]
    [NontriviallyNormedField K] [Algebra k K]
    [CompleteSpace K] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (φ : A →ₐ[k] B) (hφ : φ.toRingHom.Smooth) :
    IsOpenMap (fun x : B →ₐ[k] K ↦ x.comp φ) := by
  let f := Spec.map (CommRingCat.ofHom φ.toRingHom)
  have hf : f ≫ Spec.algebraMap k A = Spec.algebraMap k B := by
    rw [← Spec.map_comp]
    congr 1
    ext k
    exact φ.commutes k
  have : Smooth f := (HasRingHomProperty.Spec_iff (P := @Smooth)).2 hφ
  have hop := TauCeti.SchemePointTopology.isOpenMap_map_of_smooth (K := K) f hf
  let eA := TauCeti.SchemePointTopology.affineHomeomorph (k := k) (R := K) A
  let eB := TauCeti.SchemePointTopology.affineHomeomorph (k := k) (R := K) B
  have hcomp := eA.symm.isOpenMap.comp (hop.comp eB.isOpenMap)
  convert hcomp using 1
  funext x
  apply eA.injective
  simpa only [Function.comp_apply, Homeomorph.apply_symm_apply, eA, eB, f, AlgHom.toRingHom_eq_coe,
    TauCeti.SchemePointTopology.affineHomeomorph_apply] using
    (TauCeti.SchemePointTopology.map_homEquivAlgHom_symm φ x).symm

end AlgHom
