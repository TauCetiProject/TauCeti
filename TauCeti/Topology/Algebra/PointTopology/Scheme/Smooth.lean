/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.Topology.Algebra.PointTopology.Scheme.Functoriality
import Mathlib.Analysis.Normed.Field.Lemmas
import TauCeti.AlgebraicGeometry.Morphisms.FiniteType.Basic
import TauCeti.Topology.Algebra.PointTopology.Smooth.Basic

/-!
# Smooth morphisms are open on field-valued points

A smooth morphism of schemes over a complete nontrivially normed field is open on points
if the target is locally of finite type over the field. Around each source point, take
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

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of K)} {fY : Y ⟶ Spec (.of K)}

/-- A smooth morphism to a scheme locally of finite type over a complete nontrivially normed
field is open on field-valued points with the chart topology. -/
theorem isOpenMap_of_smooth (g : X ⟶ Y) (hg : g ≫ fY = fX)
    [Smooth g] [LocallyOfFiniteType fY] : IsOpenMap (map (R := K) g hg) := by
  intro s hs
  refine isOpen_iff_forall_mem_open.2 fun y hy ↦ ?_
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨U, hU, V, hV, hxV, hVU, hstd⟩ :=
    Smooth.exists_isStandardSmooth g (x.val (IsLocalRing.closedPoint K))
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let q : R →+* S := (g.appLE U V hVU).hom
  let a : K →+* R := (Spec.preimage (hU.fromSpec ≫ fY)).hom
  let : Algebra K R := a.toAlgebra
  let : Algebra R S := q.toAlgebra
  let : Algebra K S := (q.comp a).toAlgebra
  let : IsScalarTower K R S := .of_algebraMap_eq' rfl
  let φ := IsScalarTower.toAlgHom K R S
  let A := CommAlgCat.of K R
  let B := CommAlgCat.of K S
  have hA : hU.fromSpec ≫ fY = Spec.algebraMap K A :=
    (Spec.map_preimage _).symm
  have hcomm :
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hU.fromSpec = hV.fromSpec ≫ g :=
    IsAffineOpen.SpecMap_appLE_fromSpec g hU hV hVU
  have hB : hV.fromSpec ≫ fX = Spec.algebraMap K B := by
    rw [← hg, ← Category.assoc, ← hcomm, Category.assoc, hA, ← Spec.map_comp]
    rfl
  have hφ : IsOpenMap (fun z : S →ₐ[K] K ↦ z.comp φ) := by
    have : Algebra.FiniteType K R :=
      LocallyOfFiniteType.Spec_algebraMap_iff.mp (hA ▸ inferInstance)
    have : Algebra.IsStandardSmooth R S := hstd
    exact Algebra.IsStandardSmooth.isOpenMap_comap
  obtain ⟨z, rfl⟩ : x ∈ Set.range (chartPoint fX B hV.fromSpec hB) := by
    apply (mem_range_chartPoint_iff_closedPoint fX B hV.fromSpec hB x).2
    simpa only [IsAffineOpen.opensRange_fromSpec] using hxV
  have hmap (z' : S →ₐ[K] K) :
      map g hg (chartPoint fX B hV.fromSpec hB z') =
        chartPoint fY A hU.fromSpec hA (z'.comp φ) := by
    apply Subtype.ext
    simp only [map_val, chartPoint_val, Category.assoc, ← hcomm, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, AlgHom.toRingHom_eq_coe]
  let w := chartPoint fY A hU.fromSpec hA ∘ (fun z' : S →ₐ[K] K ↦ z'.comp φ)
  have hw := (isOpenEmbedding_chartPoint (R := K) fY A hU.fromSpec hA).isOpenMap.comp hφ
  refine ⟨w '' (chartPoint fX B hV.fromSpec hB ⁻¹' s), ?_,
    hw _ (hs.preimage (continuous_chartPoint fX B hV.fromSpec hB)),
    ⟨z, hx, (hmap z).symm⟩⟩
  rintro _ ⟨z', hz', rfl⟩
  exact ⟨chartPoint fX B hV.fromSpec hB z', hz', hmap z'⟩

end TauCeti.SchemePointTopology

namespace AlgHom

/-- A smooth algebra map with finite-type domain over a complete nontrivially normed
field induces an open map on point spaces by precomposition. -/
theorem isOpenMap_comap_of_smooth {K A B : Type u} [NontriviallyNormedField K]
    [CompleteSpace K] [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [Algebra.FiniteType K A] (φ : A →ₐ[K] B) (hφ : φ.toRingHom.Smooth) :
    IsOpenMap (fun x : B →ₐ[K] K ↦ x.comp φ) := by
  let f := Spec.map (CommRingCat.ofHom φ.toRingHom)
  have hf : f ≫ Spec.algebraMap K A = Spec.algebraMap K B := by
    rw [← Spec.map_comp]
    congr 1
    ext k
    exact φ.commutes k
  have : Smooth f := (HasRingHomProperty.Spec_iff (P := @Smooth)).2 hφ
  have hop := TauCeti.SchemePointTopology.isOpenMap_of_smooth f hf
  let eA := TauCeti.SchemePointTopology.affineHomeomorph (k := K) (R := K) A
  let eB := TauCeti.SchemePointTopology.affineHomeomorph (k := K) (R := K) B
  have hcomp := eA.symm.isOpenMap.comp (hop.comp eB.isOpenMap)
  convert hcomp using 1
  funext x
  apply eA.injective
  simpa only [Function.comp_apply, Homeomorph.apply_symm_apply, eA, eB, f, AlgHom.toRingHom_eq_coe,
    TauCeti.SchemePointTopology.affineHomeomorph_apply] using
    (TauCeti.SchemePointTopology.map_homEquivAlgHom_symm φ x).symm

end AlgHom
