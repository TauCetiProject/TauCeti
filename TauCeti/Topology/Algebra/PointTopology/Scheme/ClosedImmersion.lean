/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.Scheme.Functoriality
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed immersions on scheme-valued points

A closed immersion of schemes over an affine base induces a closed embedding on
points over a local topological ring with open units and continuous inversion on
its units, provided the coefficient ring is T1. No finiteness or separation
hypothesis on the schemes is needed.

The result lets closed subschemes carry their subspace point topology, just as open
subschemes do. On each affine target chart, the inverse image is the spectrum of a
quotient algebra. Its points are the closed locus on which the defining ideal
vanishes. These affine descriptions glue using the open-chart topology.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Prop. 2.1 and
  Prop. 3.1, pp. 2–4.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open scoped TauCeti.PointTopology TauCeti.SchemePointTopology

universe u

namespace TauCeti.SchemePointTopology

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}

/-- The affine point description of the pullback square identifies the inverse image
of a scheme-point image with the image of the corresponding algebra-point map. -/
private theorem preimage_chartPoint_image_map
    (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (A B : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ Y) (j : Spec (.of B) ⟶ X)
    (hi : i ≫ fY = Spec.algebraMap k A) (hj : j ≫ fX = Spec.algebraMap k B)
    (φ : A →ₐ[k] B)
    (h : IsPullback j (Spec.map (CommRingCat.ofHom φ.toRingHom)) g i)
    (s : Set (Points (R := R) fX)) :
    chartPoint fY A i hi ⁻¹' (map g hg '' s) =
      (fun z : B →ₐ[k] R ↦ z.comp φ) '' (chartPoint fX B j hj ⁻¹' s) := by
  simp only [AlgHom.toRingHom_eq_coe] at h
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hc : x.val ≫ g = Spec.map (CommRingCat.ofHom y.toRingHom) ≫ i :=
      by simpa only [map_val, chartPoint_val] using congrArg Subtype.val hxy
    let z := h.lift x.val (Spec.map (CommRingCat.ofHom y.toRingHom)) hc
    have hz : z ≫ Spec.algebraMap k B = Spec.algebraMap k R := by
      rw [← hj, ← Category.assoc, h.lift_fst, x.property]
    let b : B →ₐ[k] R := Spec.homEquivAlgHom ⟨z, hz⟩
    have hb : Spec.map (CommRingCat.ofHom (b : B →+* R)) = z := by
      rw [← AlgHom.toRingHom_eq_coe, ← Spec.homEquivAlgHom_symm_apply_val,
        Equiv.symm_apply_apply]
    refine ⟨b, ?_, ?_⟩
    · have : chartPoint fX B j hj b = x := by
        apply Subtype.ext
        rw [chartPoint_val, AlgHom.toRingHom_eq_coe, hb]
        exact h.lift_fst _ _ _
      simpa only [Set.mem_preimage, this] using hx
    · apply Spec.homEquivAlgHom.symm.injective
      apply Subtype.ext
      simp only [Spec.homEquivAlgHom_symm_apply_val, AlgHom.toRingHom_eq_coe,
        AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp]
      rw [hb]
      exact h.lift_snd _ _ _
  · rintro ⟨b, hb, rfl⟩
    refine ⟨chartPoint fX B j hj b, hb, ?_⟩
    apply Subtype.ext
    simp only [map_val, chartPoint_val, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rw [h.w]

variable [TopologicalSpace R] [T1Space R]

/-- A closed immersion over the base is a closed map on points with T1 coefficients.
This property of the chart topology needs neither locality nor hypotheses on units. -/
theorem isClosedMap_of_isClosedImmersion (g : X ⟶ Y) (hg : g ≫ fY = fX)
    [IsClosedImmersion g] : IsClosedMap (map (R := R) g hg) := by
  intro s hs
  rw [← isOpen_compl_iff, isOpen_iff]
  intro A i hi _
  suffices IsClosed (chartPoint fY A i hi ⁻¹' (map g hg '' s)) by
    simpa only [Set.preimage_compl] using this.isOpen_compl
  let P := pullback g i
  let q : P ⟶ Spec (.of A) := pullback.snd g i
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp (inferInstance : IsClosedImmersion q)
  let B := CommAlgCat.of k (A ⧸ I)
  let φ : A →ₐ[k] B := Ideal.Quotient.mkₐ k I
  let j : Spec (.of B) ⟶ X := e.inv ≫ pullback.fst g i
  have he' : pullback.snd g i = e.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    simpa only [q, φ, Ideal.Quotient.mkₐ_toRingHom] using he
  have hcomm : j ≫ g = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ i := by
    rw [Category.assoc, pullback.condition, he']
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hj : j ≫ fX = Spec.algebraMap k B := by
    rw [← hg, ← Category.assoc, hcomm, Category.assoc, hi]
    simpa only [Spec.homEquivAlgHom_symm_apply_val] using
      (Spec.homEquivAlgHom.symm φ).property
  have hpb : IsPullback j (Spec.map (CommRingCat.ofHom φ.toRingHom)) g i := by
    have h := IsPullback.of_hasPullback g i
    exact h.of_iso' e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]; rfl)
      (by simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, he',
        Iso.inv_hom_id_assoc]) (by simp) (by simp)
  rw [preimage_chartPoint_image_map g hg A B i j hi hj φ hpb]
  exact (PointTopology.isClosedEmbedding_comap_of_surjective φ
    (Ideal.Quotient.mk_surjective)).isClosedMap _
      (hs.preimage (continuous_chartPoint fX B j hj))

variable [ContinuousMul R] [IsLocalRing R] [IsOpenUnits R]

/-- A closed immersion over the base induces a closed embedding on points over a local
T1 coefficient ring with continuous multiplication, open units and continuous inversion
on its units. -/
theorem isClosedEmbedding_of_isClosedImmersion (g : X ⟶ Y) (hg : g ≫ fY = fX)
    [IsClosedImmersion g] : IsClosedEmbedding (map (R := R) g hg) :=
  .of_continuous_injective_isClosedMap (continuous_map g hg) (map_injective g hg)
    (isClosedMap_of_isClosedImmersion g hg)

end TauCeti.SchemePointTopology
