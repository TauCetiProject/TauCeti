/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.Scheme.Basic
public import TauCeti.Topology.Algebra.PointTopology.Localization
public import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Affine charts are open on scheme-valued points

Over a local topological ring with open units and continuous inversion on the units,
every affine open chart induces an open embedding on points. Thus the chart topology
really glues the coordinate-evaluation topologies, without finiteness or separation
assumptions on the scheme or coefficient ring.

The overlap argument refines a neighbourhood of the image of the closed point to a
principal open. Its points form an open subspace by the localization theorem. This
also shows why locality of the coefficient ring matters: containing the closed point
ensures that the entire scheme-valued point factors through that principal open.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Prop. 3.1 and its
  proof, pp. 3–4.
-/

public section

open CategoryTheory AlgebraicGeometry Topology
open scoped TauCeti.PointTopology TauCeti.SchemePointTopology

universe u

namespace TauCeti.SchemePointTopology

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A point in the overlap of two affine charts has a principal-open neighbourhood in
one chart which factors through the other chart. -/
private theorem exists_overlap_factorization [IsLocalRing R]
    (A B : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) (hj : j ≫ f = Spec.algebraMap k B)
    [IsOpenImmersion i] (x : B →ₐ[k] R)
    (hx : chartPoint f B j hj x ∈ Set.range (chartPoint f A i hi)) :
    ∃ (b : B) (ψ : A →ₐ[k] Localization.Away b), IsUnit (x b) ∧
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ i =
        Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b))) ≫ j := by
  let q : PrimeSpectrum B := (IsLocalRing.closedPoint R).comap x.toRingHom
  have hq : q ∈ j ⁻¹ᵁ i.opensRange := by
    obtain ⟨y, hy⟩ := hx
    have h := (mem_range_chartPoint_iff f A i hi (chartPoint f B j hj x)).1 ⟨y, hy⟩
    have hq' := h (Set.mem_range_self (IsLocalRing.closedPoint R))
    rw [chartPoint_val] at hq'
    -- `Spec R` and `PrimeSpectrum R` have the same underlying points; applying the
    -- composite morphism here also computes its two component maps.
    exact hq'
  obtain ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, hb, hsub⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hq (j ⁻¹ᵁ i.opensRange).isOpen
  let L := Localization.Away b
  let ℓ : Spec (.of L) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap B L))
  have hrange : Set.range (ℓ ≫ j) ⊆ Set.range i := by
    rintro _ ⟨z, rfl⟩
    apply hsub
    exact (PrimeSpectrum.localization_away_comap_range L b).le ⟨z, rfl⟩
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : i.IsOver (Spec (.of k)) := ⟨hi⟩
  have hbase : (ℓ ≫ j) ≫ f = Spec.algebraMap k L := by
    rw [Category.assoc, hj, ← Spec.map_comp]
    congr 1
  have : (ℓ ≫ j).IsOver (Spec (.of k)) := ⟨hbase⟩
  obtain ⟨ψ, hψ⟩ := AlgebraicGeometry.exists_spec_map_comp_eq_of_range_subset
    (R := k) i (ℓ ≫ j) hrange
  refine ⟨b, ψ, ?_, hψ⟩
  exact IsLocalRing.notMem_maximalIdeal.mp <| (PrimeSpectrum.mem_basicOpen b q).1 hb

variable [TopologicalSpace R] [ContinuousMul R] [IsLocalRing R] [IsOpenUnits R]

/-- The overlap of two affine chart point spaces is open, with the topology inherited
from either chart: pulling back the image of an open set in one chart is open in the other. -/
private theorem isOpen_preimage_chartPoint_image
    (A B : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) (hj : j ≫ f = Spec.algebraMap k B)
    [IsOpenImmersion i] {s : Set (A →ₐ[k] R)} (hs : IsOpen s) :
    IsOpen (chartPoint f B j hj ⁻¹' (chartPoint f A i hi '' s)) := by
  refine isOpen_iff_forall_mem_open.2 fun x hx ↦ ?_
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, ψ, hb, hψ⟩ := exists_overlap_factorization f A B i j hi hj x ⟨a, hax⟩
  let v : (Localization.Away b →ₐ[k] R) → (B →ₐ[k] R) :=
    fun y ↦ y.comp (IsScalarTower.toAlgHom k B (Localization.Away b))
  let w : (Localization.Away b →ₐ[k] R) → (A →ₐ[k] R) := fun y ↦ y.comp ψ
  have hv : IsOpenEmbedding v := PointTopology.isOpenEmbedding_localization b
    IsOpenUnits.isOpenEmbedding_unitsVal.isEmbedding (by
      exact (IsOpenUnits.isOpenEmbedding_unitsVal (M := R)).isOpen_range)
  have hcomm (y : Localization.Away b →ₐ[k] R) :
      chartPoint f A i hi (w y) = chartPoint f B j hj (v y) := by
    apply Subtype.ext
    simp only [chartPoint_val, w, v, AlgHom.toRingHom_eq_coe,
      AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    exact congrArg (fun p ↦ Spec.map (CommRingCat.ofHom y.toRingHom) ≫ p) hψ
  have hxv : x ∈ Set.range v := by
    rwa [IsLocalization.Away.range_comp_toAlgHom b]
  obtain ⟨y, hy⟩ := hxv
  refine ⟨v '' (w ⁻¹' s), ?_, hv.isOpenMap _ (hs.preimage
    (PointTopology.continuous_comap ψ)), ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨w z, hz, hcomm z⟩
  · refine ⟨y, ?_, hy⟩
    have hwy : w y = a := chartPoint_injective f A i hi <| by
      rw [hcomm, hy, ← hax]
    simpa only [Set.mem_preimage, hwy] using ha

/-- An affine open chart is open on points over a local topological ring with open units
and continuous inversion on the units. -/
private theorem isOpenMap_chartPoint (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) [IsOpenImmersion i] :
    IsOpenMap (chartPoint (R := R) f A i hi) := by
  intro s hs
  exact (isOpen_iff f _).2 fun B j hj _ ↦
    isOpen_preimage_chartPoint_image f A B i j hi hj hs

/-- Every affine open chart identifies its coordinate-evaluation point space with an open
subspace of the scheme's point space. -/
theorem isOpenEmbedding_chartPoint (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) [IsOpenImmersion i] :
    IsOpenEmbedding (chartPoint (R := R) f A i hi) :=
  .of_continuous_injective_isOpenMap (continuous_chartPoint f A i hi)
    (chartPoint_injective f A i hi) (isOpenMap_chartPoint f A i hi)

/-- A morphism from an affine scheme is continuous on points over a local topological
ring with open units and continuous inversion on the units. Unlike `continuous_chartPoint`,
the morphism need not be an open immersion. -/
theorem continuous_chartPoint_of_isLocalRing (A : CommAlgCat.{u} k)
    (i : Spec (.of A) ⟶ X) (hi : i ≫ f = Spec.algebraMap k A) :
    Continuous (chartPoint (R := R) f A i hi) := by
  refine continuous_def.2 fun s hs ↦ isOpen_iff_forall_mem_open.2 fun x hx ↦ ?_
  obtain ⟨B, j, hj, hjOpen, y, hy⟩ :=
    exists_mem_range_chartPoint f (chartPoint f A i hi x)
  have := hjOpen
  refine ⟨chartPoint f A i hi ⁻¹' (chartPoint f B j hj ''
    (chartPoint f B j hj ⁻¹' s)), ?_, ?_, ?_⟩
  · exact Set.preimage_mono (Set.image_preimage_subset _ _)
  · exact isOpen_preimage_chartPoint_image f B A j i hj hi
      (hs.preimage (continuous_chartPoint f B j hj))
  · exact ⟨y, by simpa only [Set.mem_preimage, hy] using hx, hy⟩

end TauCeti.SchemePointTopology
