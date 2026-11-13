/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.Scheme.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Hausdorff points of separated schemes

The chart topology on the points of a separated scheme over an affine base is
Hausdorff when the coefficient ring is a Hausdorff local topological ring with
open units and continuous inversion on its units. No finite type hypothesis is
needed.

On two affine charts, pairs representing the same scheme-valued point form a
closed set: the intersection of the charts is a closed subscheme of their
product over the base. The affine tensor-product homeomorphism and the closed
immersion theorem on points give this closedness. Open chart embeddings then
separate any two distinct points, even when they lie in different charts.

The main result is `TauCeti.SchemePointTopology.t2Space_of_isSeparated`.
It is a scoped instance in `TauCeti.SchemePointTopology`. Its T1 hypothesis on
the coefficient ring is equivalent to Hausdorffness for topological rings.
It applies, in particular, to separated schemes over a nonarchimedean local field.
The proof uses Mathlib's `pullback.mapDesc` description of the base change of
the diagonal, together with `PointTopology.tensorProductHomeomorph`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Prop. 3.1
  and its proof, pp. 3–4.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open scoped TensorProduct TauCeti.PointTopology TauCeti.SchemePointTopology

universe u

namespace TauCeti.SchemePointTopology

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [TopologicalSpace R] [IsTopologicalRing R] [T1Space R]

/-- The equality relation between points in two affine charts of a separated
scheme is closed in the product of the affine point spaces. -/
private theorem isClosed_eq_chartPoint [IsSeparated f]
    (A B : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) (hj : j ≫ f = Spec.algebraMap k B) :
    IsClosed {p : (A →ₐ[k] R) × (B →ₐ[k] R) |
      chartPoint f A i hi p.1 = chartPoint f B j hj p.2} := by
  -- The intersection maps by a closed immersion to the product over the base.
  let P := pullback (i ≫ f) (j ≫ f)
  let fP : P ⟶ Spec (.of k) := pullback.fst _ _ ≫ (i ≫ f)
  let fU : pullback i j ⟶ Spec (.of k) := pullback.fst i j ≫ i ≫ f
  let q : pullback i j ⟶ P := pullback.mapDesc i j f
  have hq : q ≫ fP = fU := by simp [q, fP, fU]
  let e : P ≅ Spec (.of (A ⊗[k] B)) :=
    pullback.congrHom hi hj ≪≫ pullbackSpecIso k A B
  have he₁ : e.inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
    simp [e]
  have he₂ : e.inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom) := by
    simp [e]
  have he : e.inv ≫ fP = Spec.algebraMap k (A ⊗[k] B) := by
    dsimp only [fP]
    rw [← Category.assoc, he₁, hi, ← Spec.map_comp]
    congr 1
  -- Read pairs of affine points as points of that product, keeping both projections.
  let t : (A →ₐ[k] R) × (B →ₐ[k] R) → Points (R := R) fP :=
    chartPoint fP (CommAlgCat.of k (A ⊗[k] B)) e.inv he ∘
      (PointTopology.tensorProductHomeomorph k A B R).symm
  have ht : Continuous t :=
    (continuous_chartPoint (R := R) fP (CommAlgCat.of k (A ⊗[k] B)) e.inv he).comp
      (PointTopology.tensorProductHomeomorph k A B R).symm.continuous
  have ht₁ (p : (A →ₐ[k] R) × (B →ₐ[k] R)) :
      (t p).val ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom p.1.toRingHom) := by
    simp only [t, Function.comp_apply, chartPoint_val, Category.assoc, he₁,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp [PointTopology.tensorProductHomeomorph_symm_apply_tmul]
  have ht₂ (p : (A →ₐ[k] R) × (B →ₐ[k] R)) :
      (t p).val ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom p.2.toRingHom) := by
    simp only [t, Function.comp_apply, chartPoint_val, Category.assoc, he₂,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext b
    simp [PointTopology.tensorProductHomeomorph_symm_apply_tmul]
  have hclosed : IsClosed (Set.range (map (R := R) q hq)) :=
    (isClosedMap_of_isClosedImmersion q hq).isClosed_range
  -- A pair factors through the intersection exactly when its two images agree.
  convert hclosed.preimage ht using 1
  ext p
  constructor
  · intro hp
    have hp' : Spec.map (CommRingCat.ofHom p.1.toRingHom) ≫ i =
        Spec.map (CommRingCat.ofHom p.2.toRingHom) ≫ j := by
      simpa only [chartPoint_val] using congrArg Subtype.val hp
    let z := pullback.lift _ _ hp'
    have hz : z ≫ fU = Spec.algebraMap k R := by
      dsimp only [fU, z]
      rw [pullback.lift_fst_assoc]
      simpa only [chartPoint_val, Category.assoc] using (chartPoint f A i hi p.1).property
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    apply pullback.hom_ext
    · simp [q, z, ht₁]
    · simp [q, z, ht₂]
  · rintro ⟨z, hz⟩
    have hz' := congrArg Subtype.val hz
    apply Subtype.ext
    simp only [chartPoint_val]
    rw [← ht₁ p, ← ht₂ p, ← hz']
    simp only [map_val, q, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      Category.comp_id, pullback.condition]

variable [IsLocalRing R] [IsOpenUnits R]

/-- Points of a separated scheme over a Hausdorff local topological ring with open
units and continuous inversion on its units are Hausdorff for the chart topology.
No finiteness hypothesis on the scheme is required. -/
theorem t2Space_of_isSeparated [IsSeparated f] : T2Space (Points (R := R) f) := by
  refine ⟨fun x y hxy ↦ ?_⟩
  obtain ⟨A, i, hi, _, a, rfl⟩ := exists_mem_range_chartPoint f x
  obtain ⟨B, j, hj, _, b, rfl⟩ := exists_mem_range_chartPoint f y
  have hopen := (isClosed_eq_chartPoint (R := R) f A B i j hi hj).isOpen_compl
  obtain ⟨s, t, hs, ht, ha, hb, hst⟩ := isOpen_prod_iff.1 hopen a b hxy
  refine ⟨chartPoint f A i hi '' s, chartPoint f B j hj '' t,
    (isOpenEmbedding_chartPoint f A i hi).isOpenMap _ hs,
    (isOpenEmbedding_chartPoint f B j hj).isOpenMap _ ht,
    ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro _ ⟨a', ha', rfl⟩ ⟨b', hb', heq⟩
  have hp : (a', b') ∈ s ×ˢ t := ⟨ha', hb'⟩
  exact hst hp heq.symm

attribute [scoped instance] t2Space_of_isSeparated

end TauCeti.SchemePointTopology
