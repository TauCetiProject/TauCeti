/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization

/-!
# Subcomplexes in the weak realization topology

An inclusion of abstract simplicial complexes realizes to a closed embedding, without a
finiteness or local-finiteness hypothesis. Thus a subcomplex has exactly the subspace topology
inside the larger polyhedron. This permits closed subcomplexes to be used as local models and
as the fixed parts of geometric deformations.

Closedness in the weak topology is tested on each closed simplex. On any one simplex, a
subcomplex meets it in finitely many faces. This finite-face argument proves that inclusion
sends every closed subset to a closed subset, even when the whole complex is infinite.

For a precomplex, its polyhedron is the subset of ambient realization points whose supports
are its faces. The closed-set and continuity criteria apply to this actual subset, so links
and deletions introduce no extra vertices. Continuity into an arbitrary topological space
is determined by restriction to the subcomplex's closed simplices.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (polyhedra and their weak topology).
-/

public section

noncomputable section

open Set Topology TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} {K L : AbstractSimplicialComplex ι}

/-- A point of the larger realization lies in the subcomplex precisely when its carrier is a
face of that subcomplex. -/
-- Normalize to carrier membership before `Set.mem_range` expands the existential.
@[simp 1100]
theorem mem_range_realizationMap (h : K ≤ L) (x : Realization L) :
    x ∈ range (realizationMap h) ↔ x.1.support ∈ K := by
  constructor
  · rintro ⟨y, rfl⟩
    simpa only [realizationMap_val] using support_mem K y
  · intro hx
    refine ⟨⟨x.1, mem_realization_iff.mpr
      ⟨x.1.support, hx, by simpa only [carrier_val] using mem_convexHull_carrier L x⟩⟩, ?_⟩
    exact Subtype.ext (realizationMap_val h _)

/-- If every point of `s` is carried by a precomplex `P`, closedness of `s` can be tested
only on the faces of `P`. Unlike an abstract complex, `P` need not contain every ambient
vertex; in particular, this applies to links, closed stars, and deletions. -/
theorem isClosed_of_faceInclusion {P : PreAbstractSimplicialComplex ι}
    (hP : P ≤ L.toPreAbstractSimplicialComplex) {s : Set (Realization L)}
    (hsupp : ∀ x ∈ s, x.1.support ∈ P)
    (hs : ∀ (σ : Finset ι) (hσ : σ ∈ P),
      IsClosed (faceInclusion L ⟨σ, hP hσ⟩ ⁻¹' s)) : IsClosed s := by
  classical
  apply isClosed_iff_faceInclusion.mpr
  intro τ
  -- Only the finitely many subfaces of `τ` can contribute to this inverse image.
  let A := {σ : Finset ι | σ ⊆ τ.1 ∧ σ ∈ P}
  have hAfin : A.Finite := τ.1.powerset.finite_toSet.subset fun σ hσ =>
    Finset.mem_powerset.mpr hσ.1
  let j (σ : A) : StandardSimplex σ.1 → StandardSimplex τ.1 :=
    Set.inclusion (convexHull_mono
      (Finset.coe_subset.mpr (Finset.image_mono _ σ.2.1)))
  have hjc (σ : A) : Continuous (j σ) := by
    apply continuous_induced_rng.mpr
    exact continuous_induced_dom
  have hjclosed (σ : A) : IsClosedMap (j σ) := by
    let : CompactSpace (StandardSimplex σ.1) :=
      (Finset.standardSimplexHomeomorph σ.1).symm.compactSpace
    have ht : IsEmbedding (fun x : StandardSimplex τ.1 => (x.1 : ι → ℝ)) :=
      .induced (fun x y hxy => Subtype.ext (Finsupp.ext fun v => congrFun hxy v))
    let : T2Space (StandardSimplex τ.1) := ht.t2Space
    exact (hjc σ).isClosedMap
  have heq : faceInclusion L τ ⁻¹' s =
      ⋃ σ : A, j σ '' (faceInclusion L ⟨σ.1, hP σ.2.2⟩ ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      let σ : A := ⟨x.1.support, StandardSimplex.support_subset x, by
        simpa only [faceInclusion_val] using hsupp _ hx⟩
      let z : StandardSimplex σ.1 := ⟨x.1, StandardSimplex.mem_convexHull_support x⟩
      refine mem_iUnion.mpr ⟨σ, z, ?_, ?_⟩
      · have hz : faceInclusion L ⟨σ.1, hP σ.2.2⟩ z = faceInclusion L τ x :=
          Subtype.ext (by simp only [faceInclusion_val]; rfl)
        simpa only [mem_preimage, hz] using hx
      · exact Subtype.ext rfl
    · intro hx
      obtain ⟨σ, z, hz, hzx⟩ := mem_iUnion.mp hx
      have he : faceInclusion L ⟨σ.1, hP σ.2.2⟩ z = faceInclusion L τ x := by
        apply Subtype.ext
        simpa only [faceInclusion_val] using congrArg Subtype.val hzx
      simpa only [mem_preimage, he] using hz
  rw [heq]
  let : Finite A := hAfin.to_subtype
  exact isClosed_iUnion_of_finite fun σ => hjclosed σ _ (hs σ.1 σ.2.2)

/-- The support of every point of a face of a precomplex is itself a face of that
precomplex, even when the precomplex omits ambient vertices. -/
theorem support_faceInclusion_mem {P : PreAbstractSimplicialComplex ι}
    (hP : P ≤ L.toPreAbstractSimplicialComplex) {σ : Finset ι} (hσ : σ ∈ P)
    (x : StandardSimplex σ) : (faceInclusion L ⟨σ, hP hσ⟩ x).1.support ∈ P := by
  rw [faceInclusion_val]
  exact P.isRelLowerSet_faces.mem_of_le hσ (StandardSimplex.support_subset x)
    (by simpa only [faceInclusion_val] using
      L.isRelLowerSet_faces.prop_of_mem (support_mem L (faceInclusion L ⟨σ, hP hσ⟩ x)))

/-- The polyhedron of any precomplex inside a weak realization is closed, including when the
precomplex omits ambient vertices or has no faces. -/
theorem isClosed_setOf_support_mem {P : PreAbstractSimplicialComplex ι}
    (hP : P ≤ L.toPreAbstractSimplicialComplex) :
    IsClosed {x : Realization L | x.1.support ∈ P} := by
  apply isClosed_of_faceInclusion hP (fun _ hx => hx)
  intro σ hσ
  have heq : faceInclusion L ⟨σ, hP hσ⟩ ⁻¹'
      {x : Realization L | x.1.support ∈ P} = univ := by
    ext x
    exact iff_true_intro (support_faceInclusion_mem hP hσ x)
  exact heq.symm ▸ isClosed_univ

/-- A map defined on a precomplex polyhedron is continuous exactly when its composition
with each canonical face map into that polyhedron is continuous. The domain carries the
subspace topology of the ambient weak realization, without any finiteness assumption. -/
theorem continuous_subtype_iff_faceInclusion {X : Type*} [TopologicalSpace X]
    {P : PreAbstractSimplicialComplex ι} (hP : P ≤ L.toPreAbstractSimplicialComplex)
    {g : {x : Realization L // x.1.support ∈ P} → X} :
    Continuous g ↔ ∀ (σ : Finset ι) (hσ : σ ∈ P),
      Continuous (g ∘ fun x : StandardSimplex σ =>
        ⟨faceInclusion L ⟨σ, hP hσ⟩ x, support_faceInclusion_mem hP hσ x⟩) := by
  constructor
  · intro hg σ hσ
    exact hg.comp ((continuous_faceInclusion L ⟨σ, hP hσ⟩).subtype_mk
      (support_faceInclusion_mem hP hσ))
  · intro hg
    apply continuous_iff_isClosed.mpr
    intro t ht
    rw [(isClosed_setOf_support_mem hP).isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed]
    apply isClosed_of_faceInclusion hP
    · rintro x ⟨y, _, rfl⟩
      exact y.2
    · intro σ hσ
      convert ht.preimage (hg σ hσ) using 1
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        have he : y = ⟨faceInclusion L ⟨σ, hP hσ⟩ x,
            support_faceInclusion_mem hP hσ x⟩ := Subtype.ext hxy
        simpa only [he, mem_preimage, Function.comp_apply] using hy
      · intro hx
        exact ⟨⟨faceInclusion L ⟨σ, hP hσ⟩ x, support_faceInclusion_mem hP hσ x⟩, hx, rfl⟩

/-- Continuity on a subcomplex can be checked on its closed simplices, with the subspace
topology inherited from the ambient weak realization. The subcomplex may omit vertices. -/
theorem continuousOn_iff_faceInclusion {X : Type*} [TopologicalSpace X]
    {P : PreAbstractSimplicialComplex ι} (hP : P ≤ L.toPreAbstractSimplicialComplex)
    {f : Realization L → X} :
    ContinuousOn f {x | x.1.support ∈ P} ↔
      ∀ (σ : Finset ι) (hσ : σ ∈ P), Continuous (f ∘ faceInclusion L ⟨σ, hP hσ⟩) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_iff_faceInclusion hP

/-- Realizing a subcomplex inclusion gives a closed embedding for the weak topologies. No
finiteness assumption on the complexes or their ambient vertex type is needed. -/
theorem isClosedEmbedding_realizationMap (h : K ≤ L) :
    IsClosedEmbedding (realizationMap h) := by
  refine .of_continuous_injective_isClosedMap (continuous_realizationMap h)
    (realizationMap_injective h) ?_
  intro s hs
  apply isClosed_of_faceInclusion (P := K.toPreAbstractSimplicialComplex) h
  · rintro x ⟨y, hy, rfl⟩
    simpa only [realizationMap_val, mem_toPreAbstractSimplicialComplex] using support_mem K y
  · intro σ hσ
    rw [← realizationMap_comp_faceInclusion h ⟨σ, hσ⟩, preimage_comp,
      Set.preimage_image_eq _ (realizationMap_injective h)]
    exact hs.preimage (continuous_faceInclusion K ⟨σ, hσ⟩)

end AbstractSimplicialComplex
