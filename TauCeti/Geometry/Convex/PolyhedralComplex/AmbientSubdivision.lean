/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.SignCell.Face
public import TauCeti.Analysis.Convex.Polyhedron.SignCell.Rational
public import TauCeti.Geometry.Convex.PolyhedralComplex.CommonRefinement
public import TauCeti.Geometry.Convex.PolyhedralComplex.OfPolyhedron
public import TauCeti.Geometry.Convex.PolyhedralComplex.Subcomplex

/-!
# Sign-cell complexes and ambient subdivisions of presented polyhedra

A finite rational-normal affine arrangement `g : ι → (V →ᴬ[ℝ] ℝ)` partitions the ambient space into
its strict sign cells; their nonempty closures form a `TauCeti.FinitePolyhedralComplex`
(`TauCeti.FinitePolyhedralComplex.ofSignCells`) with support `Set.univ`. Any polyhedron whose
defining affine inequalities belong up to sign to `g` is the union of the cells of `ofSignCells`
that it contains, and those cells assemble into a subcomplex subdividing `ofPolyhedron`.

Applying `ofSignCells` to the combined inequality rows of a finite family
`P : κ → RationalAffinePolyhedron h` produces `TauCeti.FinitePolyhedralComplex.ambientSubdivision`,
a global finite rational-normal polyhedral complex subdividing `Set.univ` such that:
* every member carrier `(P k).carrier` (and every exposed subset of `(P k).carrier`) is the union
  of the cells of `ambientSubdivision P` contained in it
  (`carrier_eq_biUnion_cells_ambientSubdivision`,
  `isExposed_eq_biUnion_cells_ambientSubdivision`);
* a cell of `ambientSubdivision P` lies in `(P k).carrier` if and only if its relative interior
  meets `(P k).carrier` (`subset_carrier_iff_inter_intrinsicInterior_nonempty`);
* the cells contained in `(P k).carrier` form a subcomplex `memberSubcomplex P k` which subdivides
  `ofPolyhedron h (P k).carrier ⟨P k, rfl⟩` (`memberSubcomplex_isSubdivision_ofPolyhedron`);
* disjoint unions of families correspond to `commonRefinement`
  (`ambientSubdivision_sum_eq_commonRefinement`), and `ofSignCells` commutes with
  `Toric.IntegralAffineEquiv` (`image_ofSignCells`).

No boundedness, salience, full-dimensionality, nonemptiness of member carriers, or rationality of
affine offsets is assumed. When all defining affine functionals vanish at the origin, every cell of
`ofSignCells` contains `0`.

## References

* G. M. Ziegler, *Lectures on Polytopes*, Springer, 1995, Chapter 1 and Lecture 7.
* M. Gross, P. Hacking, S. Keel, and M. Kontsevich, *Canonical bases for cluster algebras*,
  J. Amer. Math. Soc. 31 (2018), 497–608, Appendix C.1.
* T. Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*,
  Algebr. Geom. 4 (2017), 523–561, Sections 2.2–2.5.
-/

public section

namespace TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V}

section SubsetSubcomplex

variable {h : Toric.IsIntegralLattice i}

/-- Generating a subcomplex from the ambient cells contained in a set `S` retains precisely those
cells of `C` that lie in `S`, since every face of such a cell also lies in `S`. -/
theorem mem_cells_generatedSubcomplex_setOf_subset {C : FinitePolyhedralComplex h}
    {S P : Set V} :
    P ∈ (C.generatedSubcomplex {Q | Q ⊆ S}).cells ↔ P ∈ C.cells ∧ P ⊆ S := by
  rw [mem_cells_generatedSubcomplex]
  exact ⟨fun ⟨hP, Q, _, hQS, hPQ⟩ => ⟨hP, hPQ.trans hQS⟩,
    fun ⟨hP, hPS⟩ => ⟨hP, P, hP, hPS, Set.Subset.rfl⟩⟩

end SubsetSubcomplex

section OfSignCells

variable (h : Toric.IsIntegralLattice i)

/-- The finite rational-normal polyhedral complex formed by the closures of the nonempty sign
cells of a finite rational-normal affine arrangement `g`. Arbitrary real offsets, unbounded cells,
and lineality are allowed. -/
noncomputable def ofSignCells {ι : Type*} [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear) :
    FinitePolyhedralComplex h :=
  let hfin := Convex.finite_realizedSignCellClosures g
  have hmem {P : Set V} (hP : P ∈ hfin.toFinset) : P ∈ Convex.realizedSignCellClosures g :=
    hfin.mem_toFinset.mp hP
  { cells := hfin.toFinset
    nonempty _ hP := Convex.nonempty_of_mem_realizedSignCellClosures (hmem hP)
    rational _ hP := Convex.isRationalNormalPolyhedron_of_mem_realizedSignCellClosures hg (hmem hP)
    face_closed _ hP _ hF := hfin.mem_toFinset.mpr
      (hF.isExposed.mem_realizedSignCellClosures (hmem hP) hF.nonempty)
    inter_face _ hP _ hQ _ :=
      Convex.isExposed_inter_of_mem_realizedSignCellClosures (hmem hP) (hmem hQ) }

variable {h}

/-- The cells of `ofSignCells h g hg` are precisely the realized closed sign cells of `g`. -/
@[simp]
theorem mem_cells_ofSignCells {ι : Type*} [Finite ι] {g : ι → (V →ᴬ[ℝ] ℝ)}
    {hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear} {P : Set V} :
    P ∈ (ofSignCells h g hg).cells ↔ P ∈ Convex.realizedSignCellClosures g :=
  (Convex.finite_realizedSignCellClosures g).mem_toFinset

/-- The closure of every nonempty strict sign cell of `g` is a cell of `ofSignCells h g hg`. -/
theorem closure_signCell_mem_cells_ofSignCells {ι : Type*} [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)}
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear)
    {σ : ι → SignType} (hne : (Convex.signCell g σ).Nonempty) :
    closure (Convex.signCell g σ) ∈ (ofSignCells h g hg).cells :=
  mem_cells_ofSignCells.mpr (Convex.mem_realizedSignCellClosures.mpr ⟨σ, hne, rfl⟩)

/-- Every nonempty weak sign cell of `g` is a cell of `ofSignCells h g hg`. -/
theorem weakSignCell_mem_cells_ofSignCells {ι : Type*} [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)}
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear)
    {σ : ι → SignType} (hne : (Convex.weakSignCell g σ).Nonempty) :
    Convex.weakSignCell g σ ∈ (ofSignCells h g hg).cells :=
  mem_cells_ofSignCells.mpr (Convex.weakSignCell_mem_realizedSignCellClosures hne)

/-- The sign-cell complex covers the entire ambient space. -/
@[simp]
theorem support_ofSignCells {ι : Type*} [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear) :
    (ofSignCells h g hg).support = Set.univ := by
  ext x
  simp only [mem_support, mem_cells_ofSignCells, ← Set.mem_sUnion,
    Convex.sUnion_realizedSignCellClosures, Set.mem_univ]

/-- Every sign-cell complex subdivides the single-cell complex `univ h`. -/
theorem ofSignCells_isSubdivision_univ {ι : Type*} [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear) :
    (ofSignCells h g hg).IsSubdivision (univ h) :=
  isSubdivision_iff.mpr ⟨isWeakRefinement_iff.mpr fun _ _ =>
    ⟨Set.univ, mem_cells_univ.mpr rfl, Set.subset_univ _⟩,
    (support_ofSignCells g hg).trans (support_univ (h := h)).symm⟩

/-- On an empty index type, `ofSignCells` is the trivial complex `univ h`. -/
@[simp]
theorem ofSignCells_empty {ι : Type*} [IsEmpty ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear) :
    ofSignCells h g hg = univ h := by
  apply (ofSignCells_isSubdivision_univ g hg).antisymm
  refine isSubdivision_iff.mpr ⟨isWeakRefinement_iff.mpr fun P hP => ?_,
    (support_univ (h := h)).trans (support_ofSignCells g hg).symm⟩
  obtain rfl := mem_cells_univ.mp hP
  have huniv : Convex.signCell g isEmptyElim = Set.univ :=
    Set.eq_univ_of_forall fun _ => Convex.mem_signCell.mpr fun j => isEmptyElim j
  refine ⟨Set.univ, ?_, Set.Subset.rfl⟩
  simpa only [huniv, closure_univ] using
    closure_signCell_mem_cells_ofSignCells hg (σ := isEmptyElim)
      (by rw [huniv]; exact Set.univ_nonempty)

/-- Each defining affine functional has a fixed weak sign on every cell of `ofSignCells`. -/
theorem nonneg_or_nonpos_of_mem_cells_ofSignCells {ι : Type*} [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)}
    {hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear}
    {P : Set V} (hP : P ∈ (ofSignCells h g hg).cells) (j : ι) :
    (∀ x ∈ P, 0 ≤ g j x) ∨ ∀ x ∈ P, g j x ≤ 0 := by
  obtain ⟨σ, hσ, rfl⟩ := Convex.mem_realizedSignCellClosures.mp (mem_cells_ofSignCells.mp hP)
  rw [Convex.closure_signCell hσ]
  exact Convex.nonneg_or_nonpos_of_subset_weakSignCell Set.Subset.rfl j

/-- For a homogeneous arrangement (`∀ j, g j 0 = 0`), the origin lies in every cell of
`ofSignCells`. -/
theorem zero_mem_of_mem_cells_ofSignCells {ι : Type*} [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)}
    {hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear}
    {P : Set V} (hP : P ∈ (ofSignCells h g hg).cells) (h0 : ∀ j, g j 0 = 0) :
    (0 : V) ∈ P := by
  obtain ⟨σ, hσ, rfl⟩ := Convex.mem_realizedSignCellClosures.mp (mem_cells_ofSignCells.mp hP)
  rw [Convex.closure_signCell hσ, Convex.mem_weakSignCell]
  intro j
  simp [h0 j]

/-- `ofSignCells` depends on the arrangement only pointwise and is independent of the rationality
witness. -/
theorem ofSignCells_congr {ι : Type*} [Finite ι]
    {g₁ g₂ : ι → (V →ᴬ[ℝ] ℝ)}
    {hg₁ : ∀ j, Toric.IsRationalFunctional h (g₁ j).toAffineMap.linear}
    {hg₂ : ∀ j, Toric.IsRationalFunctional h (g₂ j).toAffineMap.linear}
    (hgg : ∀ j, g₁ j = g₂ j) :
    ofSignCells h g₁ hg₁ = ofSignCells h g₂ hg₂ := by
  obtain rfl : g₁ = g₂ := funext hgg
  rfl

/-- Reindexing an arrangement along a surjective map does not change `ofSignCells`. -/
theorem ofSignCells_comp_of_surjective {ι κ : Type*} [Finite ι] [Finite κ]
    (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear)
    {α : κ → ι} (hα : Function.Surjective α)
    (hg' : ∀ k, Toric.IsRationalFunctional h ((g ∘ α) k).toAffineMap.linear :=
      fun k => hg (α k)) :
    ofSignCells h (g ∘ α) hg' = ofSignCells h g hg := by
  ext P
  simp only [mem_cells_ofSignCells, Convex.realizedSignCellClosures_comp_of_surjective g hα]

/-- If every row of `f` agrees up to sign with some row of `g`, then `ofSignCells h g hg`
subdivides `ofSignCells h f hf`. -/
theorem ofSignCells_isSubdivision_of_forall_eq_or_eq_neg {ι κ : Type*} [Finite ι] [Finite κ]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {f : κ → (V →ᴬ[ℝ] ℝ)}
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear)
    (hf : ∀ k, Toric.IsRationalFunctional h (f k).toAffineMap.linear)
    (hfg : ∀ k, ∃ j, f k = g j ∨ f k = -g j) :
    (ofSignCells h g hg).IsSubdivision (ofSignCells h f hf) := by
  refine isSubdivision_iff.mpr ⟨isWeakRefinement_iff.mpr fun P hP => ?_,
    (support_ofSignCells g hg).trans (support_ofSignCells f hf).symm⟩
  obtain ⟨Q, hQ, hPQ⟩ :=
    Convex.exists_mem_realizedSignCellClosures_subset hfg (mem_cells_ofSignCells.mp hP)
  exact ⟨Q, mem_cells_ofSignCells.mpr hQ, hPQ⟩

/-- The sign-cell complex of a disjoint union `Sum.elim g₁ g₂` is the common refinement of the
two individual sign-cell complexes. -/
theorem ofSignCells_sum_eq_commonRefinement {ι κ : Type*} [Finite ι] [Finite κ]
    (g₁ : ι → (V →ᴬ[ℝ] ℝ)) (g₂ : κ → (V →ᴬ[ℝ] ℝ))
    (hg₁ : ∀ j, Toric.IsRationalFunctional h (g₁ j).toAffineMap.linear)
    (hg₂ : ∀ k, Toric.IsRationalFunctional h (g₂ k).toAffineMap.linear)
    (hsum : ∀ a, Toric.IsRationalFunctional h (Sum.elim g₁ g₂ a).toAffineMap.linear :=
      Sum.rec hg₁ hg₂) :
    ofSignCells h (Sum.elim g₁ g₂) hsum =
      (ofSignCells h g₁ hg₁).commonRefinement (ofSignCells h g₂ hg₂) := by
  ext R
  simp only [mem_cells_ofSignCells, mem_commonRefinement_cells,
    Convex.mem_realizedSignCellClosures_sum_iff]

/-- Integral affine transport commutes with `ofSignCells` by pulling the arrangement back along
the inverse equivalence. -/
theorem image_ofSignCells {N' W ι : Type*} [AddCommGroup N']
    [NormedAddCommGroup W] [NormedSpace ℝ W] {i' : N' →+ W}
    {h' : Toric.IsIntegralLattice i'} [Finite ι]
    (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear)
    (e : Toric.IntegralAffineEquiv h h')
    (hg' : ∀ j, Toric.IsRationalFunctional h'
      ((g j).comp e.symm.toContinuousAffineMap).toAffineMap.linear := fun j =>
        e.symm.isRational_toContinuousAffineMap.map_functional (hg j)) :
    (ofSignCells h g hg).image e =
      ofSignCells h' (fun j => (g j).comp e.symm.toContinuousAffineMap) hg' := by
  have hsymm : e.toContinuousAffineEquiv.symm.toContinuousAffineMap =
      e.symm.toContinuousAffineMap := by
    ext y
    exact e.toContinuousAffineEquiv.injective (by simp)
  ext Q
  have himg := Set.ext_iff.mp
    (Convex.image_realizedSignCellClosures g e.toContinuousAffineEquiv) Q
  rw [hsymm] at himg
  rw [mem_cells_image, @mem_cells_ofSignCells N' W]
  simpa only [mem_cells_ofSignCells, Set.mem_image,
    Toric.IntegralAffineEquiv.coe_toContinuousAffineEquiv] using himg

/-- Any polyhedron presentation whose rows agree up to sign with rows of `g` has carrier equal to
the union of the cells of `ofSignCells h g hg` contained in it. -/
theorem carrier_eq_biUnion_cells_ofSignCells {ι : Type*} [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)}
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear)
    (Q : RationalAffinePolyhedron h)
    (hQ : ∀ m, ∃ j, Q.inequality m = g j ∨ Q.inequality m = -g j) :
    Q.carrier = ⋃ C ∈ (ofSignCells h g hg).cells, ⋃ (_ : C ⊆ Q.carrier), C := by
  have hcar : Q.carrier = {x | ∀ m, Q.inequality m x ≤ 0} :=
    Set.ext fun _ => RationalAffinePolyhedron.mem_carrier
  simpa only [← hcar, mem_cells_ofSignCells] using
    Convex.setOf_forall_le_eq_biUnion_realizedSignCellClosures (g := g) (f := Q.inequality) hQ

/-- For a polyhedron presentation `Q` whose rows agree up to sign with rows of `g`, the
subcomplex of `ofSignCells h g hg` consisting of cells inside `Q.carrier` has support
`Q.carrier`. -/
theorem support_generatedSubcomplex_ofSignCells {ι : Type*} [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)}
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear)
    (Q : RationalAffinePolyhedron h)
    (hQ : ∀ m, ∃ j, Q.inequality m = g j ∨ Q.inequality m = -g j) :
    ((ofSignCells h g hg).generatedSubcomplex {C | C ⊆ Q.carrier}).support = Q.carrier := by
  rw [support_generatedSubcomplex]
  exact (carrier_eq_biUnion_cells_ofSignCells hg Q hQ).symm

/-- For a polyhedron presentation `Q` whose rows agree up to sign with rows of `g`, the cells of
`ofSignCells h g hg` contained in `Q.carrier` form a subcomplex subdividing `ofPolyhedron` of
`Q.carrier`, including when `Q.carrier` is empty. -/
theorem generatedSubcomplex_ofSignCells_isSubdivision_ofPolyhedron {ι : Type*} [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)}
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear)
    (Q : RationalAffinePolyhedron h)
    (hQ : ∀ m, ∃ j, Q.inequality m = g j ∨ Q.inequality m = -g j) :
    ((ofSignCells h g hg).generatedSubcomplex {C | C ⊆ Q.carrier}).IsSubdivision
      (ofPolyhedron h Q.carrier (isRationalNormalPolyhedron_iff.mpr ⟨Q, rfl⟩)) := by
  have hQrat : IsRationalNormalPolyhedron h Q.carrier :=
    isRationalNormalPolyhedron_iff.mpr ⟨Q, rfl⟩
  refine isSubdivision_iff.mpr ⟨isWeakRefinement_iff.mpr fun C hC => ?_, ?_⟩
  · obtain ⟨hCcell, hCQ⟩ := mem_cells_generatedSubcomplex_setOf_subset.mp hC
    have hQne : Q.carrier.Nonempty := ((ofSignCells h g hg).nonempty C hCcell).mono hCQ
    exact ⟨Q.carrier, self_mem_cells_ofPolyhedron hQrat hQne, hCQ⟩
  · rw [support_generatedSubcomplex_ofSignCells hg Q hQ, support_ofPolyhedron]

end OfSignCells

section AmbientSubdivision

variable {h : Toric.IsIntegralLattice i}

/-- Subdivide the ambient space by the sign cells of all defining affine inequalities of a finite
family `P` of rational-normal polyhedron presentations. Each member `(P k).carrier` is the union
of the cells of `ambientSubdivision P` contained in it. -/
noncomputable def ambientSubdivision {κ : Type*} [Finite κ]
    (P : κ → RationalAffinePolyhedron h) : FinitePolyhedralComplex h :=
  ofSignCells h (fun a : Σ k, Fin (P k).numConstraints => (P a.1).inequality a.2)
    (fun a => (P a.1).rational_linear a.2)

/-- Membership in `(ambientSubdivision P).cells` means being a realized closed sign cell of the
combined inequality family `fun a : Σ k, Fin (P k).numConstraints => (P a.1).inequality a.2`. -/
theorem mem_cells_ambientSubdivision {κ : Type*} [Finite κ]
    {P : κ → RationalAffinePolyhedron h} {C : Set V} :
    C ∈ (ambientSubdivision P).cells ↔
      C ∈ Convex.realizedSignCellClosures
        (fun a : Σ k, Fin (P k).numConstraints => (P a.1).inequality a.2) :=
  mem_cells_ofSignCells

/-- The ambient subdivision covers the entire space `Set.univ`. -/
@[simp]
theorem support_ambientSubdivision {κ : Type*} [Finite κ]
    (P : κ → RationalAffinePolyhedron h) :
    (ambientSubdivision P).support = Set.univ :=
  support_ofSignCells _ _

/-- `ambientSubdivision P` subdivides the trivial complex `univ h`. -/
theorem ambientSubdivision_isSubdivision_univ {κ : Type*} [Finite κ]
    (P : κ → RationalAffinePolyhedron h) :
    (ambientSubdivision P).IsSubdivision (univ h) :=
  ofSignCells_isSubdivision_univ _ _

/-- The ambient subdivision of an empty family of presentations is `univ h`. -/
@[simp]
theorem ambientSubdivision_empty {κ : Type*} [IsEmpty κ]
    (P : κ → RationalAffinePolyhedron h) :
    ambientSubdivision P = univ h :=
  ofSignCells_empty _ _

/-- Every defining inequality of every member `P k` has a fixed weak sign on each cell of
`ambientSubdivision P`. -/
theorem nonneg_or_nonpos_inequality_of_mem_cells_ambientSubdivision
    {κ : Type*} [Finite κ] {P : κ → RationalAffinePolyhedron h} {C : Set V}
    (hC : C ∈ (ambientSubdivision P).cells) (k : κ) (j : Fin (P k).numConstraints) :
    (∀ x ∈ C, 0 ≤ (P k).inequality j x) ∨ ∀ x ∈ C, (P k).inequality j x ≤ 0 :=
  nonneg_or_nonpos_of_mem_cells_ofSignCells hC ⟨k, j⟩

/-- When every inequality of every member vanishes at `0`, the origin belongs to every cell of
`ambientSubdivision P`. -/
theorem zero_mem_of_mem_cells_ambientSubdivision {κ : Type*} [Finite κ]
    {P : κ → RationalAffinePolyhedron h} {C : Set V}
    (hC : C ∈ (ambientSubdivision P).cells)
    (h0 : ∀ k j, (P k).inequality j 0 = 0) :
    (0 : V) ∈ C :=
  zero_mem_of_mem_cells_ofSignCells hC (fun a => h0 a.1 a.2)

/-- At any relative interior point `x` of a cell `C` of `ambientSubdivision P`, membership in
`(P k).carrier` is equivalent to `C ⊆ (P k).carrier`. Thus the set of members containing `x`
depends only on the cell `C`, not on the choice of `x ∈ intrinsicInterior ℝ C`. -/
theorem mem_carrier_iff_subset_of_mem_intrinsicInterior
    {κ : Type*} [Finite κ] {P : κ → RationalAffinePolyhedron h} {C : Set V}
    (hC : C ∈ (ambientSubdivision P).cells) {x : V}
    (hx : x ∈ intrinsicInterior ℝ C) (k : κ) :
    x ∈ (P k).carrier ↔ C ⊆ (P k).carrier := by
  have hcar : (P k).carrier = {y | ∀ j, (P k).inequality j y ≤ 0} :=
    Set.ext fun _ => RationalAffinePolyhedron.mem_carrier
  rw [RationalAffinePolyhedron.mem_carrier, hcar]
  exact Convex.forall_le_iff_subset_of_mem_intrinsicInterior
    (fun j => ⟨⟨k, j⟩, Or.inl rfl⟩) (mem_cells_ambientSubdivision.mp hC) hx

/-- A cell of `ambientSubdivision P` lies in `(P k).carrier` if and only if its relative interior
meets `(P k).carrier`. -/
theorem subset_carrier_iff_inter_intrinsicInterior_nonempty
    {κ : Type*} [Finite κ] {P : κ → RationalAffinePolyhedron h} {C : Set V}
    (hC : C ∈ (ambientSubdivision P).cells) (k : κ) :
    C ⊆ (P k).carrier ↔ (intrinsicInterior ℝ C ∩ (P k).carrier).Nonempty := by
  have hcar : (P k).carrier = {x | ∀ j, (P k).inequality j x ≤ 0} :=
    Set.ext fun _ => RationalAffinePolyhedron.mem_carrier
  rw [hcar]
  exact Convex.subset_setOf_forall_le_iff_inter_intrinsicInterior_nonempty
    (fun j => ⟨⟨k, j⟩, Or.inl rfl⟩) (mem_cells_ambientSubdivision.mp hC)

/-- Every cell of `ambientSubdivision P` either lies entirely in `(P k).carrier` or has relative
interior disjoint from `(P k).carrier`. -/
theorem subset_or_disjoint_intrinsicInterior_carrier
    {κ : Type*} [Finite κ] {P : κ → RationalAffinePolyhedron h} {C : Set V}
    (hC : C ∈ (ambientSubdivision P).cells) (k : κ) :
    C ⊆ (P k).carrier ∨ Disjoint (intrinsicInterior ℝ C) (P k).carrier := by
  have hcar : (P k).carrier = {x | ∀ j, (P k).inequality j x ≤ 0} :=
    Set.ext fun _ => RationalAffinePolyhedron.mem_carrier
  rw [hcar]
  exact Convex.subset_or_disjoint_intrinsicInterior_setOf_forall_le
    (fun j => ⟨⟨k, j⟩, Or.inl rfl⟩) (mem_cells_ambientSubdivision.mp hC)

/-- Each member `(P k).carrier` is the union of the cells of `ambientSubdivision P` contained in
it. -/
theorem carrier_eq_biUnion_cells_ambientSubdivision {κ : Type*} [Finite κ]
    (P : κ → RationalAffinePolyhedron h) (k : κ) :
    (P k).carrier =
      ⋃ C ∈ (ambientSubdivision P).cells, ⋃ (_ : C ⊆ (P k).carrier), C :=
  carrier_eq_biUnion_cells_ofSignCells _ (P k) (fun j => ⟨⟨k, j⟩, Or.inl rfl⟩)

/-- The subcomplex of `ambientSubdivision P` consisting of all cells contained in the `k`-th
member `(P k).carrier`. -/
noncomputable def memberSubcomplex {κ : Type*} [Finite κ]
    (P : κ → RationalAffinePolyhedron h) (k : κ) : FinitePolyhedralComplex h :=
  (ambientSubdivision P).generatedSubcomplex {C | C ⊆ (P k).carrier}

/-- The cells of `memberSubcomplex P k` are precisely the cells of `ambientSubdivision P`
contained in `(P k).carrier`. -/
@[simp]
theorem mem_cells_memberSubcomplex {κ : Type*} [Finite κ]
    {P : κ → RationalAffinePolyhedron h} {k : κ} {C : Set V} :
    C ∈ (memberSubcomplex P k).cells ↔
      C ∈ (ambientSubdivision P).cells ∧ C ⊆ (P k).carrier :=
  mem_cells_generatedSubcomplex_setOf_subset

/-- `memberSubcomplex P k` is a subcomplex of `ambientSubdivision P`. -/
theorem memberSubcomplex_isSubcomplex {κ : Type*} [Finite κ]
    (P : κ → RationalAffinePolyhedron h) (k : κ) :
    (memberSubcomplex P k).IsSubcomplex (ambientSubdivision P) :=
  (ambientSubdivision P).generatedSubcomplex_isSubcomplex _

/-- The support of `memberSubcomplex P k` is `(P k).carrier`. -/
@[simp]
theorem support_memberSubcomplex {κ : Type*} [Finite κ]
    (P : κ → RationalAffinePolyhedron h) (k : κ) :
    (memberSubcomplex P k).support = (P k).carrier :=
  support_generatedSubcomplex_ofSignCells _ (P k) (fun j => ⟨⟨k, j⟩, Or.inl rfl⟩)

/-- `memberSubcomplex P k` subdivides the canonical face complex `ofPolyhedron` of `(P k).carrier`,
even when `(P k).carrier` is empty. -/
theorem memberSubcomplex_isSubdivision_ofPolyhedron {κ : Type*} [Finite κ]
    (P : κ → RationalAffinePolyhedron h) (k : κ) :
    (memberSubcomplex P k).IsSubdivision
      (ofPolyhedron h (P k).carrier (isRationalNormalPolyhedron_iff.mpr ⟨P k, rfl⟩)) :=
  generatedSubcomplex_ofSignCells_isSubdivision_ofPolyhedron _ (P k)
    (fun j => ⟨⟨k, j⟩, Or.inl rfl⟩)

/-- Every exposed subset `F` of a member `(P k).carrier` (including every face of `P k` and the
empty subset) is the union of the cells of `ambientSubdivision P` contained in `F`. -/
theorem isExposed_eq_biUnion_cells_ambientSubdivision {κ : Type*} [Finite κ]
    (P : κ → RationalAffinePolyhedron h) (k : κ) {F : Set V}
    (hF : IsExposed ℝ (P k).carrier F) :
    F = ⋃ C ∈ (ambientSubdivision P).cells, ⋃ (_ : C ⊆ F), C := by
  apply Set.Subset.antisymm
  · intro x hx
    have hPrat : IsRationalNormalPolyhedron h (P k).carrier :=
      isRationalNormalPolyhedron_iff.mpr ⟨P k, rfl⟩
    have hFcell : F ∈ (ofPolyhedron h (P k).carrier hPrat).cells :=
      (mem_cells_ofPolyhedron hPrat).mpr ⟨⟨x, hx⟩, hF⟩
    obtain ⟨C, hCmem, hCF, hxC⟩ :=
      (memberSubcomplex_isSubdivision_ofPolyhedron P k).exists_mem_cells_subset hFcell hx
    exact Set.mem_iUnion₂.mpr ⟨C, (mem_cells_memberSubcomplex.mp hCmem).1,
      Set.mem_iUnion.mpr ⟨hCF, hxC⟩⟩
  · exact Set.iUnion₂_subset fun C _ => Set.iUnion_subset fun hCF => hCF

/-- Pullback of a family of presentations along any map of finite index types yields a coarser
ambient subdivision: `ambientSubdivision P` subdivides `ambientSubdivision (P ∘ α)`. -/
theorem ambientSubdivision_isSubdivision_comp {κ κ' : Type*} [Finite κ] [Finite κ']
    (P : κ → RationalAffinePolyhedron h) (α : κ' → κ) :
    (ambientSubdivision P).IsSubdivision (ambientSubdivision (P ∘ α)) :=
  ofSignCells_isSubdivision_of_forall_eq_or_eq_neg _ _
    (fun a => ⟨⟨α a.1, a.2⟩, Or.inl rfl⟩)

/-- Reindexing a family of presentations along a surjective map leaves `ambientSubdivision`
unchanged. -/
theorem ambientSubdivision_comp_of_surjective {κ κ' : Type*} [Finite κ] [Finite κ']
    (P : κ → RationalAffinePolyhedron h) {α : κ' → κ} (hα : Function.Surjective α) :
    ambientSubdivision (P ∘ α) = ambientSubdivision P := by
  apply IsSubdivision.antisymm _ (ambientSubdivision_isSubdivision_comp P α)
  refine ofSignCells_isSubdivision_of_forall_eq_or_eq_neg _ _ ?_
  rintro ⟨k, m⟩
  obtain ⟨k', rfl⟩ := hα k
  exact ⟨⟨k', m⟩, Or.inl rfl⟩

/-- The ambient subdivision of a disjoint union `Sum.elim P₁ P₂` of two finite families is the
common refinement of their ambient subdivisions. -/
theorem ambientSubdivision_sum_eq_commonRefinement {κ₁ κ₂ : Type*} [Finite κ₁] [Finite κ₂]
    (P₁ : κ₁ → RationalAffinePolyhedron h) (P₂ : κ₂ → RationalAffinePolyhedron h) :
    ambientSubdivision (Sum.elim P₁ P₂) =
      (ambientSubdivision P₁).commonRefinement (ambientSubdivision P₂) := by
  let α : (Σ k, Fin (P₁ k).numConstraints) ⊕ (Σ k, Fin (P₂ k).numConstraints) →
      Σ k : κ₁ ⊕ κ₂, Fin (Sum.elim P₁ P₂ k).numConstraints :=
    Sum.elim (fun a => ⟨Sum.inl a.1, a.2⟩) (fun b => ⟨Sum.inr b.1, b.2⟩)
  have hα : Function.Surjective α := by
    rintro ⟨k₁ | k₂, j⟩
    · exact ⟨Sum.inl ⟨k₁, j⟩, rfl⟩
    · exact ⟨Sum.inr ⟨k₂, j⟩, rfl⟩
  rw [ambientSubdivision, ← ofSignCells_comp_of_surjective _ _ hα]
  exact (ofSignCells_congr fun x => by cases x <;> rfl).trans
    (ofSignCells_sum_eq_commonRefinement _ _ _ _)

/-- Integral affine transport carries `memberSubcomplex P k` to the subcomplex of
`(ambientSubdivision P).image e` generated by cells inside `((P k).image e).carrier`. -/
theorem image_memberSubcomplex {N' W κ : Type*} [AddCommGroup N']
    [NormedAddCommGroup W] [NormedSpace ℝ W] {i' : N' →+ W}
    {h' : Toric.IsIntegralLattice i'} [Finite κ]
    (P : κ → RationalAffinePolyhedron h) (k : κ) (e : Toric.IntegralAffineEquiv h h') :
    (memberSubcomplex P k).image e =
      ((ambientSubdivision P).image e).generatedSubcomplex
        {Q | Q ⊆ ((P k).image e).carrier} := by
  ext Q
  simp only [mem_cells_memberSubcomplex, mem_cells_generatedSubcomplex_setOf_subset,
    RationalAffinePolyhedron.carrier_image, mem_cells_image]
  constructor
  · rintro ⟨C, ⟨hC, hCP⟩, rfl⟩
    exact ⟨⟨C, hC, rfl⟩, Set.image_mono hCP⟩
  · rintro ⟨⟨C, hC, rfl⟩, hsub⟩
    refine ⟨C, ⟨hC, ?_⟩, rfl⟩
    simpa only [e.symm_image_image] using Set.image_mono (f := e.symm) hsub

end AmbientSubdivision

end TauCeti.FinitePolyhedralComplex
