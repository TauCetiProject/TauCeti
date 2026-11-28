/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Map
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Restriction

/-!
# Simplicial approximations

Let `K` and `L` be abstract simplicial complexes and `φ : |K| → |L|` a map of their weak
realizations. Every point `y` of `|L|` lies in the interior of a unique closed simplex, the one
spanned by its support. A simplicial map `f : K → L` is a **simplicial approximation** of `φ`
(`PreAbstractSimplicialComplex.SimplicialMap.IsSimplicialApproximation`) if for every point `x`
of `|K|`, the point `|f| x` lies in the closed simplex carrying `φ x`; that is, the support of
`|f| x` is contained in the support of `φ x`.

This is equivalent to the **star condition**: `φ` maps the open star of each vertex `v` of `K`
into the open star of `f v` in `L`
(`PreAbstractSimplicialComplex.SimplicialMap.isSimplicialApproximation_iff_mapsTo`). Conversely,
the star condition alone makes a vertex map simplicial: if a vertex map `g` satisfies it, then
the vertices of a face `σ` of `K` go to vertices in the support of `φ` at the barycenter of `σ`,
which span a face of `L` (`PreAbstractSimplicialComplex.SimplicialMap.ofMapsTo`). So `φ` has a
simplicial approximation exactly when the open star of every vertex of `K` is mapped into some
open star of `L`
(`PreAbstractSimplicialComplex.SimplicialMap.exists_isSimplicialApproximation_iff`). The
simplicial approximation theorem (Hatcher, Theorem 2C.1) meets this condition by subdividing a
finite complex `K` until its open stars refine the cover of `|K|` by the preimages of the open
stars of `L` (`AbstractSimplicialComplex.eventually_exists_isSimplicialApproximation`, in
`TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Iterated.Basic`).

A continuous map `φ` is homotopic to the realization of any simplicial approximation `f`
(`PreAbstractSimplicialComplex.SimplicialMap.IsSimplicialApproximation.homotopic`): for each
`x`, the points `|f| x` and `φ x` lie in a common closed simplex of `L`, so they are joined by a
segment in `|L|`. This straight-line homotopy is available for any two continuous maps whose
values at each point lie in a common closed simplex (`AbstractSimplicialComplex.affineHomotopy`),
with no finiteness assumption on `K` or `L`. It is the analogue of Mathlib's
`ContinuousMap.Homotopy.affine`, which does not apply here: the weak topology of `|L|` is in
general not the topology of a subspace of a topological vector space. Two simplicial
approximations of the same map are contiguous: the images of a face under them together span a
face
(`PreAbstractSimplicialComplex.SimplicialMap.IsSimplicialApproximation.image_union_image_mem`),
and contiguous simplicial maps have homotopic realizations
(`PreAbstractSimplicialComplex.SimplicialMap.homotopic_realizationMap_of_image_union_image_mem`).
Simplicial approximations compose
(`PreAbstractSimplicialComplex.SimplicialMap.IsSimplicialApproximation.comp`), and a
simplicial map is the only simplicial approximation of its own realization
(`PreAbstractSimplicialComplex.SimplicialMap.isSimplicialApproximation_realizationMap_iff`).

Simplicial approximations replace continuous self-maps of a triangulated space by simplicial
maps whose induced chain maps compute the action on homology; this is the route to the
Lefschetz fixed-point formula through traces on simplicial chains.

## Main definitions

* `AbstractSimplicialComplex.affineHomotopy`: the straight-line homotopy between two continuous
  maps into `|L|` whose values at each point lie in a common closed simplex.
* `PreAbstractSimplicialComplex.SimplicialMap.IsSimplicialApproximation`: `f` is a simplicial
  approximation of `φ`.
* `PreAbstractSimplicialComplex.SimplicialMap.ofMapsTo`: the simplicial map given by a vertex
  map satisfying the star condition.

## Main results

* `PreAbstractSimplicialComplex.SimplicialMap.isSimplicialApproximation_iff_mapsTo`: the star
  condition.
* `PreAbstractSimplicialComplex.SimplicialMap.exists_isSimplicialApproximation_iff`: existence
  of a simplicial approximation.
* `PreAbstractSimplicialComplex.SimplicialMap.IsSimplicialApproximation.homotopic`: a
  continuous map is homotopic to the realization of each of its simplicial approximations.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.C, pp. 177–178 (simplicial approximations and the
  star condition; the proof of Theorem 2C.1).
* J. R. Munkres, *Elements of Algebraic Topology*, Addison–Wesley 1984, §14 (simplicial
  approximations).
-/

public section

noncomputable section

open Set Topology TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι κ : Type*} [DecidableEq κ] {K : AbstractSimplicialComplex ι}
  {L : AbstractSimplicialComplex κ}

/-- The straight-line family between two continuous maps into `|L|` whose values at each point
lie in a common closed simplex is jointly continuous. -/
private theorem continuous_lineMap_realization (g₀ g₁ : C(Realization K, Realization L))
    (h : ∀ x, (g₀ x).val.support ∪ (g₁ x).val.support ∈ L) :
    Continuous fun p : unitInterval × Realization K =>
      (⟨AffineMap.lineMap (g₀ p.2).val (g₁ p.2).val (p.1 : ℝ),
        lineMap_mem_realization (h p.2) p.1⟩ : Realization L) := by
  -- Test continuity on the cylinders over the closed simplices of `K`. Over one simplex the
  -- homotopy only uses finitely many vertices of `L`, where the weak topology of `|L|` is the
  -- coordinate topology.
  refine continuous_prod_iff_faceInclusion.mpr fun σ => ?_
  have hc (g : C(Realization K, Realization L)) :=
    isCompact_range (g.continuous.comp (continuous_faceInclusion K σ))
  obtain ⟨V, hV⟩ := exists_finset_support_subset_of_isCompact ((hc g₀).union (hc g₁))
  have hs := isCompact_setOf_support_subset L (V : Set κ) V.finite_toSet
  have hmem (p : unitInterval × StandardSimplex σ.val) :
      AffineMap.lineMap (g₀ (faceInclusion K σ p.2)).val (g₁ (faceInclusion K σ p.2)).val
        (p.1 : ℝ) ∈ (standardGeometricComplex L).space :=
    lineMap_mem_realization (h _) p.1
  let F : unitInterval × StandardSimplex σ.val →
      {y : Realization L | (y.val.support : Set κ) ⊆ V} := fun p =>
    ⟨⟨_, hmem p⟩, by
      intro w hw
      simp only [AffineMap.lineMap_apply_module, Finset.mem_coe] at hw
      rcases Finset.mem_union.1 (Finsupp.support_add hw) with hw | hw
      · exact hV _ (Or.inl ⟨p.2, rfl⟩) (Finsupp.support_smul hw)
      · exact hV _ (Or.inr ⟨p.2, rfl⟩) (Finsupp.support_smul hw)⟩
  have hF : Continuous F := by
    refine (isClosedEmbedding_realization_coe_restrict L hs).isEmbedding.continuous_iff.mpr ?_
    have hg (g : C(Realization K, Realization L)) :
        Continuous fun p : unitInterval × StandardSimplex σ.val =>
          ((g (faceInclusion K σ p.2)).val : κ → ℝ) :=
      (continuous_realization_coe L).comp
        ((g.continuous.comp (continuous_faceInclusion K σ)).comp continuous_snd)
    have ht : Continuous fun p : unitInterval × StandardSimplex σ.val => (p.1 : ℝ) :=
      continuous_subtypeVal.comp continuous_fst
    have h1 : Continuous fun _ : unitInterval × StandardSimplex σ.val => (1 : ℝ) :=
      continuous_const
    convert ((h1.sub ht).smul (hg g₀)).add (ht.smul (hg g₁)) using 1
    funext p
    simp [F, AffineMap.lineMap_apply_module]
  exact continuous_subtypeVal.comp hF

/-- Two continuous maps into `|L|` whose values at each point of `|K|` lie in a common closed
simplex of `L` are homotopic, by the straight-line homotopy
`(t, x) ↦ (1 - t) • g₀ x + t • g₁ x` in barycentric coordinates. Neither complex is assumed
finite or locally finite. This is the analogue for weak realizations of
`ContinuousMap.Homotopy.affine`. -/
def affineHomotopy (g₀ g₁ : C(Realization K, Realization L))
    (h : ∀ x, (g₀ x).val.support ∪ (g₁ x).val.support ∈ L) : g₀.Homotopy g₁ where
  toFun p := ⟨AffineMap.lineMap (g₀ p.2).val (g₁ p.2).val (p.1 : ℝ),
    lineMap_mem_realization (h p.2) p.1⟩
  continuous_toFun := continuous_lineMap_realization g₀ g₁ h
  map_zero_left x := Subtype.ext (by simp)
  map_one_left x := Subtype.ext (by simp)

/-- The straight-line homotopy has the affine-combination barycentric coordinates. -/
@[simp]
theorem coe_affineHomotopy_apply (g₀ g₁ : C(Realization K, Realization L))
    (h : ∀ x, (g₀ x).val.support ∪ (g₁ x).val.support ∈ L) (t : unitInterval)
    (x : Realization K) :
    (affineHomotopy g₀ g₁ h (t, x) : κ →₀ ℝ) = AffineMap.lineMap (g₀ x).val (g₁ x).val (t : ℝ) :=
  (rfl)

end AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex.SimplicialMap

open AbstractSimplicialComplex

variable {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
  {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β}
  {M : AbstractSimplicialComplex γ}

/-- A simplicial map `f : K → L` is a **simplicial approximation** of a map `φ : |K| → |L|` if
`|f| x` lies in the closed simplex carrying `φ x` for every point `x`: the support of `|f| x` is
contained in the support of `φ x`. -/
def IsSimplicialApproximation
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (φ : Realization K → Realization L) : Prop :=
  ∀ x, (f.realizationMap x).val.support ⊆ (φ x).val.support

variable {f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex}
  {φ : Realization K → Realization L}

/-- A simplicial map is a simplicial approximation of `φ` when it maps the support of every
point `x` into the support of `φ x`. -/
theorem isSimplicialApproximation_iff :
    f.IsSimplicialApproximation φ ↔ ∀ x, x.val.support.image f ⊆ (φ x).val.support := by
  simp only [IsSimplicialApproximation,
    TauCeti.PreAbstractSimplicialComplex.SimplicialMap.support_realizationMap]

/-- If `φ` maps the open star of every vertex `v` of `K` into the open star of `g v`, then `g`
sends the support of every point `x` into the support of `φ x`. -/
theorem image_support_subset_of_mapsTo {g : α → β}
    (h : ∀ v, MapsTo φ (K.openStarRealization v) (L.openStarRealization (g v)))
    (x : Realization K) : x.val.support.image g ⊆ (φ x).val.support := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
  exact (L.mem_openStarRealization_iff_mem_support).1
    (h v ((K.mem_openStarRealization_iff_mem_support).2 hv))

/-- **The star condition.** A simplicial map `f` is a simplicial approximation of `φ` exactly
when `φ` maps the open star of every vertex `v` of `K` into the open star of `f v`. -/
theorem isSimplicialApproximation_iff_mapsTo :
    f.IsSimplicialApproximation φ ↔
      ∀ v, MapsTo φ (K.openStarRealization v) (L.openStarRealization (f v)) := by
  rw [isSimplicialApproximation_iff]
  constructor
  · intro h v x hx
    exact (L.mem_openStarRealization_iff_mem_support).2
      (h x (Finset.mem_image_of_mem f ((K.mem_openStarRealization_iff_mem_support).1 hx)))
  · exact fun h => image_support_subset_of_mapsTo h

/-- A simplicial approximation of `φ` sends each vertex `v` into the support of `φ` at `v`. -/
theorem IsSimplicialApproximation.apply_mem_support (hf : f.IsSimplicialApproximation φ)
    (v : α) : f v ∈ (φ (vertex K v)).val.support :=
  isSimplicialApproximation_iff.1 hf (vertex K v) (by simp)

/-- **Contiguity.** The images of a face of `K` under two simplicial approximations of the same
map together span a face of `L`. -/
theorem IsSimplicialApproximation.image_union_image_mem
    {g : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex}
    (hf : f.IsSimplicialApproximation φ) (hg : g.IsSimplicialApproximation φ) {σ : Finset α}
    (hσ : σ ∈ K) : σ.image f ∪ σ.image g ∈ L := by
  obtain ⟨x, rfl⟩ := exists_support_eq hσ
  refine L.isRelLowerSet_faces.mem_of_le (support_mem L (φ x))
    (Finset.union_subset (isSimplicialApproximation_iff.1 hf x)
      (isSimplicialApproximation_iff.1 hg x)) ?_
  exact ((K.isRelLowerSet_faces.prop_of_mem (support_mem K x)).image f).mono
    Finset.subset_union_left

/-- **Contiguous simplicial maps are homotopic.** If the images of every face of `K` under two
simplicial maps together span a face of `L`, their realizations are homotopic. -/
theorem homotopic_realizationMap_of_image_union_image_mem
    {g : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex}
    (h : ∀ σ ∈ K, σ.image f ∪ σ.image g ∈ L) : f.realizationMap.Homotopic g.realizationMap :=
  ⟨affineHomotopy f.realizationMap g.realizationMap fun x => by
    simpa only [TauCeti.PreAbstractSimplicialComplex.SimplicialMap.support_realizationMap] using
      h _ (support_mem K x)⟩

/-- The vertex map `g`, when `φ` maps the open star of every vertex `v` of `K` into the open
star of `g v`, as a simplicial map: the vertices of a face `σ` are sent into the support of `φ`
at the barycenter of `σ`, which is a face of `L`. -/
def ofMapsTo (φ : Realization K → Realization L) (g : α → β)
    (h : ∀ v, MapsTo φ (K.openStarRealization v) (L.openStarRealization (g v))) :
    SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex where
  toFun := g
  map_face' σ hσ := by
    obtain ⟨x, rfl⟩ := exists_support_eq hσ
    exact L.isRelLowerSet_faces.mem_of_le (support_mem L (φ x))
      (image_support_subset_of_mapsTo h x) ((K.isRelLowerSet_faces.prop_of_mem hσ).image g)

/-- The simplicial map given by a vertex map satisfying the star condition is that vertex map. -/
@[simp]
theorem coe_ofMapsTo (φ : Realization K → Realization L) (g : α → β)
    (h : ∀ v, MapsTo φ (K.openStarRealization v) (L.openStarRealization (g v))) :
    ⇑(ofMapsTo φ g h) = g :=
  (rfl)

/-- The simplicial map given by a vertex map satisfying the star condition is a simplicial
approximation. -/
theorem isSimplicialApproximation_ofMapsTo (φ : Realization K → Realization L) (g : α → β)
    (h : ∀ v, MapsTo φ (K.openStarRealization v) (L.openStarRealization (g v))) :
    (ofMapsTo φ g h).IsSimplicialApproximation φ :=
  isSimplicialApproximation_iff_mapsTo.2 h

/-- A map `φ : |K| → |L|` has a simplicial approximation exactly when it maps the open star of
every vertex of `K` into some open star of `L`. -/
theorem exists_isSimplicialApproximation_iff (φ : Realization K → Realization L) :
    (∃ f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex,
        f.IsSimplicialApproximation φ) ↔
      ∀ v, ∃ w, MapsTo φ (K.openStarRealization v) (L.openStarRealization w) := by
  constructor
  · rintro ⟨f, hf⟩ v
    exact ⟨f v, isSimplicialApproximation_iff_mapsTo.1 hf v⟩
  · intro h
    choose g hg using h
    exact ⟨ofMapsTo φ g hg, isSimplicialApproximation_ofMapsTo φ g hg⟩

/-- A simplicial map `f` is a simplicial approximation of the realization of a simplicial map
`g` only when `f = g`. -/
@[simp]
theorem isSimplicialApproximation_realizationMap_iff
    {g : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex} :
    f.IsSimplicialApproximation g.realizationMap ↔ f = g := by
  constructor
  · intro hf
    refine DFunLike.ext _ _ fun v => ?_
    simpa using hf.apply_mem_support v
  · rintro rfl x
    exact subset_rfl

/-- If `f` is a simplicial approximation of `φ` and `g` one of `ψ`, then `g ∘ f` is a
simplicial approximation of `ψ ∘ φ`. -/
theorem IsSimplicialApproximation.comp
    {g : SimplicialMap L.toPreAbstractSimplicialComplex M.toPreAbstractSimplicialComplex}
    {ψ : Realization L → Realization M} (hg : g.IsSimplicialApproximation ψ)
    (hf : f.IsSimplicialApproximation φ) : (g.comp f).IsSimplicialApproximation (ψ ∘ φ) := by
  rw [isSimplicialApproximation_iff_mapsTo] at hf hg ⊢
  intro v
  rw [comp_apply]
  exact (hg (f v)).comp (hf v)

/-- The straight-line homotopy from the realization of a simplicial approximation `f` of a
continuous map `φ` to `φ`: for each point `x`, the points `|f| x` and `φ x` lie in the closed
simplex carrying `φ x`. -/
def IsSimplicialApproximation.homotopy {φ : C(Realization K, Realization L)}
    (hf : f.IsSimplicialApproximation φ) : f.realizationMap.Homotopy φ :=
  affineHomotopy f.realizationMap φ fun x => by
    rw [Finset.union_eq_right.2 (hf x)]
    exact support_mem L (φ x)

/-- The straight-line homotopy of a simplicial approximation has the affine-combination
barycentric coordinates. -/
@[simp]
theorem IsSimplicialApproximation.coe_homotopy_apply {φ : C(Realization K, Realization L)}
    (hf : f.IsSimplicialApproximation φ) (t : unitInterval) (x : Realization K) :
    (hf.homotopy (t, x) : β →₀ ℝ) =
      AffineMap.lineMap (f.realizationMap x).val (φ x).val (t : ℝ) :=
  (rfl)

/-- The realization of a simplicial approximation of a continuous map `φ` is homotopic to `φ`. -/
theorem IsSimplicialApproximation.homotopic {φ : C(Realization K, Realization L)}
    (hf : f.IsSimplicialApproximation φ) : f.realizationMap.Homotopic φ :=
  ⟨hf.homotopy⟩

end PreAbstractSimplicialComplex.SimplicialMap
