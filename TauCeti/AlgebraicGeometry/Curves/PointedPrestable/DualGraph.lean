/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.DualGraph.Iso
public import TauCeti.AlgebraicGeometry.Curves.PointedPrestable.Category

/-!
# The dual graph of a pointed prestable curve

Over a separably closed field `K`, the dual graph `AlgebraicGeometry.Scheme.dualGraph` of a
prestable curve records the irreducible components of its normalization, their genera and the
branches over the nodes, and places markings at given points of the smooth locus. For a pointed
prestable curve `P` over `K`, the markings are the values of its sections at the point of `Spec K`
(`TauCeti.AlgebraicGeometry.PointedPrestableFamily.markingPoint`).

This file develops the geometric and functorial API of `P.dualGraph`:

* geometric formulas for `numMarkings`, special flags (`valence + numMarkings`), and
  `logCanonicalDegree`;
* functorial `DualGraph.Iso` equivalences under pointed curve isomorphisms (`dualGraphIso`) and
  extensions of separably closed base fields (`dualGraphPullbackIso`), together with invariance of
  semistability, stability, arithmetic genus, and first Betti number;
* specialization of `logCanonicalDegree` on smooth pointed curves (`logCanonicalDegree_ofSmooth`);
* geometric classification of unstable components (`dualGraph_logCanonicalDegree_nonpos_iff`) into
  geometric rational tails with at most one marking and unmarked geometric rational bridges.

## Main definitions

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.dualGraph`: the dual graph of a pointed
  prestable curve over a separably closed field, with its markings.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.dualGraphIso`: isomorphism of dual graphs
  induced by an isomorphism of pointed prestable curves.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.dualGraphPullbackIso`: isomorphism of dual
  graphs under base change along an extension of separably closed fields.

## Main results

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.dualGraph_reindex`: reindexing the markings
  of the curve reindexes the markings of its dual graph.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.ncard_specialPoints_eq_valence_add_numMarkings`
  and `TauCeti.AlgebraicGeometry.PointedPrestableFamily.logCanonicalDegree_dualGraph`: geometric
  formulas for special flags and `logCanonicalDegree`.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.logCanonicalDegree_ofSmooth`: on a smooth
  `n`-pointed curve of genus `g`, `logCanonicalDegree v = 2g - 2 + n`.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.dualGraph_logCanonicalDegree_nonpos_iff`:
  geometric classification of components of nonpositive log-canonical degree on a reducible curve.

## References

* F. F. Knudsen, *The projectivity of the moduli space of stable curves, II: The stacks
  `M_{g,n}`*, Math. Scand. 52 (1983), 161–199, Definition 1.1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Set

namespace TauCeti.AlgebraicGeometry

universe u

namespace PointedPrestableFamily

section Basic

variable {K : Type u} [Field K] {m n : ℕ} (P : PointedPrestableFamily (Spec (.of K)) n)

/-- The **dual graph** of a pointed prestable curve over a separably closed field: the dual graph
`AlgebraicGeometry.Scheme.dualGraph` of its total space, with the `i`th marking at the point of
the `i`th section. -/
abbrev dualGraph [IsSepClosed K] : DualGraph.{u} (Fin n) :=
  P.total.dualGraph P.markingPoint

/-- The dual graph of a reindexed pointed prestable curve is the dual graph with reindexed
markings. -/
@[simp]
theorem dualGraph_reindex [IsSepClosed K] (e : Fin m ↪ Fin n) :
    (P.reindex e).dualGraph = P.dualGraph.reindex e := by
  rw [dualGraph, show (P.reindex e).markingPoint = P.markingPoint ∘ e from
    funext (P.markingPoint_reindex e)]
  exact P.total.dualGraph_comp P.markingPoint e

end Basic

section SepClosed

variable {K : Type u} [Field K] [IsSepClosed K] {n : ℕ}
  (P : PointedPrestableFamily (Spec (.of K)) n)

/-- `v` carries the `i`th marking iff `range (P.marking i)` lies in the corresponding component of
`P.total`. -/
theorem dualGraph_marking_eq_iff (i : Fin n) (v : P.dualGraph.Vertex) :
    P.dualGraph.marking i = v ↔
      Set.range (P.marking i) ⊆
        ((P.total.blowupComponentEquiv K PrestableFamily.atWorstNodalOfRelativeDimensionOne
          (P.total.dualGraphVertexEquiv P.markingPoint v) :
            irreducibleComponents P.total) : Set P.total) := by
  rw [P.total.dualGraph_marking_eq_iff_mem_blowupComponentEquiv P.markingPoint i v,
    P.range_marking_eq_singleton i, singleton_subset_iff]

/-- `numMarkings v` equals the number of marked points on the corresponding component of
`P.total`. -/
theorem numMarkings_dualGraph_eq_ncard_inter_iUnion_marking (v : P.dualGraph.Vertex) :
    let E := P.total.blowupComponentEquiv K PrestableFamily.atWorstNodalOfRelativeDimensionOne
      (P.total.dualGraphVertexEquiv P.markingPoint v)
    P.dualGraph.numMarkings v = ((E : Set P.total) ∩ ⋃ i, Set.range (P.marking i)).ncard := by
  dsimp only
  let := P.dualGraph.vertexDecidableEq
  let E := P.total.blowupComponentEquiv K PrestableFamily.atWorstNodalOfRelativeDimensionOne
    (P.total.dualGraphVertexEquiv P.markingPoint v)
  let S : Finset (Fin n) := Finset.univ.filter fun i ↦ P.dualGraph.marking i = v
  have himg : (Subtype.val ∘ P.markingPoint) '' (S : Set (Fin n)) =
      (E : Set P.total) ∩ ⋃ i, Set.range (P.marking i) := Set.ext fun x ↦ by
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, mem_image,
      Function.comp_apply, mem_inter_iff, mem_iUnion, P.range_marking_eq_singleton,
      mem_singleton_iff]
    exact ⟨fun ⟨i, hi, hx⟩ ↦
      ⟨hx ▸ (P.total.dualGraph_marking_eq_iff_mem_blowupComponentEquiv P.markingPoint i v).mp hi,
        i, hx.symm⟩,
      fun ⟨hxE, i, hx⟩ ↦ ⟨i,
        (P.total.dualGraph_marking_eq_iff_mem_blowupComponentEquiv P.markingPoint i v).mpr
          (hx ▸ hxE), hx.symm⟩⟩
  rw [DualGraph.numMarkings_def, ← himg,
    Set.ncard_image_of_injective _ (Subtype.val_injective.comp P.injective_markingPoint),
    Set.ncard_coe_finset]

/-- `numMarkings v` equals the number of points of `v` in `Bl P.total` lying over the markings. -/
theorem numMarkings_dualGraph_eq_ncard_preimage_iUnion_marking (v : P.dualGraph.Vertex) :
    P.dualGraph.numMarkings v =
      ((P.total.dualGraphVertexEquiv P.markingPoint v : Set (P.total.singularLocus K).blowup) ∩
        (P.total.singularLocus K).blowupToBase ⁻¹' ⋃ i, Set.range (P.marking i)).ncard := by
  let ν := (P.total.singularLocus K).blowupToBase
  let v' := P.total.dualGraphVertexEquiv P.markingPoint v
  let E := P.total.blowupComponentEquiv K PrestableFamily.atWorstNodalOfRelativeDimensionOne v'
  let M : Set P.total := ⋃ i, Set.range (P.marking i)
  have hMU : M ⊆ (P.total ↘ Spec (.of K)).smoothLocus :=
    iUnion_subset fun i ↦ P.range_marking_subset_smoothLocus i
  have hinj : Set.InjOn ν ((v' : Set (P.total.singularLocus K).blowup) ∩ ν ⁻¹' M) :=
    fun _ hy₁ _ _ heq ↦ P.total.eq_of_blowupToBase_singularLocus_eq_of_mem_smoothLocus heq
      (hMU hy₁.2)
  have himg : ν '' ((v' : Set (P.total.singularLocus K).blowup) ∩ ν ⁻¹' M) =
      (E : Set P.total) ∩ M := by
    rw [P.total.coe_blowupComponentEquiv _ v']
    ext x; simp only [mem_image, mem_inter_iff, mem_preimage]
    exact ⟨fun ⟨y, ⟨hyv, hyM⟩, hyx⟩ ↦ ⟨⟨y, hyv, hyx⟩, hyx ▸ hyM⟩,
      fun ⟨⟨y, hyv, hyx⟩, hxM⟩ ↦ ⟨y, ⟨hyv, hyx.symm ▸ hxM⟩, hyx⟩⟩
  rw [P.numMarkings_dualGraph_eq_ncard_inter_iUnion_marking v, ← himg, hinj.ncard_image]

/-- `valence v + numMarkings v` equals the number of points of `v` over nodes or markings. -/
theorem ncard_specialPoints_eq_valence_add_numMarkings (v : P.dualGraph.Vertex) :
    ((P.total.dualGraphVertexEquiv P.markingPoint v : Set (P.total.singularLocus K).blowup) ∩
      (P.total.singularLocus K).blowupToBase ⁻¹'
        (((P.total.singularLocus K).support : Set P.total) ∪
          ⋃ i, Set.range (P.marking i))).ncard =
      P.dualGraph.valence v + P.dualGraph.numMarkings v := by
  let hnodal := PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K))
  have := P.total.isFinite_blowupToBase_singularLocus hnodal
  have := P.total.isFinite_singularLocus_subschemeι_comp hnodal
  let Bl := (P.total.singularLocus K).blowup; let ν := (P.total.singularLocus K).blowupToBase
  let v' := P.total.dualGraphVertexEquiv P.markingPoint v
  let A : Set Bl := (v' : Set Bl) ∩ ν ⁻¹' ((P.total.singularLocus K).support : Set P.total)
  let B : Set Bl := (v' : Set Bl) ∩ ν ⁻¹' ⋃ i, Set.range (P.marking i)
  have hdisj : Disjoint A B := disjoint_left.mpr fun _ hyA hyB ↦ by
    have hSing := hyA.2
    rw [mem_preimage, P.total.support_singularLocus_eq_compl_smoothLocus, mem_compl_iff] at hSing
    obtain ⟨i, hi⟩ := mem_iUnion.mp hyB.2; exact hSing (P.range_marking_subset_smoothLocus i hi)
  have : Finite (P.total.singularLocus K).subscheme := Set.finite_univ_iff.mp
    (((P.total.singularLocus K).subschemeι ≫ (P.total ↘ Spec (.of K))).finite_preimage
      Set.finite_univ)
  have hA_fin : A.Finite := (ν.finite_preimage
    (Scheme.IdealSheafData.range_subschemeι _ ▸ Set.finite_range _)).subset inter_subset_right
  have hB_fin : B.Finite := (ν.finite_preimage (finite_iUnion fun i ↦ by
    rw [P.range_marking_eq_singleton i]; exact finite_singleton _)).subset inter_subset_right
  rw [preimage_union, inter_union_distrib_left, Set.ncard_union_eq hdisj hA_fin hB_fin,
    ← P.total.valence_dualGraph P.markingPoint v,
    ← P.numMarkings_dualGraph_eq_ncard_preimage_iUnion_marking v]

/-- Geometric formula for the log-canonical degree on a component `v`. -/
theorem logCanonicalDegree_dualGraph (v : P.dualGraph.Vertex) :
    P.dualGraph.logCanonicalDegree v =
      2 * ((P.total.blowupComponent
          (P.total.dualGraphVertexEquiv P.markingPoint v)).toScheme.genus K : ℤ) - 2 +
        (((P.total.dualGraphVertexEquiv P.markingPoint v :
            Set (P.total.singularLocus K).blowup) ∩
          (P.total.singularLocus K).blowupToBase ⁻¹'
            (((P.total.singularLocus K).support : Set P.total) ∪
              ⋃ i, Set.range (P.marking i))).ncard : ℤ) := by
  rw [P.ncard_specialPoints_eq_valence_add_numMarkings v, DualGraph.logCanonicalDegree_def,
    P.total.dualGraph_genus P.markingPoint v]
  omega

/-! ### Functoriality under curve isomorphisms and field extensions -/

variable {P} {Q R : PointedPrestableFamily (Spec (.of K)) n}

/-- An isomorphism `e : P ≅ Q` of pointed prestable curves induces an isomorphism of their dual
graphs. -/
def dualGraphIso (e : P ≅ Q) : P.dualGraph.Iso Q.dualGraph :=
  Scheme.dualGraphIsoOfIso (K := K)
    { hom := e.hom.hom, inv := e.inv.hom,
      hom_inv_id := congr(($e.hom_inv_id).hom), inv_hom_id := congr(($e.inv_hom_id).hom) }
    (by rw [Q.over_eq_toBase, P.over_eq_toBase]; exact e.hom.hom_comp_toBase)
    P.markingPoint Q.markingPoint fun i ↦ by
      dsimp only
      rw [coe_markingPoint, coe_markingPoint, ← Scheme.Hom.comp_apply, e.hom.marking_comp_hom]

@[simp]
theorem dualGraphIso_refl :
    dualGraphIso (CategoryTheory.Iso.refl P) = DualGraph.Iso.refl P.dualGraph := by
  rw [dualGraphIso]
  exact Scheme.dualGraphIsoOfIso_refl P.markingPoint

theorem dualGraphIso_symm (e : P ≅ Q) :
    dualGraphIso e.symm = (dualGraphIso e).symm := by
  simp only [dualGraphIso, ← Scheme.dualGraphIsoOfIso_symm]
  rfl

theorem dualGraphIso_trans (e : P ≅ Q) (e' : Q ≅ R) :
    dualGraphIso (e ≪≫ e') = (dualGraphIso e).trans (dualGraphIso e') := by
  simp only [dualGraphIso, ← Scheme.dualGraphIsoOfIso_trans]
  rfl

theorem dualGraph_isSemistable_iff_of_iso (e : P ≅ Q) :
    P.dualGraph.IsSemistable ↔ Q.dualGraph.IsSemistable := (dualGraphIso e).isSemistable_iff

theorem dualGraph_isStable_iff_of_iso (e : P ≅ Q) :
    P.dualGraph.IsStable ↔ Q.dualGraph.IsStable := (dualGraphIso e).isStable_iff

theorem dualGraph_arithmeticGenus_eq_of_iso (e : P ≅ Q) :
    P.dualGraph.arithmeticGenus = Q.dualGraph.arithmeticGenus := (dualGraphIso e).arithmeticGenus_eq

theorem dualGraph_firstBetti_eq_of_iso (e : P ≅ Q) :
    P.dualGraph.firstBetti = Q.dualGraph.firstBetti := (dualGraphIso e).firstBetti_eq

variable (P) in
/-- Invariance of `P.dualGraph` under extension of a separably closed base field. -/
def dualGraphPullbackIso (L : Type u) [Field L] [IsSepClosed L] [Algebra K L] :
    P.dualGraph.Iso (P.pullback (Spec.algebraMap K L)).dualGraph := by
  let g := Spec.algebraMap K L
  let : (Limits.pullback P.toBase g).Over (Spec (.of L)) := (P.pullback g).instOverTotal
  let : PrestableFamily ((Limits.pullback P.toBase g) ↘ Spec (.of L)) :=
    (P.pullback g).prestableFamily_over
  have H : IsPullback (Limits.pullback.fst P.toBase g) ((P.pullback g).total ↘ Spec (.of L))
      (P.total ↘ Spec (.of K)) g := by
    rw [(P.pullback g).over_eq_toBase, P.over_eq_toBase, pullback_toBase]
    exact IsPullback.of_hasPullback P.toBase g
  exact Scheme.dualGraphBaseChangeIso H P.markingPoint (P.pullback g).markingPoint fun i ↦ by
    rw [coe_markingPoint, P.coe_markingPoint_eq_apply i (g default)]
    exact (Scheme.Hom.comp_apply ((P.pullback g).marking i) _ default).symm.trans
      (congr($(P.pullback_marking_fst g i) default).trans (Scheme.Hom.comp_apply _ _ default))

theorem dualGraph_pullback_isSemistable_iff (L : Type u) [Field L] [IsSepClosed L] [Algebra K L] :
    (P.pullback (Spec.algebraMap K L)).dualGraph.IsSemistable ↔ P.dualGraph.IsSemistable :=
  (P.dualGraphPullbackIso L).isSemistable_iff.symm

theorem dualGraph_pullback_isStable_iff (L : Type u) [Field L] [IsSepClosed L] [Algebra K L] :
    (P.pullback (Spec.algebraMap K L)).dualGraph.IsStable ↔ P.dualGraph.IsStable :=
  (P.dualGraphPullbackIso L).isStable_iff.symm

@[simp]
theorem dualGraph_pullback_arithmeticGenus (L : Type u) [Field L] [IsSepClosed L] [Algebra K L] :
    (P.pullback (Spec.algebraMap K L)).dualGraph.arithmeticGenus = P.dualGraph.arithmeticGenus :=
  (P.dualGraphPullbackIso L).arithmeticGenus_eq.symm

@[simp]
theorem dualGraph_pullback_firstBetti (L : Type u) [Field L] [IsSepClosed L] [Algebra K L] :
    (P.pullback (Spec.algebraMap K L)).dualGraph.firstBetti = P.dualGraph.firstBetti :=
  (P.dualGraphPullbackIso L).firstBetti_eq.symm

/-- Log-canonical degree on the unique vertex of a smooth `n`-pointed prestable curve. -/
theorem logCanonicalDegree_ofSmooth {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]
    (s : Fin n → (Spec (.of K) ⟶ X)) (hs : ∀ i, s i ≫ f = 𝟙 (Spec (.of K)))
    (hdisj : Pairwise fun i j ↦ Disjoint (Set.range (s i)) (Set.range (s j)))
    (v : (ofSmooth f s hs hdisj).dualGraph.Vertex) :
    let P := ofSmooth f s hs hdisj
    haveI : SmoothOfRelativeDimension 1 (P.total ↘ Spec (.of K)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 f)
    P.dualGraph.logCanonicalDegree v = 2 * (P.total.genus K : ℤ) - 2 + n := by
  dsimp only
  let P := ofSmooth f s hs hdisj
  have : SmoothOfRelativeDimension 1 (P.total ↘ Spec (.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 f)
  rw [P.dualGraph.logCanonicalDegree_eq_of_forall_eq fun w ↦
      (P.total.subsingleton_vertex_dualGraph_of_smooth P.markingPoint).elim w v,
    Fintype.card_fin, P.total.arithmeticGenus_dualGraph_of_smooth P.markingPoint]

/-- Geometric classification of components of nonpositive log-canonical degree on a reducible
pointed prestable curve. -/
theorem dualGraph_logCanonicalDegree_nonpos_iff
    (P : PointedPrestableFamily (Spec (.of K)) n) {v : P.dualGraph.Vertex} (hw : ∃ w, w ≠ v) :
    let v' := P.total.dualGraphVertexEquiv P.markingPoint v
    let hnodal := PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K))
    P.dualGraph.logCanonicalDegree v ≤ 0 ↔
      (P.total.IsRationalTail K hnodal v' ∧ P.dualGraph.numMarkings v ≤ 1) ∨
      (P.total.IsRationalBridge K hnodal v' ∧
        ∀ i, Disjoint (Set.range (P.marking i))
          ((P.total.blowupComponentEquiv K hnodal v' : irreducibleComponents P.total) :
            Set P.total)) := by
  dsimp only
  let v' := P.total.dualGraphVertexEquiv P.markingPoint v
  let hnodal := PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K))
  have hmark (i : Fin n) : P.dualGraph.marking i ≠ v ↔ Disjoint (Set.range (P.marking i))
      ((P.total.blowupComponentEquiv K hnodal v' : irreducibleComponents P.total) : Set _) := by
    rw [ne_eq, P.dualGraph_marking_eq_iff i v, P.range_marking_eq_singleton i,
      singleton_subset_iff, disjoint_singleton_left]
  refine ⟨fun hv ↦ ?_, ?_⟩
  · rcases P.dualGraph.isRationalTail_or_isRationalBridge_of_logCanonicalDegree_nonpos hv hw with
      ⟨ht, hm⟩ | ⟨hb, hm⟩
    · exact .inl ⟨(P.total.dualGraph_isRationalTail_iff P.markingPoint v).mp ht, hm⟩
    · exact .inr ⟨(P.total.dualGraph_isRationalBridge_iff P.markingPoint v).mp hb,
        fun i ↦ (hmark i).mp (hm i)⟩
  · rintro (⟨ht, hm⟩ | ⟨hb, hm⟩)
    · have ht' : P.dualGraph.IsRationalTail v :=
        (P.total.dualGraph_isRationalTail_iff P.markingPoint v).mpr ht
      rw [ht'.logCanonicalDegree_eq]; omega
    · have hb' : P.dualGraph.IsRationalBridge v :=
        (P.total.dualGraph_isRationalBridge_iff P.markingPoint v).mpr hb
      rw [hb'.logCanonicalDegree_eq,
        P.dualGraph.numMarkings_eq_zero_iff.mpr fun i ↦ (hmark i).mpr (hm i)]; omega

end SepClosed

end PointedPrestableFamily

end TauCeti.AlgebraicGeometry
