/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.DualGraph
public import TauCeti.AlgebraicGeometry.Curves.PointedPrestable.Category

/-!
# The dual graph of a geometric pointed prestable curve

Let `P : PointedPrestableFamily (Spec (.of K)) n` be an `n`-pointed prestable curve over a
separably closed field `K`. Its total space `P.total` is proper, nodal of relative dimension one,
and geometrically connected over `Spec K` (hence connected), and its `n` sections `P.marking i`
evaluate at the unique point of `Spec K` to pairwise distinct smooth points `P.markingPoint i` of
`P.total`.

This file attaches to `P` its `Fin n`-marked dual graph `P.dualGraph : DualGraph (Fin n)` via
`AlgebraicGeometry.Scheme.markedDualGraph`, relates reindexing of markings on `P` to
`TauCeti.DualGraph.reindex`, identifies the total number `valence v + numMarkings v` of special
flags on a normalized component `v` with the number of points of `v` lying over nodes or markings
of `P`, establishes functorial isomorphisms of dual graphs under isomorphisms of pointed curves and
under arbitrary extensions `L / K` of separably closed fields, computes the dual graph and
log-canonical degree of a smooth pointed curve `PointedPrestableFamily.ofSmooth`, and translates the
numerical unstable-component classification into geometric rational tails and rational bridges.

## Main definitions

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.markingPoint`: the `i`-th smooth marked point
  of `P.total` over `Spec K`.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.dualGraph`: the `Fin n`-marked dual graph of a
  pointed prestable curve over a separably closed field.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.dualGraphReindexIso`: the canonical isomorphism
  `(P.reindex e).dualGraph.Iso (P.dualGraph.reindex e)` along `e : Fin m ↪ Fin n`.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.dualGraphIso`: the isomorphism of dual graphs
  induced by an isomorphism `P ≅ Q` of pointed prestable curves.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.dualGraphPullbackIso`: the isomorphism of dual
  graphs between `P` and its base change `P.pullback (Spec.algebraMap K L)` along an extension
  `L / K` of separably closed fields.

## Main results

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.ncard_specialPoints_eq_valence_add_numMarkings`
  and `TauCeti.AlgebraicGeometry.PointedPrestableFamily.logCanonicalDegree_dualGraph`: geometric
  formulas for the special flags and log-canonical degree `2g_v - 2 + #(special points on v)` on
  each normalized component.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.dualGraph_logCanonicalDegree_nonpos_iff`:
  on a reducible pointed prestable curve, any component of nonpositive log-canonical degree is a
  geometric rational tail carrying at most one marking or an unmarked geometric rational bridge.

## References

* F. F. Knudsen, *The projectivity of the moduli space of stable curves, II: The stacks
  `M_{g,n}`*, Math. Scand. 52 (1983), 161–199, Definition 1.1.
* E. Arbarello, M. Cornalba and P. A. Griffiths, *Geometry of Algebraic Curves, Volume II*,
  Chapter X, §2.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Set

namespace TauCeti.AlgebraicGeometry.PointedPrestableFamily

universe u

section OverBase

variable {S : Scheme.{u}} {n : ℕ} (P : PointedPrestableFamily S n)

instance isProper_over_total : IsProper (P.total ↘ S) := by
  rw [P.over_eq_toBase]; infer_instance

instance syntomicOfRelativeDimension_over_total :
    SyntomicOfRelativeDimension 1 (P.total ↘ S) := by
  rw [P.over_eq_toBase]; exact P.prestableFamily.syntomic

instance geometricallyConnected_over_total :
    GeometricallyConnected (P.total ↘ S) := by
  rw [P.over_eq_toBase]; infer_instance

/-- The over-base structure morphism `P.total ↘ S` is at-worst-nodal of relative dimension one. -/
theorem atWorstNodalOfRelativeDimensionOne_over_total :
    AtWorstNodalOfRelativeDimensionOne (P.total ↘ S) := by
  rw [P.over_eq_toBase]; exact P.prestableFamily.atWorstNodalOfRelativeDimensionOne

theorem smoothLocus_over_total : (P.total ↘ S).smoothLocus = P.toBase.smoothLocus := by
  have aux : ∀ (f : P.total ⟶ S) [LocallyOfFinitePresentation f],
      f = P.toBase → f.smoothLocus = P.toBase.smoothLocus := by
    rintro f _ rfl; rfl
  exact aux (P.total ↘ S) P.over_eq_toBase

end OverBase

section OverField

variable {K : Type u} [Field K] {n : ℕ} (P : PointedPrestableFamily (Spec (.of K)) n)

/-- The total space of a pointed prestable curve over a field is connected, since the structure
morphism is geometrically connected over a one-point base. -/
instance connectedSpace_total_of_field : ConnectedSpace P.total :=
  GeometricallyConnected.connectedSpace_of_subsingleton (f := P.toBase)

/-- The `i`-th marked point of a pointed prestable curve over `Spec K`, viewed in the smooth locus
of `P.total ↘ Spec K`. -/
def markingPoint (i : Fin n) : (P.total ↘ Spec (.of K)).smoothLocus :=
  let ptK : Spec (.of K) := IsLocalRing.closedPoint K
  ⟨P.marking i ptK, by
    rw [P.smoothLocus_over_total]
    exact P.range_marking_subset_smoothLocus i ⟨ptK, rfl⟩⟩

theorem coe_markingPoint_eq_apply (i : Fin n) (s : Spec (.of K)) :
    (P.markingPoint i).1 = P.marking i s :=
  congrArg (P.marking i) (Subsingleton.elim _ s)

/-- Distinct markings give distinct points of the smooth locus. -/
theorem injective_markingPoint : Function.Injective P.markingPoint := by
  intro i j hij
  let ptK : Spec (.of K) := IsLocalRing.closedPoint K
  by_contra hne
  have hval := congrArg Subtype.val hij
  rw [P.coe_markingPoint_eq_apply i ptK, P.coe_markingPoint_eq_apply j ptK] at hval
  exact P.marking_apply_ne hne ptK hval

/-- Over `Spec K`, the image of the `i`-th marking section is the singleton
`{(P.markingPoint i).1}`. -/
theorem range_marking_eq_singleton (i : Fin n) :
    Set.range (P.marking i) = {(P.markingPoint i).1} := by
  let ptK : Spec (.of K) := IsLocalRing.closedPoint K
  ext x
  rw [mem_range, mem_singleton_iff, P.coe_markingPoint_eq_apply i ptK]
  exact ⟨fun ⟨s, hs⟩ ↦ hs ▸ congrArg (P.marking i) (Subsingleton.elim s ptK),
    fun hx ↦ ⟨ptK, hx.symm⟩⟩

end OverField

section SepClosed

variable {K : Type u} [Field K] [IsSepClosed K] {n : ℕ}
  (P : PointedPrestableFamily (Spec (.of K)) n)

/-- **The dual graph of an `n`-pointed prestable curve over a separably closed field.** -/
abbrev dualGraph : DualGraph.{u, 0} (Fin n) :=
  P.total.markedDualGraph K P.atWorstNodalOfRelativeDimensionOne_over_total P.markingPoint

/-- Reindexing the markings of `P` along `e : Fin m ↪ Fin n` induces a canonical isomorphism from
`(P.reindex e).dualGraph` to `P.dualGraph.reindex e`. -/
def dualGraphReindexIso {m : ℕ} (e : Fin m ↪ Fin n) :
    (P.reindex e).dualGraph.Iso (P.dualGraph.reindex e) :=
  @Scheme.markedDualGraphIsoOfOverIso K _ _
    (P.reindex e).total (P.reindex e).instOverTotal
    (P.reindex e).isProper_over_total (P.reindex e).connectedSpace_total_of_field
    P.total P.instOverTotal P.isProper_over_total P.connectedSpace_total_of_field
    (P.reindex e).atWorstNodalOfRelativeDimensionOne_over_total
    P.atWorstNodalOfRelativeDimensionOne_over_total
    (Iso.refl P.total)
    (by
      change 𝟙 P.total ≫ ((P.reindex e).total ↘ Spec (.of K)) = P.total ↘ Spec (.of K)
      rw [(P.reindex e).over_eq_toBase, P.over_eq_toBase]
      exact Category.id_comp P.toBase)
    (Fin m)
    (P.reindex e).markingPoint (P.markingPoint ∘ e)
    fun i ↦ by
      let ptK : Spec (.of K) := IsLocalRing.closedPoint K
      change (P.markingPoint (e i)).1 = ((P.reindex e).markingPoint i).1
      rw [P.coe_markingPoint_eq_apply (e i) ptK, (P.reindex e).coe_markingPoint_eq_apply i ptK]
      rfl

theorem dualGraph_genus (v : P.dualGraph.Vertex) :
    P.dualGraph.genus v =
      P.total.componentGenus K P.atWorstNodalOfRelativeDimensionOne_over_total v :=
  (rfl)

/-- A component `v` carries the `i`-th marking in `P.dualGraph` if and only if the image of the
`i`-th marking section is contained in the corresponding irreducible component of `P.total`. -/
theorem dualGraph_marking_eq_iff (i : Fin n) (v : P.dualGraph.Vertex) :
    P.dualGraph.marking i = v ↔
      Set.range (P.marking i) ⊆
        ((P.total.blowupComponentEquiv K P.atWorstNodalOfRelativeDimensionOne_over_total v :
            irreducibleComponents P.total) : Set P.total) := by
  rw [P.total.markedDualGraph_marking_eq_iff P.atWorstNodalOfRelativeDimensionOne_over_total
      P.markingPoint i v,
    P.range_marking_eq_singleton i, singleton_subset_iff]

/-- The number of markings carried by `v` equals the number of marked points lying on the
corresponding irreducible component of `P.total`. -/
theorem numMarkings_dualGraph_eq_ncard_inter_iUnion_marking (v : P.dualGraph.Vertex) :
    let E := P.total.blowupComponentEquiv K P.atWorstNodalOfRelativeDimensionOne_over_total v
    P.dualGraph.numMarkings v = ((E : Set P.total) ∩ ⋃ i, Set.range (P.marking i)).ncard := by
  classical
  dsimp only
  let hnodal := P.atWorstNodalOfRelativeDimensionOne_over_total
  let E := P.total.blowupComponentEquiv K hnodal v
  let S : Finset (Fin n) := Finset.univ.filter fun i ↦ P.dualGraph.marking i = v
  have himg : (Subtype.val ∘ P.markingPoint) '' (S : Set (Fin n)) =
      (E : Set P.total) ∩ ⋃ i, Set.range (P.marking i) := by
    ext x
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, mem_image,
      Function.comp_apply, mem_inter_iff, mem_iUnion, P.range_marking_eq_singleton,
      mem_singleton_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(P.total.markedDualGraph_marking_eq_iff hnodal P.markingPoint i v).mp hi, i, rfl⟩
    · rintro ⟨hxE, i, rfl⟩
      exact ⟨i, (P.total.markedDualGraph_marking_eq_iff hnodal P.markingPoint i v).mpr hxE, rfl⟩
  rw [DualGraph.numMarkings_def, ← himg,
    Set.ncard_image_of_injective (S : Set (Fin n))
      (Subtype.val_injective.comp P.injective_markingPoint),
    Set.ncard_coe_finset]
  congr 1
  ext i
  simp [S]

/-- The number of markings carried by `v` equals the number of points of `v` in the singular-locus
blowup lying over the union of the markings. -/
theorem numMarkings_dualGraph_eq_ncard_preimage_iUnion_marking (v : P.dualGraph.Vertex) :
    P.dualGraph.numMarkings v =
      ((v : Set (P.total.singularLocus K).blowup) ∩
        (P.total.singularLocus K).blowupToBase ⁻¹' ⋃ i, Set.range (P.marking i)).ncard := by
  let hnodal := P.atWorstNodalOfRelativeDimensionOne_over_total
  let ν := (P.total.singularLocus K).blowupToBase
  let E := P.total.blowupComponentEquiv K hnodal v
  let M : Set P.total := ⋃ i, Set.range (P.marking i)
  have hMU : M ⊆ (P.total ↘ Spec (.of K)).smoothLocus := by
    refine iUnion_subset fun i ↦ ?_
    rw [P.smoothLocus_over_total]
    exact P.range_marking_subset_smoothLocus i
  have hinj : Set.InjOn ν ((v : Set (P.total.singularLocus K).blowup) ∩ ν ⁻¹' M) :=
    fun y₁ hy₁ y₂ _ heq ↦
      Scheme.eq_of_blowupToBase_eq_of_mem_smoothLocus hnodal heq (hMU hy₁.2)
  have himg : ν '' ((v : Set (P.total.singularLocus K).blowup) ∩ ν ⁻¹' M) =
      (E : Set P.total) ∩ M := by
    rw [show (E : Set P.total) = ν '' (v : Set (P.total.singularLocus K).blowup) from
      P.total.coe_blowupComponentEquiv hnodal v]
    ext x
    simp only [mem_image, mem_inter_iff, mem_preimage]
    refine ⟨?_, ?_⟩
    · rintro ⟨y, ⟨hyv, hyM⟩, rfl⟩
      exact ⟨⟨y, hyv, rfl⟩, hyM⟩
    · rintro ⟨⟨y, hyv, rfl⟩, hxM⟩
      exact ⟨y, ⟨hyv, hxM⟩, rfl⟩
  rw [P.numMarkings_dualGraph_eq_ncard_inter_iUnion_marking v]
  dsimp only
  rw [← himg, hinj.ncard_image]

/-- **Special flags on a normalized component.** The total number `valence v + numMarkings v` of
special flags on a component `v` equals the number of points of `v` lying over either the singular
locus or the marked sections of `P`. -/
theorem ncard_specialPoints_eq_valence_add_numMarkings (v : P.dualGraph.Vertex) :
    ((v : Set (P.total.singularLocus K).blowup) ∩
      (P.total.singularLocus K).blowupToBase ⁻¹'
        (((P.total.singularLocus K).support : Set P.total) ∪
          ⋃ i, Set.range (P.marking i))).ncard =
      P.dualGraph.valence v + P.dualGraph.numMarkings v := by
  let hnodal := P.atWorstNodalOfRelativeDimensionOne_over_total
  have := P.total.isFinite_blowupToBase_singularLocus hnodal
  have := P.total.isFinite_singularLocus_subschemeι_comp hnodal
  have := P.total.etale_singularLocus_subschemeι_comp hnodal
  let Bl := (P.total.singularLocus K).blowup
  let ν := (P.total.singularLocus K).blowupToBase
  let A : Set Bl := (v : Set Bl) ∩ ν ⁻¹' ((P.total.singularLocus K).support : Set P.total)
  let B : Set Bl := (v : Set Bl) ∩ ν ⁻¹' ⋃ i, Set.range (P.marking i)
  have hdisj : Disjoint A B := by
    refine disjoint_left.mpr fun y hyA hyB ↦ ?_
    have hSing := hyA.2
    rw [mem_preimage, P.total.support_singularLocus_eq_compl_smoothLocus, mem_compl_iff,
      P.smoothLocus_over_total] at hSing
    obtain ⟨i, hi⟩ := mem_iUnion.mp hyB.2
    exact hSing (P.range_marking_subset_smoothLocus i hi)
  have hA_fin : A.Finite := by
    have : Finite (P.total.singularLocus K).subscheme :=
      Scheme.finite_of_isFinite_of_etale
        ((P.total.singularLocus K).subschemeι ≫ (P.total ↘ Spec (.of K)))
    have hsupp_fin : ((P.total.singularLocus K).support : Set P.total).Finite := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact Set.finite_range _
    exact (ν.finite_preimage hsupp_fin).subset inter_subset_right
  have hB_fin : B.Finite := by
    have hM_fin : (⋃ i, Set.range (P.marking i)).Finite :=
      finite_iUnion fun i ↦ by rw [P.range_marking_eq_singleton i]; exact finite_singleton _
    exact (ν.finite_preimage hM_fin).subset inter_subset_right
  have hunion : (v : Set Bl) ∩ ν ⁻¹'
      (((P.total.singularLocus K).support : Set P.total) ∪
        ⋃ i, Set.range (P.marking i)) = A ∪ B := by
    rw [preimage_union, inter_union_distrib_left]
  rw [hunion, Set.ncard_union_eq hdisj hA_fin hB_fin,
    ← P.total.valence_markedDualGraph hnodal P.markingPoint v,
    ← P.numMarkings_dualGraph_eq_ncard_preimage_iUnion_marking v]

/-- **Geometric formula for the log-canonical degree on a component.** -/
theorem logCanonicalDegree_dualGraph (v : P.dualGraph.Vertex) :
    P.dualGraph.logCanonicalDegree v =
      2 * (P.total.componentGenus K P.atWorstNodalOfRelativeDimensionOne_over_total v : ℤ) -
        2 +
        (((v : Set (P.total.singularLocus K).blowup) ∩
          (P.total.singularLocus K).blowupToBase ⁻¹'
            (((P.total.singularLocus K).support : Set P.total) ∪
              ⋃ i, Set.range (P.marking i))).ncard : ℤ) := by
  rw [P.ncard_specialPoints_eq_valence_add_numMarkings v, DualGraph.logCanonicalDegree_def,
    dualGraph_genus]
  omega

/-! ### Functoriality under curve isomorphisms and field extensions -/

variable {P} {Q : PointedPrestableFamily (Spec (.of K)) n}

/-- **An isomorphism of pointed prestable curves induces an isomorphism of their dual graphs.** -/
def dualGraphIso (e : P ≅ Q) : P.dualGraph.Iso Q.dualGraph :=
  P.total.markedDualGraphIsoOfOverIso
    P.atWorstNodalOfRelativeDimensionOne_over_total
    Q.atWorstNodalOfRelativeDimensionOne_over_total
    { hom := e.inv.hom
      inv := e.hom.hom
      hom_inv_id := congr(($e.inv_hom_id).hom)
      inv_hom_id := congr(($e.hom_inv_id).hom) }
    (by rw [P.over_eq_toBase, Q.over_eq_toBase]; exact e.inv.hom_comp_toBase)
    P.markingPoint Q.markingPoint
    fun i ↦ by
      let ptK : Spec (.of K) := IsLocalRing.closedPoint K
      change e.inv.hom (Q.markingPoint i).1 = (P.markingPoint i).1
      rw [Q.coe_markingPoint_eq_apply i ptK, P.coe_markingPoint_eq_apply i ptK,
        ← Scheme.Hom.comp_apply, e.inv.marking_comp_hom]

theorem dualGraph_isSemistable_iff_of_iso (e : P ≅ Q) :
    P.dualGraph.IsSemistable ↔ Q.dualGraph.IsSemistable :=
  (dualGraphIso e).isSemistable_iff

theorem dualGraph_isStable_iff_of_iso (e : P ≅ Q) :
    P.dualGraph.IsStable ↔ Q.dualGraph.IsStable :=
  (dualGraphIso e).isStable_iff

theorem dualGraph_arithmeticGenus_eq_of_iso (e : P ≅ Q) :
    P.dualGraph.arithmeticGenus = Q.dualGraph.arithmeticGenus :=
  (dualGraphIso e).arithmeticGenus_eq

theorem dualGraph_firstBetti_eq_of_iso (e : P ≅ Q) :
    P.dualGraph.firstBetti = Q.dualGraph.firstBetti :=
  (dualGraphIso e).firstBetti_eq

variable (P) in
/-- **Invariance of the dual graph of a pointed prestable curve under extension of a separably
closed base field.** -/
def dualGraphPullbackIso (L : Type u) [Field L] [IsSepClosed L] [Algebra K L] :
    P.dualGraph.Iso (P.pullback (Spec.algebraMap K L)).dualGraph := by
  let g := Spec.algebraMap K L
  let : (Limits.pullback P.toBase g).Over (Spec (.of L)) := (P.pullback g).instOverTotal
  have H : IsPullback (Limits.pullback.fst P.toBase g)
      ((P.pullback g).total ↘ Spec (.of L))
      (P.total ↘ Spec (.of K)) g := by
    rw [(P.pullback g).over_eq_toBase, P.over_eq_toBase, pullback_toBase]
    exact IsPullback.of_hasPullback P.toBase g
  exact P.total.markedDualGraphBaseChangeIso
    P.atWorstNodalOfRelativeDimensionOne_over_total H P.markingPoint
    (P.pullback g).markingPoint fun i ↦ by
      let ptL : Spec (.of L) := IsLocalRing.closedPoint L
      let ptK : Spec (.of K) := IsLocalRing.closedPoint K
      have hfst : Limits.pullback.fst P.toBase g ((P.pullback g).marking i ptL) =
          P.marking i (g ptL) :=
        (Scheme.Hom.comp_apply ((P.pullback g).marking i)
          (Limits.pullback.fst P.toBase g) ptL).symm.trans
          (congr($(P.pullback_marking_fst g i) ptL).trans
            (Scheme.Hom.comp_apply g (P.marking i) ptL))
      rw [(P.pullback g).coe_markingPoint_eq_apply i ptL, P.coe_markingPoint_eq_apply i ptK, hfst]
      exact congrArg (P.marking i) (Subsingleton.elim _ _)

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

/-! ### Smooth pointed curves and geometric classification of unstable components -/

/-- For a smooth `n`-pointed proper connected curve `X` over `K`, the log-canonical degree on its
unique dual-graph vertex is `2 * (X.genus K) - 2 + n`. -/
theorem logCanonicalDegree_ofSmooth {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]
    (s : Fin n → (Spec (.of K) ⟶ X)) (hs : ∀ i, s i ≫ f = 𝟙 (Spec (.of K)))
    (hdisj : Pairwise fun i j ↦ Disjoint (Set.range (s i)) (Set.range (s j)))
    (v : (ofSmooth f s hs hdisj).dualGraph.Vertex) :
    let P := ofSmooth f s hs hdisj
    letI : X.Over (Spec (.of K)) := P.instOverTotal
    haveI : IsProper (X ↘ Spec (.of K)) := P.isProper_over_total
    haveI : ConnectedSpace X := P.connectedSpace_total_of_field
    haveI : SmoothOfRelativeDimension 1 (X ↘ Spec (.of K)) :=
      (P.over_eq_toBase.trans (ofSmooth_toBase f s hs hdisj)).symm ▸ inferInstance
    haveI : (InvertibleSheaf.trivial X).obj.IsFinitePresentation :=
      ((InvertibleSheaf.toFinitelyPresented X).obj (InvertibleSheaf.trivial X)).property
    haveI := Scheme.Modules.finiteDimensional_cohomology_of_smooth K
      (InvertibleSheaf.trivial X).obj 1
    P.dualGraph.logCanonicalDegree v = 2 * (X.genus K : ℤ) - 2 + n := by
  dsimp only
  let P := ofSmooth f s hs hdisj
  let : X.Over (Spec (.of K)) := P.instOverTotal
  have : IsProper (X ↘ Spec (.of K)) := P.isProper_over_total
  have : ConnectedSpace X := P.connectedSpace_total_of_field
  have : SmoothOfRelativeDimension 1 (X ↘ Spec (.of K)) :=
    (P.over_eq_toBase.trans (ofSmooth_toBase f s hs hdisj)).symm ▸ inferInstance
  have : (InvertibleSheaf.trivial X).obj.IsFinitePresentation :=
    ((InvertibleSheaf.toFinitelyPresented X).obj (InvertibleSheaf.trivial X)).property
  have := Scheme.Modules.finiteDimensional_cohomology_of_smooth K
    (InvertibleSheaf.trivial X).obj 1
  have hsub := X.subsingleton_vertex_markedDualGraph_of_smooth (K := K) P.markingPoint
  have hg : P.dualGraph.arithmeticGenus = X.genus K :=
    X.arithmeticGenus_markedDualGraph_of_smooth (K := K) P.markingPoint
  rw [P.dualGraph.logCanonicalDegree_eq_of_forall_eq fun w ↦ hsub.elim w v, Fintype.card_fin, hg]

/-- **Geometric classification of components of nonpositive log-canonical degree.** On a pointed
prestable curve `P` with at least one component distinct from `v`,
`P.dualGraph.logCanonicalDegree v ≤ 0` holds if and only if `v` is either a geometric rational tail
carrying at most one marking or a geometric rational bridge disjoint from every marking. -/
theorem dualGraph_logCanonicalDegree_nonpos_iff
    (P : PointedPrestableFamily (Spec (.of K)) n) {v : P.dualGraph.Vertex}
    (hw : ∃ w, w ≠ v) :
    P.dualGraph.logCanonicalDegree v ≤ 0 ↔
      (P.total.IsRationalTail K P.atWorstNodalOfRelativeDimensionOne_over_total v ∧
        P.dualGraph.numMarkings v ≤ 1) ∨
      (P.total.IsRationalBridge K P.atWorstNodalOfRelativeDimensionOne_over_total v ∧
        ∀ i, Disjoint (Set.range (P.marking i))
          ((P.total.blowupComponentEquiv K P.atWorstNodalOfRelativeDimensionOne_over_total v :
              irreducibleComponents P.total) : Set P.total)) := by
  let hnodal := P.atWorstNodalOfRelativeDimensionOne_over_total
  have hmark (i : Fin n) : P.dualGraph.marking i ≠ v ↔
      Disjoint (Set.range (P.marking i))
        ((P.total.blowupComponentEquiv K hnodal v : irreducibleComponents P.total) :
          Set P.total) := by
    rw [ne_eq, P.dualGraph_marking_eq_iff i v, P.range_marking_eq_singleton i,
      singleton_subset_iff, disjoint_singleton_left]
  refine ⟨fun hv ↦ ?_, ?_⟩
  · rcases P.dualGraph.isRationalTail_or_isRationalBridge_of_logCanonicalDegree_nonpos hv hw with
      ⟨ht, hm⟩ | ⟨hb, hm⟩
    · exact .inl ⟨(P.total.markedDualGraph_isRationalTail_iff hnodal P.markingPoint v).mp ht, hm⟩
    · exact .inr ⟨(P.total.markedDualGraph_isRationalBridge_iff hnodal P.markingPoint v).mp hb,
        fun i ↦ (hmark i).mp (hm i)⟩
  · rintro (⟨ht, hm⟩ | ⟨hb, hm⟩)
    · have ht' : P.dualGraph.IsRationalTail v :=
        (P.total.markedDualGraph_isRationalTail_iff hnodal P.markingPoint v).mpr ht
      rw [ht'.logCanonicalDegree_eq]
      omega
    · have hb' : P.dualGraph.IsRationalBridge v :=
        (P.total.markedDualGraph_isRationalBridge_iff hnodal P.markingPoint v).mpr hb
      have hm₀ : P.dualGraph.numMarkings v = 0 :=
        P.dualGraph.numMarkings_eq_zero_iff.mpr fun i ↦ (hmark i).mpr (hm i)
      rw [hb'.logCanonicalDegree_eq, hm₀]
      omega

end SepClosed

end TauCeti.AlgebraicGeometry.PointedPrestableFamily
